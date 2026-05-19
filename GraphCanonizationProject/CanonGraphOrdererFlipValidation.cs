using System;
using System.Collections.Generic;
using System.Linq;

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    // Flip-validation canonizer: a two-pass design aimed at polynomial worst-
    // case time. See docs/flip-validation-strategy.md for the full design.
    //
    // ── Algorithm at a glance ────────────────────────────────────────────────
    //   Forward pass (greedy): at each step pick one single-pair guess
    //     (within-cell if any cell has an internal Unknown pair, else
    //     between-cell on a P-incomparable cell pair) by a lex-min-by-index
    //     rule, write it into P, transitively close, push a Primary record
    //     with the at-guess-time cell snapshot. Repeat until P is total.
    //   Backward pass (§6.5 eager rotation): walk the primary stack deepest
    //     to shallowest. For each primary i, enumerate branches over
    //     {direction × a' ∈ CellSnapshotA × b' ∈ CellSnapshotB}, replay
    //     each branch through prefix + deeper + ContinueForward, lex-min
    //     over the resulting canonicals, adopt the winner.
    //   Fixpoint iteration: adopting at a shallow primary replaces deeper
    //     primaries with fresh ones (from ContinueForward) that haven't
    //     been backward-processed. The backward pass is iterated until a
    //     sweep adopts zero branches; termination follows from canonical-
    //     lex monotonicity.
    //
    // ── v1 simplifications (see §10/§11 of the strategy doc) ────────────────
    //   - DERIVED closure records are not tracked; transitive closure is
    //     re-run from scratch on each replay. Constant-factor cost increase,
    //     polynomial preserved.
    //   - When a shallow change invalidates a deeper guess's pair,
    //     TryReplayWithDeeper bails out and re-runs ContinueForward from the
    //     breakage. The surgical "detect-and-redo only affected locks"
    //     fallback from §6.3 is deferred to a later version.
    //   - The §3.6 transposition test as a fast path is omitted; eager
    //     enumeration covers its case as one branch among many.
    //
    // ── Diagnostic counters ─────────────────────────────────────────────────
    //   Public properties below are updated by Run() and reflect the LAST
    //   run, cumulative across forward pass plus backward-pass sweeps.
    //   LastLockedThenInvalidated is the §9 most-diagnostic counter.
    public sealed class CanonGraphOrdererFlipValidation : ICanonGraphOrderer
    {
        private const sbyte LESS = -1, UNKNOWN = 0, GREATER = 1;

        // Diagnostic counters from the last Run() call.
        public int LastPrimaryCount { get; private set; }
        public int LastWithinCellGuesses { get; private set; }
        public int LastBetweenCellGuesses { get; private set; }
        public int LastBackwardFlips { get; private set; }
        public int LastPairRotationsAttempted { get; private set; }
        public int LastLockedThenInvalidated { get; private set; }

        // Per-primary branch-distinctness instrumentation for §11.10 calculator
        // viability study. When CollectBranchStats is true, the backward pass
        // records (CellSizeA, CellSizeB, BranchCount, DistinctCanonicalCount)
        // for every primary visited in every sweep. DistinctCanonicalCount is
        // the number of distinct permuted-adjacency-matrix outcomes among the
        // branches enumerated at that primary (including the baseline). If
        // distinct-count stays small relative to branch-count across input
        // families, route 1 (equivalence-detection sharing) is structurally
        // viable.
        public bool CollectBranchStats { get; set; }
        public List<BranchStats>? LastBranchStats { get; private set; }

        // L4.3 (single-pass equivalence) test harness. When true, Run() stops
        // after one backward-pass sweep regardless of whether adoption occurred,
        // skipping the fixpoint iteration that the current implementation
        // requires. If the resulting canonical matches the fixpoint canonical
        // across all inputs, deeper primaries are determined by shallower
        // primaries + branch (the local-cascade-dependence conjecture), and
        // the calculator can be designed as a single-pass evaluator.
        public bool SkipFixpoint { get; set; }
        public int LastSweepCount { get; private set; }

        // L4.3-memo-polynomial instrumentation. When true, hash every distinct
        // intermediate P-state encountered across all backward-pass branch
        // evaluations (including the continuations spawned by ContinueForward).
        // LastDistinctStateCount is the size of the resulting set — a direct
        // empirical estimate of the DP memo size if the calculator were
        // implemented as bottom-up dynamic programming over P-states.
        public bool CollectStateCount { get; set; }
        public int LastDistinctStateCount { get; private set; }
        private HashSet<ulong>? _stateHashes;

        public readonly struct BranchStats(
            int sweep, int primary, int cellA, int cellB,
            int branches, int distinct)
        {
            public int SweepIndex { get; } = sweep;
            public int PrimaryIndex { get; } = primary;
            public int CellSizeA { get; } = cellA;
            public int CellSizeB { get; } = cellB;
            public int BranchCount { get; } = branches;
            public int DistinctCanonicalCount { get; } = distinct;
        }

        public AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            int n = G.VertexCount;
            int[] adj = ExtractAdj(G);

            LastWithinCellGuesses = 0;
            LastBetweenCellGuesses = 0;
            LastBackwardFlips = 0;
            LastPairRotationsAttempted = 0;
            LastLockedThenInvalidated = 0;
            LastBranchStats = CollectBranchStats ? [] : null;
            _stateHashes = CollectStateCount ? [] : null;
            LastDistinctStateCount = 0;

            // Forward pass. Partition is warm-refined at every state-mutation
            // point (see ContinueForward / PickAndApplyGuess) so each refine
            // call starts from a partition that's at most one ApplyOne stale.
            sbyte[] p = SeedFromTypes(n, vertexTypes);
            var partition = new WarmPartition(n);
            List<Primary> record = ContinueForward(n, adj, p, partition);

            // Backward pass to fixpoint. A single deepest-first sweep optimizes
            // each primary against its forward-pass snapshot, but adopting a
            // branch at a shallow primary replaces deeper primaries with fresh
            // ones from ContinueForward (in TryReplayWithDeeper) that haven't
            // been backward-processed. Iterating until no branch is adopted
            // gives every deeper primary a chance. Termination: each adoption
            // strictly decreases the canonical lex-value, and canonicals form a
            // finite set. The dependency calculator (§11.10) replaces this
            // with a one-shot diagram read.
            int prevFlips;
            int sweepIndex = 0;
            do
            {
                prevFlips = LastBackwardFlips;
                record = BackwardPass(n, adj, vertexTypes, record, sweepIndex);
                sweepIndex++;
                if (SkipFixpoint) break;
            } while (LastBackwardFlips > prevFlips);
            LastSweepCount = sweepIndex;
            LastDistinctStateCount = _stateHashes?.Count ?? 0;
            LastPrimaryCount = record.Count;

            // Replay the (possibly updated) record and read off the canonical
            // form.
            sbyte[] pFinal = ReplayRecord(n, vertexTypes, record, record.Count)
                ?? throw new InvalidOperationException(
                    "FlipValidation: final replay produced a contradiction");
            if (!IsTotal(n, pFinal))
                throw new InvalidOperationException("FlipValidation: final P not total");

            return PermuteByPartialOrder(G, pFinal, n);
        }

        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // ── Internal record ──────────────────────────────────────────────────

        private struct Primary
        {
            public int A, B;
            public sbyte Direction;   // LESS (A<B) or GREATER (A>B)
            public bool BetweenCell;  // false = within-cell, true = between-cell

            // Cell-tree fragment captured at guess time (§3.5). CellSnapshotA
            // is the membership of A's cell *before* this guess was applied;
            // CellSnapshotB is B's. For within-cell guesses the two arrays
            // point to the same instance. §6.5's backward-pass rotation
            // enumerates (a' ∈ CellSnapshotA) × (b' ∈ CellSnapshotB).
            public int[] CellSnapshotA;
            public int[] CellSnapshotB;
        }

        // ── Forward pass ─────────────────────────────────────────────────────

        // Walk P toward total via single-pair guesses; mutate p (and partition),
        // return the primaries pushed (in order).
        private List<Primary> ContinueForward(int n, int[] adj, sbyte[] p, WarmPartition partition)
        {
            var record = new List<Primary>();
            while (!IsTotal(n, p))
            {
                if (!PickAndApplyGuess(n, adj, p, partition, record))
                    throw new InvalidOperationException(
                        "FlipValidation: P not total but no guess candidate found");
            }
            return record;
        }

        // Pick the next primary guess (within-cell first, else between-cell),
        // apply it to p (mutating partition to match), and push onto record.
        // Returns false only if there really is no candidate, which is a bug
        // given P is not total.
        private bool PickAndApplyGuess(int n, int[] adj, sbyte[] p, WarmPartition partition,
                                       List<Primary> record)
        {
            // Warm-refine the partition to current P state. Partition is
            // expected to be at most one-ApplyOne stale; warm-refine converges
            // in a few rounds typically.
            partition.Refine(adj, p);
            int[] cellOf = partition.CellOf;
            int numCells = partition.NumCells;

            var cells = new List<List<int>>(numCells);
            for (int c = 0; c < numCells; c++) cells.Add(new List<int>());
            for (int v = 0; v < n; v++) cells[cellOf[v]].Add(v);

            if (TryFindWithinCellGuess(n, p, cells, numCells, out int a, out int b))
            {
                var snap = cells[cellOf[a]].ToArray();
                var prim = new Primary
                {
                    A = a, B = b, Direction = LESS, BetweenCell = false,
                    CellSnapshotA = snap, CellSnapshotB = snap,
                };
                if (!ApplyOne(p, n, prim))
                    throw new InvalidOperationException(
                        "FlipValidation: within-cell guess produced a contradiction");
                record.Add(prim);
                LastWithinCellGuesses++;
                return true;
            }

            if (TryFindBetweenCellGuess(n, p, cellOf, cells, numCells, out a, out b))
            {
                var snapA = cells[cellOf[a]].ToArray();
                var snapB = cells[cellOf[b]].ToArray();
                var prim = new Primary
                {
                    A = a, B = b, Direction = LESS, BetweenCell = true,
                    CellSnapshotA = snapA, CellSnapshotB = snapB,
                };
                if (!ApplyOne(p, n, prim))
                    return false; // contradiction on between-cell closure; caller decides
                record.Add(prim);
                LastBetweenCellGuesses++;
                return true;
            }

            return false;
        }

        // Lex-min cell (by canonical id) that holds an internal Unknown pair;
        // within it, lex-min (a, b) by vertex index.
        //
        // This rule is NOT iso-invariant on cells that contain multiple pair-
        // orbits — different input scramblings can pick representatives in
        // different pair-orbits and the backward pass cannot recover from
        // that with direction flips alone. See the strategy doc §6.1 / §11
        // for the limitation; the planned future mechanism is to ensure
        // every canonical form is reachable from any pair selection (the
        // "one guess per symmetry" invariant), which is not yet
        // implemented. The current rule is left simple on purpose so that
        // the failure pattern is visible in the test bed.
        private static bool TryFindWithinCellGuess(int n, sbyte[] p,
                                                   List<List<int>> cells, int numCells,
                                                   out int a, out int b)
        {
            a = -1; b = -1;
            for (int c = 0; c < numCells; c++)
            {
                var mem = cells[c];
                if (mem.Count < 2) continue;
                for (int i = 0; i < mem.Count; i++)
                    for (int j = i + 1; j < mem.Count; j++)
                        if (p[mem[i] * n + mem[j]] == UNKNOWN)
                        {
                            a = mem[i]; b = mem[j];
                            return true;
                        }
            }
            return false;
        }

        // Lex-min P-incomparable cell pair (by canonical cell id), then lex-min
        // representative pair (x, y) within it by vertex index. Same iso-
        // invariance limitation as the within-cell case.
        private static bool TryFindBetweenCellGuess(int n, sbyte[] p, int[] cellOf,
                                                    List<List<int>> cells, int numCells,
                                                    out int a, out int b)
        {
            int bestCA = -1, bestCB = -1;
            for (int u = 0; u < n; u++)
                for (int v = 0; v < n; v++)
                {
                    if (cellOf[u] == cellOf[v] || p[u * n + v] != UNKNOWN) continue;
                    int c1 = Math.Min(cellOf[u], cellOf[v]);
                    int c2 = Math.Max(cellOf[u], cellOf[v]);
                    if (bestCA < 0 || c1 < bestCA || (c1 == bestCA && c2 < bestCB))
                    {
                        bestCA = c1; bestCB = c2;
                    }
                }

            if (bestCA < 0) { a = -1; b = -1; return false; }

            int xMin = -1, yMin = -1;
            foreach (int x in cells[bestCA])
                foreach (int y in cells[bestCB])
                {
                    if (p[x * n + y] != UNKNOWN) continue;
                    if (xMin < 0 || x < xMin || (x == xMin && y < yMin))
                    {
                        xMin = x; yMin = y;
                    }
                }

            a = xMin; b = yMin;
            return xMin >= 0;
        }

        // ── Backward pass ────────────────────────────────────────────────────

        // §6.5 eager rotation: for each primary, enumerate branches over
        // {direction × a' ∈ CellSnapshotA × b' ∈ CellSnapshotB}, replay each
        // via the prefix + deeper machinery, lex-min over the resulting
        // canonical matrices, and adopt the winner. The transposition test is
        // no longer a fast path — it would only let us skip 2 of the 2·|C_a|·
        // |C_b| branches in the "true symmetry pair" case, which is a
        // marginal optimization that the dependency calculator (§11.10) will
        // make redundant. Keeping the loop uniform makes correctness clearer.
        private List<Primary> BackwardPass(int n, int[] adj, VertexType[] vertexTypes,
                                           List<Primary> record, int sweepIndex)
        {
            var current = new List<Primary>(record);

            // Precompute the prefix stack once per sweep. pPrefix[i] is the
            // P state after applying current[0..i-1]; partPrefix[i] is the
            // matching warm-refined partition. Built bottom-up by incremental
            // ApplyOne + warm Refine (so O(n²) per primary, O(n⁴) total). Each
            // branch evaluation copies (pPrefix[i], partPrefix[i]) instead of
            // re-applying 0..i-1 primaries from scratch.
            //
            // Validity across the sweep: adoptions at outer-iter i overwrite
            // current[i..end] only; positions <i (and therefore both
            // pPrefix[0..i] and partPrefix[0..i]) remain valid for subsequent
            // iterations i-1, i-2, ...
            var (pPrefix, partPrefix) = BuildPrefixStack(n, vertexTypes, adj, current);
            if (pPrefix == null) return current; // baseline broken (shouldn't happen)

            // Baseline canonical: pPrefix[current.Count] is the full state
            // after applying every primary in `current`. Reusing it here
            // avoids a redundant ReplayRecord call (saves one O(n⁴) replay
            // per sweep). Cached across outer iterations since `current`
            // only changes on adoption.
            int[] matBest = BuildPermutedMatrix(adj, ReadPermutation(n, pPrefix[current.Count]), n);

            for (int i = current.Count - 1; i >= 0; i--)
            {
                var primI = current[i];
                List<Primary> bestRecord = current;
                bool adopted = false;

                // Deeper region is constant for this outer iter; hoist out of
                // the inner branch loops.
                var deeper = new List<Primary>(current.Count - i - 1);
                for (int j = i + 1; j < current.Count; j++) deeper.Add(current[j]);

                // Per-primary branch-distinct-canonical tracking (§11.10
                // viability study). Hash every branch outcome we evaluate
                // plus the baseline; the size of the resulting set is the
                // number of distinct canonicals at this primary.
                HashSet<ulong>? distinctHashes = CollectBranchStats ? [] : null;
                int branchesAtThisPrimary = 0;
                distinctHashes?.Add(HashMatrix(matBest));

                // Enumerate rotation branches. (primI.A, primI.B,
                // primI.Direction) is the no-change branch — skip it.
                //
                // Within-cell dedup: (a', b', LESS) and (b', a', GREATER)
                // write the same P entry, so enumerating both is wasted
                // work. Restrict a' < b' for within-cell and cover both
                // directions per ordered pair; the baseline check is
                // normalised against the same ordering.
                bool isWithinCell = !primI.BetweenCell;
                int wA = primI.A, wB = primI.B;
                sbyte wDir = primI.Direction;
                if (isWithinCell && wA > wB)
                {
                    (wA, wB) = (wB, wA);
                    wDir = (sbyte)(-wDir);
                }

                foreach (int aPrime in primI.CellSnapshotA)
                {
                    foreach (int bPrime in primI.CellSnapshotB)
                    {
                        if (aPrime == bPrime) continue;
                        if (isWithinCell && aPrime > bPrime) continue;

                        foreach (sbyte dir in new sbyte[] { LESS, GREATER })
                        {
                            if (aPrime == wA && bPrime == wB && dir == wDir)
                                continue;

                            var branchPrim = new Primary
                            {
                                A = aPrime, B = bPrime, Direction = dir,
                                BetweenCell = primI.BetweenCell,
                                CellSnapshotA = primI.CellSnapshotA,
                                CellSnapshotB = primI.CellSnapshotB,
                            };

                            LastPairRotationsAttempted++;
                            branchesAtThisPrimary++;

                            var suffix = TryReplayFromState(n, adj,
                                                            pPrefix[i], partPrefix[i],
                                                            branchPrim, deeper,
                                                            out bool deeperBroken,
                                                            out sbyte[]? pBranch);
                            if (suffix == null || pBranch == null) continue;
                            if (deeperBroken) LastLockedThenInvalidated++;

                            int[] permBranch = ReadPermutation(n, pBranch);
                            int[] matBranch = BuildPermutedMatrix(adj, permBranch, n);
                            distinctHashes?.Add(HashMatrix(matBranch));

                            if (LexLess(matBranch, matBest))
                            {
                                matBest = matBranch;
                                // Assemble: prefix (current[0..i-1]) + suffix
                                // (branchPrim + replayed deeper + continued).
                                var newRecord = new List<Primary>(i + suffix.Count);
                                for (int j = 0; j < i; j++) newRecord.Add(current[j]);
                                newRecord.AddRange(suffix);
                                bestRecord = newRecord;
                                adopted = true;
                            }
                        }
                    }
                }

                if (distinctHashes != null && LastBranchStats != null)
                {
                    LastBranchStats.Add(new BranchStats(
                        sweep: sweepIndex,
                        primary: i,
                        cellA: primI.CellSnapshotA.Length,
                        cellB: primI.CellSnapshotB.Length,
                        branches: branchesAtThisPrimary,
                        distinct: distinctHashes.Count));
                }

                if (adopted)
                {
                    current = bestRecord;
                    LastBackwardFlips++;
                }
            }

            return current;
        }

        // Fast FNV-1a hash of a canonical adjacency matrix for use in distinct-
        // outcome counting. Collisions are tolerable for measurement (false
        // sharing only underestimates distinct counts, which is the conservative
        // direction for the route-1-feasibility check).
        private static ulong HashMatrix(int[] mat)
        {
            ulong h = 14695981039346656037UL;
            for (int i = 0; i < mat.Length; i++)
            {
                h ^= (uint)mat[i];
                h *= 1099511628211UL;
            }
            return h;
        }

        // Build paired stacks: pStack[k] = P after applying record[0..k-1],
        // partStack[k] = matching warm-refined partition. Returns (null, _)
        // if any primary produces a contradiction (shouldn't happen for a
        // valid record). Cost: O(n²) primaries × (O(n²) ApplyOne + O(n²)
        // typical warm Refine) = O(n⁴) typical.
        private static (sbyte[][]?, WarmPartition[]) BuildPrefixStack(
            int n, VertexType[] vertexTypes, int[] adj, List<Primary> record)
        {
            var pStack = new sbyte[record.Count + 1][];
            var partStack = new WarmPartition[record.Count + 1];

            sbyte[] running = SeedFromTypes(n, vertexTypes);
            var runningPart = new WarmPartition(n);
            runningPart.Refine(adj, running);  // initial cold refine for the seed state

            pStack[0] = (sbyte[])running.Clone();
            partStack[0] = runningPart.Clone();

            for (int k = 0; k < record.Count; k++)
            {
                if (!ApplyOne(running, n, record[k])) return (null, partStack);
                runningPart.Refine(adj, running);  // warm-refine to keep partition in sync
                pStack[k + 1] = (sbyte[])running.Clone();
                partStack[k + 1] = runningPart.Clone();
            }
            return (pStack, partStack);
        }

        // Replay from a cached (prefix-P, prefix-partition) state instead of
        // re-applying primaries 0..i-1 from scratch: clone initialP and
        // initialPart, apply the branch primary (refining partition), then
        // apply each deeper primary (refining after each, to keep partition
        // staleness bounded for the warm refines in ContinueForward).
        // Returns the suffix record (branchPrim + applied-deeper + continued)
        // and the final P.
        private List<Primary>? TryReplayFromState(int n, int[] adj,
                                                  sbyte[] initialP, WarmPartition initialPart,
                                                  Primary branchPrim,
                                                  List<Primary> deeper,
                                                  out bool anyBroken, out sbyte[]? finalP)
        {
            anyBroken = false;
            finalP = null;
            sbyte[] p = (sbyte[])initialP.Clone();
            WarmPartition partition = initialPart.Clone();
            var result = new List<Primary>(deeper.Count + 1);

            if (!ApplyOne(p, n, branchPrim)) return null;
            partition.Refine(adj, p);
            result.Add(branchPrim);
            RecordStateHash(p);

            foreach (var prim in deeper)
            {
                if (!ApplyOne(p, n, prim))
                {
                    anyBroken = true;
                    break;
                }
                partition.Refine(adj, p);
                result.Add(prim);
                RecordStateHash(p);
            }

            while (!IsTotal(n, p))
            {
                if (!PickAndApplyGuess(n, adj, p, partition, result))
                    return null;
                RecordStateHash(p);
            }

            finalP = p;
            return result;
        }

        // Hash the current P state and record it. Cheap no-op when state
        // collection is off. The hash is FNV-1a over the (n×n)-byte P matrix;
        // collisions are tolerable for memo-size estimation.
        private void RecordStateHash(sbyte[] p)
        {
            if (_stateHashes == null) return;
            ulong h = 14695981039346656037UL;
            for (int i = 0; i < p.Length; i++)
            {
                h ^= (byte)p[i];
                h *= 1099511628211UL;
            }
            _stateHashes.Add(h);
        }

        // ── Helpers ──────────────────────────────────────────────────────────

        // Apply one primary to p, transitively closing. Returns false on
        // contradiction (cycle or direction conflict). A "match in the same
        // direction" is treated as a no-op success (closure may have already
        // implied it).
        private static bool ApplyOne(sbyte[] p, int n, Primary prim)
        {
            int a = prim.A, b = prim.B;
            sbyte dir = prim.Direction;
            sbyte cur = p[a * n + b];
            if (cur == dir) return true;
            if (cur != UNKNOWN) return false;

            // Normalise the new edge into a LESS edge x → y, so closure reads
            // "what new transitive LESS chains pass through x → y".
            int x, y;
            if (dir == LESS) { x = a; y = b; }
            else            { x = b; y = a; }
            p[x * n + y] = LESS;
            p[y * n + x] = GREATER;
            return CloseAfterInsert(p, n, x, y);
        }

        // Incremental closure for a single new LESS edge x → y. Assumes p was
        // transitively closed before the edge was inserted. New chains are
        // exactly {(i, j) : i ∈ ancestors(x) ∪ {x}, j ∈ descendants(y) ∪ {y}}
        // because any new chain must factor as i → ... → x → y → ... → j.
        // Cost: O(|anc| · |desc|), worst case O(n²) — beats Floyd-Warshall's
        // O(n³) by an O(n) factor per ApplyOne call.
        private static bool CloseAfterInsert(sbyte[] p, int n, int x, int y)
        {
            // ancestors(x) ∪ {x}: i with P[i, x] = LESS, plus x itself.
            Span<int> anc = stackalloc int[n];
            int ancCount = 0;
            anc[ancCount++] = x;
            for (int i = 0; i < n; i++)
                if (i != x && p[i * n + x] == LESS) anc[ancCount++] = i;

            // descendants(y) ∪ {y}: j with P[y, j] = LESS, plus y itself.
            Span<int> desc = stackalloc int[n];
            int descCount = 0;
            desc[descCount++] = y;
            for (int j = 0; j < n; j++)
                if (j != y && p[y * n + j] == LESS) desc[descCount++] = j;

            // Cross product. Any (i, j) where i is also a descendant (i.e.
            // i appears in both anc and desc, or i == j here) marks a cycle.
            for (int ia = 0; ia < ancCount; ia++)
            {
                int i = anc[ia];
                int iRow = i * n;
                for (int jd = 0; jd < descCount; jd++)
                {
                    int j = desc[jd];
                    if (i == j) return false;  // cycle: i is both ancestor of x and descendant of y
                    sbyte cur = p[iRow + j];
                    if (cur == GREATER) return false;
                    if (cur == UNKNOWN)
                    {
                        p[iRow + j] = LESS;
                        p[j * n + i] = GREATER;
                    }
                }
            }
            return true;
        }

        // Replay the first `count` primaries from a record into a fresh P.
        // Returns null on contradiction.
        private static sbyte[]? ReplayRecord(int n, VertexType[] vertexTypes,
                                             List<Primary> record, int count)
        {
            sbyte[] p = SeedFromTypes(n, vertexTypes);
            int end = Math.Min(count, record.Count);
            for (int j = 0; j < end; j++)
                if (!ApplyOne(p, n, record[j])) return null;
            return p;
        }

        // Build the permuted adjacency matrix as a flat int[].
        private static int[] BuildPermutedMatrix(int[] adj, int[] perm, int n)
        {
            int[] m = new int[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    m[perm[i] * n + perm[j]] = adj[i * n + j];
            return m;
        }

        private static AdjMatrix PermuteByPartialOrder(AdjMatrix G, sbyte[] p, int n)
        {
            int[] perm = ReadPermutation(n, p);
            var result = new EdgeType[n, n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    result[perm[i], perm[j]] = G[i, j];
            return new AdjMatrix(result);
        }

        // ── Self-contained helpers ───────────────────────────────────────────
        //
        // Refinement lives in IncrementalPartition.cs (WarmPartition).
        // SeedFromTypes uses full Floyd-Warshall TransitiveClose for the
        // one-time bootstrap; CloseAfterInsert handles all subsequent
        // single-edge insertions.

        private static int[] ExtractAdj(AdjMatrix G)
        {
            int n = G.VertexCount;
            var adj = new int[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    adj[i * n + j] = G[i, j];
            return adj;
        }

        private static sbyte[] SeedFromTypes(int n, int[] types)
        {
            var p = new sbyte[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (i != j && types[i] < types[j]) { p[i * n + j] = LESS; p[j * n + i] = GREATER; }
            TransitiveClose(p, n);
            return p;
        }

        private static bool TransitiveClose(sbyte[] p, int n)
        {
            for (int k = 0; k < n; k++)
                for (int i = 0; i < n; i++)
                {
                    if (p[i * n + k] != LESS) continue;
                    for (int j = 0; j < n; j++)
                    {
                        if (p[k * n + j] != LESS) continue;
                        if (i == j) return false;
                        sbyte cur = p[i * n + j];
                        if (cur == GREATER) return false;
                        if (cur == UNKNOWN) { p[i * n + j] = LESS; p[j * n + i] = GREATER; }
                    }
                }
            return true;
        }

        private static bool IsTotal(int n, sbyte[] p)
        {
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (i != j && p[i * n + j] == UNKNOWN) return false;
            return true;
        }

        private static int[] ReadPermutation(int n, sbyte[] p)
        {
            var perm = new int[n];
            for (int v = 0; v < n; v++)
            {
                int r = 0;
                for (int u = 0; u < n; u++)
                    if (p[u * n + v] == LESS) r++;
                perm[v] = r;
            }
            return perm;
        }

        private static bool LexLess(int[] a, int[] b)
        {
            for (int i = 0; i < a.Length; i++)
                if (a[i] != b[i]) return a[i] < b[i];
            return false;
        }
    }
}
