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

            // Forward pass.
            sbyte[] p = SeedFromTypes(n, vertexTypes);
            List<Primary> record = ContinueForward(n, adj, p);

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
            do
            {
                prevFlips = LastBackwardFlips;
                record = BackwardPass(n, adj, vertexTypes, record);
            } while (LastBackwardFlips > prevFlips);
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

        // Walk P toward total via single-pair guesses; mutate p, return the
        // primaries pushed (in order).
        private List<Primary> ContinueForward(int n, int[] adj, sbyte[] p)
        {
            var record = new List<Primary>();
            while (!IsTotal(n, p))
            {
                if (!PickAndApplyGuess(n, adj, p, record))
                    throw new InvalidOperationException(
                        "FlipValidation: P not total but no guess candidate found");
            }
            return record;
        }

        // Pick the next primary guess (within-cell first, else between-cell),
        // apply it to p, and push it onto record. Returns false only if there
        // really is no candidate, which is a bug given P is not total.
        private bool PickAndApplyGuess(int n, int[] adj, sbyte[] p, List<Primary> record)
        {
            int[] cellOf = Refine(n, adj, p);
            int numCells = cellOf.Max() + 1;
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
                                           List<Primary> record)
        {
            var current = new List<Primary>(record);

            // Baseline canonical: cached across outer iterations. Only the
            // prefix part of `current` (positions 0..i-1) is ever read by an
            // iteration at position i, and adopting at i never touches
            // positions <i — so an iteration that doesn't adopt leaves the
            // canonical unchanged. Recomputing per outer iter was an O(n^5)
            // redundant cost per sweep.
            sbyte[]? pCur = ReplayRecord(n, vertexTypes, current, current.Count);
            if (pCur == null) return current;
            int[] matBest = BuildPermutedMatrix(adj, ReadPermutation(n, pCur), n);

            for (int i = current.Count - 1; i >= 0; i--)
            {
                var primI = current[i];
                List<Primary> bestRecord = current;
                bool adopted = false;

                // Enumerate rotation branches. Note: (primI.A, primI.B,
                // primI.Direction) is the no-change branch — skip it (the
                // baseline already represents it).
                foreach (int aPrime in primI.CellSnapshotA)
                {
                    foreach (int bPrime in primI.CellSnapshotB)
                    {
                        if (aPrime == bPrime) continue;

                        foreach (sbyte dir in new sbyte[] { LESS, GREATER })
                        {
                            if (aPrime == primI.A && bPrime == primI.B && dir == primI.Direction)
                                continue;

                            var branchPrim = new Primary
                            {
                                A = aPrime, B = bPrime, Direction = dir,
                                BetweenCell = primI.BetweenCell,
                                CellSnapshotA = primI.CellSnapshotA,
                                CellSnapshotB = primI.CellSnapshotB,
                            };

                            var prefix = new List<Primary>(i + 1);
                            for (int j = 0; j < i; j++) prefix.Add(current[j]);
                            prefix.Add(branchPrim);

                            var deeper = new List<Primary>(current.Count - i - 1);
                            for (int j = i + 1; j < current.Count; j++) deeper.Add(current[j]);

                            LastPairRotationsAttempted++;

                            var branchFull = TryReplayWithDeeper(n, adj, vertexTypes,
                                                                 prefix, deeper,
                                                                 out bool deeperBroken,
                                                                 out sbyte[]? pBranch);
                            if (branchFull == null || pBranch == null) continue;
                            if (deeperBroken) LastLockedThenInvalidated++;

                            int[] permBranch = ReadPermutation(n, pBranch);
                            int[] matBranch = BuildPermutedMatrix(adj, permBranch, n);

                            if (LexLess(matBranch, matBest))
                            {
                                matBest = matBranch;
                                bestRecord = branchFull;
                                adopted = true;
                            }
                        }
                    }
                }

                if (adopted)
                {
                    current = bestRecord;
                    LastBackwardFlips++;
                }
            }

            return current;
        }

        // Apply prefix; then try to apply deeper guesses one by one. If a
        // deeper guess can't be applied (its pair is no longer Unknown in the
        // current P), bump the broken flag and re-run ContinueForward to fill
        // out the remainder. Returns the final P alongside the record so the
        // caller doesn't have to replay everything from scratch again.
        private List<Primary>? TryReplayWithDeeper(int n, int[] adj, VertexType[] vertexTypes,
                                                   List<Primary> prefix, List<Primary> deeper,
                                                   out bool anyBroken, out sbyte[]? finalP)
        {
            anyBroken = false;
            finalP = null;
            sbyte[] p = SeedFromTypes(n, vertexTypes);
            var result = new List<Primary>(prefix.Count + deeper.Count);

            foreach (var prim in prefix)
            {
                if (!ApplyOne(p, n, prim)) return null;
                result.Add(prim);
            }

            foreach (var prim in deeper)
            {
                if (!ApplyOne(p, n, prim))
                {
                    anyBroken = true;
                    break;
                }
                result.Add(prim);
            }

            while (!IsTotal(n, p))
            {
                if (!PickAndApplyGuess(n, adj, p, result))
                    return null;
            }

            finalP = p;
            return result;
        }

        // ── Helpers ──────────────────────────────────────────────────────────

        // Apply one primary to p, transitively closing. Returns false on
        // contradiction (cycle or direction conflict). A "match in the same
        // direction" is treated as a no-op success (closure may have already
        // implied it).
        private static bool ApplyOne(sbyte[] p, int n, Primary prim)
        {
            sbyte cur = p[prim.A * n + prim.B];
            if (cur == prim.Direction) return true;
            if (cur != UNKNOWN) return false;
            p[prim.A * n + prim.B] = prim.Direction;
            p[prim.B * n + prim.A] = (sbyte)(-prim.Direction);
            return TransitiveClose(p, n);
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

        // ── Mirrored from CanonGraphOrdererPartialOrderSinglePair ────────────
        //
        // Refine / TransitiveClose / SeedFromTypes / IsTotal / ReadPermutation
        // / LexLess kept locally so this class is self-contained.

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

        private static int[] Refine(int n, int[] adj, sbyte[] p)
        {
            int[] color = new int[n];
            while (true)
            {
                int[] next = RefineRound(n, adj, p, color);
                bool same = SamePartition(n, color, next);
                color = next;
                if (same) break;
            }
            return color;
        }

        // Each vertex's signature is its own color followed by the sorted
        // multiset of neighbour (color, edge-label, Prel)-tuples, packed into
        // longs. Two vertices share a signature iff they have equal own-color
        // and equal multisets — equivalent to the previous string-based check,
        // just without per-round string allocation.
        private static int[] RefineRound(int n, int[] adj, sbyte[] p, int[] color)
        {
            var sigs = new long[n][];
            for (int v = 0; v < n; v++)
            {
                var tuples = new long[n]; // [0] = own color; [1..n-1] = sorted neighbours
                tuples[0] = color[v];
                int k = 1;
                for (int u = 0; u < n; u++)
                {
                    if (u == v) continue;
                    tuples[k++] = ((long)color[u] << 24)
                                  | ((long)(uint)adj[v * n + u] << 8)
                                  | ((long)(p[v * n + u] + 1) & 0xFF);
                }
                Array.Sort(tuples, 1, n - 1);
                sigs[v] = tuples;
            }

            // Canonical rank: sort distinct signatures lex, assign sequential
            // ids. The lex sort preserves iso-invariance of the cell ids
            // (relied on by between-cell guess selection).
            var distinct = new SortedSet<long[]>(LongArrayLex.Instance);
            for (int v = 0; v < n; v++) distinct.Add(sigs[v]);
            var rank = new Dictionary<long[], int>(distinct.Count, LongArrayEq.Instance);
            int r = 0;
            foreach (var sig in distinct) rank[sig] = r++;

            var nextColor = new int[n];
            for (int v = 0; v < n; v++) nextColor[v] = rank[sigs[v]];
            return nextColor;
        }

        private sealed class LongArrayEq : IEqualityComparer<long[]>
        {
            public static readonly LongArrayEq Instance = new();
            public bool Equals(long[]? a, long[]? b)
            {
                if (ReferenceEquals(a, b)) return true;
                if (a is null || b is null || a.Length != b.Length) return false;
                for (int i = 0; i < a.Length; i++) if (a[i] != b[i]) return false;
                return true;
            }
            public int GetHashCode(long[] a)
            {
                unchecked
                {
                    ulong h = 14695981039346656037UL;
                    for (int i = 0; i < a.Length; i++)
                    {
                        h ^= (ulong)a[i];
                        h *= 1099511628211UL;
                    }
                    return (int)h;
                }
            }
        }

        private sealed class LongArrayLex : IComparer<long[]>
        {
            public static readonly LongArrayLex Instance = new();
            public int Compare(long[]? a, long[]? b)
            {
                if (ReferenceEquals(a, b)) return 0;
                if (a is null) return -1;
                if (b is null) return 1;
                int min = a.Length < b.Length ? a.Length : b.Length;
                for (int i = 0; i < min; i++)
                {
                    if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
                }
                return a.Length.CompareTo(b.Length);
            }
        }

        private static bool SamePartition(int n, int[] a, int[] b)
        {
            for (int i = 0; i < n; i++)
                for (int j = i + 1; j < n; j++)
                    if ((a[i] == a[j]) != (b[i] == b[j])) return false;
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
