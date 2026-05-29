using System;
using System.Collections.Generic;

namespace Canonizer
{
    // The chain-descent harness — docs/chain-descent-strategy.md §4.
    //
    // A recursive descent of the individualization-refinement tree. At each
    // node: warm-refine the partition; if it is discrete the cell ids are a
    // leaf labelling; otherwise pick the iso-invariant target cell, ask the
    // oracle which vertices to branch on, and recurse — skipping a branch a
    // posteriori once a harvested automorphism shows it redundant. The
    // lex-smallest leaf matrix is the canonical form.
    //
    // The descent carries a polynomial node budget (docs/chain-descent-strategy.md
    // §6). Exhausting it makes the run flag — an honest "not handled", never a
    // wrong answer. Automorphisms are harvested from coinciding leaf matrices
    // into a PermutationGroup — the residual-symmetry object, the stabilizer
    // chain of docs/chain-descent-strategy.md §6. Both the oracle and the
    // a-posteriori pruning consume it.
    //
    // Phase-1 conversion: the oracle is CascadeOracle, which certifies nothing
    // a priori, so all pruning is the a-posteriori path-fixing-orbit skip
    // below. Behaviour matches the previous IR search, now bounded by the
    // budget and structured around the oracle seam the deferred linear oracle
    // (docs/chain-descent-calculator.md §6) will plug into.
    //
    // ── Proof contract (docs/chain-descent-strategy.md §7–§8, §15) ───────────────
    //
    // Correctness (oracle-agnostic). For ANY oracle whose representatives
    // cover every orbit of the target cell, Canonize returns an isomorphism-
    // invariant, complete canonical form — or a flag, never a wrong answer.
    // Rests on: cell ids are iso-invariant; the target cell is chosen by cell
    // id; the representatives cover every orbit; a leaf matrix determines the
    // isomorphism class.
    //
    // Complexity (conditional). With a polynomial-time oracle the run is
    // polynomial-or-flag: the node count is ≤ budget by construction and
    // per-node work is polynomial. Unconditional given the budget.
    //
    // Tier-1 target (open — docs/chain-descent-calculator.md §9). On cascade
    // (Tier-1) graphs the descent is conjectured to fit within B(n), so the run
    // canonizes rather than flags. Proving it — characterising the cascade
    // class — is the open Tier-1 theorem; the NodesByDepth instrumentation
    // exposes the cost shape that proof reasons about.
    internal sealed class ChainDescent
    {
        private const sbyte LESS = -1, GREATER = 1;

        private readonly int _n;
        private readonly int[] _adj;
        private readonly ITransversalOracle _oracle;
        private readonly long _budget;

        private readonly List<int> _path = new();
        // Leaf-collision table for a-posteriori automorphism harvesting, keyed by
        // a 64-bit hash of the leaf matrix (value: the first permutation that
        // produced that matrix). Hashing keeps this O(distinct-leaves · n) rather
        // than O(distinct-leaves · n²); the canonical form is tracked separately
        // (_bestMatrix), and a (vanishingly rare) hash collision only costs a
        // missed harvest — the harvested twist is edge-verified regardless, so
        // correctness never depends on the key being exact.
        private readonly Dictionary<long, int[]> _seen = new();

        private long _nodeCount;
        private int _maxDepth;
        private int _prunedBranches;
        private int _leafCount;
        private bool _flagged;
        private string? _flagReason;
        private int[]? _bestMatrix;

        // Descent-tree node count per depth — the per-level cost profile.
        private readonly List<int> _nodesByDepth = new();

        // ── A-priori cascade/linear oracle harvest attribution ──────────────
        // Cost-shape accumulators for the cascade oracle, emitted as
        // DescentStats.Cascade (docs/chain-descent-cascade-oracle.md): residual
        // branching split by footprint class, generators harvested, and the
        // single-path recursion depth (~ tw(H) on CFI). The decisive signal is
        // _branchStarved → 0 (the cascade recursion resolved the starvation).
        private long _decisionNodes, _branchingNodes,
                     _branchAllSingleton, _branchResolved, _branchStarved,
                     _generatorsHarvested, _resolvedByRecursion,
                     _deferralActiveNodes, _phase2Nodes;
        private int _maxRecursionDepth;

        // ── Linear oracle (docs/chain-descent-linear-oracle.md) ──────────────
        // When enabled, after exploring the first representative of a genuine
        // decision the descent constructs a candidate twist carrying it onto
        // each other representative (canonical-colour matching on an
        // all-singletons footprint, §4.2), verifies it edge-by-edge, and
        // harvests it into Automorphisms *before* the branch loop reaches those
        // representatives — so the existing CoveredByPathFixingAut prunes them
        // a-priori. Sound regardless of the construction: only edge-verified
        // automorphisms are harvested, and a non-all-singleton footprint falls
        // back to the normal k-way branch (recursion, §4.4).
        internal bool EnableLinearOracle { get; set; } = true;

        // ── Deferred decisions (docs/chain-descent-deferred-decisions.md) ────
        // When enabled, target-cell selection prefers a cell the a-priori oracle
        // collapses to a single orbit (symmetric — consume it) and DEFERS real
        // decisions, branching them only when no symmetric cell remains (Phase 2).
        // Sound (real-stays-real: a deferred real stays real) and iso-invariant
        // (scramble-invariant + Even≠Odd hold). NOTE: it produces a *different*
        // canonical form than the lowest-id schedule — the leaf labelling depends
        // on the individualisation order (via P), so reordering the schedule
        // changes the lex-min. (This refines the design's §4 claim that deferral
        // "reaches the same lex-min".) Off by default so the established canonical
        // and the off==on oracle cross-check are preserved.
        internal bool EnableDeferral { get; set; } = false;

        // The residual automorphism group, grown by leaf-collision harvesting.
        public PermutationGroup Automorphisms { get; }

        public ChainDescent(int n, int[] adj, ITransversalOracle oracle, long budget)
        {
            _n = n;
            _adj = adj;
            _oracle = oracle;
            _budget = budget;
            Automorphisms = new PermutationGroup(n);
        }

        // A generous polynomial default node budget. Configurable so the
        // scaling probe can tune it; the exact value is pinned later by the
        // Tier-1 proof (docs/chain-descent-calculator.md §9).
        public static long DefaultBudget(int n) =>
            Math.Max(200_000L, 16L * n * n * n * n);

        public CanonResult Canonize(sbyte[] p, WarmPartition partition)
        {
            Search(p, partition);

            var stats = new DescentStats(
                _nodeCount, _maxDepth, _leafCount, _prunedBranches,
                _budget, _nodesByDepth.ToArray(),
                new CascadeStats(
                    _decisionNodes, _branchingNodes,
                    _branchAllSingleton, _branchResolved, _branchStarved,
                    _generatorsHarvested, _resolvedByRecursion, _maxRecursionDepth,
                    _deferralActiveNodes, _phase2Nodes));

            if (_flagged)
                return CanonResult.Flag(_flagReason ?? "flagged", Automorphisms, stats);
            if (_bestMatrix == null)
                return CanonResult.Flag("descent produced no leaf", Automorphisms, stats);
            return CanonResult.Canonical(_bestMatrix, Automorphisms, stats);
        }

        // One descent node: refine, emit a leaf if discrete, else branch on the
        // target cell's representatives.
        private void Search(sbyte[] p, WarmPartition partition)
        {
            if (_flagged) return;
            if (++_nodeCount > _budget)
            {
                _flagged = true;
                _flagReason = $"node budget {_budget} exceeded";
                return;
            }
            int depth = _path.Count;
            if (depth > _maxDepth) _maxDepth = depth;
            while (_nodesByDepth.Count <= depth) _nodesByDepth.Add(0);
            _nodesByDepth[depth]++;

            partition.Refine(_adj, p);
            int numCells = partition.NumCells;
            int[] cellOf = partition.CellOf;

            if (numCells == _n)
            {
                HandleLeaf(cellOf);
                return;
            }

            var cellMembers = new List<List<int>>(numCells);
            for (int c = 0; c < numCells; c++) cellMembers.Add(new List<int>());
            for (int v = 0; v < _n; v++) cellMembers[cellOf[v]].Add(v);

            // Target-cell selection. Cell ids are iso-invariant, so the lowest-id
            // non-singleton cell is the canonical default.
            //
            // With deferred decisions enabled (docs/chain-descent-deferred-decisions.md):
            // among the non-singleton cells in id order, prefer one the a-priori
            // oracle collapses to a single orbit (symmetric — consume it, a free
            // single descent) and DEFER real decisions (cells that stay
            // multi-orbit); branch a real one only when none is symmetric (Phase 2,
            // the rigid residue). Sound because a deferred real stays real
            // (`OrbitPartition.real_stays_real`, ChainDescent/CascadeOracle.lean).
            // It changes the canonical form (the schedule fixes the leaf labelling),
            // so it is off by default.
            int target, footprintClass = -1;
            bool harvestedInSelection = false;
            if (EnableLinearOracle && EnableDeferral)
            {
                target = -1;
                int firstNonSingleton = -1, fallback = -1, fallbackClass = -1;
                for (int c = 0; c < numCells; c++)
                {
                    if (cellMembers[c].Count < 2) continue;
                    if (firstNonSingleton == -1) firstNonSingleton = c;
                    int cls = ClassifyCell(p, partition, cellMembers[c], out int survivors);
                    if (survivors <= 1) { target = c; footprintClass = cls; break; }
                    if (fallback == -1) { fallback = c; fallbackClass = cls; }
                }
                if (target == -1) { target = fallback; footprintClass = fallbackClass; _phase2Nodes++; }
                if (target != firstNonSingleton) _deferralActiveNodes++;
                harvestedInSelection = true; // ClassifyCell already harvested `target`
            }
            else
            {
                target = 0;
                while (cellMembers[target].Count < 2) target++;
            }
            var members = cellMembers[target];

            var decision = _oracle.Classify(_n, _adj, members, _path, Automorphisms);

            // Branch over the chosen cell's representatives, in canonical order,
            // skipping any covered a posteriori by a harvested path-fixing
            // automorphism (its subtree is isomorphic to an explored one's). When
            // deferral did the harvest during classification, the loop only
            // descends and prunes; otherwise it harvests after the first rep.
            var explored = new List<int>();
            bool harvested = harvestedInSelection;
            foreach (int v in decision.Representatives)
            {
                if (_flagged) return;
                if (explored.Count > 0 && CoveredByPathFixingAut(v, explored))
                {
                    _prunedBranches++;
                    continue;
                }
                explored.Add(v);
                Branch(p, partition, members, v);

                // Linear/cascade oracle: after the first explored representative,
                // harvest verified twists/orbit-maps onto the others so
                // CoveredByPathFixingAut prunes them a priori (§4.2, §6.2).
                if (EnableLinearOracle && !harvested)
                {
                    harvested = true;
                    footprintClass = HarvestTwists(p, partition, members, v);
                }
            }

            // Cascade attribution: classify this node's surviving branches by the
            // footprint class the harvest saw (1 = all-singleton/linear, 3 = resolved
            // by the recursion, 2 = starved past the depth bound). Feeds CascadeStats.
            _decisionNodes++;
            if (explored.Count > 1)
            {
                _branchingNodes++;
                if (footprintClass == 1) _branchAllSingleton++;
                else if (footprintClass == 3) _branchResolved++;
                else if (footprintClass == 2) _branchStarved++;
            }
        }

        // Classify a cell by running the a-priori oracle harvest (exploratory, on
        // copies — adding only verified generators) and counting the representatives
        // that survive path-fixing-orbit pruning. survivorCount == 1 ⟺ the cell is a
        // single orbit (symmetric, consumable); > 1 ⟺ a real decision. Returns the
        // harvest's footprint class for attribution. This is the per-cell
        // classification the deferred-decision scheduler consults.
        private int ClassifyCell(sbyte[] p, WarmPartition partition, List<int> cell,
                                 out int survivorCount)
        {
            int cls = HarvestTwists(p, partition, cell, cell[0]);
            var survivors = new List<int> { cell[0] };
            for (int i = 1; i < cell.Count; i++)
                if (!CoveredByPathFixingAut(cell[i], survivors))
                    survivors.Add(cell[i]);
            survivorCount = survivors.Count;
            return cls;
        }

        // A-priori cascade / linear oracle harvest (docs/chain-descent-cascade-oracle.md).
        //
        // Explore the anchor rep r1 and harvest verified path-fixing automorphisms
        // carrying it onto each other representative, so CoveredByPathFixingAut
        // prunes those a priori. When r1's refinement footprint is already
        // all-singleton the candidate map is forced directly (the linear oracle,
        // §4.2). When it is non-singleton the cascade recursion (§4.4) deepens the
        // anchor along a single iso-invariant cell-id path until the footprint is
        // all-singleton, then replays that same cell-id sequence on each other rep
        // (lockstep, §4.4) so their deep partitions are comparable for the
        // colour-match. Sound regardless of the construction: only edge-verified
        // automorphisms are harvested; an unverifiable candidate leaves the reps
        // separate (a sound over-split). The whole deepening is exploratory — it
        // runs on cloned partitions and never commits to _path.
        //
        // Returns the footprint class for attribution: 0 = empty/closure-fail,
        // 1 = all-singleton at depth 0 (linear oracle), 3 = resolved by the cascade
        // recursion, 2 = still non-singleton past the depth bound (starved).
        private int HarvestTwists(sbyte[] p, WarmPartition partition, List<int> cell, int r1)
        {
            var seq = new List<int>();
            if (!DeepenAnchor(p, partition, cell, r1, seq,
                              out var b1, out var footprint, out int cls))
                return cls; // 0 (nothing to harvest) or 2 (depth-bound, still non-singleton)

            foreach (int rj in cell)
            {
                if (rj == r1) continue;
                var bj = ReplayDeepening(p, partition, cell, rj, seq);
                if (bj is null) continue; // rj could not follow the sequence ⇒ no candidate
                var t = TwistConstruction.TryConstruct(_n, footprint!, b1!.CellOf, bj.CellOf);
                if (t is not null && IsAutomorphism(t))
                {
                    Automorphisms.AddGenerator(t);
                    _generatorsHarvested++;
                }
            }
            return cls; // 1 (depth 0) or 3 (resolved via recursion)
        }

        // Exploratory single-path deepening of the anchor rep r1: individualize r1,
        // then repeatedly descend the lowest-id non-singleton footprint sub-cell —
        // recording its iso-invariant cell id into `seq` — and re-refine, until the
        // footprint (vs the original parent partition) is all-singleton or the depth
        // bound is spent. ONE sub-cell, ONE vertex per level: a single path, never a
        // branch over reps (docs/chain-descent-cascade-oracle.md §4.4). On success
        // (all-singleton) returns the deep partition + footprint, cls = 1 if no
        // deepening was needed else 3. On failure returns false, cls = 0 (nothing
        // split) or 2 (depth bound hit with the footprint still non-singleton).
        private bool DeepenAnchor(
            sbyte[] p, WarmPartition parent, List<int> cell, int r1, List<int> seq,
            out WarmPartition? deep, out RefinementFootprint? footprint, out int cls)
        {
            deep = null; footprint = null; cls = 0;

            var curP = Individualize(p, cell, r1);
            if (curP is null) return false;
            var curPart = parent.Clone();
            curPart.Refine(_adj, curP);

            for (int depth = 0; depth <= _n; depth++)
            {
                var fp = RefinementFootprint.Compute(_n, parent.CellOf, curPart.CellOf);
                if (fp.SplitCells.Count == 0) { cls = 0; return false; }

                // Lowest-id non-singleton sub-cell to descend (iso-invariant choice).
                int[]? chosen = null;
                int chosenId = int.MaxValue;
                foreach (var sc in fp.SplitCells)
                    foreach (var sub in sc.SubCells)
                        if (sub.Length >= 2 && curPart.CellOf[sub[0]] < chosenId)
                        {
                            chosenId = curPart.CellOf[sub[0]];
                            chosen = sub;
                        }

                if (chosen is null) // all-singleton: done
                {
                    deep = curPart; footprint = fp;
                    cls = seq.Count == 0 ? 1 : 3;
                    if (seq.Count > 0) _resolvedByRecursion++;
                    if (seq.Count > _maxRecursionDepth) _maxRecursionDepth = seq.Count;
                    return true;
                }

                if (depth == _n) { cls = 2; return false; } // depth bound, still non-singleton

                seq.Add(chosenId);
                var sub2 = new List<int>(chosen);          // ascending ⇒ sub2[0] is lowest id
                var nextP = Individualize(curP, sub2, sub2[0]);
                if (nextP is null) { cls = 2; return false; }
                curP = nextP;
                curPart = curPart.Clone();
                curPart.Refine(_adj, curP);
            }
            cls = 2; return false;
        }

        // Replay the anchor's cell-id sequence on rep rj: individualize rj, then for
        // each recorded id individualize the lowest-id vertex of the cell carrying
        // that id and re-refine. Single path, exploratory (on clones). Returns rj's
        // deep partition, or null if the sequence cannot be followed (rj is
        // structurally unlike r1 ⇒ no candidate ⇒ the reps stay separate, sound).
        private WarmPartition? ReplayDeepening(
            sbyte[] p, WarmPartition parent, List<int> cell, int rj, List<int> seq)
        {
            var curP = Individualize(p, cell, rj);
            if (curP is null) return null;
            var curPart = parent.Clone();
            curPart.Refine(_adj, curP);

            foreach (int id in seq)
            {
                var members = new List<int>();
                for (int v = 0; v < _n; v++)
                    if (curPart.CellOf[v] == id) members.Add(v);
                if (members.Count < 2) return null; // id absent or already singleton

                var nextP = Individualize(curP, members, members[0]);
                if (nextP is null) return null;
                curP = nextP;
                curPart = curPart.Clone();
                curPart.Refine(_adj, curP);
            }
            return curPart;
        }

        // Individualise rep below its cellmates (as Branch does) and close;
        // returns the closed child P, or null on a closure contradiction.
        private sbyte[]? Individualize(sbyte[] p, List<int> cell, int rep)
        {
            var pc = (sbyte[])p.Clone();
            foreach (int w in cell)
                if (w != rep) { pc[rep * _n + w] = LESS; pc[w * _n + rep] = GREATER; }
            return TransitiveClose(pc) ? pc : null;
        }

        // Individualise v below every other member of its cell, then recurse.
        private void Branch(sbyte[] p, WarmPartition partition, List<int> cell, int v)
        {
            var pChild = (sbyte[])p.Clone();
            foreach (int w in cell)
            {
                if (w == v) continue;
                pChild[v * _n + w] = LESS;
                pChild[w * _n + v] = GREATER;
            }
            // v below its cellmates is always consistent (v becomes their
            // minimum); guard defensively against a closure contradiction.
            if (!TransitiveClose(pChild)) return;

            _path.Add(v);
            Search(pChild, partition.Clone());
            _path.RemoveAt(_path.Count - 1);
        }

        // True if v is reachable from an already-explored representative via
        // discovered automorphisms that fix every individualised path vertex.
        // Such an automorphism carries an explored vertex's subtree onto v's,
        // so v's subtree yields no canonical the explored one omits.
        private bool CoveredByPathFixingAut(int v, List<int> explored)
        {
            var gens = new List<int[]>();
            foreach (var g in Automorphisms.Generators)
            {
                bool fixesPath = true;
                foreach (int pt in _path)
                    if (g[pt] != pt) { fixesPath = false; break; }
                if (fixesPath) gens.Add(g);
            }
            if (gens.Count == 0) return false;

            var inOrbit = new bool[_n];
            var queue = new Queue<int>();
            foreach (int r in explored)
                if (!inOrbit[r]) { inOrbit[r] = true; queue.Enqueue(r); }
            while (queue.Count > 0)
            {
                int u = queue.Dequeue();
                foreach (var g in gens)
                {
                    int w = g[u];
                    if (!inOrbit[w]) { inOrbit[w] = true; queue.Enqueue(w); }
                }
            }
            return inOrbit[v];
        }

        // A discrete partition: cellOf is a bijection onto {0..n-1}, the
        // canonical labelling. Track the lex-min leaf matrix; harvest a
        // (verified) automorphism whenever two leaves coincide.
        private void HandleLeaf(int[] cellOf)
        {
            _leafCount++;
            int[] perm = (int[])cellOf.Clone();
            int[] matrix = BuildPermutedMatrix(perm);

            if (_bestMatrix == null || LexLess(matrix, _bestMatrix))
                _bestMatrix = matrix;

            long key = HashMatrix(matrix);
            if (_seen.TryGetValue(key, out int[]? firstPerm))
            {
                // perm and firstPerm produced matrices with the same hash; if the
                // matrices truly coincide the relabelling between them is an
                // automorphism — verified edge-by-edge before being harvested
                // (a hash collision simply fails the check, harmlessly).
                int[] auto = Perm.Compose(Perm.Inverse(perm), firstPerm);
                if (IsAutomorphism(auto))
                    Automorphisms.AddGenerator(auto);
            }
            else
            {
                _seen[key] = perm;
            }
        }

        // FNV-1a 64-bit hash of a leaf matrix, for the collision table above.
        private static long HashMatrix(int[] m)
        {
            ulong h = 14695981039346656037UL;
            foreach (int x in m)
            {
                h ^= (uint)x;
                h *= 1099511628211UL;
            }
            return unchecked((long)h);
        }

        // ── helpers ──────────────────────────────────────────────────────────

        private int[] BuildPermutedMatrix(int[] perm)
        {
            int[] m = new int[_n * _n];
            for (int i = 0; i < _n; i++)
                for (int j = 0; j < _n; j++)
                    m[perm[i] * _n + perm[j]] = _adj[i * _n + j];
            return m;
        }

        private bool IsAutomorphism(int[] g)
        {
            for (int i = 0; i < _n; i++)
                for (int j = 0; j < _n; j++)
                    if (_adj[g[i] * _n + g[j]] != _adj[i * _n + j])
                        return false;
            return true;
        }

        // Floyd–Warshall transitive closure of the partial order; false on a
        // cycle / direction conflict. Entries are LESS / 0 (unknown) / GREATER.
        private bool TransitiveClose(sbyte[] p)
        {
            int n = _n;
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
                        if (cur == 0) { p[i * n + j] = LESS; p[j * n + i] = GREATER; }
                    }
                }
            return true;
        }

        private static bool LexLess(int[] a, int[] b)
        {
            for (int i = 0; i < a.Length; i++)
                if (a[i] != b[i]) return a[i] < b[i];
            return false;
        }
    }
}
