using System;
using System.Collections.Generic;

namespace Canonizer
{
    // The chain-descent harness — docs/chain-descent-simplified-overview.md §4.
    //
    // A recursive descent of the individualization-refinement tree. At each
    // node: warm-refine the partition; if it is discrete the cell ids are a
    // leaf labelling; otherwise pick the iso-invariant target cell, ask the
    // oracle which vertices to branch on, and recurse — skipping a branch a
    // posteriori once a harvested automorphism shows it redundant. The
    // lex-smallest leaf matrix is the canonical form.
    //
    // The descent carries a polynomial node budget (§4.2). Exhausting it makes
    // the run flag — an honest "not handled", never a wrong answer.
    // Automorphisms are harvested from coinciding leaf matrices into a
    // PermutationGroup, the residual-symmetry object (§4.3); both the oracle
    // and the a-posteriori pruning consume it.
    //
    // Phase-1 conversion: the oracle is CascadeOracle, which certifies nothing
    // a priori, so all pruning is the a-posteriori path-fixing-orbit skip
    // below. Behaviour matches the previous IR search, now bounded by the
    // budget and structured around the oracle seam the deferred linear oracle
    // (§7) will plug into.
    //
    // ── Proof contract (docs/chain-descent-simplified-overview.md §8–§9) ──────────────
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
    // Tier-1 target (open — §9 gap 3). On cascade (Tier-1) graphs the descent
    // is conjectured to fit within B(n), so the run canonizes rather than
    // flags. Proving it — characterising the cascade class — is the open
    // Tier-1 theorem; the NodesByDepth instrumentation exposes the cost shape
    // that proof reasons about.
    internal sealed class ChainDescent
    {
        private const sbyte LESS = -1, GREATER = 1;

        private readonly int _n;
        private readonly int[] _adj;
        private readonly ITransversalOracle _oracle;
        private readonly long _budget;

        private readonly List<int> _path = new();
        private readonly Dictionary<int[], int[]> _seen;

        private long _nodeCount;
        private int _maxDepth;
        private int _prunedBranches;
        private int _leafCount;
        private bool _flagged;
        private string? _flagReason;
        private int[]? _bestMatrix;

        // Descent-tree node count per depth — the per-level cost profile.
        private readonly List<int> _nodesByDepth = new();

        // The residual automorphism group, grown by leaf-collision harvesting.
        public PermutationGroup Automorphisms { get; }

        public ChainDescent(int n, int[] adj, ITransversalOracle oracle, long budget)
        {
            _n = n;
            _adj = adj;
            _oracle = oracle;
            _budget = budget;
            Automorphisms = new PermutationGroup(n);
            _seen = new Dictionary<int[], int[]>(IntArrayEq.Instance);
        }

        // A generous polynomial default node budget. Configurable so the
        // scaling probe can tune it; the exact value is pinned later by the
        // Tier-1 proof (docs/chain-descent-simplified-overview.md §9 gap 3).
        public static long DefaultBudget(int n) =>
            Math.Max(200_000L, 16L * n * n * n * n);

        public CanonResult Canonize(sbyte[] p, WarmPartition partition)
        {
            Search(p, partition);

            var stats = new DescentStats(
                _nodeCount, _maxDepth, _leafCount, _prunedBranches,
                _budget, _nodesByDepth.ToArray());

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

            // Target cell: the lowest-id non-singleton cell. Cell ids are
            // iso-invariant, so the choice is too. One exists (numCells < n).
            int target = 0;
            while (cellMembers[target].Count < 2) target++;
            var members = cellMembers[target];

            var decision = _oracle.Classify(_n, _adj, members, _path, Automorphisms);

            // Branch over the oracle's representatives, in canonical order,
            // skipping any covered a posteriori by a harvested path-fixing
            // automorphism (its subtree is isomorphic to an explored one's).
            var explored = new List<int>();
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
            }
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

            if (_seen.TryGetValue(matrix, out int[]? firstPerm))
            {
                // perm and firstPerm both produce `matrix`; the relabelling
                // between them is an automorphism of the graph.
                int[] auto = Perm.Compose(Perm.Inverse(perm), firstPerm);
                if (IsAutomorphism(auto))
                    Automorphisms.AddGenerator(auto);
            }
            else
            {
                _seen[matrix] = perm;
            }
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

        private sealed class IntArrayEq : IEqualityComparer<int[]>
        {
            public static readonly IntArrayEq Instance = new();

            public bool Equals(int[]? a, int[]? b)
            {
                if (ReferenceEquals(a, b)) return true;
                if (a is null || b is null || a.Length != b.Length) return false;
                for (int i = 0; i < a.Length; i++)
                    if (a[i] != b[i]) return false;
                return true;
            }

            public int GetHashCode(int[] a)
            {
                var h = new HashCode();
                foreach (int x in a) h.Add(x);
                return h.ToHashCode();
            }
        }
    }
}
