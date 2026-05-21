using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    // ── Phase 1 instrumentation records ─────────────────────────────────────
    //
    // Returned by CanonGraphOrdererFlipValidation.ProbeRotationsSingleFlip.
    // Used by the calculator-viability tests to measure how many backward-pass
    // rotation alternatives actually change the canonical's P state ("false
    // symmetries") vs. leave it untouched ("true symmetries"), and how often
    // a single P entry is moved by multiple different rotation alternatives
    // (coupling candidates for Phase 2's XOR-fit step).
    //
    // See docs/flip-validation-calculator.md, the rotation-coupling section.

    public record RotationProbeData(
        int LayerId,
        int OriginalA, int OriginalB, sbyte OriginalDirection,
        bool BetweenCell,
        int AlternativeA, int AlternativeB, sbyte AlternativeDirection,
        int[] AffectedEntries);   // flat indices i*n + j into P where the
                                  // alternative-applied branch differs from
                                  // the forward-pass baseline.

    public sealed class RotationProbingReport
    {
        public int N { get; init; }
        public int PrimaryCount { get; init; }
        public IReadOnlyList<RotationProbeData> Probes { get; init; } = [];
        public int CouplingCandidateEntries { get; init; }

        // Aggregates over Probes.
        public int TotalProbes => Probes.Count;
        public int FalseSymmetryProbes =>
            Probes.Count(p => p.AffectedEntries.Length > 0);
        public int TrueSymmetryProbes => TotalProbes - FalseSymmetryProbes;
        public int MaxAffectedEntries =>
            Probes.Count == 0 ? 0 : Probes.Max(p => p.AffectedEntries.Length);
        public double AvgAffectedEntriesOverFalseSymProbes =>
            FalseSymmetryProbes == 0
                ? 0.0
                : Probes.Where(p => p.AffectedEntries.Length > 0)
                        .Average(p => p.AffectedEntries.Length);
    }

    // Phase 2 instrumentation: XOR-fit data per coupling-candidate entry.
    // For an entry whose direction is affected by multiple rotation
    // alternatives, this reports whether the value-as-a-function of those
    // alternatives is linear over Z₂ (XOR of the involved variables, plus a
    // constant). Linearity is the load-bearing class assumption for the
    // route-2 calculator: if formulas stay AND-of-XOR through construction,
    // every coupling must fit XOR. Failure here directly refutes that
    // assumption on the failing graph.

    public record XorCouplingFit(
        int EntryFlatIndex,
        int[] InvolvedPrimaries,        // primary indices contributing to E
        bool FitsXor,                   // every pair-verification matched
        bool[] XorCoefficients,         // c_i ∈ {0, 1} aligned with InvolvedPrimaries
        bool ConstantTerm,              // c_0 (baseline value of E)
        int PairsChecked,
        int PairsMatched);

    public sealed class CouplingFitReport
    {
        public int N { get; init; }
        public int PrimaryCount { get; init; }
        public int CouplingCandidatesTested { get; init; }
        public int ForwardPassesRun { get; init; }
        public IReadOnlyList<XorCouplingFit> Fits { get; init; } = [];

        public int FitCount => Fits.Count(f => f.FitsXor);
        public int NonFitCount => Fits.Count(f => !f.FitsXor);
        public double FitRate =>
            CouplingCandidatesTested == 0 ? 1.0
            : (double)FitCount / CouplingCandidatesTested;
        public int MaxVariablesPerEntry =>
            Fits.Count == 0 ? 0 : Fits.Max(f => f.InvolvedPrimaries.Length);
        public double AvgVariablesPerEntry =>
            Fits.Count == 0 ? 0.0 : Fits.Average(f => f.InvolvedPrimaries.Length);
    }

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

        // Order of the automorphism group harvested by the route-2 calculator
        // on the last connected-component canonization.
        public BigInteger LastAutomorphismGroupOrder { get; private set; }

        // Branches the calculator's orbit-pruning skipped on the last
        // connected-component canonization.
        public int LastPrunedBranches { get; private set; }

        public AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            // Tier 0 — component decomposition. A disjoint union's automorphism
            // group factors as a (wreath) product over connected components;
            // canonizing each component independently and combining keeps
            // disjoint unions linear in the number of components. The old
            // whole-graph forward pass instead ran over the union as one cell
            // and manufactured cross-component coupling, going superpolynomial
            // on disjoint CFI. See docs/flip-validation-calculator.md "Tier 0".
            var components = ConnectedComponents(G);
            if (components.Count <= 1)
                return RunConnected(vertexTypes, G);
            return CombineComponents(vertexTypes, G, components);
        }

        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // The single-component canonizer. Run() dispatches here for connected
        // graphs and for each component of a disconnected one.
        private AdjMatrix RunConnected(VertexType[] vertexTypes, AdjMatrix G)
        {
            int n = G.VertexCount;
            int[] adj = ExtractAdj(G);

            LastWithinCellGuesses = 0;
            LastBetweenCellGuesses = 0;
            LastBackwardFlips = 0;
            LastPairRotationsAttempted = 0;
            LastLockedThenInvalidated = 0;

            // Route-2 group calculator: recursive lex-min over the
            // individualization-refinement tree. Replaces the forward-greedy +
            // direction-only backward pass, which was incomplete on connected
            // graphs with a multi-orbit cell (e.g. graph #135 of the size-6
            // corpus). See docs/flip-validation-calculator.md.
            sbyte[] p = SeedFromTypes(n, vertexTypes);
            var partition = new WarmPartition(n);

            var calc = new GroupCalculator(n, adj);
            calc.Search(p, partition);
            if (calc.BestMatrix == null)
                throw new InvalidOperationException(
                    "FlipValidation: calculator produced no leaf");

            LastPrimaryCount = calc.LeafCount;
            LastAutomorphismGroupOrder = calc.Automorphisms.Order;
            LastPrunedBranches = calc.PrunedBranches;

            int[] best = calc.BestMatrix;
            var result = new EdgeType[n, n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    result[i, j] = best[i * n + j];
            return new AdjMatrix(result);
        }

        // ── Route-2 group calculator ─────────────────────────────────────────
        //
        // Recursive lex-min over the individualization-refinement tree
        // (nauty-shaped). At each node: warm-refine the partition; if it is
        // discrete the cell ids are the canonical labelling and the node is a
        // leaf; otherwise pick the lowest-id non-singleton cell as the target
        // and branch by individualising each of its vertices, then recurse.
        // The lex-smallest leaf matrix is the canonical.
        //
        // Correctness: cell ids are iso-invariant (IncrementalPartition assigns
        // them by canonical lex-sort of refinement signatures), the target
        // cell is chosen by cell id, and branching covers every orbit of the
        // target cell — so the set of leaf matrices is iso-invariant: every
        // scrambling yields the same lex-min. A leaf matrix determines its
        // isomorphism class, so the invariant is also complete.
        //
        // Orbit pruning: leaves with an equal permuted matrix differ by an
        // automorphism; these are harvested (verified, then added to a
        // PermutationGroup — the residual-symmetry object of the calculator
        // doc's model). At a branch node, a target-cell vertex reachable from
        // an already-explored one via automorphisms that fix the individualised
        // path is skipped — its subtree is isomorphic to an explored one's and
        // yields no new canonical. This makes the search a sum over the target
        // cell's orbits rather than a product over all its vertices.
        private sealed class GroupCalculator
        {
            private readonly int _n;
            private readonly int[] _adj;
            private readonly List<int> _path = new();
            private readonly Dictionary<int[], int[]> _seen;

            public int[]? BestMatrix { get; private set; }
            public int LeafCount { get; private set; }
            public int PrunedBranches { get; private set; }
            public PermutationGroup Automorphisms { get; }

            public GroupCalculator(int n, int[] adj)
            {
                _n = n;
                _adj = adj;
                Automorphisms = new PermutationGroup(n);
                _seen = new Dictionary<int[], int[]>(IntArrayEq.Instance);
            }

            // Refine; emit a leaf if discrete, else branch on the target cell.
            public void Search(sbyte[] p, WarmPartition partition)
            {
                partition.Refine(_adj, p);

                int numCells = partition.NumCells;
                int[] cellOf = partition.CellOf;

                if (numCells == _n)
                {
                    // Discrete: cellOf is a bijection onto {0..n-1} — the
                    // canonical labelling.
                    HandleLeaf(cellOf);
                    return;
                }

                var cellMembers = new List<List<int>>(numCells);
                for (int c = 0; c < numCells; c++) cellMembers.Add(new List<int>());
                for (int v = 0; v < _n; v++) cellMembers[cellOf[v]].Add(v);

                // Target cell: the lowest-id non-singleton cell (one exists,
                // numCells < n). Cell id is iso-invariant.
                int target = 0;
                while (cellMembers[target].Count < 2) target++;
                var members = cellMembers[target];

                // Branch over one vertex per orbit of the target cell under
                // path-fixing automorphisms discovered so far.
                var explored = new List<int>();
                foreach (int v in members)
                {
                    if (explored.Count > 0 && ReachableByPathFixingAut(v, explored))
                    {
                        PrunedBranches++;
                        continue;
                    }
                    explored.Add(v);
                    Branch(p, partition, members, v);
                }
            }

            // Individualise vertex v within its cell — order it below every
            // other member of the cell — then recurse.
            private void Branch(sbyte[] p, WarmPartition partition, List<int> cell, int v)
            {
                var pChild = (sbyte[])p.Clone();
                foreach (int w in cell)
                {
                    if (w == v) continue;
                    var prim = new Primary { A = v, B = w, Direction = LESS, BetweenCell = false };
                    // v and w share a cell, hence are P-incomparable, so
                    // ApplyOne never fails here; guard defensively.
                    if (!ApplyOne(pChild, _n, prim)) return;
                }
                _path.Add(v);
                Search(pChild, partition.Clone());
                _path.RemoveAt(_path.Count - 1);
            }

            // True if v is reachable from an already-explored target-cell
            // vertex via discovered automorphisms that fix every path vertex.
            // Such an automorphism carries an explored vertex's subtree onto
            // v's, so v's subtree yields no canonical the explored one omits.
            private bool ReachableByPathFixingAut(int v, List<int> explored)
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

            private void HandleLeaf(int[] cellOf)
            {
                LeafCount++;
                int[] perm = (int[])cellOf.Clone();
                int[] matrix = BuildPermutedMatrix(_adj, perm, _n);

                if (BestMatrix == null || LexLess(matrix, BestMatrix))
                    BestMatrix = matrix;

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

            private bool IsAutomorphism(int[] g)
            {
                for (int i = 0; i < _n; i++)
                    for (int j = 0; j < _n; j++)
                        if (_adj[g[i] * _n + g[j]] != _adj[i * _n + j])
                            return false;
                return true;
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

        // ── Tier 0: component decomposition ──────────────────────────────────

        // Connected components of G, treated as undirected (u ~ v if G has an
        // edge either way). Each component is a sorted vertex-index array.
        private static List<int[]> ConnectedComponents(AdjMatrix G)
        {
            int n = G.VertexCount;
            var compOf = new int[n];
            for (int i = 0; i < n; i++) compOf[i] = -1;
            var components = new List<int[]>();
            var queue = new Queue<int>();
            for (int s = 0; s < n; s++)
            {
                if (compOf[s] >= 0) continue;
                int id = components.Count;
                var members = new List<int> { s };
                compOf[s] = id;
                queue.Clear();
                queue.Enqueue(s);
                while (queue.Count > 0)
                {
                    int u = queue.Dequeue();
                    for (int v = 0; v < n; v++)
                    {
                        if (compOf[v] >= 0) continue;
                        if (G[u, v] != 0 || G[v, u] != 0)
                        {
                            compOf[v] = id;
                            members.Add(v);
                            queue.Enqueue(v);
                        }
                    }
                }
                members.Sort();
                components.Add(members.ToArray());
            }
            return components;
        }

        // Canonize each connected component independently, then lay the
        // component canonicals out block-diagonally in an iso-invariant order.
        // The order key is (vertex count, sorted type multiset, canonical
        // adjacency) — a complete invariant for uniform-type graphs (the
        // project's test corpus) and a sound partial one otherwise.
        private AdjMatrix CombineComponents(VertexType[] vertexTypes, AdjMatrix G,
                                            List<int[]> components)
        {
            int n = G.VertexCount;
            var canon = new List<(int Size, int[] TypeMultiset, AdjMatrix Canon)>(components.Count);

            foreach (var members in components)
            {
                int k = members.Length;
                var subEdges = new EdgeType[k, k];
                for (int i = 0; i < k; i++)
                    for (int j = 0; j < k; j++)
                        subEdges[i, j] = G[members[i], members[j]];

                var subTypes = new VertexType[k];
                for (int i = 0; i < k; i++) subTypes[i] = vertexTypes[members[i]];
                var typeMultiset = (int[])subTypes.Clone();
                Array.Sort(typeMultiset);

                AdjMatrix subCanon = RunConnected(subTypes, new AdjMatrix(subEdges));
                canon.Add((k, typeMultiset, subCanon));
            }

            canon.Sort(CompareComponent);

            var result = new EdgeType[n, n];
            int offset = 0;
            foreach (var (size, _, sub) in canon)
            {
                for (int i = 0; i < size; i++)
                    for (int j = 0; j < size; j++)
                        result[offset + i, offset + j] = sub[i, j];
                offset += size;
            }
            return new AdjMatrix(result);
        }

        private static int CompareComponent(
            (int Size, int[] TypeMultiset, AdjMatrix Canon) a,
            (int Size, int[] TypeMultiset, AdjMatrix Canon) b)
        {
            if (a.Size != b.Size) return a.Size.CompareTo(b.Size);
            for (int i = 0; i < a.Size; i++)
                if (a.TypeMultiset[i] != b.TypeMultiset[i])
                    return a.TypeMultiset[i].CompareTo(b.TypeMultiset[i]);
            return string.CompareOrdinal(a.Canon.ToString(), b.Canon.ToString());
        }

        // ── Internal record ──────────────────────────────────────────────────

        private struct Primary
        {
            public int A, B;
            public sbyte Direction;   // LESS (A<B) or GREATER (A>B)
            public bool BetweenCell;  // false = within-cell, true = between-cell
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
                var prim = new Primary
                {
                    A = a, B = b, Direction = LESS, BetweenCell = false,
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
                var prim = new Primary
                {
                    A = a, B = b, Direction = LESS, BetweenCell = true,
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

                // Direction-only flip: try (primI.A, primI.B, -primI.Direction).
                // If the resulting canonical is lex-smaller, adopt.
                var flipped = new Primary
                {
                    A = primI.A, B = primI.B,
                    Direction = (sbyte)(-primI.Direction),
                    BetweenCell = primI.BetweenCell,
                };

                var deeper = new List<Primary>(current.Count - i - 1);
                for (int j = i + 1; j < current.Count; j++) deeper.Add(current[j]);

                var suffix = TryReplayFromState(n, adj,
                                                pPrefix[i], partPrefix[i],
                                                flipped, deeper,
                                                out bool deeperBroken,
                                                out sbyte[]? pBranch);
                if (suffix == null || pBranch == null) continue;
                if (deeperBroken) LastLockedThenInvalidated++;

                int[] permBranch = ReadPermutation(n, pBranch);
                int[] matBranch = BuildPermutedMatrix(adj, permBranch, n);

                if (LexLess(matBranch, matBest))
                {
                    matBest = matBranch;
                    var newRecord = new List<Primary>(i + suffix.Count);
                    for (int j = 0; j < i; j++) newRecord.Add(current[j]);
                    newRecord.AddRange(suffix);
                    current = newRecord;
                    LastBackwardFlips++;
                }
            }

            return current;
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

            foreach (var prim in deeper)
            {
                if (!ApplyOne(p, n, prim))
                {
                    anyBroken = true;
                    break;
                }
                partition.Refine(adj, p);
                result.Add(prim);
            }

            while (!IsTotal(n, p))
            {
                if (!PickAndApplyGuess(n, adj, p, partition, result))
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

        // ── Phase 1 instrumentation: single-flip rotation probing ────────────
        //
        // Runs the forward pass to get a baseline P, then enumerates every
        // rotation alternative at every primary (the same loop the backward
        // pass uses) and records, per alternative, which P entries differ
        // from baseline. Reports false-symmetry counts and per-entry
        // coupling-candidate counts.
        //
        // Cost: O(n²) primaries × O(n²) alternatives per primary × O(n⁴)
        // per replay = O(n⁸) total — same as one backward sweep, just
        // recording diffs instead of doing lex-min. The polynomial-bound
        // calculator (route 2) would replace this measurement with a
        // closed-form symbolic representation; this method exists to
        // empirically validate the load-bearing assumption that affected-
        // entry sets fit XOR structure on the test corpus.
        public RotationProbingReport ProbeRotationsSingleFlip(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            int n = G.VertexCount;
            int[] adj = ExtractAdj(G);

            // Forward pass: baseline record + warm-refined partition.
            sbyte[] p = SeedFromTypes(n, vertexTypes);
            var partition = new WarmPartition(n);
            List<Primary> record = ContinueForward(n, adj, p, partition);

            // Cached prefix state for efficient per-branch replay.
            var (pPrefix, partPrefix) = BuildPrefixStack(n, vertexTypes, adj, record);
            if (pPrefix == null)
                throw new InvalidOperationException("Baseline prefix stack failed");

            sbyte[] baselineP = pPrefix[record.Count];

            var probes = new List<RotationProbeData>();
            var entryAffectCount = new Dictionary<int, int>();

            for (int i = 0; i < record.Count; i++)
            {
                var primI = record[i];

                var deeper = new List<Primary>(record.Count - i - 1);
                for (int j = i + 1; j < record.Count; j++) deeper.Add(record[j]);

                // Direction-only probe: flip primary i's direction, keep
                // pair (a, b). One probe per primary.
                var flipped = new Primary
                {
                    A = primI.A, B = primI.B,
                    Direction = (sbyte)(-primI.Direction),
                    BetweenCell = primI.BetweenCell,
                };

                var suffix = TryReplayFromState(n, adj,
                                                pPrefix[i], partPrefix[i],
                                                flipped, deeper,
                                                out _, out sbyte[]? branchP);
                if (suffix == null || branchP == null) continue;

                // Diff vs baseline.
                var affected = new List<int>();
                for (int idx = 0; idx < n * n; idx++)
                {
                    if (baselineP[idx] != branchP[idx])
                    {
                        affected.Add(idx);
                        entryAffectCount[idx] =
                            entryAffectCount.GetValueOrDefault(idx, 0) + 1;
                    }
                }

                probes.Add(new RotationProbeData(
                    LayerId: i,
                    OriginalA: primI.A, OriginalB: primI.B,
                    OriginalDirection: primI.Direction,
                    BetweenCell: primI.BetweenCell,
                    AlternativeA: primI.A, AlternativeB: primI.B,
                    AlternativeDirection: flipped.Direction,
                    AffectedEntries: affected.ToArray()));
            }

            int couplingCandidates = 0;
            foreach (var kv in entryAffectCount)
                if (kv.Value >= 2) couplingCandidates++;

            return new RotationProbingReport
            {
                N = n,
                PrimaryCount = record.Count,
                Probes = probes,
                CouplingCandidateEntries = couplingCandidates,
            };
        }

        // Replay the baselineRecord from scratch, substituting `subs[i]` for
        // baselineRecord[i] wherever a substitution is specified. After every
        // primary is applied (substituted or not), refine the partition and
        // continue forward to total. Used by ProbeXorCouplings to compute the
        // P state resulting from any combination of primary substitutions.
        private List<Primary>? ReplayWithSubstitutions(
            int n, int[] adj, VertexType[] vertexTypes,
            List<Primary> baselineRecord,
            Dictionary<int, Primary> subs,
            out sbyte[]? finalP)
        {
            sbyte[] p = SeedFromTypes(n, vertexTypes);
            var partition = new WarmPartition(n);
            partition.Refine(adj, p);

            var result = new List<Primary>(baselineRecord.Count);

            for (int i = 0; i < baselineRecord.Count; i++)
            {
                var prim = subs.TryGetValue(i, out var sub) ? sub : baselineRecord[i];
                if (!ApplyOne(p, n, prim))
                {
                    finalP = null;
                    return null;
                }
                partition.Refine(adj, p);
                result.Add(prim);
            }

            while (!IsTotal(n, p))
            {
                if (!PickAndApplyGuess(n, adj, p, partition, result))
                {
                    finalP = null;
                    return null;
                }
            }

            finalP = p;
            return result;
        }

        // Phase 2 instrumentation: for each coupling-candidate entry from
        // Phase 1 (one affected by ≥ 2 single-flip probes), test whether the
        // entry's direction as a function of involved-primary substitutions
        // fits a linear-over-Z₂ (XOR) model.
        //
        // Procedure:
        //   1. Run Phase 1 to learn which primaries' alternatives affect which
        //      entries.
        //   2. Pick one representative alternative per "involved" primary
        //      (any primary whose alternatives affect some entry). The
        //      representative is the first probe (in Phase 1's enumeration
        //      order) that has non-empty AffectedEntries at this primary.
        //   3. Precompute K single-substitution P arrays and K(K-1)/2 pair-
        //      substitution P arrays, where K = involved primary count.
        //   4. For each coupling-candidate entry E:
        //        a. Identify primaries involved for E (subset of the K).
        //        b. Compute fit coefficients: c_0 = baselineP[E];
        //           c_i = singleP_i[E] XOR c_0.
        //        c. Verify on every pair (i, j):
        //           pairP_{i,j}[E] should equal c_0 XOR c_i XOR c_j.
        //        d. If all pair verifications match, FitsXor = true.
        //
        // Cost: O(K² · n⁴) for the precomputed forward passes + O(entries · k²)
        // for lookups, where K ≤ PrimaryCount and k is per-entry variable
        // count. Polynomial; tractable up to CFI(Cycle4) within this design.
        public CouplingFitReport ProbeXorCouplings(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            int n = G.VertexCount;
            int[] adj = ExtractAdj(G);

            // Forward pass: baseline record + baseline P.
            sbyte[] p = SeedFromTypes(n, vertexTypes);
            var partition = new WarmPartition(n);
            List<Primary> baseline = ContinueForward(n, adj, p, partition);

            var (pPrefix, _) = BuildPrefixStack(n, vertexTypes, adj, baseline);
            if (pPrefix == null)
                throw new InvalidOperationException("Baseline prefix stack failed");
            sbyte[] baselineP = pPrefix[baseline.Count];

            // Phase 1: get single-flip probes + affected-entries map.
            var phase1 = ProbeRotationsSingleFlip(vertexTypes, G);

            // Choose one representative alternative per involved primary.
            // The first probe (in phase1.Probes order) with non-empty
            // AffectedEntries at that primary wins.
            // Each "involved" primary has exactly one alternative — its
            // direction flip. Map: primary index → flipped Primary record.
            var primaryReps = new Dictionary<int, Primary>();
            foreach (var probe in phase1.Probes)
            {
                if (probe.AffectedEntries.Length == 0) continue;
                if (!primaryReps.ContainsKey(probe.LayerId))
                {
                    primaryReps[probe.LayerId] = new Primary
                    {
                        A = probe.AlternativeA,
                        B = probe.AlternativeB,
                        Direction = probe.AlternativeDirection,
                        BetweenCell = probe.BetweenCell,
                    };
                }
            }

            int[] involvedPrimaries = primaryReps.Keys.OrderBy(k => k).ToArray();
            int K = involvedPrimaries.Length;
            int forwardPassesRun = 0;

            // Precompute single-substitution P arrays.
            var singleP = new sbyte[K][];
            for (int idx = 0; idx < K; idx++)
            {
                var sub = new Dictionary<int, Primary>
                {
                    [involvedPrimaries[idx]] = primaryReps[involvedPrimaries[idx]]
                };
                ReplayWithSubstitutions(n, adj, vertexTypes, baseline, sub, out sbyte[]? sp);
                singleP[idx] = sp ?? baselineP;
                forwardPassesRun++;
            }

            // Precompute pair-substitution P arrays (lower triangular keyed
            // by (i, j) with i < j).
            var pairP = new Dictionary<(int, int), sbyte[]>();
            for (int i = 0; i < K; i++)
            {
                for (int j = i + 1; j < K; j++)
                {
                    var sub = new Dictionary<int, Primary>
                    {
                        [involvedPrimaries[i]] = primaryReps[involvedPrimaries[i]],
                        [involvedPrimaries[j]] = primaryReps[involvedPrimaries[j]],
                    };
                    ReplayWithSubstitutions(n, adj, vertexTypes, baseline, sub, out sbyte[]? pp);
                    if (pp != null) pairP[(i, j)] = pp;
                    forwardPassesRun++;
                }
            }

            // For each coupling-candidate entry, fit XOR coefficients and
            // verify against precomputed pair P arrays.
            var entryToProbes = new Dictionary<int, List<RotationProbeData>>();
            foreach (var probe in phase1.Probes)
            {
                if (probe.AffectedEntries.Length == 0) continue;
                foreach (var entry in probe.AffectedEntries)
                {
                    if (!entryToProbes.TryGetValue(entry, out var list))
                    {
                        list = new List<RotationProbeData>();
                        entryToProbes[entry] = list;
                    }
                    list.Add(probe);
                }
            }

            var primaryToIdx = new Dictionary<int, int>();
            for (int i = 0; i < K; i++) primaryToIdx[involvedPrimaries[i]] = i;

            var fits = new List<XorCouplingFit>();
            int couplingCandidatesTested = 0;

            foreach (var (entryIdx, probesForEntry) in entryToProbes)
            {
                // Coupling candidate: at least 2 distinct involved primaries.
                var primaries = probesForEntry.Select(p => p.LayerId).Distinct().OrderBy(p => p).ToArray();
                if (primaries.Length < 2) continue;
                couplingCandidatesTested++;

                // Compute fit coefficients from baseline + singles.
                bool c0 = (baselineP[entryIdx] == LESS);
                bool[] coefs = new bool[primaries.Length];
                bool fitFailed = false;
                for (int i = 0; i < primaries.Length; i++)
                {
                    int pidx = primaryToIdx[primaries[i]];
                    bool singleVal = (singleP[pidx][entryIdx] == LESS);
                    coefs[i] = singleVal ^ c0;
                }

                // Verify on every pair.
                int pairsChecked = 0, pairsMatched = 0;
                for (int i = 0; i < primaries.Length; i++)
                {
                    for (int j = i + 1; j < primaries.Length; j++)
                    {
                        int pi = primaryToIdx[primaries[i]];
                        int pj = primaryToIdx[primaries[j]];
                        int pmin = Math.Min(pi, pj), pmax = Math.Max(pi, pj);
                        if (!pairP.TryGetValue((pmin, pmax), out var pp))
                        {
                            // Pair substitution failed at replay time; can't
                            // verify; conservatively mark fit as failed.
                            fitFailed = true;
                            pairsChecked++;
                            continue;
                        }
                        pairsChecked++;
                        bool pairVal = (pp[entryIdx] == LESS);
                        bool predicted = c0 ^ coefs[i] ^ coefs[j];
                        if (pairVal == predicted) pairsMatched++;
                        else fitFailed = true;
                    }
                }

                fits.Add(new XorCouplingFit(
                    EntryFlatIndex: entryIdx,
                    InvolvedPrimaries: primaries,
                    FitsXor: !fitFailed,
                    XorCoefficients: coefs,
                    ConstantTerm: c0,
                    PairsChecked: pairsChecked,
                    PairsMatched: pairsMatched));
            }

            return new CouplingFitReport
            {
                N = n,
                PrimaryCount = baseline.Count,
                CouplingCandidatesTested = couplingCandidatesTested,
                ForwardPassesRun = forwardPassesRun,
                Fits = fits,
            };
        }
    }
}
