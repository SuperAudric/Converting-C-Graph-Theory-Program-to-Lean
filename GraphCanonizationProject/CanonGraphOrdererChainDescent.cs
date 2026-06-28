using System;
using System.Collections.Generic;
using System.Numerics;

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    // Chain-descent graph canonizer — see docs/chain-descent-strategy.md.
    //
    // Run() decomposes the graph into connected components (Tier 0), canonizes
    // each with the chain-descent harness, and lays the component canonicals
    // out block-diagonally in an iso-invariant order; a connected graph goes
    // straight to the harness.
    //
    // The harness (ChainDescent) is a budget-bounded recursive lex-min over the
    // individualization-refinement tree. A run that exceeds the polynomial node
    // budget raises CanonizationFlaggedException rather than continuing — an
    // honest "not handled", never a wrong answer.
    public sealed class CanonGraphOrdererChainDescent : ICanonGraphOrderer
    {
        private const sbyte LESS = -1, UNKNOWN = 0, GREATER = 1;

        // ── Diagnostics from the last Run() (the last connected component) ───
        public int LastLeafCount { get; private set; }
        public int LastPrunedBranches { get; private set; }
        public long LastNodeCount { get; private set; }
        public int LastMaxDepth { get; private set; }

        // Cascade-harvest attribution (CascadeStats). LastBranchingNodes/LastPhase2Nodes
        // = whether REAL branching occurred (≈0 ⇒ single path via harvested symmetry).
        // LastMaxRecursionDepth/LastResolvedByRecursion/LastGeneratorsHarvested = the
        // (unbudgeted) exploratory-harvest cost — the suspect for off-budget grind.
        public long LastBranchingNodes { get; private set; }
        public long LastDecisionNodes { get; private set; }
        public long LastPhase2Nodes { get; private set; }
        public long LastGeneratorsHarvested { get; private set; }
        public long LastResolvedByRecursion { get; private set; }
        public int LastMaxRecursionDepth { get; private set; }

        // Resolution-mechanism histogram (Route A): how the single-path symmetric
        // cells got resolved. LastClassifyStarved > 0 ⟹ the existing harvest is NOT
        // provably complete on this case (a real decision the harvest could not
        // collapse). All resolution via class 1/3 with starved == 0 ⟹ the harvest
        // always recovered the cell's orbit — the Route-A invariant holds here.
        public long LastClassifyClass1 { get; private set; }
        public long LastClassifyClass3 { get; private set; }
        public long LastClassifyStarved { get; private set; }
        public long LastConsumedSymmetric { get; private set; }

        // The node budget the last run carried (interpret LastNodeCount
        // against it), and the descent-tree node count per depth — the cost
        // shape (a flat all-ones profile is a single descent path).
        public long LastBudget { get; private set; }
        public IReadOnlyList<int> LastNodesByDepth { get; private set; } = [];

        // Order of the automorphism group harvested during the descent.
        public BigInteger LastAutomorphismGroupOrder { get; private set; }

        // The automorphism group itself, harvested during the descent. Same
        // group whose .Order is exposed above. Useful for analyses needing
        // explicit generators or orbit computations.
        public PermutationGroup? LastAutomorphisms { get; private set; }

        // The flag reason (null when the run produced a canonical form) and
        // its classification (docs/chain-descent-strategy.md §15).
        public string? LastFlagReason { get; private set; }
        public FlagKind LastFlagKind { get; private set; }

        // Optional override for the descent's polynomial node budget; null
        // uses ChainDescent.DefaultBudget(n).
        public long? BudgetOverride { get; set; }

        public AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            // Tier 0 — component decomposition. A disjoint union's automorphism
            // group factors over its connected components; canonizing each
            // independently and combining keeps disjoint unions linear in the
            // component count. See docs/chain-descent-strategy.md §15.
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

            sbyte[] p = SeedFromTypes(n, vertexTypes);
            var partition = new WarmPartition(n);

            long budget = BudgetOverride ?? ChainDescent.DefaultBudget(n);
            var descent = new ChainDescent(n, adj, new CascadeOracle(), budget);
            CanonResult result = descent.Canonize(p, partition);

            LastNodeCount = result.Stats.NodeCount;
            LastMaxDepth = result.Stats.MaxDepth;
            LastPrunedBranches = result.Stats.PrunedBranches;
            LastLeafCount = result.Stats.LeafCount;
            LastBranchingNodes = result.Stats.Cascade.BranchingNodes;
            LastDecisionNodes = result.Stats.Cascade.DecisionNodes;
            LastPhase2Nodes = result.Stats.Cascade.Phase2Nodes;
            LastGeneratorsHarvested = result.Stats.Cascade.GeneratorsHarvested;
            LastResolvedByRecursion = result.Stats.Cascade.ResolvedByRecursion;
            LastMaxRecursionDepth = result.Stats.Cascade.MaxRecursionDepth;
            LastClassifyClass1 = result.Stats.Cascade.ClassifyClass1;
            LastClassifyClass3 = result.Stats.Cascade.ClassifyClass3;
            LastClassifyStarved = result.Stats.Cascade.ClassifyStarved;
            LastConsumedSymmetric = result.Stats.Cascade.ConsumedSymmetric;
            LastBudget = result.Stats.Budget;
            LastNodesByDepth = result.Stats.NodesByDepth;
            LastAutomorphismGroupOrder = result.ResidualGroup.Order;
            LastAutomorphisms = result.ResidualGroup;
            LastFlagReason = result.Flagged ? result.FlagReason : null;
            LastFlagKind = result.Flagged
                ? CanonizationFlaggedException.ClassifyFlag(result.ResidualGroup)
                : FlagKind.None;

            if (result.Flagged)
                throw new CanonizationFlaggedException(
                    result.FlagReason ?? "flagged", result.ResidualGroup);

            int[] best = result.Matrix!;
            var canonical = new EdgeType[n, n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    canonical[i, j] = best[i * n + j];
            return new AdjMatrix(canonical);
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

        // ── Seed / adjacency helpers ─────────────────────────────────────────

        private static int[] ExtractAdj(AdjMatrix G)
        {
            int n = G.VertexCount;
            var adj = new int[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    adj[i * n + j] = G[i, j];
            return adj;
        }

        // Bootstrap the seed partial order from vertex types: i < j whenever
        // type(i) < type(j); a uniform-type graph seeds to all-unknown.
        private static sbyte[] SeedFromTypes(int n, int[] types)
        {
            var p = new sbyte[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (i != j && types[i] < types[j]) { p[i * n + j] = LESS; p[j * n + i] = GREATER; }
            TransitiveClose(p, n);
            return p;
        }

        // Full Floyd–Warshall transitive closure, used once to close the
        // type-seeded partial order. Returns false on a cycle / conflict.
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
    }
}
