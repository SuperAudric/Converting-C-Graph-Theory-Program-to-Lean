using Xunit;
using Xunit.Abstractions;
using Canonizer;

// M4 — the linear oracle wired into the descent: after exploring the first
// representative, construct/verify/harvest twists onto the others so
// CoveredByPathFixingAut prunes them a priori. Validated against the harness's
// own warm partitions (docs/chain-descent-linear-oracle.md §4.2, §6.2).
public class LinearOracleTests
{
    private readonly ITestOutputHelper _out;
    public LinearOracleTests(ITestOutputHelper output) => _out = output;

    private static int[] ExtractAdj(AdjMatrix g)
    {
        int n = g.VertexCount;
        var adj = new int[n * n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                adj[i * n + j] = g[i, j];
        return adj;
    }

    private static CanonResult Run(int n, int[] adj, bool oracle)
    {
        var d = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        {
            EnableLinearOracle = oracle
        };
        return d.Canonize(new sbyte[n * n], new WarmPartition(n));
    }

    // Relabel adj by a permutation: new[perm[i], perm[j]] = old[i, j].
    private static int[] ApplyPerm(int n, int[] adj, int[] perm)
    {
        var m = new int[n * n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                m[perm[i] * n + perm[j]] = adj[i * n + j];
        return m;
    }

    private static int[] SeededPerm(int n, int seed)
    {
        var p = new int[n];
        for (int i = 0; i < n; i++) p[i] = i;
        var rng = new System.Random(seed);
        for (int i = n - 1; i > 0; i--)
        {
            int j = rng.Next(i + 1);
            (p[i], p[j]) = (p[j], p[i]);
        }
        return p;
    }

    // The linear oracle must not change the answer (sound pruning by verified
    // automorphisms) and must not increase work — and on genuine-decision CFI
    // it should drop the explored leaf count.
    [Theory]
    [InlineData("K4")]
    [InlineData("K33")]
    [InlineData("Petersen")]
    public void LinearOracle_PreservesCanonical_AndDropsLeaves(string baseGraph)
    {
        var pair = CfiGraphGenerator.Generate(baseGraph);
        foreach (var (label, g) in new[] { ("even", pair.Even), ("odd", pair.Odd) })
        {
            int n = g.VertexCount;
            var adj = ExtractAdj(g);

            var off = Run(n, adj, oracle: false);
            var on = Run(n, adj, oracle: true);

            Assert.False(off.Flagged);
            Assert.False(on.Flagged);
            Assert.NotNull(off.Matrix);
            Assert.NotNull(on.Matrix);

            // Correctness: the linear oracle reaches the same canonical form.
            Assert.Equal(off.Matrix, on.Matrix);

            // Payoff: never more leaves with the oracle on.
            Assert.True(on.Stats.LeafCount <= off.Stats.LeafCount,
                $"CFI({baseGraph},{label}): leaves on={on.Stats.LeafCount} > off={off.Stats.LeafCount}");

            _out.WriteLine(
                $"CFI({baseGraph,-9}{label,-4}) n={n,4}  " +
                $"leaves off={off.Stats.LeafCount,5} on={on.Stats.LeafCount,5}  " +
                $"nodes off={off.Stats.NodeCount,6} on={on.Stats.NodeCount,6}  " +
                $"|Aut| off={off.ResidualGroup.Order} on={on.ResidualGroup.Order}");
        }
    }

    // Even and Odd CFI graphs stay distinguishable with the oracle on.
    [Theory]
    [InlineData("K4")]
    [InlineData("K33")]
    [InlineData("Petersen")]
    public void LinearOracle_EvenOddRemainDistinct(string baseGraph)
    {
        var pair = CfiGraphGenerator.Generate(baseGraph);
        var even = Run(pair.Even.VertexCount, ExtractAdj(pair.Even), oracle: true);
        var odd = Run(pair.Odd.VertexCount, ExtractAdj(pair.Odd), oracle: true);
        Assert.NotNull(even.Matrix);
        Assert.NotNull(odd.Matrix);
        Assert.NotEqual(even.Matrix, odd.Matrix);
    }

    // M6 — the leaf-count scaling bar (docs/chain-descent-linear-oracle.md §8.1,
    // build brief M6). The metric is *leaf count*, not memory: the spine (or any
    // runtime optimization) lowers memory/time but never the leaf count, so leaf
    // count isolates the oracle's behavioural effect (strategy §12). Logs the
    // off-vs-on curve so we can see whether the oracle changes the growth
    // *exponent* (polynomial vs exponential) or only a constant factor.
    [Fact]
    public void M6_LeafScaling_OffVsOn()
    {
        var bases = new (string Name, int Beta)[]
        {
            ("K4", 3), ("K33", 4), ("Petersen", 6), ("Rook3x3", 10), ("K6", 10),
        };

        _out.WriteLine($"{"base",-9}{"β",3} {"par",-5}{"n",5}  " +
                       $"{"leavesOff",10}{"leavesOn",10}{"ratio",7}   " +
                       $"{"nodesOff",10}{"nodesOn",10}  |Aut|");
        foreach (var (name, beta) in bases)
        {
            var pair = CfiGraphGenerator.Generate(name);
            foreach (var (label, g) in new[] { ("even", pair.Even), ("odd", pair.Odd) })
            {
                int n = g.VertexCount;
                var adj = ExtractAdj(g);
                var off = Run(n, adj, oracle: false);
                var on = Run(n, adj, oracle: true);

                Assert.False(off.Flagged);
                Assert.False(on.Flagged);
                Assert.Equal(off.Matrix, on.Matrix);                       // correctness
                Assert.True(on.Stats.LeafCount <= off.Stats.LeafCount);    // no worse

                double ratio = off.Stats.LeafCount == 0
                    ? 1.0 : (double)on.Stats.LeafCount / off.Stats.LeafCount;
                _out.WriteLine($"{name,-9}{beta,3} {label,-5}{n,5}  " +
                               $"{off.Stats.LeafCount,10}{on.Stats.LeafCount,10}{ratio,7:F2}   " +
                               $"{off.Stats.NodeCount,10}{on.Stats.NodeCount,10}  {on.ResidualGroup.Order}");
            }
        }
    }

    // The a-priori cascade oracle's cost-shape probe (docs/chain-descent-cascade-oracle.md
    // §8.1 M5). Attributes the residual branching on a CFI base by footprint
    // class: all-singleton (linear oracle, depth 0), resolved (cascade recursion
    // deepened to all-singleton), or starved (still non-singleton past the depth
    // bound). The bar the cascade oracle must clear: *no branching survives at a
    // starved footprint* — the recursion resolves every non-singleton case on
    // these CFI bases (baseline before M2: every branching node was starved, e.g.
    // K7 had 555). The recursion depth bottoms out near tw(H), far below n.
    [Theory]
    [Trait("Category", "LongRunning")]
    [InlineData("Petersen")]
    [InlineData("Rook3x3")]
    [InlineData("K6")]
    [InlineData("K7")]
    public void Cascade_Attribution_StarvationResolved(string baseGraph)
    {
        var g = CfiGraphGenerator.Generate(baseGraph).Odd;
        int n = g.VertexCount;
        var adj = ExtractAdj(g);
        var d = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        {
            EnableLinearOracle = true
        };
        var r = d.Canonize(new sbyte[n * n], new WarmPartition(n));
        var c = r.Stats.Cascade;

        _out.WriteLine($"CFI({baseGraph}) n={n}: {(r.Flagged ? "FLAG" : "CANON")} " +
                       $"leaves={r.Stats.LeafCount} nodes={r.Stats.NodeCount}");
        _out.WriteLine($"  decisionNodes={c.DecisionNodes} branchingNodes={c.BranchingNodes} " +
                       $"harvested={c.GeneratorsHarvested} resolvedByRecursion={c.ResolvedByRecursion} maxRecDepth={c.MaxRecursionDepth}");
        _out.WriteLine($"  branch[allSingleton]={c.BranchAllSingleton}  (linear, depth 0)");
        _out.WriteLine($"  branch[resolved]    ={c.BranchResolved}  (cascade recursion harvested but a real rep remained)");
        _out.WriteLine($"  branch[starved]     ={c.BranchStarved}  (still non-singleton past the depth bound)");

        Assert.False(r.Flagged);
        // The decisive bar: the cascade recursion leaves no starved branching.
        Assert.Equal(0, c.BranchStarved);
    }

    // Deferred decisions (docs/chain-descent-deferred-decisions.md), oracle ON.
    // Deferral consumes symmetric cells first and defers real decisions to Phase 2.
    // It produces a *different* canonical form than the lowest-id schedule (the
    // schedule fixes the leaf labelling), so it is off by default; the property
    // that must still hold is **iso-invariance** — relabellings canonize identically
    // — plus Even≠Odd distinguishing. This is the correctness guard for the deferral
    // path and the empirical check of the schedule-iso-invariance obligation.
    [Theory]
    [Trait("Category", "LongRunning")]
    [InlineData("Petersen")]
    [InlineData("Rook3x3")]
    public void Deferral_ScrambleInvariant_AndDistinguishes(string baseGraph)
    {
        var pair = CfiGraphGenerator.Generate(baseGraph);
        string? even = null, odd = null;
        long deferralActive = 0, phase2 = 0;
        foreach (var (slot, g) in new[] { ("even", pair.Even), ("odd", pair.Odd) })
        {
            int n = g.VertexCount;
            var baseAdj = ExtractAdj(g);
            string? canon = null;
            for (int i = 0; i < 3; i++)
            {
                var adj = ApplyPerm(n, baseAdj, SeededPerm(n, 90210 + i));
                var d = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
                {
                    EnableLinearOracle = true,
                    EnableDeferral = true
                };
                var r = d.Canonize(new sbyte[n * n], new WarmPartition(n));
                Assert.False(r.Flagged);
                Assert.NotNull(r.Matrix);
                string c = string.Join(",", r.Matrix!);
                canon ??= c;
                Assert.Equal(canon, c); // scramble-invariant under deferral
                deferralActive += r.Stats.Cascade.DeferralActiveNodes;
                phase2 += r.Stats.Cascade.Phase2Nodes;
            }
            if (slot == "even") even = canon; else odd = canon;
        }
        Assert.NotEqual(even, odd); // deferral still distinguishes Even/Odd

        // Does deferral change the canonical vs the lowest-id schedule? Compare the
        // even graph's canonical with deferral on vs off (no assert — informational).
        int ne = pair.Even.VertexCount;
        var offR = Run(ne, ExtractAdj(pair.Even), oracle: true); // deferral off (default)
        bool sameCanon = even == string.Join(",", offR.Matrix!);
        _out.WriteLine($"CFI({baseGraph}) deferral on: " +
                       $"deferralActiveNodes(sum/6)={deferralActive} phase2Nodes(sum/6)={phase2}  " +
                       $"canonical(on==off)={sameCanon}");
    }
}
