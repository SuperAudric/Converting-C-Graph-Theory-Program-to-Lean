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

    // TEMP (cascade-oracle build M1) — attribute the residual branching on a CFI
    // base: all-singleton (linear oracle fired; leftover reps are true-symmetry
    // the gauge twist doesn't cover) vs non-singleton footprint (linear oracle
    // starved — the case the a-priori cascade recursion targets). Establishes the
    // baseline M2's lockstep-deepen recursion is measured against.
    [Theory]
    [Trait("Category", "LongRunning")]
    [InlineData("Petersen")]
    [InlineData("Rook3x3")]
    [InlineData("K6")]
    [InlineData("K7")]
    public void M5_Attribution(string baseGraph)
    {
        var g = CfiGraphGenerator.Generate(baseGraph).Odd;
        int n = g.VertexCount;
        var adj = ExtractAdj(g);
        var d = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        {
            EnableLinearOracle = true
        };
        var r = d.Canonize(new sbyte[n * n], new WarmPartition(n));

        _out.WriteLine($"CFI({baseGraph}) n={n}: {(r.Flagged ? "FLAG" : "CANON")} " +
                       $"leaves={r.Stats.LeafCount} nodes={r.Stats.NodeCount}");
        _out.WriteLine($"  decisionNodes={d.DiagDecisionNodes} branchingNodes={d.DiagBranchingNodes} " +
                       $"twistsHarvested={d.DiagTwistsHarvested} resolvedByRecursion={d.DiagResolvedNodes} maxRecDepth={d.DiagMaxRecursionDepth}");
        _out.WriteLine($"  branch[allSingleton]={d.DiagBranchAllSingleton} extraReps={d.DiagExtraRepsAllSingleton}   (linear, depth 0)");
        _out.WriteLine($"  branch[resolved]    ={d.DiagBranchResolved} extraReps={d.DiagExtraRepsResolved}   (cascade recursion harvested but left reps)");
        _out.WriteLine($"  branch[nonSingleton]={d.DiagBranchNonSingleton} extraReps={d.DiagExtraRepsNonSingleton}   (still starved past depth bound)");
    }
}
