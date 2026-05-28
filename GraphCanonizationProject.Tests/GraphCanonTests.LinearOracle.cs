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
}
