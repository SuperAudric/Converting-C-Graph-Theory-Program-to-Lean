using Xunit;
using Canonizer;
using VertexType = int;

// Scaling probe for the chain-descent canonizer (docs/chain-descent-strategy.md
// §8, §14). Not a correctness test: it runs CFI graphs of growing size under a
// small node budget and records the descent cost (node count, depth, the flag
// verdict and kind). It confirms the canonizer is *bounded* — every run either
// returns a canonical form or raises CanonizationFlaggedException, and never
// explores past the budget. The recorded numbers are the diagnostic value.
public partial class GraphCanonTests
{
    [Theory]
    [InlineData("Cycle3")]
    [InlineData("Cycle4")]
    [InlineData("Cycle6")]
    [InlineData("Cycle8")]
    [InlineData("K4")]
    public void CDScale_Cfi_CanonizesOrFlags_WithinBudget(string baseGraph)
    {
        const long budget = 5000;
        var pair = CfiGraphGenerator.Generate(baseGraph);

        foreach (var (label, g) in new[] { ("even", pair.Even), ("odd", pair.Odd) })
        {
            var cd = new CanonGraphOrdererChainDescent { BudgetOverride = budget };
            int n = g.VertexCount;

            string outcome;
            try
            {
                cd.Run(new VertexType[n], g);
                outcome = "canonical";
            }
            catch (CanonizationFlaggedException ex)
            {
                outcome = $"flagged [{cd.LastFlagKind}] — {ex.Reason}";
            }

            // Bounded: the descent never explores past the budget. The
            // load-bearing assertion — polynomial-or-flag, never unbounded.
            Assert.True(cd.LastNodeCount <= budget + 1,
                $"CFI({baseGraph}) {label}: node count {cd.LastNodeCount} exceeded budget {budget}");

            output.WriteLine(
                $"CFI({baseGraph},{label}) n={n,3}  {outcome,-46}  " +
                $"nodes={cd.LastNodeCount,6}/{budget}  depth={cd.LastMaxDepth,3}  " +
                $"leaves={cd.LastLeafCount,6}  pruned={cd.LastPrunedBranches,6}  " +
                $"|Aut|~{cd.LastAutomorphismGroupOrder}");
        }
    }

    // The flag mechanism itself: a budget far below any non-trivial descent
    // forces budget exhaustion, exercising the CanonizationFlaggedException
    // path deterministically. A *natural* flag needs a graph whose descent
    // genuinely outgrows a polynomial budget — the rigid multipede family;
    // CFI, being abelian, is collapsed cheaply by orbit pruning (see the probe
    // above), and no multipede generator exists yet.
    [Fact]
    public void CDScale_TinyBudget_ForcesFlag()
    {
        var pair = CfiGraphGenerator.Generate("Cycle3");
        var cd = new CanonGraphOrdererChainDescent { BudgetOverride = 3 };

        var ex = Assert.Throws<CanonizationFlaggedException>(
            () => { cd.Run(new VertexType[pair.Odd.VertexCount], pair.Odd); });

        Assert.Contains("budget", ex.Reason);
        Assert.True(cd.LastNodeCount <= 4,
            $"node count {cd.LastNodeCount} should respect budget 3");
        Assert.NotEqual(FlagKind.None, cd.LastFlagKind);
    }
}
