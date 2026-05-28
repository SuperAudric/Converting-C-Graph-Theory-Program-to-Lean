using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// M3 — candidate twist construction (docs/chain-descent-linear-oracle.md §4.2).
// Canonical-colour matching on the all-singletons footprint; soundness is the
// caller's IsAutomorphism check, validated here on a real CFI(K4) decision.
public class TwistConstructionTests
{
    private readonly ITestOutputHelper _out;
    public TwistConstructionTests(ITestOutputHelper output) => _out = output;

    private static RefinementFootprint Footprint(int n, int[] parent, int[] child) =>
        RefinementFootprint.Compute(n, parent, child);

    // ── Pure construction logic ──────────────────────────────────────────

    [Fact]
    public void TryConstruct_AllSingletons_MatchesByColour()
    {
        // parent: one cell → branch1 four singletons; branchJ swaps the colour
        // assignment pairwise. t should map by colour: 0↔1, 2↔3.
        var fp = Footprint(4, new[] { 0, 0, 0, 0 }, new[] { 0, 1, 2, 3 });
        var t = TwistConstruction.TryConstruct(4, fp,
            branch1CellOf: new[] { 0, 1, 2, 3 },
            branchJCellOf: new[] { 1, 0, 3, 2 });
        Assert.NotNull(t);
        Assert.Equal(new[] { 1, 0, 3, 2 }, t);
    }

    [Fact]
    public void TryConstruct_IdentityOffFootprint()
    {
        // parent {0,1}=cell0, {2,3}=cell1; only cell0 splits (singletons),
        // cell1 untouched. t must be identity on the untouched cell.
        var fp = Footprint(4, new[] { 0, 0, 1, 1 }, new[] { 0, 1, 2, 2 });
        var t = TwistConstruction.TryConstruct(4, fp,
            branch1CellOf: new[] { 0, 1, 2, 2 },
            branchJCellOf: new[] { 1, 0, 2, 2 });
        Assert.NotNull(t);
        Assert.Equal(new[] { 1, 0, 2, 3 }, t); // swap 0,1; fix 2,3
    }

    [Fact]
    public void TryConstruct_NonSingletonSubCell_ReturnsNull()
    {
        // split cell 0 → {0,1},{2,3}: sub-cells of size 2, not all-singletons.
        var fp = Footprint(4, new[] { 0, 0, 0, 0 }, new[] { 0, 0, 1, 1 });
        var t = TwistConstruction.TryConstruct(4, fp,
            branch1CellOf: new[] { 0, 0, 1, 1 },
            branchJCellOf: new[] { 1, 1, 0, 0 });
        Assert.Null(t);
    }

    [Fact]
    public void TryConstruct_MismatchedBranches_ReturnsNull()
    {
        // all-singletons footprint, but branchJ's colours over K don't form a
        // matching bijection (colour 2 doubled, 3 absent) ⇒ no candidate.
        var fp = Footprint(4, new[] { 0, 0, 0, 0 }, new[] { 0, 1, 2, 3 });
        var t = TwistConstruction.TryConstruct(4, fp,
            branch1CellOf: new[] { 0, 1, 2, 3 },
            branchJCellOf: new[] { 0, 1, 2, 2 });
        Assert.Null(t);
    }

    [Fact]
    public void TryConstruct_EmptyFootprint_ReturnsNull()
    {
        var fp = Footprint(4, new[] { 0, 0, 1, 1 }, new[] { 0, 0, 1, 1 });
        Assert.Null(TwistConstruction.TryConstruct(4, fp,
            new[] { 0, 0, 1, 1 }, new[] { 0, 0, 1, 1 }));
    }

}
