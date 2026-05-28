using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// M1 — refinement-footprint extraction (docs/chain-descent-linear-oracle.md §3,
// build brief M1/M2). The coupled component is read from the parent↔child
// partition diff, not from transitive-closure provenance (TC is inert here).
public class RefinementFootprintTests
{
    private readonly ITestOutputHelper _out;
    public RefinementFootprintTests(ITestOutputHelper output) => _out = output;

    // ── Pure diff logic ──────────────────────────────────────────────────

    [Fact]
    public void Compute_OneCellSplitsInTwo()
    {
        var parent = new[] { 0, 0, 0, 0 };
        var child = new[] { 0, 0, 1, 1 };
        var fp = RefinementFootprint.Compute(4, parent, child);

        var sc = Assert.Single(fp.SplitCells);
        Assert.Equal(0, sc.ParentCell);
        Assert.Equal(2, sc.SubCells.Length);
        Assert.Equal(new[] { 0, 1 }, sc.SubCells[0]);
        Assert.Equal(new[] { 2, 3 }, sc.SubCells[1]);
        Assert.Equal(new[] { 0, 1, 2, 3 }, fp.CoupledVertices());
        Assert.False(sc.AllSingletons);
    }

    [Fact]
    public void Compute_NoSplit_EmptyFootprint()
    {
        var parent = new[] { 0, 0, 1, 1 };
        var child = new[] { 0, 0, 1, 1 };
        var fp = RefinementFootprint.Compute(4, parent, child);

        Assert.Empty(fp.SplitCells);
        Assert.Empty(fp.CoupledVertices());
    }

    [Fact]
    public void Compute_OnlySplitCellsAppear()
    {
        // parent: {0,1}=cell 0, {2,3}=cell 1. child splits cell 1 only.
        var parent = new[] { 0, 0, 1, 1 };
        var child = new[] { 0, 0, 1, 2 };
        var fp = RefinementFootprint.Compute(4, parent, child);

        var sc = Assert.Single(fp.SplitCells);
        Assert.Equal(1, sc.ParentCell);
        Assert.Equal(new[] { 2 }, sc.SubCells[0]);
        Assert.Equal(new[] { 3 }, sc.SubCells[1]);
        Assert.True(sc.AllSingletons);
        Assert.Equal(new[] { 2, 3 }, fp.CoupledVertices());
    }

    [Fact]
    public void Compute_AllSingletons_DetectsForcedMatching()
    {
        var parent = new[] { 0, 0, 0 };
        var child = new[] { 0, 1, 2 };
        var fp = RefinementFootprint.Compute(3, parent, child);

        var sc = Assert.Single(fp.SplitCells);
        Assert.True(sc.AllSingletons);
        Assert.Equal(3, sc.SubCells.Length);
    }

    // ── Mechanism smoke on a real CFI graph ──────────────────────────────
    //
    // CFI(Cycle3) cascades by distance (no genuine abelian decision — that is
    // CFI(K4)'s regime), so this only validates that the diff captures the
    // cells refinement splits when a representative is individualized.

    [Fact]
    public void CfiCycle3_IndividualizationSplitsCells()
    {
        var g = CfiGraphGenerator.Generate("Cycle3").Odd;
        int n = g.VertexCount;
        var adj = new int[n * n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                adj[i * n + j] = g[i, j];

        var p = new sbyte[n * n]; // uniform: all UNKNOWN
        var parent = new WarmPartition(n);
        parent.Refine(adj, p);

        // The harness's target: lowest-id non-singleton cell; individualize its
        // smallest member below its cellmates.
        var byCell = new Dictionary<int, List<int>>();
        for (int v = 0; v < n; v++)
            (byCell.TryGetValue(parent.CellOf[v], out var l) ? l : byCell[parent.CellOf[v]] = new()).Add(v);
        int target = byCell.Where(kv => kv.Value.Count >= 2).Select(kv => kv.Key).Min();
        var members = byCell[target];
        int rep = members.Min();

        var childP = (sbyte[])p.Clone();
        foreach (int w in members)
            if (w != rep)
            {
                childP[rep * n + w] = -1; // LESS
                childP[w * n + rep] = 1;  // GREATER
            }
        var child = parent.Clone();
        child.Refine(adj, childP);

        var fp = RefinementFootprint.Compute(n, parent.CellOf, child.CellOf);
        _out.WriteLine($"n={n} parentCells={parent.NumCells} childCells={child.NumCells} " +
                       $"target={target} rep={rep} splitCells={fp.SplitCells.Count} " +
                       $"coupledVerts={fp.CoupledVertices().Length}");

        Assert.NotEmpty(fp.SplitCells);               // the cascade split cells
        Assert.True(fp.CoupledVertices().Length > 1); // coupling propagated beyond rep

        // The child partition refines the parent: every coupled vertex's child
        // sub-cell is nested in the one parent cell it came from.
        foreach (var sc in fp.SplitCells)
            foreach (var sub in sc.SubCells)
                foreach (var v in sub)
                    Assert.Equal(sc.ParentCell, parent.CellOf[v]);
    }
}
