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

    // ── CFI(K4): mirror-matching yields a verifiable automorphism ─────────
    //
    // The M3 / M6 de-risking check: at a genuine Z_2^3 decision with an
    // all-singletons footprint, the constructed twist passes IsAutomorphism —
    // the empirical analogue of LeafTwistSpec.
    [Fact]
    public void CfiK4_ConstructedTwist_IsAutomorphism()
    {
        var g = CfiGraphGenerator.Generate("K4").Odd;
        int n = g.VertexCount;
        var adj = new int[n * n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                adj[i * n + j] = g[i, j];

        bool IsAut(int[] t)
        {
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (adj[t[i] * n + t[j]] != adj[i * n + j]) return false;
            return true;
        }
        int[] ColdRefine(sbyte[] p)
        {
            var wp = new WarmPartition(n);
            wp.Refine(adj, p);
            return (int[])wp.CellOf.Clone();
        }
        sbyte[] Individualize(sbyte[] parentP, int rep, int[] members)
        {
            var pc = (sbyte[])parentP.Clone();
            foreach (int w in members)
                if (w != rep) { pc[rep * n + w] = -1; pc[w * n + rep] = 1; } // LESS/GREATER; TC inert
            return pc;
        }

        var descent = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        {
            CaptureFootprints = true
        };
        descent.Canonize(new sbyte[n * n], new WarmPartition(n));

        int allSingletonDecisions = 0, constructed = 0, verified = 0;
        foreach (var cap in descent.CapturedFootprints)
        {
            if (cap.CellMembers.Length < 2) continue;

            int[] parentCellOf = ColdRefine(cap.ParentP);
            int[] branch1 = ColdRefine(Individualize(cap.ParentP, cap.Rep, cap.CellMembers));
            var fp = RefinementFootprint.Compute(n, parentCellOf, branch1);
            if (fp.SplitCells.Count == 0 || !fp.SplitCells.All(s => s.AllSingletons)) continue;
            allSingletonDecisions++;

            foreach (int rj in cap.CellMembers)
            {
                if (rj == cap.Rep) continue;
                int[] branchJ = ColdRefine(Individualize(cap.ParentP, rj, cap.CellMembers));
                var t = TwistConstruction.TryConstruct(n, fp, branch1, branchJ);
                if (t is null) continue;
                constructed++;
                if (!Perm.IsIdentity(t) && IsAut(t)) verified++;
            }
        }

        _out.WriteLine($"K4: allSingletonDecisions={allSingletonDecisions} " +
                       $"constructed={constructed} verified={verified}");

        // The headline: mirror-matching constructs at least one non-trivial
        // twist that verifies as a genuine automorphism on CFI(K4).
        Assert.True(verified > 0,
            $"expected ≥1 verified twist; got constructed={constructed}, verified={verified}");
    }
}
