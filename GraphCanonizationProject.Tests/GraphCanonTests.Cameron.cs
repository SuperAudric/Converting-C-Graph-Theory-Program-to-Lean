using System;
using System.Numerics;
using Xunit;
using Canonizer;
using VertexType = int;

// Cameron-battery probe (docs/chain-descent-exhaustive-obstruction.md §5 Approach 2).
// Positive controls for the EOL: graphs whose visible Aut is a Cameron group —
// Johnson J(n,k) (the d=1 case, A_k on k-subsets, Aut = S_n), Hamming H(d,q) (the
// product action S_q ≀ S_d — the direct control for refutation angle R1), and
// Kneser K(n,k) (a second S_n control; Petersen = K(5,2)).
//
// The near-theorem (docs/chain-descent-hidden-johnson.md, calculator §7) predicts
// these are scheme graphs that CASCADE and CANONIZE — symmetry consumed, NEVER a
// Tier2Like flag — and theorem_2_HOR_of_pPolynomial proves the metric/DRG family
// recovers at depth 1. The probe asserts that, and validates the harvested |Aut|
// against the known closed form: the strongest checkable signal that the
// scheme/cascade leg and the a-posteriori harvest fire and compute the full
// (non-abelian) automorphism group, plus the canonicity bar (scramble-invariant
// canonical form, strategy §14).
//
// The genuinely hard half — an ENCODED non-cascade non-abelian obstruction — is
// the GI-hard (O*)-existence construction (the open EOL research frontier); it is
// not constructible here and is deliberately out of this battery's scope.
public partial class GraphCanonTests
{
    [Theory]
    [InlineData("J", 4, 2)]   // octahedron, Aut = 2·4! = 48 (n = 2k)
    [InlineData("J", 5, 2)]   // triangular T(5), Aut = S_5 = 120
    [InlineData("J", 6, 2)]   // Aut = S_6 = 720
    [InlineData("J", 7, 2)]   // Aut = S_7 = 5040
    [InlineData("J", 8, 2)]   // bigger d=1 control — still cascades
    [InlineData("H", 2, 3)]   // 3×3 rook's graph, Aut = S_3 ≀ S_2 = 72
    [InlineData("H", 3, 2)]   // 3-cube Q_3, Aut = S_2 ≀ S_3 = 48
    [InlineData("H", 2, 4)]   // Aut = S_4 ≀ S_2 = 1152
    [InlineData("H", 3, 3)]   // Aut = S_3 ≀ S_3 = 1296
    [InlineData("K", 5, 2)]   // Petersen, Aut = S_5 = 120
    [InlineData("K", 7, 3)]   // Aut = S_7 = 5040
    public void CameronBattery_SchemeGraph_CanonizesWithExactAut(string family, int a, int b)
    {
        var cg = MakeCameron(family, a, b);
        CameronGraphGenerator.AssertWellFormed(cg);
        const long budget = 20000;

        var r0 = RunCameron(cg.Graph, budget);

        // Bounded — polynomial-or-flag.
        Assert.True(r0.Nodes <= budget + 1,
            $"{cg.Name} n={cg.VertexCount}: node count {r0.Nodes} exceeded budget {budget}");

        // The near-theorem: a visible Cameron group is a scheme graph, so it
        // CASCADES and CANONIZES — never a flag, in particular never Tier2Like.
        Assert.Equal("canonical", r0.Verdict);
        Assert.Equal(FlagKind.None, r0.Kind);

        // The harvest computes the FULL (non-abelian) automorphism group exactly —
        // the ground-truth validation of the scheme/cascade leg.
        Assert.Equal(cg.KnownAutOrder, r0.Residual);

        // Canonicity: every relabelling yields the same canonical form (and the
        // same harvested |Aut|).
        for (int s = 0; s < 4; s++)
        {
            var scrambled = ScrambleGraph(cg.Graph, seed: 5001 + s);
            var r = RunCameron(scrambled, budget);
            Assert.Equal("canonical", r.Verdict);
            Assert.Equal(cg.KnownAutOrder, r.Residual);
            Assert.Equal(r0.Canon, r.Canon);
        }
    }

    private static CameronGraphGenerator.CameronGraph MakeCameron(string family, int a, int b) =>
        family switch
        {
            "J" => CameronGraphGenerator.Johnson(a, b),
            "H" => CameronGraphGenerator.Hamming(a, b),
            "K" => CameronGraphGenerator.Kneser(a, b),
            _   => throw new ArgumentException($"Unknown Cameron family '{family}'."),
        };

    private readonly record struct CameronRun(
        string Verdict, FlagKind Kind, long Nodes, int Depth, BigInteger Residual, string? Canon);

    private static CameronRun RunCameron(AdjMatrix g, long budget)
    {
        var cd = new CanonGraphOrdererChainDescent { BudgetOverride = budget };
        string verdict; string? canon = null;
        try { canon = cd.Run(new VertexType[g.VertexCount], g).ToString(); verdict = "canonical"; }
        catch (CanonizationFlaggedException) { verdict = "flagged"; }
        return new CameronRun(verdict, cd.LastFlagKind, cd.LastNodeCount, cd.LastMaxDepth,
            cd.LastAutomorphismGroupOrder, canon);
    }

    // Relabel a graph by one seeded permutation (reuses the partial class's
    // in-place Scramble helper; these graphs are uncoloured / uniform-type).
    private static AdjMatrix ScrambleGraph(AdjMatrix g, int seed)
    {
        var m = g.ToArray();
        Scramble(m, seed);
        return new AdjMatrix(m);
    }
}
