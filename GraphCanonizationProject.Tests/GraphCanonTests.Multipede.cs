using System.Numerics;
using Xunit;
using Canonizer;
using VertexType = int;

// IR-blind-spot probe (docs/chain-descent-exhaustive-obstruction.md §0.6,
// strategy §14 / §15 gap 5). Multipedes are RIGID and IR-hard: chain descent
// has no symmetry to harvest, so any flag carries a TRIVIAL residual and is
// classified IrBlindSpot. They are the project's only IR-core fixture and the
// rigid counterpart of CFI (which the canonizer canonizes by consuming its
// Z_2^β gauge group).
//
// This is the rigid analogue of CDScale_Cfi_CanonizesOrFlags_WithinBudget, run
// at the SAME node budget so the contrast is meaningful. Because whether a given
// instance discretizes within budget (canonize) or exhausts it (flag) is the
// empirical question, the probe asserts only the invariants that hold either
// way, and records the descent cost as the diagnostic value:
//   (1) bounded by budget — polynomial-or-flag, never unbounded;
//   (2) the canonize/flag verdict is SCRAMBLE-INVARIANT — flag iso-invariance
//       (strategy §15 gap 2); this is the first fixture that genuinely flags,
//       since CFI canonizes within budget and so never exercises that path;
//   (3) IF an instance flags, its residual is trivial (rigidity, certified at
//       generation by oddness) and its kind is IrBlindSpot.
public partial class GraphCanonTests
{
    [Theory]
    [InlineData(5)]
    [InlineData(6)]
    [InlineData(8)]
    [InlineData(9)]
    [InlineData(10)]
    [InlineData(12)]
    public void Multipede_CanonizesOrFlags_RigidWithinBudget(int m)
    {
        var mp = MultipedeGenerator.BuildCirculant(m);
        MultipedeGenerator.AssertWellFormed(mp);
        MultipedeGenerator.AssertRigid(mp);          // odd base ⟹ provably rigid
        const long budget = 5000;                    // same budget as the CFI scaling probe

        var r0 = RunMultipede(mp.Graph, mp.VertexTypes, budget);

        // (1) Bounded — the load-bearing assertion: polynomial-or-flag.
        Assert.True(r0.Nodes <= budget + 1,
            $"Multipede({m}) n={mp.Graph.VertexCount}: node count {r0.Nodes} exceeded budget {budget}");

        // (3) A rigid graph has no automorphisms to harvest, so a flag must be an
        //     IR blind spot with a trivial residual — never Tier2Like/AbelianUnconsumed.
        if (r0.Verdict == "flagged")
        {
            Assert.Equal(FlagKind.IrBlindSpot, r0.Kind);
            Assert.Equal(BigInteger.One, r0.Residual);
        }

        // (2) The verdict (and, when flagged, the kind) is invariant under relabelling.
        for (int s = 0; s < 4; s++)
        {
            var (g2, t2) = ScrambleWithTypes(mp.Graph, mp.VertexTypes, seed: 9001 + s);
            var r = RunMultipede(g2, t2, budget);
            Assert.Equal(r0.Verdict, r.Verdict);
            if (r.Verdict == "flagged")
            {
                Assert.Equal(r0.Kind, r.Kind);
                Assert.Equal(BigInteger.One, r.Residual);
            }
        }

        output.WriteLine(
            $"Multipede(Circulant{m}) n={mp.Graph.VertexCount,3}  {r0.Verdict,-9}[{r0.Kind}]  " +
            $"nodes={r0.Nodes,6}/{budget}  depth={r0.Depth,3}  leaves={r0.Leaves,5}  |resid|={r0.Residual}");
    }

    // The IR-blind-spot CLASSIFICATION, exercised directly. A rigid multipede has
    // no symmetry to harvest, so however the descent is interrupted the residual
    // is trivial. Run under a budget below the descent's natural node count to
    // force a flag, and confirm the classifier buckets it as IrBlindSpot with a
    // trivial residual — the §0.6 flag cause that CFI, being symmetric, cannot
    // exercise (a tight-budget CFI flag may have already harvested gauge twists).
    // Here the trivial residual is GENUINE rigidity, certified by oddness.
    [Theory]
    [InlineData(8)]
    [InlineData(10)]
    public void Multipede_UnderTightBudget_FlagsAsIrBlindSpot(int m)
    {
        var mp = MultipedeGenerator.BuildCirculant(m);
        MultipedeGenerator.AssertRigid(mp);
        const long budget = 5;   // below the ~15 nodes these instances naturally use

        // The IrBlindSpot flag path (rigidSolver: false = the pre-B2 exhaustive/flag behaviour). With the
        // Phase-2 rigid solver ON (below) these very instances now CANONIZE — the flag-set shrink — so the
        // classifier is exercised here with the solver off.
        var r0 = RunMultipede(mp.Graph, mp.VertexTypes, budget, rigidSolver: false);
        Assert.Equal("flagged", r0.Verdict);
        Assert.Equal(FlagKind.IrBlindSpot, r0.Kind);
        Assert.Equal(BigInteger.One, r0.Residual);     // rigid ⟹ nothing harvested
        Assert.True(r0.Nodes <= budget + 1);

        // The flag and its IrBlindSpot classification are scramble-invariant.
        for (int s = 0; s < 4; s++)
        {
            var (g2, t2) = ScrambleWithTypes(mp.Graph, mp.VertexTypes, seed: 7001 + s);
            var r = RunMultipede(g2, t2, budget, rigidSolver: false);
            Assert.Equal("flagged", r.Verdict);
            Assert.Equal(FlagKind.IrBlindSpot, r.Kind);
            Assert.Equal(BigInteger.One, r.Residual);
        }

        // ★ Flag-set shrink: with the Phase-2 rigid solver ON (B2 default), the SAME rigid multipede is
        // CANONIZED at the root (poly, budget-independent) instead of flagging as the IR blind spot.
        var solved = RunMultipede(mp.Graph, mp.VertexTypes, budget, rigidSolver: true);
        Assert.Equal("canonical", solved.Verdict);
    }

    private readonly record struct MultipedeRun(
        string Verdict, FlagKind Kind, long Nodes, int Depth, int Leaves, BigInteger Residual);

    private static MultipedeRun RunMultipede(AdjMatrix g, int[] types, long budget, bool rigidSolver = true)
    {
        var cd = new CanonGraphOrdererChainDescent { BudgetOverride = budget, EnableRigidSolver = rigidSolver };
        string verdict;
        try
        {
            cd.Run((VertexType[])types.Clone(), g);
            verdict = "canonical";
        }
        catch (CanonizationFlaggedException)
        {
            verdict = "flagged";
        }
        return new MultipedeRun(
            verdict, cd.LastFlagKind, cd.LastNodeCount, cd.LastMaxDepth,
            cd.LastLeafCount, cd.LastAutomorphismGroupOrder);
    }

    // Apply one random relabelling to both the adjacency matrix and the vertex
    // types, so a coloured graph scrambles consistently (the same Fisher–Yates
    // row/col swaps used by Scramble, extended to the 1-D type array).
    private static (AdjMatrix, int[]) ScrambleWithTypes(AdjMatrix g, int[] types, int seed)
    {
        int n = g.VertexCount;
        var m = g.ToArray();
        var t = (int[])types.Clone();
        var rng = new System.Random(seed);
        for (int r = 0; r < n - 1; r++)
        {
            int s = r + rng.Next() % (n - r);
            for (int i = 0; i < n; i++) (m[s, i], m[r, i]) = (m[r, i], m[s, i]);
            for (int i = 0; i < n; i++) (m[i, s], m[i, r]) = (m[i, r], m[i, s]);
            (t[s], t[r]) = (t[r], t[s]);
        }
        return (new AdjMatrix(m), t);
    }
}
