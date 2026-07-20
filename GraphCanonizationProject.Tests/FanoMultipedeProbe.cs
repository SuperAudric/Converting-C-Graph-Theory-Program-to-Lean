using System.Numerics;
using Xunit;
using Xunit.Abstractions;
using Canonizer;
using VertexType = int;

// C3b PROBE (2026-07-20) — the NON-RIGID multipede, i.e. the C# counterpart of the
// Lean C3 witness `mp7` (Regression §15 / PerformanceTest §13).
//
// WHY THIS FIXTURE DID NOT EXIST. GraphCanonTests.Multipede runs m = 5,6,8,9,10,12
// and calls AssertRigid, because the circulant base with offsets {0,1,3} is odd —
// hence the multipede rigid — EXACTLY when 7 ∤ m (1+x+x^3 is primitive of order 7
// over F_2). Multiples of 7 are precisely the excluded case: there the F_2 column
// rank drops, the kernel is the [7,3,4] simplex code, and the multipede carries a
// genuine gauge group PLUS the Z_7 base translation. m = 7 gives 6m = 42 vertices —
// the same construction as Lean's `mp7`.
//
// So the existing suite tests only the rigid branch, and the question "does the C#
// implementation handle the C3 case?" was open. This probe answers it by running it.
public class FanoMultipedeProbe
{
    private readonly ITestOutputHelper _out;
    public FanoMultipedeProbe(ITestOutputHelper o) => _out = o;

    [Theory]
    [InlineData(7)]
    [InlineData(14)]
    public void NonRigidMultipede_IsNotRigid_AndRecordsVerdict(int m)
    {
        var mp = MultipedeGenerator.BuildCirculant(m);
        MultipedeGenerator.AssertWellFormed(mp);

        // The premise of the whole existing multipede suite fails here — this is the
        // structural reason the case was never covered, asserted rather than assumed.
        Assert.False(mp.BaseIsOdd, $"expected a NON-odd (non-rigid) base at m={m}");

        const long budget = 5000;
        var r = Run(mp.Graph, mp.VertexTypes, budget, rigidSolver: true);
        var rNo = Run(mp.Graph, mp.VertexTypes, budget, rigidSolver: false);

        _out.WriteLine(
            $"Multipede(Circulant{m}) n={mp.Graph.VertexCount} baseOdd={mp.BaseIsOdd}\n" +
            $"  rigidSolver=ON   verdict={r.Verdict,-9} kind={r.Kind,-14} nodes={r.Nodes,6} " +
            $"depth={r.Depth,3} leaves={r.Leaves,5} |residual|={r.Residual}\n" +
            $"  rigidSolver=OFF  verdict={rNo.Verdict,-9} kind={rNo.Kind,-14} nodes={rNo.Nodes,6} " +
            $"depth={rNo.Depth,3} leaves={rNo.Leaves,5} |residual|={rNo.Residual}");

        // The one invariant that must hold either way: polynomial-or-flag, never unbounded.
        Assert.True(r.Nodes <= budget + 1, $"node count {r.Nodes} exceeded budget {budget}");

        // Scramble-invariance of the verdict (flag iso-invariance) — the load-bearing
        // correctness property, and the one a gauge/base symmetry could plausibly break.
        for (int seed = 1; seed <= 3; seed++)
        {
            var (g2, t2) = ScrambleWithTypes(mp.Graph, mp.VertexTypes, seed);
            var r2 = Run(g2, t2, budget, rigidSolver: true);
            Assert.Equal(r.Verdict, r2.Verdict);
            _out.WriteLine($"  scramble{seed}: verdict={r2.Verdict,-9} kind={r2.Kind,-14} " +
                           $"nodes={r2.Nodes,6} |residual|={r2.Residual}");
        }
    }

    // ── The apples-to-apples test ────────────────────────────────────────────
    // BuildMultipede's "fine colouring" gives segment w its OWN colour w and gadget
    // v its OWN colour nW+v. That individualizes every segment and every cluster, so
    // the Z_7 base translation (segment w ↦ w+1) is not colour-preserving — the base
    // symmetry is excluded BY FIAT, not solved. Only the within-segment gauge survives
    // colour, which is why the fine-coloured run reports residual = 8 = |L| = 2^3.
    //
    // Lean's `mp7` uses warmRefineVec mp7 (fun _ => 0) — UNIFORM, WL-refined — where
    // the segments are indistinguishable and the base symmetry is live. This runs the
    // C# canonizer on that same object, which is the only comparison that answers
    // "does the C# implementation handle the C3 case?".
    [Theory]
    [InlineData(7)]
    [InlineData(9)]
    public void UniformlyColoured_IsTheLeanObject_RecordsVerdict(int m)
    {
        var mp = MultipedeGenerator.BuildCirculant(m);
        var uniform = new int[mp.Graph.VertexCount];   // all zero = Lean's initial colouring

        const long budget = 200000;
        var fine = Run(mp.Graph, mp.VertexTypes, budget, rigidSolver: true);
        var uni = Run(mp.Graph, uniform, budget, rigidSolver: true);
        var uniNo = Run(mp.Graph, uniform, budget, rigidSolver: false);

        _out.WriteLine(
            $"Circulant{m} n={mp.Graph.VertexCount} baseOdd={mp.BaseIsOdd}  (7|m = {m % 7 == 0})\n" +
            $"  FINE colouring  verdict={fine.Verdict,-9} kind={fine.Kind,-14} nodes={fine.Nodes,7} " +
            $"depth={fine.Depth,3} leaves={fine.Leaves,4} |residual|={fine.Residual}\n" +
            $"  UNIFORM  rigid=ON   verdict={uni.Verdict,-9} kind={uni.Kind,-14} nodes={uni.Nodes,7} " +
            $"depth={uni.Depth,3} leaves={uni.Leaves,4} |residual|={uni.Residual}\n" +
            $"  UNIFORM  rigid=OFF  verdict={uniNo.Verdict,-9} kind={uniNo.Kind,-14} nodes={uniNo.Nodes,7} " +
            $"depth={uniNo.Depth,3} leaves={uniNo.Leaves,4} |residual|={uniNo.Residual}");
    }

    private readonly record struct Res(
        string Verdict, FlagKind Kind, long Nodes, int Depth, int Leaves, BigInteger Residual);

    private static Res Run(AdjMatrix g, int[] types, long budget, bool rigidSolver)
    {
        var cd = new CanonGraphOrdererChainDescent
        { BudgetOverride = budget, EnableRigidSolver = rigidSolver };
        string verdict;
        try { cd.Run((VertexType[])types.Clone(), g); verdict = "canonical"; }
        catch (CanonizationFlaggedException) { verdict = "flagged"; }
        return new Res(verdict, cd.LastFlagKind, cd.LastNodeCount, cd.LastMaxDepth,
                       cd.LastLeafCount, cd.LastAutomorphismGroupOrder);
    }

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
