// Archived V4Fast-specific falsification harness.
//
// These tests probe `CanonGraphOrdererV4Fast.RunConvergeLoopForTesting`
// directly — the V4Fast internals are no longer the active orderer, so they
// were always Skip'd. Empirically they DO fail on Cycle3/Cycle5/Cycle7/K4
// CFI bases, refuting `OrbitCompleteAfterConv_general` (one of the reasons
// V4 was retired). Kept here as the falsifying-counterexample harness in case
// V4Fast is ever reactivated.
//
// Both this file and the orderer it exercises live under `Archive/V4/`; they
// are excluded from the Tests project build (see csproj `Compile Remove`).

#if INCLUDE_ARCHIVED_V4
using Xunit;
using Xunit.Abstractions;
using Canonizer;
using System.Collections.Generic;
using System.Numerics;
using VertexType = int;
using EdgeType = int;

public partial class GraphCanonTests
{
    // ── CFI direct-probe test ────────────────────────────────────────────────
    // Build G = Even ⊕ Odd and run a single ConvergeLoop pass (no BreakTie, no
    // OrderVertices outer loop). Aut(G) = Aut(Even) × Aut(Odd) since Even and
    // Odd are connected and non-isomorphic, so no orbit of G crosses components.
    // Per OrbitCompleteAfterConv_general: equal converged value ⇒ same orbit.
    // Therefore Even-half ranks and Odd-half ranks must be disjoint sets.
    // Any shared rank is a direct counterexample (no BreakTie cascade involved).

    [Theory(Skip = "V4Fast-specific harness; not applicable while a non-V4Fast orderer is active.")]
    [InlineData("Cycle3")]
    [InlineData("Cycle4")]
    [InlineData("Cycle5")]
    [InlineData("K4")]
    [InlineData("K33")]
    public void CfiPair_DisjointUnion_ConvergeLoop_RanksDisjoint(string baseName)
    {
        var pair = CfiGraphGenerator.Generate(baseName);
        CfiGraphGenerator.AssertWellFormedPair(pair);

        var union = CfiGraphGenerator.BuildDisjointUnion(pair.Even, pair.Odd);
        int nEven = pair.Even.VertexCount;
        int nTotal = union.VertexCount;
        var ranks = CanonGraphOrdererV4Fast.RunConvergeLoopForTesting(new VertexType[nTotal], union);

        var evenSet = new HashSet<int>();
        for (int i = 0; i < nEven; i++) evenSet.Add(ranks[i]);
        var oddSet = new HashSet<int>();
        for (int i = nEven; i < nTotal; i++) oddSet.Add(ranks[i]);

        var shared = new HashSet<int>(evenSet);
        shared.IntersectWith(oddSet);

        Assert.True(shared.Count == 0,
            $"CFI pair on base {baseName}: ConvergeLoop on Even ⊕ Odd assigned " +
            $"{shared.Count} rank value(s) shared between halves — direct counterexample " +
            $"to OrbitCompleteAfterConv_general. Shared ranks: [{string.Join(", ", shared)}].\n" +
            CfiGraphGenerator.DescribePair(pair));
    }

    // ── CFI direct-probe long cases ──────────────────────────────────────────
    // One ConvergeLoop on a 2n-vertex disjoint union is ~n× cheaper than full
    // Run on a 2n-vertex graph (no OrderVertices outer loop), so these long-
    // running cases scale better than the small variants above.

    [Theory(Skip = "V4Fast-specific harness; not applicable while a non-V4Fast orderer is active.")]
    [Trait("Category", "LongRunning")]
    [InlineData("Petersen")]
    [InlineData("K6")]
    [InlineData("K7")]
    public void CfiPair_DisjointUnion_ConvergeLoop_RanksDisjoint_Extended(string baseName)
    {
        var pair = CfiGraphGenerator.Generate(baseName);
        CfiGraphGenerator.AssertWellFormedPair(pair);

        var union = CfiGraphGenerator.BuildDisjointUnion(pair.Even, pair.Odd);
        int nEven = pair.Even.VertexCount;
        int nTotal = union.VertexCount;
        var ranks = CanonGraphOrdererV4Fast.RunConvergeLoopForTesting(new VertexType[nTotal], union);

        var evenSet = new HashSet<int>();
        for (int i = 0; i < nEven; i++) evenSet.Add(ranks[i]);
        var oddSet = new HashSet<int>();
        for (int i = nEven; i < nTotal; i++) oddSet.Add(ranks[i]);

        var shared = new HashSet<int>(evenSet);
        shared.IntersectWith(oddSet);

        Assert.True(shared.Count == 0,
            $"CFI pair on base {baseName}: ConvergeLoop on Even ⊕ Odd assigned " +
            $"{shared.Count} rank value(s) shared between halves — direct counterexample " +
            $"to OrbitCompleteAfterConv_general. Shared ranks: [{string.Join(", ", shared)}].\n" +
            CfiGraphGenerator.DescribePair(pair));
    }
}
#endif
