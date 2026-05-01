using Xunit.Abstractions;
using Canonizer;
using System.Numerics;
using VertexType = int;
using EdgeType = int;

// Long-running test cases — discoverable in VSCode test explorer but not run by
// default (they carry [Trait("Category","LongRunning")] so they must be selected
// explicitly). Use scripts/run-long-tests.sh or the VSCode "Run Long Tests" task.
public partial class GraphCanonTests
{
    // ── CFI long cases ───────────────────────────────────────────────────────
    // Same logic as CfiPair_ProducesDifferentCanonical; split out so the trait
    // can be applied at method level without touching the fast InlineData cases.

    [Theory]
    [Trait("Category", "LongRunning")]
    [InlineData("K33")]      // ~30 s
    //[InlineData("Petersen")] // ~370 s
    //[InlineData("K6")]       // ~3000 s  (passed once manually)
    //[InlineData("K7")]       // ~21 h    (projected from n^4.74 fit)
    public void CfiPair_ProducesDifferentCanonical_Extended(string baseName)
    {
        var pair = CfiGraphGenerator.Generate(baseName);
        CfiGraphGenerator.AssertWellFormedPair(pair);

        var verts   = new VertexType[pair.Even.VertexCount];
        string even = _orderer.Run(verts, pair.Even).ToString();
        string odd  = _orderer.Run(verts, pair.Odd).ToString();

        Assert.True(even != odd,
            $"CFI pair on base {baseName} produced equal canonicals — " +
            $"possible counterexample to OrbitCompleteAfterConv_general.\n" +
            CfiGraphGenerator.DescribePair(pair));
    }

    // ── CFI direct-probe long cases ──────────────────────────────────────────
    // See CfiPair_DisjointUnion_ConvergeLoop_RanksDisjoint in GraphCanonTests.cs
    // for the full rationale. One ConvergeLoop on a 2n-vertex disjoint union is
    // ~n× cheaper than full Run on a 2n-vertex graph (no OrderVertices outer
    // loop), so these long-running cases scale better than the 1a counterparts.

    // Skipped while _orderer is not CanonGraphOrdererV4Fast: hardcodes
    // CanonGraphOrdererV4Fast.RunConvergeLoopForTesting, so it probes V4Fast
    // internals regardless of the active orderer. Re-enable by removing Skip
    // when V4Fast is the active orderer.

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

        output.WriteLine($"{baseName}: Even ranks={evenSet.Count} distinct, Odd ranks={oddSet.Count} distinct, shared={shared.Count}");
        Assert.True(shared.Count == 0,
            $"CFI pair on base {baseName}: ConvergeLoop on Even ⊕ Odd assigned " +
            $"{shared.Count} rank value(s) shared between halves — direct counterexample " +
            $"to OrbitCompleteAfterConv_general. Shared ranks: [{string.Join(", ", shared)}].\n" +
            CfiGraphGenerator.DescribePair(pair));
    }


    // ── Exhaustive permutation long cases ────────────────────────────────────

    [Theory]
    [Trait("Category", "LongRunning")]
    [InlineData(5, 34)]
    [InlineData(6, 156)]
    //[InlineData(7, 1044)]
    public void AllPermutations_UniqueCanonicalCount_MatchesExpected_Extended(int size, int expected)
    {
        BigInteger total = BigInteger.Pow(2, size * (size - 1) / 2);
        var seen = new HashSet<string>();
        for (BigInteger p = 0; p < total; p++)
            seen.Add(_orderer.Run_ToString(new VertexType[size], GeneratePermutedAdjacencyMatrix(size, p)));

        output.WriteLine($"size {size}: {seen.Count} unique graphs");
        Assert.Equal(expected, seen.Count);
    }
}
