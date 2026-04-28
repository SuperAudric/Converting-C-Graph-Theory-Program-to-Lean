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
    [InlineData("Petersen")] // ~370 s
    [InlineData("K6")]       // ~3000 s  (passed once manually)
    [InlineData("K7")]       // ~21 h    (projected from n^4.74 fit)
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

    // ── Exhaustive permutation long cases ────────────────────────────────────

    [Theory]
    [Trait("Category", "LongRunning")]
    [InlineData(5, 34)]
    [InlineData(6, 156)]
    [InlineData(7, 1044)]
    [InlineData(8, 12346)]
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
