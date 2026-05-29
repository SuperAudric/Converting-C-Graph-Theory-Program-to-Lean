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

    [Theory(Skip ="Long running not enabled")]
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

    // CFI direct-probe long cases (CfiPair_DisjointUnion_ConvergeLoop_RanksDisjoint_Extended)
    // archived to Archive/V4/GraphCanonTests.V4FastFalsification.cs — see that file
    // for the V4Fast-specific harness.

    // ── A-priori cascade oracle: scramble-invariance on the larger CFI bases ────
    //
    // The cascade recursion collapses these to a near-single path (K6/K7 to a
    // single leaf), so the off-vs-on canonical comparison (M6 leaf-scaling) cannot
    // run — the oracle-off tree is astronomically large. Scramble-invariance is the
    // correctness guard there: relabellings must canonize identically, and even
    // must stay distinct from odd. The empirical check that M2's harvesting (with
    // its iso-invariant lockstep cell-id sequence) introduces no labelling
    // dependence in the verdict (docs/chain-descent-cascade-oracle.md §4.4, §10.2).
    //
    // Feasible only because the cascade oracle collapsed these: pre-M2 a single
    // K7 even+odd canonization was projected at ~21 h (see the Extended case
    // above); post-M2 it is ~78 s per canonization. LongRunning: K6 ~4 s, K7
    // ~80 s per canonization (×6 here).
    [Theory]
    [Trait("Category", "LongRunning")]
    [InlineData("K6")]
    [InlineData("K7")]
    public void CD_CfiLargeBase_ScramblingsProduceSameCanonical_AndEvenOddDistinct(string baseGraph)
    {
        var pair = CfiGraphGenerator.Generate(baseGraph);
        var cd = new CanonGraphOrdererChainDescent();
        string? even = null, odd = null;
        foreach (var (slot, g) in new[] { ("even", pair.Even), ("odd", pair.Odd) })
        {
            int n = g.VertexCount;
            var baseEdges = g.ToArray();
            string? canonical = null;
            for (int i = 0; i < 3; i++)
            {
                var scrambled = (EdgeType[,])baseEdges.Clone();
                Scramble(scrambled, seed: 60101 + i);
                string result = cd.Run_ToString(new VertexType[n], scrambled);
                canonical ??= result;
                Assert.Equal(canonical, result);
            }
            if (slot == "even") even = canonical; else odd = canonical;
        }
        Assert.NotEqual(even, odd);
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
