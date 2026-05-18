using Xunit;
using Canonizer;
using System.Collections.Generic;
using VertexType = int;
using EdgeType = int;

// Tests for CanonGraphOrdererFlipValidation — the two-pass canonizer
// (forward greedy + backward flip-validation, see
// docs/flip-validation-strategy.md). Reuses the helpers (Scramble,
// BuildGraph, ConvertJaggedArrayType, …) declared on the partial class.
public partial class GraphCanonTests
{
    private readonly CanonGraphOrdererFlipValidation _fv = new();

    // ── Two graphs from the original spec ───────────────────────────────────

    [Fact]
    public void FV_TwoDisjointPair_ScramblingsProduceSameCanonical()
    {
        var form1 = BuildGraph((0, 1), (2, 3));
        var form2 = BuildGraph((0, 2), (1, 3));
        var form3 = BuildGraph((1, 2), (0, 3));
        string c1 = _fv.Run_ToString(EmptyVerts(form1), form1);
        string c2 = _fv.Run_ToString(EmptyVerts(form2), form2);
        string c3 = _fv.Run_ToString(EmptyVerts(form3), form3);
        Assert.Equal(c1, c2);
        Assert.Equal(c1, c3);
    }

    [Fact]
    public void FV_ThreeCycle_ScramblingsProduceSameCanonical()
    {
        EdgeType[,] edges =
        {
            { 0, 1, 1 },
            { 1, 0, 1 },
            { 1, 1, 0 },
        };
        string canonical = _fv.Run_ToString(new VertexType[3], edges);
        for (int i = 0; i < 5; i++)
        {
            var scrambled = (EdgeType[,])edges.Clone();
            Scramble(scrambled, seed: 4711 + i);
            Assert.Equal(canonical, _fv.Run_ToString(new VertexType[3], scrambled));
        }
    }

    // ── Isomorphism invariance + completeness across the small-graph corpus ─

    [Theory]
    [InlineData(4)]
    [InlineData(5)]
    [InlineData(6)]
    public void FV_KnownGraphs_DifferentScramblings_ProduceSameCanonical(int size)
    {
        var graphs = ConvertJaggedArrayType<EdgeType>(UniqueGraphsBySize.graphsBySize[size]);
        var seen = new HashSet<string>();
        for (int i = 0; i < graphs.Length; i++)
        {
            Assert.Equal(i, seen.Count); // every graph so far got its own canonical
            string? canonical = null;
            for (int j = 0; j < 5; j++)
            {
                var matrix = (EdgeType[,])graphs[i].Clone();
                Scramble(matrix, seed: 22701 + j);
                string result = _fv.Run_ToString(new VertexType[size], matrix);
                seen.Add(result);
                canonical ??= result;
                Assert.True(canonical == result,
                    $"Graph {i} (size {size}): scramble {j} produced a different canonical.\n" +
                    $"Expected:\n{canonical}\nGot:\n{result}\n{DisplayMatrix(matrix)}");
            }
        }
        Assert.Equal(graphs.Length, seen.Count); // all distinct ⇒ complete invariant
    }

    [Theory]
    [InlineData(4)]
    [InlineData(5)]
    [InlineData(6)]
    public void FV_ScrambledLine_ProducesSameCanonical(int lineSize)
    {
        string? canonical = null;
        for (int i = 0; i < 8; i++)
        {
            var edges = NewGraph();
            for (int j = 0; j < lineSize - 1; j++)
                edges = AddEdge(edges, j, j + 1);
            Scramble(edges, seed: 110227 + i);
            string result = _fv.Run_ToString(EmptyVerts(edges), edges);
            canonical ??= result;
            Assert.Equal(canonical, result);
        }
    }

    // ── Determinism / no leaked state ───────────────────────────────────────

    [Fact]
    public void FV_Run_CalledTwiceOnSameInput_ReturnsSameResult()
    {
        VertexType[] verts = [0, 0, 0, 0];
        EdgeType[,] edges = { { 0, 0, 0, 0 }, { 0, 0, 0, 1 }, { 0, 0, 0, 1 }, { 0, 1, 1, 0 } };
        Assert.Equal(_fv.Run_ToString(verts, edges), _fv.Run_ToString(verts, edges));
    }

    [Fact]
    public void FV_Run_CorrectResultAfterDifferentSizedGraphCall()
    {
        VertexType[] verts4 = [0, 0, 0, 0];
        EdgeType[,] edges4a = { { 0, 0, 0, 0 }, { 0, 0, 0, 1 }, { 0, 0, 0, 1 }, { 0, 1, 1, 0 } };
        EdgeType[,] edges4b = { { 0, 1, 1, 0 }, { 1, 0, 0, 0 }, { 1, 0, 0, 0 }, { 0, 0, 0, 0 } };
        var edges3 = BuildGraph((0, 1), (1, 2), (2, 0));

        string resultBefore = _fv.Run_ToString(verts4, edges4a);
        _fv.Run_ToString(EmptyVerts(edges3), edges3);
        string resultAfter = _fv.Run_ToString(verts4, edges4b);

        Assert.Equal(resultBefore, resultAfter);
    }
}
