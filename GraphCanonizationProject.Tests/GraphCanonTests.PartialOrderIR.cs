using Xunit;
using Canonizer;
using System.Collections.Generic;
using System.Linq;
using VertexType = int;
using EdgeType = int;

// Tests for CanonGraphOrdererPartialOrderIR — the canonizer whose only state is
// the partial-ordering matrix P. Reuses the helpers (Scramble, BuildGraph,
// ConvertJaggedArrayType, …) declared on the GraphCanonTests partial class.
public partial class GraphCanonTests
{
    private readonly CanonGraphOrdererPartialOrderIR _po = new();

    // ── Guess-count discipline ───────────────────────────────────────────────
    //
    // The two graphs from the design spec. The count is the number of guesses on
    // every root-to-leaf path of the search (GuessesPerPath throws if ragged).

    [Fact]
    public void PO_TwoDisjointPair_TakesExactlyThreeGuesses()
    {
        // edges 0-1 and 2-3
        EdgeType[,] edges =
        {
            { 0, 1, 0, 0 },
            { 1, 0, 0, 0 },
            { 0, 0, 0, 1 },
            { 0, 0, 1, 0 },
        };
        // One guess to individualise within each pair, one to order the pairs.
        Assert.Equal(3, _po.GuessesPerPath(new VertexType[4], new AdjMatrix(edges)));
    }
        [Fact]
    public void PO_CountDisjointGuesses()
    {
        for(int i=2;i<7;i++)
        {
            EdgeType[,] edges = new EdgeType[i,i];
            var guesses = _po.GuessesPerPath(new VertexType[i], new AdjMatrix(edges));
            Console.WriteLine(guesses);
        }
    }

    [Fact]
    public void PO_ThreeCycle_TakesTwoGuesses_NotOne()
    {
        EdgeType[,] edges =
        {
            { 0, 1, 1 },
            { 1, 0, 1 },
            { 1, 1, 0 },
        };
        // Must be > 1: individualising one vertex leaves the other two a genuine
        // 2-cell, so a second guess is unavoidable. Finishing in 1 would mean a
        // total order was written per guess — P not used as a partial order.
        int guesses = _po.GuessesPerPath(new VertexType[3], new AdjMatrix(edges));
        Assert.True(guesses == 2 || guesses == 3, $"expected 2 or 3 guesses, got {guesses}");
        Assert.Equal(2, guesses);
    }

    // ── Isomorphism invariance ───────────────────────────────────────────────

    [Theory]
    [InlineData(4)]
    [InlineData(5)]
    [InlineData(6)]
    // [InlineData(7)] — passes (all 1044 graphs, every scrambling stable & distinct)
    //   but takes ~4.5 min; left out so the suite stays fast.
    public void PO_KnownGraphs_DifferentScramblings_ProduceSameCanonical(int size)
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
                Scramble(matrix, seed: 15326 + j);
                string result = _po.Run_ToString(new VertexType[size], matrix);
                seen.Add(result);
                canonical ??= result;
                Assert.True(canonical == result,
                    $"Graph {i} (size {size}): scramble {j} produced a different canonical.\n" +
                    $"Expected:\n{canonical}\nGot:\n{result}\n{DisplayMatrix(matrix)}");
            }
        }
        Assert.Equal(graphs.Length, seen.Count); // all distinct ⇒ complete invariant
    }

    [Fact]
    public void PO_TwoDisjointPair_ScramblingsProduceSameCanonical()
    {
        var form1 = BuildGraph((0, 1), (2, 3));
        var form2 = BuildGraph((0, 2), (1, 3));
        var form3 = BuildGraph((1, 2), (0, 3));
        string c1 = _po.Run_ToString(EmptyVerts(form1), form1);
        string c2 = _po.Run_ToString(EmptyVerts(form2), form2);
        string c3 = _po.Run_ToString(EmptyVerts(form3), form3);
        Assert.Equal(c1, c2);
        Assert.Equal(c1, c3);
    }

    [Theory]
    [InlineData(4)]
    [InlineData(5)]
    [InlineData(6)]
    public void PO_ScrambledLine_ProducesSameCanonical(int lineSize)
    {
        string? canonical = null;
        for (int i = 0; i < 8; i++)
        {
            var edges = NewGraph();
            for (int j = 0; j < lineSize - 1; j++)
                edges = AddEdge(edges, j, j + 1);
            Scramble(edges, seed: 778201 + i);
            string result = _po.Run_ToString(EmptyVerts(edges), edges);
            canonical ??= result;
            Assert.Equal(canonical, result);
        }
    }

    // ── Single-constraint variant ────────────────────────────────────────────
    //
    // CanonGraphOrdererPartialOrderSinglePair: every guess writes exactly one
    // cell of P, and both directions of every guessed pair are explored.

    private readonly CanonGraphOrdererPartialOrderSinglePair _pos = new();

    [Fact]
    public void POS_TwoDisjointPair_GuessRange()
    {
        EdgeType[,] edges =
        {
            { 0, 1, 0, 0 },
            { 1, 0, 0, 0 },
            { 0, 0, 0, 1 },
            { 0, 0, 1, 0 },
        };
        var (min, max, leaves) = _pos.GuessDepthRange(new VertexType[4], new AdjMatrix(edges));
        // ragged tree: a lucky chain closes transitively in 3, others take more.
        Assert.Equal(3, min);
        Assert.True(max >= min && leaves > 0, $"min={min} max={max} leaves={leaves}");
    }

    [Fact]
    public void POS_ThreeCycle_GuessRange()
    {
        EdgeType[,] edges =
        {
            { 0, 1, 1 },
            { 1, 0, 1 },
            { 1, 1, 0 },
        };
        var (min, max, _) = _pos.GuessDepthRange(new VertexType[3], new AdjMatrix(edges));
        // never 1: the first single constraint leaves a genuine Unknown pair.
        Assert.True(min >= 2, $"min={min}");
        Assert.True(max <= 3, $"max={max}");
    }

    [Theory]
    [InlineData(4)]
    //[InlineData(5)] too slow for normal use, passes after 30-40s
    public void POS_KnownGraphs_DifferentScramblings_ProduceSameCanonical(int size)
    {
        var graphs = ConvertJaggedArrayType<EdgeType>(UniqueGraphsBySize.graphsBySize[size]);
        var seen = new HashSet<string>();
        for (int i = 0; i < graphs.Length; i++)
        {
            Assert.Equal(i, seen.Count);
            string? canonical = null;
            for (int j = 0; j < 5; j++)
            {
                var matrix = (EdgeType[,])graphs[i].Clone();
                Scramble(matrix, seed: 15326 + j);
                string result = _pos.Run_ToString(new VertexType[size], matrix);
                seen.Add(result);
                canonical ??= result;
                Assert.True(canonical == result,
                    $"Graph {i} (size {size}): scramble {j} produced a different canonical.\n" +
                    $"Expected:\n{canonical}\nGot:\n{result}\n{DisplayMatrix(matrix)}");
            }
        }
        Assert.Equal(graphs.Length, seen.Count);
    }
}
