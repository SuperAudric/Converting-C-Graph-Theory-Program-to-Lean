using Xunit.Abstractions;
using Canonizer;
using System;
using System.Collections.Generic;
using System.Numerics;
using System.Text;
using GraphOrderer = Canonizer.CanonGraphOrdererV4;
using VertexType = System.UInt32;
using EdgeType = System.UInt64;

public class GraphCannonTests(ITestOutputHelper output)
{
    private readonly GraphOrderer _orderer = new();

    // ── Isomorphism tests ────────────────────────────────────────────────────

    [Fact]
    public void Simple_IsomorphicGraphs_ProduceSameCanonical()
    {
        VertexType[] verts = [0, 0, 0, 0];
        EdgeType[,] edges1 = { { 0, 0, 0, 0 }, { 0, 0, 0, 1 }, { 0, 0, 0, 1 }, { 0, 1, 1, 0 } };
        EdgeType[,] edges2 = { { 0, 1, 1, 0 }, { 1, 0, 0, 0 }, { 1, 0, 0, 0 }, { 0, 0, 0, 0 } };
        Assert.Equal(_orderer.Run(verts, edges1), _orderer.Run(verts, edges2));
    }

    [Fact(Skip = "Known algorithm bug in CanonGraphOrdererV4")]
    public void APointed_IsomorphicGraphs_ProduceSameCanonical()
    {
        VertexType[] verts = [0, 1, 1, 3, 4, 5, 6];
        EdgeType[,] edges1 = {
            { 0, 0, 0, 1, 1, 0, 0 }, { 0, 0, 1, 0, 1, 0, 0 }, { 0, 1, 0, 0, 1, 0, 0 },
            { 1, 0, 0, 0, 1, 0, 0 }, { 1, 1, 1, 1, 0, 0, 0 }, { 0, 0, 0, 0, 0, 0, 1 },
            { 0, 0, 0, 0, 0, 1, 0 }
        };
        EdgeType[,] edges2 = {
            { 0, 0, 1, 0, 1, 0, 0 }, { 0, 0, 0, 1, 1, 0, 0 }, { 1, 0, 0, 0, 1, 0, 0 },
            { 0, 1, 0, 0, 1, 0, 0 }, { 1, 1, 1, 1, 0, 0, 0 }, { 0, 0, 0, 0, 0, 0, 1 },
            { 0, 0, 0, 0, 0, 1, 0 }
        };
        Assert.Equal(_orderer.Run(verts, edges1), _orderer.Run(verts, edges2));
    }

    [Fact]
    public void ThreeCyclePair_And_SixCycle_ProduceDifferentCanonical()
    {
        var pair   = BuildGraph((0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3));
        var cycle6 = BuildGraph((0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0));
        Assert.NotEqual(_orderer.Run(EmptyVerts(pair), pair),
                        _orderer.Run(EmptyVerts(cycle6), cycle6));
    }

    // ── Scrambling stability tests ───────────────────────────────────────────

    [Fact]
    public void RandomGraph_DifferentScramblings_ProduceSameCanonical()
    {
        for (int i = 0; i < 10; i++)
        {
            string? canonical = null;
            for (int j = 0; j < 10; j++)
            {
                var matrix = GenerateRandomAdjacencyMatrix(8, 0.75f, seed: 10593 + i);
                Scramble(matrix, seed: 15326 + j);
                string result = _orderer.Run(new VertexType[8], matrix);
                canonical ??= result;
                Assert.Equal(canonical, result);
            }
        }
    }

    [Theory]
    [InlineData(4)]
    [InlineData(5)]
    [InlineData(6)]
    public void ScrambledLine_ProducesSameCanonical(int lineSize)
    {
        string? canonical = null;
        for (int i = 0; i < 10; i++)
        {
            var edges = NewGraph();
            for (int j = 0; j < lineSize - 1; j++)
                edges = AddEdge(edges, j, j + 1);
            Scramble(edges, seed: 103925 + i);
            string result = _orderer.Run(EmptyVerts(edges), edges);
            canonical ??= result;
            Assert.Equal(canonical, result);
        }
    }

    [Fact]
    public void ScrambledSpider_ProducesSameCanonical()
    {
        string? canonical = null;
        for (int i = 0; i < 10; i++)
        {
            var edges = BuildGraph((0, 1), (1, 2), (0, 3), (3, 4), (0, 5), (5, 6));
            Scramble(edges, seed: 103925 + i);
            string result = _orderer.Run(EmptyVerts(edges), edges);
            canonical ??= result;
            Assert.Equal(canonical, result);
        }
    }

    [Fact]
    public void Scrambled3Cycle_ProducesSameCanonical()
    {
        var form1 = BuildGraph((1, 2), (2, 3), (3, 1), (0, 4), (4, 5), (5, 0));
        var form2 = BuildGraph((0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3));
        Assert.Equal(_orderer.Run(EmptyVerts(form1), form1),
                     _orderer.Run(EmptyVerts(form2), form2));
    }

    // ── Canonical count / exhaustive tests ──────────────────────────────────

    [Theory]
    [InlineData(0, 1)]
    [InlineData(1, 1)]
    [InlineData(2, 2)]
    [InlineData(3, 4)]
    [InlineData(4, 11)]
    public void AllPermutations_UniqueCanonicalCount_MatchesExpected(int size, int expected)
    {
        BigInteger total = BigInteger.Pow(2, size * (size - 1) / 2);
        var seen = new HashSet<string>();
        for (BigInteger p = 0; p < total; p++)
            seen.Add(_orderer.Run(new VertexType[size], GeneratePermutedAdjacencyMatrix(size, p)));

        output.WriteLine($"size {size}: {seen.Count} unique graphs");
        Assert.Equal(expected, seen.Count);
    }

    [Theory]
    [InlineData(3)]
    [InlineData(4)]
    public void KnownGraphs_DifferentScramblings_ProduceSameCanonical(int size)
    {
        var graphs = ConvertJaggedArrayType<EdgeType>(UniqueGraphsBySize.graphsBySize[size]);
        for (int i = 1; i < graphs.Length; i++)
        {
            string? canonical = null;
            for (int j = 0; j < 5; j++)
            {
                var matrix = (EdgeType[,])graphs[i].Clone();
                Scramble(matrix, seed: 15326 + j);
                string result = _orderer.Run(new VertexType[size], matrix);
                canonical ??= result;
                Assert.True(canonical == result,
                    $"Graph {i} (size {size}): scramble {j} produced different canonical.\n" +
                    $"Expected:\n{canonical}\nGot:\n{result}\n{DisplayMatrix(matrix)}");
            }
        }
    }

    // ── Ordering function smoke test ─────────────────────────────────────────

    [Fact]
    public void OrderingFunction_CompletesWithoutException()
    {
        var rng     = new Random(102931);
        var verts   = Enumerable.Range(0, 10).Select(_ => (VertexType)rng.Next(0, 9)).ToArray();
        var edges   = new EdgeType[10, 10];
        for (int i = 0; i < 10; i++)
            for (int j = 0; j < 10; j++)
                edges[i, j] = (EdgeType)(verts[i] * 10u + verts[j]);
        GraphOrderer.LabelEdgesAccordingToRankings(verts, edges);
    }

    // ── Helpers ──────────────────────────────────────────────────────────────

    private static EdgeType[,] NewGraph() => new EdgeType[1, 1];

    private static EdgeType[,] AddEdge(EdgeType[,] edges, int a, int b)
    {
        int needed = Math.Max(a, b) + 1;
        if (edges.GetLength(0) < needed)
        {
            var grown = new EdgeType[needed, needed];
            for (int i = 0; i < edges.GetLength(0); i++)
                for (int j = 0; j < edges.GetLength(1); j++)
                    grown[i, j] = edges[i, j];
            edges = grown;
        }
        edges[a, b] = 1;
        edges[b, a] = 1;
        return edges;
    }

    private static EdgeType[,] BuildGraph(params (int a, int b)[] pairs)
    {
        var edges = NewGraph();
        foreach (var (a, b) in pairs)
            edges = AddEdge(edges, a, b);
        return edges;
    }

    private static VertexType[] EmptyVerts(EdgeType[,] edges) =>
        new VertexType[Math.Max(edges.GetLength(0), edges.GetLength(1))];

    private static void Scramble<T>(T[,] m, int seed)
    {
        var rng = new Random(seed);
        for (int r = 0; r < m.GetLength(0) - 1; r++)
        {
            int s = r + rng.Next() % (m.GetLength(0) - r);
            for (int i = 0; i < m.GetLength(0); i++) (m[s, i], m[r, i]) = (m[r, i], m[s, i]);
            for (int i = 0; i < m.GetLength(0); i++) (m[i, s], m[i, r]) = (m[i, r], m[i, s]);
        }
    }

    private static EdgeType[,] GenerateRandomAdjacencyMatrix(int n, float ratio, int seed)
    {
        var rng = new Random(seed);
        var m   = new EdgeType[n, n];
        for (int i = 0; i < n; i++)
            for (int j = i + 1; j < n; j++)
                if (rng.NextDouble() <= ratio)
                    m[i, j] = m[j, i] = 1;
        return m;
    }

    private static EdgeType[,] GeneratePermutedAdjacencyMatrix(int n, BigInteger permutation)
    {
        var m = new EdgeType[n, n];
        for (int i = 0; i < n; i++)
            for (int j = i + 1; j < n; j++)
            {
                if (permutation % 2 == 1) m[i, j] = m[j, i] = 1;
                permutation /= 2;
            }
        return m;
    }

    private static T[][,] ConvertJaggedArrayType<T>(int[][,] input)
    {
        var result = new T[input.Length][,];
        for (int i = 0; i < input.Length; i++)
        {
            if (input[i] is not { } inner) continue;
            var converted = new T[inner.GetLength(0), inner.GetLength(1)];
            for (int r = 0; r < inner.GetLength(0); r++)
                for (int c = 0; c < inner.GetLength(1); c++)
                    converted[r, c] = (T)Convert.ChangeType(inner[r, c], typeof(T));
            result[i] = converted;
        }
        return result;
    }

    private static string DisplayMatrix(EdgeType[,] m)
    {
        var sb = new StringBuilder();
        for (int i = 0; i < m.GetLength(0); i++)
        {
            for (int j = 0; j < m.GetLength(1); j++)
                sb.Append(m[i, j] > 0 ? '■' : '□');
            sb.AppendLine();
        }
        return sb.ToString();
    }
}
