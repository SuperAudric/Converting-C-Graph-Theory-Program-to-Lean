using System;
using System.Linq;
using System.Numerics;
using Xunit;
using Canonizer;

// Canonizer-free unit tests for the Cameron-graph generator (CameronGraphGenerator.cs):
// structural invariants, vertex counts, and — crucially — an INDEPENDENT brute-force
// automorphism count for small instances, so the probe's |Aut|-equality assertion
// rests on verified ground truth rather than a typed-in textbook formula.
public class CameronGraphGeneratorTests
{
    // ── Structure + known vertex counts / degrees ─────────────────────────────

    [Fact]
    public void Johnson_5_2_IsTriangularGraph()
    {
        var cg = CameronGraphGenerator.Johnson(5, 2);
        Assert.Equal(10, cg.VertexCount);              // C(5,2)
        CameronGraphGenerator.AssertWellFormed(cg);    // regular, symmetric, loopless
        Assert.Equal(new BigInteger(120), cg.KnownAutOrder);  // S_5
        Assert.Equal(6, Degree(cg.Graph, 0));          // T(5) is 6-regular
    }

    [Fact]
    public void Hamming_2_3_IsRook3x3()
    {
        var cg = CameronGraphGenerator.Hamming(2, 3);
        Assert.Equal(9, cg.VertexCount);               // 3^2
        CameronGraphGenerator.AssertWellFormed(cg);
        Assert.Equal(new BigInteger(72), cg.KnownAutOrder);   // S_3 ≀ S_2
        Assert.Equal(4, Degree(cg.Graph, 0));          // rook 3×3 is 4-regular
    }

    [Fact]
    public void Hamming_3_2_IsCube()
    {
        var cg = CameronGraphGenerator.Hamming(3, 2);
        Assert.Equal(8, cg.VertexCount);               // 2^3
        CameronGraphGenerator.AssertWellFormed(cg);
        Assert.Equal(new BigInteger(48), cg.KnownAutOrder);   // S_2 ≀ S_3
        Assert.Equal(3, Degree(cg.Graph, 0));          // Q_3 is 3-regular
    }

    [Fact]
    public void Kneser_5_2_IsPetersen()
    {
        var cg = CameronGraphGenerator.Kneser(5, 2);
        Assert.Equal(10, cg.VertexCount);
        CameronGraphGenerator.AssertWellFormed(cg);
        Assert.Equal(new BigInteger(120), cg.KnownAutOrder);  // S_5
        Assert.Equal(3, Degree(cg.Graph, 0));          // Petersen is 3-regular
    }

    [Theory]
    [InlineData(6, 2, 15)]   // C(6,2)
    [InlineData(7, 2, 21)]
    [InlineData(7, 3, 35)]
    public void Johnson_VertexCount_IsBinomial(int n, int k, int expected)
        => Assert.Equal(expected, CameronGraphGenerator.Johnson(n, k).VertexCount);

    [Theory]
    [InlineData(2, 4, 16)]
    [InlineData(3, 3, 27)]
    public void Hamming_VertexCount_IsPower(int d, int q, int expected)
        => Assert.Equal(expected, CameronGraphGenerator.Hamming(d, q).VertexCount);

    // ── Independent brute-force |Aut| (ground-truth for the formulas) ─────────

    [Theory]
    [InlineData("J", 4, 2, 48)]   // octahedron — the n = 2k extra factor of 2
    [InlineData("H", 3, 2, 48)]   // 3-cube
    [InlineData("H", 2, 3, 72)]   // rook 3×3
    [InlineData("K", 5, 2, 120)]  // Petersen
    public void KnownAutOrder_MatchesBruteForce_SmallCases(string family, int a, int b, int expected)
    {
        var cg = family switch
        {
            "J" => CameronGraphGenerator.Johnson(a, b),
            "H" => CameronGraphGenerator.Hamming(a, b),
            "K" => CameronGraphGenerator.Kneser(a, b),
            _   => throw new ArgumentException(),
        };
        Assert.Equal(new BigInteger(expected), cg.KnownAutOrder);   // the typed formula
        Assert.Equal(expected, BruteForceAutCount(cg.Graph));       // independent ground truth
    }

    // ── Argument guards ───────────────────────────────────────────────────────

    [Fact]
    public void Johnson_BadParams_Throw()
    {
        Assert.Throws<ArgumentException>(() => CameronGraphGenerator.Johnson(3, 3));
        Assert.Throws<ArgumentException>(() => CameronGraphGenerator.Johnson(3, 0));
    }

    [Fact]
    public void Kneser_RequiresNAtLeastTwoKPlusOne()
    {
        Assert.Throws<ArgumentException>(() => CameronGraphGenerator.Kneser(4, 2));  // n = 2k
        var ok = CameronGraphGenerator.Kneser(5, 2);                                  // n = 2k+1
        Assert.Equal(10, ok.VertexCount);
    }

    // ── helpers ───────────────────────────────────────────────────────────────

    private static int Degree(AdjMatrix g, int v)
    {
        int d = 0;
        for (int j = 0; j < g.VertexCount; j++) if (j != v && g[v, j] != 0) d++;
        return d;
    }

    // Count automorphisms by brute force over Sym(n). Only for small n (≤ 8 here).
    private static int BruteForceAutCount(AdjMatrix g)
    {
        int n = g.VertexCount;
        var perm = Enumerable.Range(0, n).ToArray();
        int count = 0;
        do { if (Preserves(g, perm)) count++; } while (NextPermutation(perm));
        return count;
    }

    private static bool Preserves(AdjMatrix g, int[] p)
    {
        int n = g.VertexCount;
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                if (g[i, j] != g[p[i], p[j]]) return false;
        return true;
    }

    private static bool NextPermutation(int[] a)
    {
        int i = a.Length - 2;
        while (i >= 0 && a[i] >= a[i + 1]) i--;
        if (i < 0) return false;
        int j = a.Length - 1;
        while (a[j] <= a[i]) j--;
        (a[i], a[j]) = (a[j], a[i]);
        Array.Reverse(a, i + 1, a.Length - (i + 1));
        return true;
    }
}
