using System;
using System.Linq;
using Xunit;
using Canonizer;

// Canonizer-free unit tests for the multipede generator (MultipedeGenerator.cs).
// These pin the construction's structural invariants and the F_2 rigidity
// certificate (oddness ⟺ full column rank, Neuen–Schweitzer Lemma 4.4) without
// running the descent — the descent-side behaviour lives in the
// Multipede_CanonizesOrFlags_RigidWithinBudget probe.
public class MultipedeGeneratorTests
{
    // ── IsOdd: the F_2 full-column-rank rigidity test ─────────────────────────

    [Fact]
    public void IsOdd_Identity_IsOdd()
    {
        var id = new int[3, 3];
        for (int i = 0; i < 3; i++) id[i, i] = 1;
        Assert.True(MultipedeGenerator.IsOdd(id));
    }

    [Fact]
    public void IsOdd_ZeroColumn_IsNotOdd()
    {
        // Column 2 is all-zero ⟹ not full column rank.
        var b = new int[3, 3];
        b[0, 0] = 1; b[1, 1] = 1;
        Assert.False(MultipedeGenerator.IsOdd(b));
    }

    [Fact]
    public void IsOdd_DependentColumns_IsNotOdd()
    {
        // Columns 0 and 1 are equal ⟹ rank 1 < 2.
        var b = new int[2, 2];
        b[0, 0] = 1; b[0, 1] = 1;
        b[1, 0] = 1; b[1, 1] = 1;
        Assert.False(MultipedeGenerator.IsOdd(b));
    }

    [Fact]
    public void IsOdd_FewerRowsThanColumns_IsNotOdd()
    {
        var b = new int[2, 3];
        b[0, 0] = 1; b[1, 1] = 1; b[0, 2] = 1;
        Assert.False(MultipedeGenerator.IsOdd(b));
    }

    [Theory]
    // 1 + x + x^3 has order 7 over F_2, so the {0,1,3} circulant is odd iff 7 ∤ m.
    [InlineData(5, true)]
    [InlineData(6, true)]
    [InlineData(7, false)]
    [InlineData(8, true)]
    [InlineData(9, true)]
    [InlineData(10, true)]
    [InlineData(12, true)]
    [InlineData(14, false)]
    public void IsOdd_Circulant013_MatchesSevenDivisibility(int m, bool expectedOdd)
    {
        var b = MultipedeGenerator.CirculantBiadjacency(m, new[] { 0, 1, 3 });
        Assert.Equal(expectedOdd, MultipedeGenerator.IsOdd(b));
    }

    // ── BuildCirculant: structure + the rigidity certificate ──────────────────

    [Theory]
    [InlineData(5)]
    [InlineData(6)]
    [InlineData(8)]
    [InlineData(9)]
    [InlineData(10)]
    [InlineData(12)]
    public void BuildCirculant_OddSizes_AreWellFormedAndRigid(int m)
    {
        var mp = MultipedeGenerator.BuildCirculant(m);

        // 6m vertices: 2m segment (a,b per bit) + 4m middle (4 even subsets of a
        // degree-3 neighbourhood per gadget).
        Assert.Equal(6 * m, mp.Graph.VertexCount);
        Assert.Equal(m, mp.BaseV);
        Assert.Equal(m, mp.BaseW);
        Assert.True(mp.BaseIsOdd, $"Circulant{m} base should be odd (7 ∤ {m}).");

        MultipedeGenerator.AssertWellFormed(mp);
        MultipedeGenerator.AssertRigid(mp);   // must not throw on an odd base
    }

    [Fact]
    public void BuildCirculant_MultipleOfSeven_IsNotRigid_AndAssertRigidThrows()
    {
        var mp = MultipedeGenerator.BuildCirculant(7);
        Assert.False(mp.BaseIsOdd);
        Assert.Equal(42, mp.Graph.VertexCount);   // structurally well-formed regardless
        MultipedeGenerator.AssertWellFormed(mp);
        Assert.Throws<InvalidOperationException>(() => MultipedeGenerator.AssertRigid(mp));
    }

    [Fact]
    public void BuildCirculant_TooSmall_Throws()
    {
        Assert.Throws<ArgumentException>(() => MultipedeGenerator.BuildCirculant(3));
    }

    // ── Colouring shape: segments paired, middles grouped ─────────────────────

    [Fact]
    public void BuildCirculant_FineColouring_PairsSegmentsAndGroupsGadgets()
    {
        var mp = MultipedeGenerator.BuildCirculant(6);

        // Each colour class is either a segment (size 2) or a gadget middle-set
        // (size 4 for degree-3 gadgets). No class is a singleton — that is what
        // forces the descent to branch with nothing to harvest.
        var classSizes = mp.VertexTypes
            .GroupBy(t => t)
            .Select(g => g.Count())
            .OrderBy(c => c)
            .ToArray();

        Assert.All(classSizes, c => Assert.True(c == 2 || c == 4, $"unexpected colour-class size {c}"));
        Assert.Equal(6, classSizes.Count(c => c == 2));  // 6 segments
        Assert.Equal(6, classSizes.Count(c => c == 4));  // 6 gadgets
    }

    // ── Random-regular expander base ──────────────────────────────────────────

    [Fact]
    public void BuildRandomRegular_OddDegree_ProducesRigidWellFormedMultipede()
    {
        var mp = MultipedeGenerator.BuildRandomRegular(nChecks: 16, nBits: 16, degree: 3, seed: 0);
        Assert.True(mp.BaseIsOdd);                 // seed scan guarantees an odd base
        Assert.Equal(6 * 16, mp.Graph.VertexCount); // degree-3 gadgets: 4 middles each ⟹ 6·nBits
        MultipedeGenerator.AssertWellFormed(mp);
        MultipedeGenerator.AssertRigid(mp);
    }

    [Fact]
    public void BuildRandomRegular_EvenDegree_Throws()
    {
        // Even degree forces the all-ones vector into the F_2 kernel ⟹ never odd.
        Assert.Throws<ArgumentException>(
            () => MultipedeGenerator.BuildRandomRegular(nChecks: 12, nBits: 12, degree: 4, seed: 0));
    }

    // ── General builder: degree guard ─────────────────────────────────────────

    [Fact]
    public void BuildMultipede_GadgetDegreeBelowTwo_Throws()
    {
        var b = new int[2, 2];
        b[0, 0] = 1;            // gadget 0 has degree 1
        b[1, 0] = 1; b[1, 1] = 1;
        Assert.Throws<ArgumentException>(() => MultipedeGenerator.BuildMultipede(b, "degenerate"));
    }
}
