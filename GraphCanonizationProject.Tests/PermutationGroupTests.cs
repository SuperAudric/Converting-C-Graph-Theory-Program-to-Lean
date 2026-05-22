using Canonizer;
using System.Linq;

// Unit tests for the route-2 calculator's group-theoretic foundation
// (PermutationGroup / Schreier–Sims). See docs/chain-descent-calculator.md §2,
// "The model: the calculator is a stabilizer chain".
//
// Group order is the decisive test: if the chain computes |G| correctly on a
// spread of known groups, the base, transversals and sifting are sound.
public class PermutationGroupTests
{
    private static int[] Cycle(int n, params int[] points) => Perm.FromCycles(n, points);

    // ── Perm utilities ──────────────────────────────────────────────────────

    [Fact]
    public void Perm_ComposeAndInverse_RoundTrip()
    {
        var p = Cycle(5, 0, 1, 2, 3, 4);
        var inv = Perm.Inverse(p);
        Assert.True(Perm.IsIdentity(Perm.Compose(p, inv)));
        Assert.True(Perm.IsIdentity(Perm.Compose(inv, p)));
    }

    [Fact]
    public void Perm_Compose_AppliesRightOperandFirst()
    {
        // p = (0 1), q = (1 2); (p∘q) applies q then p.
        var p = Cycle(3, 0, 1);
        var q = Cycle(3, 1, 2);
        // (p∘q): 0→p[q[0]]=p[0]=1 ; 1→p[q[1]]=p[2]=2 ; 2→p[q[2]]=p[1]=0.
        Assert.Equal(new[] { 1, 2, 0 }, Perm.Compose(p, q));
    }

    // ── Group order on known groups ─────────────────────────────────────────

    [Fact]
    public void TrivialGroup_HasOrderOne()
    {
        var g = new PermutationGroup(5);
        Assert.Equal(1L, (long)g.Order);
        Assert.True(g.IsTrivial);
        Assert.True(g.Contains(Perm.Identity(5)));
    }

    [Fact]
    public void SingleTransposition_HasOrderTwo()
    {
        var g = new PermutationGroup(5);
        g.AddGenerator(Cycle(5, 0, 1));
        Assert.Equal(2L, (long)g.Order);
        Assert.True(g.Contains(Cycle(5, 0, 1)));
        Assert.False(g.Contains(Cycle(5, 0, 2)));
    }

    [Fact]
    public void CyclicGroup_HasOrderEqualToCycleLength()
    {
        var g = new PermutationGroup(6);
        g.AddGenerator(Cycle(6, 0, 1, 2, 3, 4, 5));
        Assert.Equal(6L, (long)g.Order);
    }

    [Theory]
    [InlineData(3, 6)]
    [InlineData(4, 24)]
    [InlineData(5, 120)]
    [InlineData(6, 720)]
    [InlineData(7, 5040)]
    public void SymmetricGroup_HasOrderNFactorial(int n, long expectedOrder)
    {
        var g = new PermutationGroup(n);
        g.AddGenerator(Cycle(n, 0, 1));
        g.AddGenerator(Perm.FromCycles(n, Enumerable.Range(0, n).ToArray()));
        Assert.Equal(expectedOrder, (long)g.Order);
    }

    [Fact]
    public void DihedralD4_HasOrderEight()
    {
        var g = new PermutationGroup(4);
        g.AddGenerator(Cycle(4, 0, 1, 2, 3)); // rotation
        g.AddGenerator(Cycle(4, 1, 3));       // reflection
        Assert.Equal(8L, (long)g.Order);
    }

    // Aut(C18) — the CFI(Cycle3) odd graph (calculator doc test targets).
    [Fact]
    public void DihedralD18_AutOfC18_HasOrder36()
    {
        const int n = 18;
        var rotation = Perm.FromCycles(n, Enumerable.Range(0, n).ToArray());
        var reflection = new int[n];
        for (int i = 0; i < n; i++) reflection[i] = (n - i) % n;
        var g = new PermutationGroup(n);
        g.AddGenerator(rotation);
        g.AddGenerator(reflection);
        Assert.Equal(36L, (long)g.Order);
    }

    // Aut(C9 ⊔ C9) = D9 ≀ Z2 — the CFI(Cycle3) even graph. Order 18·18·2 = 648.
    [Fact]
    public void WreathD9_AutOfTwoC9_HasOrder648()
    {
        const int n = 18;
        var g = new PermutationGroup(n);
        // rotation of cycle A = {0..8}
        g.AddGenerator(Perm.FromCycles(n, new[] { 0, 1, 2, 3, 4, 5, 6, 7, 8 }));
        // reflection of cycle A (fixes vertex 0)
        g.AddGenerator(Perm.FromCycles(n,
            new[] { 1, 8 }, new[] { 2, 7 }, new[] { 3, 6 }, new[] { 4, 5 }));
        // swap cycle A with cycle B = {9..17}
        g.AddGenerator(Perm.FromCycles(n,
            new[] { 0, 9 }, new[] { 1, 10 }, new[] { 2, 11 }, new[] { 3, 12 },
            new[] { 4, 13 }, new[] { 5, 14 }, new[] { 6, 15 }, new[] { 7, 16 }, new[] { 8, 17 }));
        Assert.Equal(648L, (long)g.Order);
    }

    // ── Orbits, incremental construction, membership ────────────────────────

    [Fact]
    public void IntransitiveGroup_OrbitsAreCorrect()
    {
        var g = new PermutationGroup(6);
        g.AddGenerator(Cycle(6, 0, 1));
        g.AddGenerator(Cycle(6, 2, 3, 4));
        Assert.Equal(new[] { 0, 1 }, g.Orbit(0));
        Assert.Equal(new[] { 2, 3, 4 }, g.Orbit(2));
        Assert.Equal(new[] { 5 }, g.Orbit(5));
        Assert.Equal(6L, (long)g.Order); // 2 × 3
    }

    [Fact]
    public void IncrementalGenerators_OrderGrowsCorrectly()
    {
        var g = new PermutationGroup(4);
        Assert.Equal(1L, (long)g.Order);
        g.AddGenerator(Cycle(4, 0, 1));
        Assert.Equal(2L, (long)g.Order);
        g.AddGenerator(Cycle(4, 0, 1, 2, 3));
        Assert.Equal(24L, (long)g.Order); // ⟨(0 1),(0 1 2 3)⟩ = S4
    }

    [Fact]
    public void RedundantGenerator_DoesNotChangeOrder()
    {
        var g = new PermutationGroup(4);
        g.AddGenerator(Cycle(4, 0, 1));
        g.AddGenerator(Cycle(4, 0, 1, 2, 3));
        Assert.Equal(24L, (long)g.Order);
        g.AddGenerator(Cycle(4, 1, 2)); // already an element of S4
        Assert.Equal(24L, (long)g.Order);
    }

    [Fact]
    public void Membership_RespectsTheCyclicSubgroupStructure()
    {
        var g = new PermutationGroup(4);
        g.AddGenerator(Cycle(4, 0, 1, 2, 3)); // ⟨4-cycle⟩, order 4
        Assert.Equal(4L, (long)g.Order);
        // ⟨(0 1 2 3)⟩ = { id, (0 1 2 3), (0 2)(1 3), (0 3 2 1) }.
        Assert.True(g.Contains(Perm.FromCycles(4, new[] { 0, 2 }, new[] { 1, 3 })));
        Assert.False(g.Contains(Cycle(4, 0, 2))); // bare transposition is not in C4
        Assert.False(g.Contains(Cycle(4, 0, 1))); // nor is this one
    }
}
