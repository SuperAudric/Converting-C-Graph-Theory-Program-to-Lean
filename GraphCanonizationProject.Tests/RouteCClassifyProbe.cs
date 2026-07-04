using System;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — C2: FormsGraphClassifier confirmation (2026-07-04).
// docs/chain-descent-route-c-plan.md §9.2.2. Detects the forms-graph family (constructive +
// self-validating for affine-polar). Misclassification must be SAFE (a non-forms graph ⟹ Unknown).
public class RouteCClassifyProbe
{
    private readonly ITestOutputHelper _out;
    public RouteCClassifyProbe(ITestOutputHelper o) => _out = o;

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    static AffineStructureRecovery.AffineStructure NaturalAff(int p, int dim)
    {
        int n = IPow(p, dim);
        var coords = new int[n][];
        for (int v = 0; v < n; v++)
        {
            var x = new int[dim]; int t = v;
            for (int i = 0; i < dim; i++) { x[i] = t % p; t /= p; }
            coords[v] = x;
        }
        return new AffineStructureRecovery.AffineStructure
        { Translations = new PermutationGroup(n), Origin = 0, P = p, Dim = dim, Coords = coords };
    }

    [Theory]
    [InlineData(3, -1)]
    [InlineData(3, +1)]
    [InlineData(5, -1)]
    [InlineData(5, +1)]
    public void Detect_AffinePolar(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim);
        var (adj, _, _) = RouteCVO4.Build(q, eps);
        var aff = NaturalAff(q, dim);

        var c = FormsGraphClassifier.Detect(adj, n, aff);
        _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_4({q}) → {c}");
        Assert.Equal(FormFamily.AffinePolar, c.Family);
        Assert.Equal(q, c.P);
        Assert.Equal(2, c.M);              // dim 4 = 2m ⟹ m = 2
        Assert.Equal(eps, c.Eps);
    }

    [Fact]
    public void Detect_NonStronglyRegular_IsSafe()
    {
        // a long cycle is regular but NOT strongly regular ⟹ must return Unknown (safe)
        int n = 81;
        var adj = new int[n * n];
        for (int v = 0; v < n; v++) { int w = (v + 1) % n; adj[v * n + w] = 1; adj[w * n + v] = 1; }
        var c = FormsGraphClassifier.Detect(adj, n, NaturalAff(3, 4));
        _out.WriteLine($"C_{n} → {c}");
        Assert.Equal(FormFamily.Unknown, c.Family);
    }

    [Fact]
    public void Detect_EmptyGraph_IsSafe()
    {
        // a degenerate SRG (empty) must not be mistaken for a forms graph (valency 0 ≠ isotropic count)
        int n = 81;
        var empty = new int[n * n];
        Assert.Equal(FormFamily.Unknown, FormsGraphClassifier.Detect(empty, n, NaturalAff(3, 4)).Family);
    }
}
