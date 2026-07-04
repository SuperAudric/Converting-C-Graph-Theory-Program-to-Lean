using System;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — C3: canonicalizer + END-TO-END ISO-STABILITY (2026-07-04).
// docs/chain-descent-route-c-plan.md §9.2.2 (C3). The Route-C canonicalization is invariant under
// relabelling: a graph and any scramble recover the SAME canonical invariant (q, m, eps), |Aut|,
// and standard adjacency. This is the runtime image of the seal's iso-invariance (F4 / L1). n=81
// (VO^eps_4(3)) — the harness harvest is fast there; large-d uses C4 (Aut-free), future work.
public class RouteCCanonicalizeProbe
{
    private readonly ITestOutputHelper _out;
    public RouteCCanonicalizeProbe(ITestOutputHelper o) => _out = o;

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    [Theory]
    [InlineData(3, -1)]
    [InlineData(3, +1)]
    public void Canonicalize_IsScrambleInvariant(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim);
        var (adj0, _, _) = RouteCVO4.Build(q, eps);

        var baseRes = RouteCCanonicalizer.Recognize(adj0, n);
        Assert.True(baseRes is not null, $"VO^{eps}_4({q}): Recognize returned null on the canonical copy");
        _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_4({q}): {baseRes!.Classification}, |Aut|={baseRes.AutOrder}");

        // the recovered standard graph must reconstruct to the SAME iso-type as the input
        Assert.Equal(FormFamily.AffinePolar, baseRes.Classification.Family);
        Assert.Equal(eps, baseRes.Classification.Eps);

        // scramble by random relabellings π and re-canonicalize — invariant must match exactly
        for (int seed = 1; seed <= 3; seed++)
        {
            var pi = RandomPerm(n, seed);
            var adjS = Relabel(adj0, n, pi);
            var r = RouteCCanonicalizer.Recognize(adjS, n);
            Assert.True(r is not null, $"scramble {seed}: Recognize returned null");
            Assert.Equal(baseRes.Classification.P, r!.Classification.P);
            Assert.Equal(baseRes.Classification.M, r.Classification.M);
            Assert.Equal(baseRes.Classification.Eps, r.Classification.Eps);
            Assert.Equal(baseRes.AutOrder, r.AutOrder);
            Assert.True(baseRes.CanonicalAdjacency.SequenceEqual(r.CanonicalAdjacency),
                $"scramble {seed}: canonical adjacency differs");
            _out.WriteLine($"    scramble {seed}: same canonical form ✓");
        }
    }

    [Fact]
    public void StandardVO_Matches_ClosedFormAut()
    {
        // sanity: the canonicalizer's own |Aut| closed form agrees with the C1b-validated one at m=2
        foreach (var (q, eps) in new[] { (3, -1), (3, 1), (5, -1), (5, 1) })
        {
            var got = RouteCCanonicalizer.AffinePolarAutOrder(q, 2, eps);
            System.Numerics.BigInteger Q = q;
            var expect = (Q * Q * Q * Q) * (2 * (Q * Q) * (Q * Q - eps) * (Q * Q - 1)) * (Q - 1);
            Assert.Equal(expect, got);
        }
    }

    // The option-ii harness wire: the ORDERER (public Run API) with EnableRouteC returns the same
    // canonical AdjMatrix for a forms graph and its scramble, and exposes the recovered |Aut|.
    [Theory]
    [InlineData(3, -1)]
    [InlineData(3, +1)]
    public void OrdererWire_RouteC_IsScrambleInvariant(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim);
        var (adj0, _, _) = RouteCVO4.Build(q, eps);
        var types = new int[n];   // uniform

        string Canon(int[] adj, out System.Numerics.BigInteger? aut)
        {
            var edges = new int[n, n];
            for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) edges[i, j] = adj[i * n + j];
            var orderer = new CanonGraphOrdererChainDescent { EnableRouteC = true };
            var canon = orderer.Run(types, new AdjMatrix(edges));
            aut = orderer.LastRouteCAutOrder;
            return canon.ToString();
        }

        string baseCanon = Canon(adj0, out var baseAut);
        Assert.True(baseAut is not null, $"VO^{eps}_4({q}): orderer did NOT take the Route-C path");
        _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_4({q}) via orderer: |Aut|={baseAut}");

        for (int seed = 1; seed <= 2; seed++)
        {
            var adjS = Relabel(adj0, n, RandomPerm(n, seed));
            string sc = Canon(adjS, out var scAut);
            Assert.True(scAut is not null, $"scramble {seed}: orderer did NOT take the Route-C path");
            Assert.Equal(baseAut, scAut);
            Assert.Equal(baseCanon, sc);
            _out.WriteLine($"    orderer scramble {seed}: same canonical AdjMatrix ✓");
        }
    }

    static int[] RandomPerm(int n, int seed)
    {
        var p = Enumerable.Range(0, n).ToArray();
        var rng = new Random(seed);
        for (int i = n - 1; i > 0; i--) { int j = rng.Next(i + 1); (p[i], p[j]) = (p[j], p[i]); }
        return p;
    }

    static int[] Relabel(int[] adj, int n, int[] pi)
    {
        var b = new int[n * n];
        for (int u = 0; u < n; u++)
            for (int v = 0; v < n; v++)
                b[pi[u] * n + pi[v]] = adj[u * n + v];
        return b;
    }
}
