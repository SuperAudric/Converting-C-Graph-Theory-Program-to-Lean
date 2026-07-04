using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — C1b: classical-group generator producer + THE ORDER-CHECK (2026-07-04).
//
// C1b (docs/chain-descent-route-c-plan.md §9.2.2 / §9.2.6) builds a generating set for the
// answer group affineG(similitudeGroup Q) = translations ⋊ AΓO(Q) from the recovered form.
// The Lean contract schemeAutGroup_coarse_eq_affineG says this group IS the graph's Aut; the
// ORDER-CHECK is its executable form. Per the §9.2.0 corrected design, the reference is the
// harness's OWN harvested |Aut| (CanonResult.ResidualGroup) at small d — bootstrap, not a
// hand-derived closed form.
//
// Checks: (i) every generated permutation stabilises the graph; (ii) the built group Contains
// the translations; (iii) built.Order == harvested |Aut|.
public class RouteCGroupProbe
{
    private readonly ITestOutputHelper _out;
    public RouteCGroupProbe(ITestOutputHelper o) => _out = o;

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    [Theory]
    [InlineData(3, -1)]
    [InlineData(3, +1)]
    public void C1b_BuiltGroup_MatchesHarvestedAut(int q, int eps) => Run(q, eps);

    [Theory]
    [Trait("Category", "LongRunning")]
    [InlineData(5, -1)]
    [InlineData(5, +1)]
    public void C1b_BuiltGroup_MatchesHarvestedAut_Large(int q, int eps) => Run(q, eps);

    void Run(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim), p = q;
        var (adj, vec, enc) = RouteCVO4.Build(q, eps);
        string nm = $"VO^{(eps < 0 ? "-" : "+")}_4({q}) n={n}";

        // harvested |Aut| (ground truth) from the real harness
        var cd = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        { EnableLinearOracle = true, EnableDeferral = true };
        var res = cd.Canonize(new sbyte[n * n], new WarmPartition(n));
        Assert.False(res.Flagged, $"{nm}: harness flagged");
        BigInteger harvested = res.ResidualGroup.Order;

        // recover structure + form, build the group
        var aff = AffineStructureRecovery.Recover(res.ResidualGroup, p, origin: 0);
        Assert.True(aff is not null, $"{nm}: F1 Recover null");
        var Q = QuadraticFormRecovery.RecoverForm(adj, n, aff!);
        Assert.True(Q is not null, $"{nm}: A1 RecoverForm null");

        var gens = ClassicalGroupGenerators.Generators(Q!, aff!);
        var G = ClassicalGroupGenerators.Build(Q!, aff!);
        BigInteger built = G.Order;

        double ratio = (double)harvested / (double)built;
        _out.WriteLine($"{nm}: harvested |Aut|={harvested}  built={built}  #gens={gens.Count}  ratio(harv/built)={ratio:0.####}");

        // (i) every generator stabilises the graph
        foreach (var g in gens)
            Assert.True(StabilisesGraph(g, adj, n), $"{nm}: a generated permutation does NOT stabilise the graph");

        // (ii) the built group contains the translations
        for (int i = 0; i < dim; i++)
        {
            var t = TranslationPerm(i, q, dim, n, vec, enc);
            Assert.True(G.Contains(t), $"{nm}: built group does NOT contain translation e_{i}");
        }

        // (iii) order-check (the Lean contract)
        Assert.True(built == harvested,
            $"{nm}: built |G|={built} != harvested |Aut|={harvested} (ratio {ratio:0.####})");
        _out.WriteLine($"    OK — order-check passed");
    }

    // C1b build-only, no harness: EVERY generated permutation is a genuine automorphism of the
    // graph (a similitude scales Q ⟹ preserves the isotropic cone ⟹ stabilises the Cayley graph).
    // Fast at n=625/2401 (O(n²·#gens)); it does NOT compute the group order (Schreier–Sims without
    // sifting does not scale past ~n=81 with the full reflection set — the order-check is validated
    // exactly at n=81, both types, in C1b_..MatchesHarvestedAut). This confirms the CONSTRUCTION
    // scales even though the order-VERIFICATION is gated on the deferred sifting optimisation.
    [Theory]
    [InlineData(5, -1)]
    [InlineData(5, +1)]
    [InlineData(7, -1)]
    [InlineData(7, +1)]
    public void C1b_BuildOnly_GeneratorsStabilise(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim);
        var (adj, vec, enc) = RouteCVO4.Build(q, eps);
        var aff = NaturalAff(q, dim);
        var Q = QuadraticFormRecovery.RecoverForm(adj, n, aff);
        Assert.True(Q is not null, $"VO^{eps}_4({q}): A1 null");

        var gens = ClassicalGroupGenerators.Generators(Q!, aff);
        foreach (var g in gens)
            Assert.True(StabilisesGraph(g, adj, n), $"VO^{eps}_4({q}): a generator does not stabilise");
        _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_4({q}) n={n}: {gens.Count} generators all stabilise the graph, closed |Aut|={ClosedFormAffineG4(q, eps)}");
    }

    // |affineG^eps_4(q)| = q^4 · 2 q^2 (q^2 - eps)(q^2 - 1)(q - 1)   (q = p prime, dim 4 = 2m, m=2)
    static BigInteger ClosedFormAffineG4(int q, int eps)
    {
        BigInteger Q = q;
        BigInteger o = 2 * (Q * Q) * (Q * Q - eps) * (Q * Q - 1);   // |O^eps_4(q)|
        BigInteger go = o * (Q - 1);                                 // × similitude factor group (q-1)
        return (Q * Q * Q * Q) * go;                                 // × translations q^4
    }

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

    static bool StabilisesGraph(int[] g, int[] adj, int n)
    {
        for (int u = 0; u < n; u++)
            for (int v = u + 1; v < n; v++)
                if (adj[g[u] * n + g[v]] != adj[u * n + v]) return false;
        return true;
    }

    static int[] TranslationPerm(int i, int q, int dim, int n, Func<int, int[]> vec, Func<int[], int> enc)
    {
        var perm = new int[n];
        for (int v = 0; v < n; v++)
        {
            var x = (int[])vec(v).Clone();
            x[i] = (x[i] + 1) % q;
            perm[v] = enc(x);
        }
        return perm;
    }
}

// Shared VO^eps_4(q) Cayley-graph construction (q prime), vertex v ↔ base-q digits.
internal static class RouteCVO4
{
    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    public static (int[] adj, Func<int, int[]> vec, Func<int[], int> enc) Build(int q, int eps)
    {
        const int dim = 4, m = 2;
        int n = IPow(q, dim);
        int bb = 0, cc = 0;
        if (eps == -1)
        {
            bool found = false;
            for (int b = 0; b < q && !found; b++)
                for (int c = 0; c < q && !found; c++)
                {
                    bool aniso = true;
                    for (int y = 0; y < q && aniso; y++)
                        for (int z = 0; z < q; z++)
                        {
                            if (y == 0 && z == 0) continue;
                            int gg = ((y * y + b * y % q * z) % q + c * (z * z % q)) % q;
                            if (gg % q == 0) { aniso = false; break; }
                        }
                    if (aniso) { bb = b; cc = c; found = true; }
                }
            if (!found) throw new Exception($"no anisotropic binary form over GF({q})");
        }
        int[] Vec(int v) { var x = new int[dim]; for (int i = 0; i < dim; i++) { x[i] = v % q; v /= q; } return x; }
        int Enc(int[] x) { int v = 0, pw = 1; for (int i = 0; i < dim; i++) { v += (((x[i] % q) + q) % q) * pw; pw *= q; } return v; }
        int Q(int[] x)
        {
            int s = 0, hyp = eps == -1 ? m - 1 : m;
            for (int i = 0; i < hyp; i++) s = (s + x[2 * i] * x[2 * i + 1]) % q;
            if (eps == -1)
            {
                int y = x[2 * (m - 1)], z = x[2 * (m - 1) + 1];
                s = (s + (y * y + bb * y % q * z) % q + cc * (z * z % q)) % q;
            }
            return ((s % q) + q) % q;
        }
        var vecs = new int[n][]; for (int v = 0; v < n; v++) vecs[v] = Vec(v);
        var adj = new int[n * n];
        var d = new int[dim];
        for (int u = 0; u < n; u++)
            for (int v = u + 1; v < n; v++)
            {
                for (int i = 0; i < dim; i++) d[i] = ((vecs[u][i] - vecs[v][i]) % q + q) % q;
                if (Q(d) == 0) { adj[u * n + v] = 1; adj[v * n + u] = 1; }
            }
        return (adj, Vec, Enc);
    }
}
