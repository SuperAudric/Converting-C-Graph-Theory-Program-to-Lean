using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — C1a: form-FAMILY recovery confirmation (2026-07-04).
//
// C1a (docs/chain-descent-route-c-plan.md §9.2.2) generalizes A1 (QuadraticFormRecovery.RecoverForm)
// from ONE quadratic (vanishing space dim 1) to a form FAMILY — the whole degree-2 vanishing-space
// basis of the connection set — which the Plücker (alternating) and spinor (half-spin) varieties
// need (they are cut by several quadrics jointly).
//
// Two checks:
//  (A) MULTI-QUADRIC, self-contained. Build a Cayley graph on (F_p)^d whose connection set is
//      DEFINED as the joint zero S = { v != 0 : Q1(v)=0 and Q2(v)=0 } of two independent quadrics.
//      Then the recovered vanishing space V (all deg-2 forms vanishing on S) satisfies
//      Z(V) = S ∪ {0} EXACTLY (Z(V) ⊆ Z(Q1,Q2) = S∪{0} ⊆ Z(V)), so:
//        - VanishDim >= 2 (Q1, Q2 both in V, independent),
//        - every recovered quadric vanishes on all of S (soundness),
//        - OnCone(x-y) <=> x~y, 0 mismatches (reconstruction, guaranteed by construction).
//  (B) SINGLE-QUADRIC consistency: on a VO^eps_4(q) cone (one quadric), RecoverFormFamily must
//      report VanishDim == 1 and reconstruct the graph identically to A1 — the dim-1 special case.
public class RouteCFormFamilyProbe
{
    private readonly ITestOutputHelper _out;
    public RouteCFormFamilyProbe(ITestOutputHelper o) => _out = o;

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    // A minimal AffineStructure with the NATURAL coordinates of (F_p)^d — the form-recovery
    // solve uses only P/Dim/Origin/Coords, so Translations is a trivial placeholder here.
    static AffineStructureRecovery.AffineStructure NaturalCoords(int p, int dim)
    {
        int n = IPow(p, dim);
        var coords = new int[n][];
        for (int v = 0; v < n; v++)
        {
            var x = new int[dim];
            int t = v;
            for (int i = 0; i < dim; i++) { x[i] = t % p; t /= p; }
            coords[v] = x;
        }
        return new AffineStructureRecovery.AffineStructure
        {
            Translations = new PermutationGroup(n),
            Origin = 0,
            P = p,
            Dim = dim,
            Coords = coords,
        };
    }

    // ── (A) multi-quadric Cayley graph ────────────────────────────────────────
    [Theory]
    [InlineData(3, 4)]
    [InlineData(5, 4)]
    [InlineData(3, 6)]
    public void RecoverFormFamily_MultiQuadric(int p, int dim)
    {
        var aff = NaturalCoords(p, dim);
        int n = IPow(p, dim);

        // two independent CROSS-TERM quadrics (even-indexed vs odd-indexed pairings): disjoint
        // monomial supports ⟹ independent, and both vanish on every basis vector e_i ⟹ the joint
        // zero set S is nonempty for every (p, dim>=4).
        int Q1(int[] x) { int s = 0; for (int i = 0; i + 1 < dim; i += 2) s += x[i] * x[i + 1]; return ((s % p) + p) % p; }
        int Q2(int[] x) { int s = 0; for (int i = 1; i + 1 < dim; i += 2) s += x[i] * x[i + 1]; return ((s % p) + p) % p; }

        // connection set S = { v != 0 : Q1(v)=0 and Q2(v)=0 }; Cayley graph adj[u,v] = (u-v in S)
        var inS = new bool[n];
        int sizeS = 0;
        var d = new int[dim];
        for (int v = 1; v < n; v++)
        {
            if (Q1(aff.Coords[v]) == 0 && Q2(aff.Coords[v]) == 0) { inS[v] = true; sizeS++; }
        }
        var adj = new int[n * n];
        for (int u = 0; u < n; u++)
            for (int w = u + 1; w < n; w++)
            {
                for (int i = 0; i < dim; i++) d[i] = ((aff.Coords[u][i] - aff.Coords[w][i]) % p + p) % p;
                int enc = 0, pw = 1; for (int i = 0; i < dim; i++) { enc += d[i] * pw; pw *= p; }
                if (inS[enc]) { adj[u * n + w] = 1; adj[w * n + u] = 1; }
            }

        _out.WriteLine($"F_{p}^{dim}: |S|={sizeS}, n={n}");
        Assert.True(sizeS > 0, "connection set empty — pick different quadrics");

        var fam = QuadraticFormRecovery.RecoverFormFamily(adj, n, aff);
        Assert.True(fam is not null, "RecoverFormFamily returned null on a non-empty odd-q cone");
        _out.WriteLine($"    VanishDim={fam!.VanishDim}");

        // VanishDim >= 2 — Q1, Q2 are independent (disjoint monomial supports) and both vanish on S
        Assert.True(fam.VanishDim >= 2, $"VanishDim {fam.VanishDim} < 2 (expected >= 2 for two independent quadrics)");

        // soundness — every recovered quadric vanishes on all of S
        for (int v = 1; v < n; v++)
            if (inS[v])
                Assert.True(fam.OnCone(aff.Coords[v]), $"a recovered quadric does NOT vanish on cone point {v}");

        // reconstruction — OnCone(x-y) <=> x ~ y, 0 mismatches (guaranteed: Z(V) = S ∪ {0})
        int mism = 0;
        for (int x = 0; x < n; x++)
            for (int y = x + 1; y < n; y++)
            {
                for (int i = 0; i < dim; i++) d[i] = ((aff.Coords[x][i] - aff.Coords[y][i]) % p + p) % p;
                bool onCone = fam.OnCone(d);   // note: d != 0 since x != y
                if (onCone != (adj[x * n + y] == 1)) mism++;
            }
        _out.WriteLine($"    reconstruction mismatches={mism}/{n * (n - 1) / 2}");
        Assert.True(mism == 0, $"recovered family does NOT reconstruct the graph ({mism} mismatches)");
    }

    // ── (B) single-quadric consistency with A1 ────────────────────────────────
    [Theory]
    [InlineData(3, -1)]
    [InlineData(3, +1)]
    [InlineData(5, -1)]
    public void RecoverFormFamily_SingleQuadric_MatchesA1(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim), p = q;
        var (adj, aff) = BuildVO4Cone(q, eps);

        var single = QuadraticFormRecovery.RecoverForm(adj, n, aff);
        var fam = QuadraticFormRecovery.RecoverFormFamily(adj, n, aff);
        Assert.True(single is not null && fam is not null, "single/family recovery returned null on VO^eps_4");
        _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_4({q}): family VanishDim={fam!.VanishDim} (expect 1)");
        Assert.True(fam.VanishDim == 1, $"single-quadric cone gave VanishDim {fam.VanishDim} != 1");

        // both reconstruct the graph identically
        int mismFam = 0, mismSingle = 0;
        var d = new int[dim];
        for (int x = 0; x < n; x++)
            for (int y = x + 1; y < n; y++)
            {
                for (int i = 0; i < dim; i++) d[i] = ((aff.Coords[x][i] - aff.Coords[y][i]) % q + q) % q;
                if ((fam.OnCone(d)) != (adj[x * n + y] == 1)) mismFam++;
                if ((single!.Evaluate(d) == 0) != (adj[x * n + y] == 1)) mismSingle++;
            }
        Assert.True(mismFam == 0 && mismSingle == 0, $"reconstruction mismatch (family {mismFam}, single {mismSingle})");
    }

    // VO^eps_4(q) cone as a Cayley graph on (F_q)^4 with natural coords (q prime). Standalone
    // (no harness) — builds the SAME cone as RouteCF1Probe but coordinatized directly.
    static (int[] adj, AffineStructureRecovery.AffineStructure aff) BuildVO4Cone(int q, int eps)
    {
        const int dim = 4, m = 2;
        int n = IPow(q, dim);
        var aff = NaturalCoords(q, dim);
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
                            int g = ((y * y + b * y % q * z) % q + c * (z * z % q)) % q;
                            if (g % q == 0) { aniso = false; break; }
                        }
                    if (aniso) { bb = b; cc = c; found = true; }
                }
            if (!found) throw new Exception($"no anisotropic binary form over GF({q})");
        }
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
        var adj = new int[n * n];
        var d = new int[dim];
        for (int u = 0; u < n; u++)
            for (int w = u + 1; w < n; w++)
            {
                for (int i = 0; i < dim; i++) d[i] = ((aff.Coords[u][i] - aff.Coords[w][i]) % q + q) % q;
                if (Q(d) == 0) { adj[u * n + w] = 1; adj[w * n + u] = 1; }
            }
        return (adj, aff);
    }
}
