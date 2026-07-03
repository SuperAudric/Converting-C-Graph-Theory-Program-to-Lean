using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — F1 + A1 CONFIRMATION PROBE (2026-07-03).
//
// F1 (docs/chain-descent-route-c-plan.md §6) recovers the additive/affine (F_p)^d structure; A1 recovers
// the quadratic form Q from the coordinatized cone. Exercises the PRODUCTION path — AffineStructure
// Recovery.Recover (F1) + QuadraticFormRecovery.RecoverForm (A1) + PermutationGroup.RegularNormalP
// Subgroup — against the REAL harness output (CanonResult.ResidualGroup). Per VO^eps_4(q):
//   (I)  INTERFACE — ResidualGroup contains the translations and has full |Aut| (ground truth = the
//        known translations in the vector encoding).
//   (II) F1 RECOVERY — the recovered translation group equals T exactly; regular + elementary-abelian.
//   (III) A1 RECOVERY — the recovered Q + F1 coords RECONSTRUCT THE ENTIRE GRAPH:
//        Q(coords[x]-coords[y]) == 0  <=>  x ~ y  (Route C's core claim). Odd q; char-2 = separate track.
public class RouteCF1Probe
{
    private readonly ITestOutputHelper _out;
    public RouteCF1Probe(ITestOutputHelper o) => _out = o;

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    // ── VO^eps_4(q) as flat adjacency, vertex v <-> Vec(v) (digit i = coeff of q^i). Vertex 0 = zero. ──
    static (int[] adj, Func<int, int[]> vec, Func<int[], int> enc) AffinePolar4(int q, int eps)
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
                            int g = ((y * y + b * y % q * z) % q + c * (z * z % q)) % q;
                            if (g % q == 0) { aniso = false; break; }
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

    sealed class PermEq : IEqualityComparer<int[]>
    {
        public static readonly PermEq I = new();
        public bool Equals(int[]? a, int[]? b)
        {
            if (ReferenceEquals(a, b)) return true;
            if (a is null || b is null || a.Length != b.Length) return false;
            for (int i = 0; i < a.Length; i++) if (a[i] != b[i]) return false;
            return true;
        }
        public int GetHashCode(int[] a) { int h = 17; foreach (int x in a) h = h * 31 + x; return h; }
    }

    // Fast confirmation (n ≤ 81): char-2 (Clebsch) + odd-q, both types.
    [Theory]
    [InlineData(2, -1)]  // VO^-_4(2) = Clebsch, n=16, p=2 (T-recovery only; cone check is char-2, skipped)
    [InlineData(2, +1)]  // VO^+_4(2), n=16
    [InlineData(3, -1)]  // VO^-_4(3), n=81  (odd q: full check incl. cone)
    [InlineData(3, +1)]  // VO^+_4(3), n=81
    public void F1_Recovers_TranslationGroup(int q, int eps) => Run(q, eps);

    // The branching case (VO^-_4(5)) + n=625; slow only because the CANONIZER at n=625 costs minutes
    // (the known per-node wall, orthogonal to F1). CONFIRMED: q=5,-1 recovered T (625), coneVanishDim=1.
    [Theory]
    [Trait("Category", "LongRunning")]
    [InlineData(5, -1)]
    [InlineData(5, +1)]
    public void F1_Recovers_TranslationGroup_Large(int q, int eps) => Run(q, eps);

    void Run(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim), p = q;   // q prime
        var (adj, Vec, Enc) = AffinePolar4(q, eps);
        string nm = $"VO^{(eps < 0 ? "-" : "+")}_{dim}({q}) n={n}";

        // ground truth: the translations in the vector encoding
        int[] Transl(int w) { var wv = Vec(w); var perm = new int[n]; for (int v = 0; v < n; v++) { var xv = Vec(v); var s = new int[dim]; for (int i = 0; i < dim; i++) s[i] = (xv[i] + wv[i]) % q; perm[v] = Enc(s); } return perm; }
        var Ttrue = new HashSet<int[]>(PermEq.I);
        for (int w = 0; w < n; w++) Ttrue.Add(Transl(w));

        // run the REAL canonizer (deferral mode = fast, single-path, recovers full |Aut|)
        var cd = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        { EnableLinearOracle = true, EnableDeferral = true };
        var res = cd.Canonize(new sbyte[n * n], new WarmPartition(n));
        var G = res.ResidualGroup;
        _out.WriteLine($"{nm}: flagged={res.Flagged} |Aut|={G.Order} #gens={G.Generators.Count}");

        // (I) INTERFACE — the harness delivers the translations
        Assert.False(res.Flagged, $"{nm}: canonizer flagged");
        foreach (var t in Ttrue) Assert.True(G.Contains(t), $"{nm}: a translation is NOT in ResidualGroup");

        // (II) RECOVERY — the PRODUCTION F1 path recovers exactly the translation group
        var s = AffineStructureRecovery.Recover(G, p, origin: 0);
        Assert.True(s is not null, $"{nm}: AffineStructureRecovery.Recover returned null");
        Assert.True(s!.Dim == dim, $"{nm}: recovered Dim {s.Dim} != {dim}");
        var Trec = new HashSet<int[]>(s.Translations.Elements(), PermEq.I);
        _out.WriteLine($"    recovered |T|={Trec.Count} (expect n={n})  Dim={s.Dim}");
        Assert.True(Trec.SetEquals(Ttrue), $"{nm}: recovered translation group != true translations (|T|={Trec.Count})");
        Assert.True((int)s.Translations.Order == n, $"{nm}: |T| != n");
        Assert.True(s.Translations.IsAbelian && s.Translations.HasExponentDividing(p), $"{nm}: T not elementary-abelian exponent {p}");
        foreach (var t in Trec) if (!Perm.IsIdentity(t)) Assert.True(Enumerable.Range(0, n).All(i => t[i] != i), $"{nm}: T not regular");

        Assert.True(s.Coords[s.Origin].All(x => x == 0), $"{nm}: origin coord not zero");

        // (III) A1 — recover Q from F1's coordinatized cone, and check it RECONSTRUCTS THE GRAPH.
        // (Odd q; char-2 is a separate Arf track, and RecoverForm returns null there.)
        if (q % 2 == 1)
        {
            var qf = QuadraticFormRecovery.RecoverForm(adj, n, s);
            Assert.True(qf is not null, $"{nm}: A1 RecoverForm returned null (cone did not pin Q up to scalar)");
            Assert.True(qf!.Coeffs.Any(a => a % p != 0), $"{nm}: recovered Q is identically zero");

            // Route C's core claim: recovered Q + F1 coords reproduce the ENTIRE adjacency —
            // Q(coords[x] - coords[y]) == 0  <=>  x ~ y.
            int mism = 0;
            var diff = new int[dim];
            for (int x = 0; x < n; x++)
                for (int y = x + 1; y < n; y++)
                {
                    for (int i = 0; i < dim; i++) diff[i] = ((s.Coords[x][i] - s.Coords[y][i]) % q + q) % q;
                    bool iso = qf.Evaluate(diff) == 0;
                    if (iso != (adj[x * n + y] == 1)) mism++;
                }
            _out.WriteLine($"    A1: recovered Q (#coeffs={qf.Coeffs.Length}) reconstructs graph, mismatches={mism}/{n * (n - 1) / 2}");
            Assert.True(mism == 0, $"{nm}: recovered Q + coords do NOT reconstruct the graph ({mism} mismatches)");
        }
        _out.WriteLine($"    OK");
    }
}
