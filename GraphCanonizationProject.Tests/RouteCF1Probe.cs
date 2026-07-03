using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — F1 CONFIRMATION PROBE (2026-07-03).
//
// F1 (docs/chain-descent-route-c-plan.md §6) recovers the additive/affine (F_p)^d structure from the
// ABSTRACT graph so that "z - t" (and later Q(z-t)) is defined. The family-agnostic recovery: the
// translation group is the SOCLE of Aut — for these affine-primitive graphs, T = O_p(Aut), the regular
// elementary-abelian translation group.
//
// This exercises the PRODUCTION path — AffineStructureRecovery.Recover / PermutationGroup.
// RegularNormalPSubgroup — against the REAL harness output (CanonResult.ResidualGroup), the interface
// F1 depends on in the larger build. Per VO^eps_4(q):
//   (I)  INTERFACE — ResidualGroup contains the translations and has full |Aut| (ground truth = the
//        known translations in the vector encoding).
//   (II) RECOVERY  — AffineStructureRecovery.Recover's translation group equals T exactly; regular +
//        elementary-abelian of order q^d.
//   (III) COORDS   — the recovered coordinates make the connection set a quadric cone (degree-2
//        vanishing dim = 1), the F1 -> A1 hand-off. (Odd q; char-2 skips this.)
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

    // rank over F_q (Gaussian elimination) for the cone / degree-2 vanishing check
    static int RankModQ(List<int[]> rows, int q)
    {
        if (rows.Count == 0) return 0;
        int ncols = rows[0].Length, r = 0;
        for (int c = 0; c < ncols && r < rows.Count; c++)
        {
            int piv = -1;
            for (int i = r; i < rows.Count; i++) if (rows[i][c] % q != 0) { piv = i; break; }
            if (piv < 0) continue;
            (rows[r], rows[piv]) = (rows[piv], rows[r]);
            int inv = ModInv(((rows[r][c] % q) + q) % q, q);
            for (int c2 = 0; c2 < ncols; c2++) rows[r][c2] = rows[r][c2] * inv % q;
            for (int i = 0; i < rows.Count; i++)
                if (i != r && rows[i][c] % q != 0)
                {
                    int f = rows[i][c];
                    for (int c2 = 0; c2 < ncols; c2++) rows[i][c2] = (((rows[i][c2] - f * rows[r][c2]) % q) + q * q) % q;
                }
            r++;
        }
        return r;
    }
    static int ModInv(int a, int q) { int r = 1; for (int i = 0; i < q - 2; i++) r = r * a % q; return r; }  // q prime

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

        // (III) COORDS — the recovered coordinates make the connection set a quadric cone (odd q)
        if (q % 2 == 1)
        {
            int o0 = s.Origin;
            Assert.True(s.Coords[o0].All(x => x == 0), $"{nm}: origin coord not zero");
            var monos = new List<(int, int)>();
            for (int i = 0; i < dim; i++) for (int j = i; j < dim; j++) monos.Add((i, j));
            var rows = new List<int[]>();
            int neigh = 0;
            for (int x = 0; x < n; x++)
                if (x != o0 && adj[o0 * n + x] == 1)
                {
                    neigh++;
                    rows.Add(monos.Select(mm => s.Coords[x][mm.Item1] * s.Coords[x][mm.Item2] % q).ToArray());
                }
            int vanish = monos.Count - RankModQ(rows, q);
            _out.WriteLine($"    coords: |neigh|={neigh} coneVanishDim={vanish} (expect 1)");
            Assert.True(vanish == 1, $"{nm}: cone vanishing dim = {vanish} != 1 (Q not uniquely recoverable in recovered coords)");
        }
        _out.WriteLine($"    OK");
    }
}
