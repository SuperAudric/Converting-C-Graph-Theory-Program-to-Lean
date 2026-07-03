using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — F1 CONFIRMATION PROBE (2026-07-03).
//
// F1 (docs/chain-descent-route-c-plan.md §6) recovers the additive/affine (F_p)^d structure from the
// ABSTRACT graph so that "z - t" (and later Q(z-t)) is defined. The family-agnostic recovery: the
// translation group is the SOCLE of Aut — for these affine-primitive graphs, T = O_p(Aut), the regular
// elementary-abelian translation group. route_c_f1_probe.py validated the O_p algorithm from *given*
// generators; THIS confirms it works against the REAL harness output (CanonResult.ResidualGroup), the
// interface F1 depends on in the larger build.
//
// What it checks, per VO^eps_4(q):
//   (I)  INTERFACE — the harness's ResidualGroup contains the translations and has full |Aut| (so O_p
//        can recover them). Ground truth = the known translations in the vector encoding.
//   (II) RECOVERY  — O_p(ResidualGroup), computed by normal closures (the production F1 algorithm),
//        equals the translation group T exactly; T is regular + elementary-abelian of order q^d.
//   (III) COORDS   — a basis of the recovered T coordinatizes the vertices so the connection set is a
//        quadric cone (degree-2 vanishing dim = 1), the F1 -> A1 hand-off. (Odd q; char-2 skips this.)
public class RouteCF1Probe
{
    private readonly ITestOutputHelper _out;
    public RouteCF1Probe(ITestOutputHelper o) => _out = o;

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    // ── VO^eps_4(q) as flat adjacency, vertex v <-> Vec(v) (digit i = coeff of q^i). Vertex 0 = zero. ──
    static (int[] adj, Func<int, int[]> vec, Func<int[], int> enc, Func<int[], int> qform) AffinePolar4(int q, int eps)
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
        return (adj, Vec, Enc, Q);
    }

    // ── permutation helpers (perms are int[]; Perm.Compose(p,q)[i]=p[q[i]] = apply q then p) ──
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
    static long Gcd(long a, long b) { while (b != 0) { (a, b) = (b, a % b); } return a; }
    static long Ord(int[] p)
    {
        int n = p.Length; var seen = new bool[n]; long o = 1;
        for (int i = 0; i < n; i++)
            if (!seen[i]) { int c = 0, j = i; while (!seen[j]) { seen[j] = true; j = p[j]; c++; } o = o / Gcd(o, c) * c; }
        return o;
    }
    static int[] Pow(int[] g, long e)
    {
        var r = Perm.Identity(g.Length); var b = (int[])g.Clone();
        while (e > 0) { if ((e & 1) == 1) r = Perm.Compose(r, b); b = Perm.Compose(b, b); e >>= 1; }
        return r;
    }
    static int[] PPart(int[] g, int p)   // g^(p'-part of its order): a p-element
    {
        long m = Ord(g); while (m % p == 0) m /= p;   // m := p'-part of the order
        return Pow(g, m);
    }
    static bool IsPPower(long m, int p) { while (m % p == 0) m /= p; return m == 1; }
    static int[] Conj(int[] c, int[] g) => Perm.Compose(Perm.Compose(g, c), Perm.Inverse(g));

    // <c^G> as a subgroup; null if it exceeds cap (=> not a small p-subgroup we want)
    static HashSet<int[]>? NormalClosure(int[] c, IReadOnlyList<int[]> gens, int cap)
    {
        var cl = new HashSet<int[]>(PermEq.I) { c };
        var fr = new Queue<int[]>(); fr.Enqueue(c);
        while (fr.Count > 0)
        {
            var x = fr.Dequeue();
            foreach (var s in gens)
                foreach (var y in new[] { Conj(x, s), Conj(x, Perm.Inverse(s)) })
                    if (cl.Add(y)) { fr.Enqueue(y); if (cl.Count > cap) return null; }
        }
        var basis = cl.ToArray();
        var K = new HashSet<int[]>(PermEq.I) { Perm.Identity(c.Length) };
        foreach (var b in basis) K.Add(b);
        var q = new Queue<int[]>(K);
        while (q.Count > 0)
        {
            var x = q.Dequeue();
            foreach (var b in basis) { var y = Perm.Compose(x, b); if (K.Add(y)) { q.Enqueue(y); if (K.Count > cap) return null; } }
        }
        return K;
    }
    static bool IsPGroup(IEnumerable<int[]> K, int p) => K.All(g => IsPPower(Ord(g), p));

    // O_p(G) = the largest normal p-subgroup, via the join of the p-group normal closures of the p-parts
    // of generators (and pairwise products, to guarantee a translation is seeded). Each such closure lies
    // in O_p; their join IS O_p. Cap at |T| = n (a translation's normal closure is exactly T, size n).
    static HashSet<int[]> ComputePCore(PermutationGroup g, int p, int n)
    {
        var gens = g.Generators;
        // seed from generators first; only if that undershoots, fall back to pairwise products.
        var core = PCoreFromSeeds(gens, gens, p, n);
        if (core.Count < n)
        {
            var seeds = new List<int[]>(gens);
            for (int i = 0; i < gens.Count; i++)
                for (int j = 0; j < gens.Count; j++)
                    if (i != j) seeds.Add(Perm.Compose(gens[i], gens[j]));
            core = PCoreFromSeeds(seeds, gens, p, n);
        }
        return core;
    }

    // join of the p-group normal closures of the p-parts of `seeds` (closed as a subgroup)
    static HashSet<int[]> PCoreFromSeeds(IReadOnlyList<int[]> seeds, IReadOnlyList<int[]> gens, int p, int n)
    {
        var all = new HashSet<int[]>(PermEq.I) { Perm.Identity(n) };
        var seenSeed = new HashSet<int[]>(PermEq.I);
        foreach (var s in seeds)
        {
            var c = PPart(s, p);
            if (Perm.IsIdentity(c) || !seenSeed.Add(c)) continue;
            var K = NormalClosure(c, gens, n);
            if (K != null && IsPGroup(K, p)) foreach (var x in K) all.Add(x);
        }
        var basis = all.ToArray();
        var q = new Queue<int[]>(all);
        while (q.Count > 0)
        {
            var x = q.Dequeue();
            foreach (var b in basis) { var y = Perm.Compose(x, b); if (all.Add(y)) q.Enqueue(y); }
        }
        return all;
    }

    // ── rank over F_q (Gaussian elimination) for the cone / degree-2 vanishing check ──
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
        var (adj, Vec, Enc, Q) = AffinePolar4(q, eps);
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
        Assert.True(G.Order >= n, $"{nm}: |Aut| < n (group too small to be full Aut)");

        // (II) RECOVERY — O_p(ResidualGroup) == T
        var Trec = ComputePCore(G, p, n);
        _out.WriteLine($"    O_p recovered |Trec|={Trec.Count} (expect n={n})");
        Assert.True(Trec.SetEquals(Ttrue), $"{nm}: O_p(ResidualGroup) != translation group (|Trec|={Trec.Count})");
        Assert.True(Trec.Count == n, $"{nm}: |O_p| != n");
        // regular: every non-identity element fixed-point-free
        foreach (var t in Trec) if (!Perm.IsIdentity(t)) Assert.True(Enumerable.Range(0, n).All(i => t[i] != i), $"{nm}: O_p not regular");
        // elementary abelian: exponent p and abelian
        foreach (var t in Trec) Assert.True(IsPPower(Ord(t), p) && Ord(t) <= p, $"{nm}: O_p not exponent p");
        var Tl = Trec.ToArray();
        for (int i = 0; i < Tl.Length; i++) for (int j = i + 1; j < Tl.Length; j++)
            Assert.True(PermEq.I.Equals(Perm.Compose(Tl[i], Tl[j]), Perm.Compose(Tl[j], Tl[i])), $"{nm}: O_p not abelian");

        // (III) COORDS — basis of recovered T coordinatizes; connection set is a quadric cone (odd q)
        if (q % 2 == 1)
        {
            const int o0 = 0;   // origin = vertex 0
            // greedy F_p-basis of Trec (subgroup grows by factor p each add)
            var basis = new List<int[]>();
            var span = new HashSet<int[]>(PermEq.I) { Perm.Identity(n) };
            foreach (var t in Trec)
            {
                if (Perm.IsIdentity(t)) continue;
                var trial = SubgroupClosure(basis.Append(t), n);
                if (trial.Count > span.Count) { basis.Add(t); span = trial; }
                if (span.Count == n) break;
            }
            Assert.True(basis.Count == dim, $"{nm}: recovered basis size {basis.Count} != {dim}");
            // coordinate of each vertex via the regular action: (c_1..c_d) -> (prod b_k^{c_k})[o0]
            var vcoord = new int[n][];
            foreach (var c in AllTuples(p, dim))
            {
                var e = Perm.Identity(n);
                for (int k = 0; k < dim; k++) e = Perm.Compose(e, Pow(basis[k], c[k]));
                vcoord[e[o0]] = c;
            }
            // connection set = neighbours of o0; degree-2 vanishing dim on their coords
            var monos = new List<(int, int)>();
            for (int i = 0; i < dim; i++) for (int j = i; j < dim; j++) monos.Add((i, j));
            var rowsList = new List<int[]>();
            int neigh = 0;
            for (int x = 0; x < n; x++)
                if (x != o0 && adj[o0 * n + x] == 1)
                {
                    neigh++;
                    var row = monos.Select(m => vcoord[x][m.Item1] * vcoord[x][m.Item2] % q).ToArray();
                    rowsList.Add(row);
                }
            int vanish = monos.Count - RankModQ(rowsList, q);
            _out.WriteLine($"    coords: |neigh|={neigh} coneVanishDim={vanish} (expect 1)");
            Assert.True(vanish == 1, $"{nm}: cone vanishing dim = {vanish} != 1 (Q not uniquely recoverable in recovered coords)");
        }
        _out.WriteLine($"    OK");
    }

    static HashSet<int[]> SubgroupClosure(IEnumerable<int[]> gens, int n)
    {
        var g = gens.ToArray();
        var K = new HashSet<int[]>(PermEq.I) { Perm.Identity(n) };
        foreach (var x in g) K.Add(x);
        var q = new Queue<int[]>(K);
        while (q.Count > 0) { var x = q.Dequeue(); foreach (var b in g) { var y = Perm.Compose(x, b); if (K.Add(y)) q.Enqueue(y); } }
        return K;
    }
    static IEnumerable<int[]> AllTuples(int p, int d)
    {
        var c = new int[d];
        while (true)
        {
            yield return (int[])c.Clone();
            int i = 0; for (; i < d; i++) { if (++c[i] < p) break; c[i] = 0; }
            if (i == d) yield break;
        }
    }
}
