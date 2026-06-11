using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Xunit;
using Xunit.Abstractions;

// ─────────────────────────────────────────────────────────────────────────────
// PDS amorphic-scheme probe — the GENUINE rank-4 amorphic-NLS residue for G2-B
// (docs/chain-descent-module-adjoin-plan.md §7/§9 route (1): Davis–Xiang partial
//  difference sets in non-elementary-abelian 2-groups).
//
// CONTEXT.  The seal closes iff G2-B is empty: a primitive, non-abelian, non-
// recovering schurian scheme.  The MOST LIKELY witness shape (largest separability
// gap Ĝ⊋G) is a **primitive rank-4 amorphic negative-Latin-square (NLS)** scheme:
// three INTERCHANGEABLE equal-valency strongly-regular classes (the amorphic S3 on
// relations the automorphism group only partly realises).  This is the one shape the
// five prior probes structurally miss (CosetSchemeProbe reached primitive non-affine
// rank 4–9 but NON-amorphic; Latin squares give L-type / imprimitive; the affine
// sweep gives the abelian/Galois gap on Z2^d = ELEMENTARY abelian).
//
// THE CONSTRUCTION (exhaustive + fully verified, no paper reproduction).  A rank-4
// amorphic NLS scheme of order v = n^2 partitions G\{0} into three NL_g(n) classes
// with g = (n-1)/3.  For a 2-group v = 4^t the smallest equal-valency case is v=16
// (n=4, g=1): three **Clebsch** graphs SRG(16,5,0,2) partitioning the 15 non-identity
// elements.  At order 16 the symmetric subsets are exhaustively enumerable, so we
// SEARCH all three-Clebsch partitions on every group of order 16 and fully verify
// each (PDS difference-distribution + BuildScheme coherence + equal SRG params).
//   • Z2^4              — the known AFFINE Clebsch amorphic scheme: a SELF-TEST anchor
//                         (the search MUST find it; = the affine-probe's F16 index-3).
//   • Z4×Z2^2, Z4^2,    — the genuine NON-elementary-abelian 2-group targets (the
//     Z8×Z2               Davis–Xiang zone).  A primitive amorphic scheme here that
//                         FAILS to separate at base+O(1) = a G2-B witness.
// Then measure recovery with the same Lean proxies as the sibling probes
// (EdgeGenerates / WLDepth / SeparatesAtBoundedBase).
//
// WHY ORDER 16 IS DECISIVE-OR-DIRECTING.  If a primitive non-elementary-abelian
// amorphic scheme exists at order 16 it is a translation (regular-group) scheme —
// exactly the kind the Hanaki–Miyamoto catalogue DATA OMITS — so it is a genuinely
// new data point.  If NONE exists on Z4^2 / Z4×Z2^2 / Z8×Z2 (only on the elementary
// Z2^4), that confirms the memory's "smallest non-elementary-abelian amorphic NLS is
// order ≥ 64" and the residue zone genuinely starts higher (→ the order-64 explicit
// DX construction is the next, heavier step).
//
// The general relation-table measurement core (BuildScheme / Primitive / EdgeGenerates
// / WLDepth / HasProperBlock) is the same logic as the sibling probes (each probe is
// self-contained by convention).  The new pieces are the mixed-radix abelian-group
// arithmetic, the PDS difference-distribution check, and the amorphic-partition search.
// No production code is touched.
// ─────────────────────────────────────────────────────────────────────────────
public class PdsAmorphicSchemeProbe(ITestOutputHelper output)
{
    sealed class Scheme
    {
        public required int N;
        public required int Rank;
        public required int[,] Rel;
        public required int[] Valency;
        public required int[,,] P;
        public required bool Symmetric;
    }

    // ── Mixed-radix finite abelian group G = Z_{m0} × … × Z_{m_{k-1}} ──────────────
    sealed class Grp
    {
        public required int V;            // order
        public required int[] M;          // moduli
        public required int[] Stride;     // place values (Stride[i] = ∏_{j<i} M[j])
        public required string Name;
    }

    static Grp MakeGroup(string name, params int[] moduli)
    {
        int v = 1; var stride = new int[moduli.Length];
        for (int i = 0; i < moduli.Length; i++) { stride[i] = v; v *= moduli[i]; }
        return new Grp { V = v, M = moduli, Stride = stride, Name = name };
    }

    static int Digit(Grp g, int x, int i) => (x / g.Stride[i]) % g.M[i];
    static int Add(Grp g, int x, int y)
    {
        int r = 0;
        for (int i = 0; i < g.M.Length; i++) r += ((Digit(g, x, i) + Digit(g, y, i)) % g.M[i]) * g.Stride[i];
        return r;
    }
    static int Neg(Grp g, int x)
    {
        int r = 0;
        for (int i = 0; i < g.M.Length; i++) r += ((g.M[i] - Digit(g, x, i)) % g.M[i]) * g.Stride[i];
        return r;
    }
    static int Sub(Grp g, int x, int y) => Add(g, x, Neg(g, y));

    // ── PDS check: the difference distribution of a symmetric set D ────────────────
    // Returns (k, λ, μ) iff D (with D = −D, 0 ∉ D) is a partial difference set, i.e.
    // count_D(t) = #{(a,b)∈D² : a−b = t} equals λ for t∈D, μ for t∉D\{0}.  Then
    // Cay(G,D) is SRG(v, |D|, λ, μ).  Returns null if not a PDS.
    static (int k, int lam, int mu)? PdsParams(Grp g, int[] D)
    {
        var inD = new bool[g.V];
        foreach (int d in D) { if (d == 0) return null; inD[d] = true; }
        foreach (int d in D) if (!inD[Neg(g, d)]) return null;     // symmetric
        var cnt = new int[g.V];
        foreach (int a in D) foreach (int b in D) cnt[Sub(g, a, b)]++;
        int lam = -1, mu = -1;
        for (int t = 1; t < g.V; t++)
        {
            if (inD[t]) { if (lam < 0) lam = cnt[t]; else if (cnt[t] != lam) return null; }
            else { if (mu < 0) mu = cnt[t]; else if (cnt[t] != mu) return null; }
        }
        if (lam < 0 || mu < 0) return null;
        return (D.Length, lam, mu);
    }

    // All symmetric subsets of G\{0} of size `size` (a union of involutions and
    // inverse-pairs).  Bounded: at order 16 ≤ C(15,5)=3003.
    static List<int[]> SymmetricSubsets(Grp g, int size)
    {
        var involutions = new List<int>();
        var pairs = new List<(int, int)>();
        var seen = new bool[g.V];
        for (int x = 1; x < g.V; x++)
        {
            if (seen[x]) continue;
            int nx = Neg(g, x);
            if (nx == x) involutions.Add(x);
            else { pairs.Add((x, nx)); seen[nx] = true; }
            seen[x] = true;
        }
        var result = new List<int[]>();
        // choose i involutions + p pairs with i + 2p = size, i ≤ |inv|, p ≤ |pairs|.
        for (int i = size % 2; i <= Math.Min(size, involutions.Count); i += 2)
        {
            int p = (size - i) / 2;
            if (p < 0 || p > pairs.Count) continue;
            foreach (var invSel in Choose(involutions.Count, i))
                foreach (var pairSel in Choose(pairs.Count, p))
                {
                    var d = new List<int>();
                    foreach (int idx in invSel) d.Add(involutions[idx]);
                    foreach (int idx in pairSel) { d.Add(pairs[idx].Item1); d.Add(pairs[idx].Item2); }
                    result.Add(d.ToArray());
                }
        }
        return result;
    }

    static IEnumerable<int[]> Choose(int n, int k)
    {
        if (k < 0 || k > n) yield break;
        var idx = Enumerable.Range(0, k).ToArray();
        if (k == 0) { yield return Array.Empty<int>(); yield break; }
        while (true)
        {
            yield return (int[])idx.Clone();
            int i = k - 1;
            while (i >= 0 && idx[i] == n - k + i) i--;
            if (i < 0) yield break;
            idx[i]++;
            for (int j = i + 1; j < k; j++) idx[j] = idx[j - 1] + 1;
        }
    }

    // Build the Cayley relation table of a partition of G\{0} into classes: M[x,y] =
    // class index of (x−y) (+1; diagonal = 0).  Symmetric since each class is −closed.
    static int[,] CayleyTable(Grp g, List<int[]> parts)
    {
        var classOf = new int[g.V];
        for (int c = 0; c < parts.Count; c++) foreach (int d in parts[c]) classOf[d] = c + 1;
        var M = new int[g.V, g.V];
        for (int x = 0; x < g.V; x++) for (int y = 0; y < g.V; y++) M[x, y] = (x == y) ? 0 : classOf[Sub(g, x, y)];
        return M;
    }

    // ── General-scheme measurement core (same logic as the sibling probes) ─────────
    static Scheme? BuildScheme(int[,] M, int n)
    {
        int diag = M[0, 0];
        var labels = new SortedSet<int>();
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) labels.Add(M[i, j]);
        var remap = new Dictionary<int, int> { [diag] = 0 };
        int next = 1;
        foreach (var v in labels) if (v != diag) remap[v] = next++;
        int rank = remap.Count;
        var rel = new int[n, n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) rel[i, j] = remap[M[i, j]];

        for (int i = 0; i < n; i++)
        {
            if (rel[i, i] != 0) return null;
            for (int j = 0; j < n; j++) if (i != j && rel[i, j] == 0) return null;
        }

        var val = new int[rank];
        for (int j = 0; j < n; j++) val[rel[0, j]]++;
        for (int i = 1; i < n; i++)
        {
            var v = new int[rank];
            for (int j = 0; j < n; j++) v[rel[i, j]]++;
            for (int k = 0; k < rank; k++) if (v[k] != val[k]) return null;
        }

        var P = new int[rank, rank, rank];
        for (int k = 0; k < rank; k++)
        {
            int rx = -1, ry = -1;
            for (int x = 0; x < n && rx < 0; x++) for (int y = 0; y < n; y++) if (rel[x, y] == k) { rx = x; ry = y; break; }
            for (int z = 0; z < n; z++) P[k, rel[rx, z], rel[z, ry]]++;
            for (int x = 0; x < n; x++)
            {
                for (int y = 0; y < n; y++)
                {
                    if (rel[x, y] != k || (x == rx && y == ry)) continue;
                    var qq = new int[rank, rank];
                    for (int z = 0; z < n; z++) qq[rel[x, z], rel[z, y]]++;
                    for (int i = 0; i < rank; i++) for (int j = 0; j < rank; j++) if (qq[i, j] != P[k, i, j]) return null;
                    goto nextK;
                }
            }
            nextK:;
        }

        bool sym = true;
        for (int i = 0; i < n && sym; i++) for (int j = 0; j < n; j++) if (rel[i, j] != rel[j, i]) { sym = false; break; }
        return new Scheme { N = n, Rank = rank, Rel = rel, Valency = val, P = P, Symmetric = sym };
    }

    // Full coherence verification (every pair with rel=k has the same intersection array).
    static bool FullyCoherent(Scheme s)
    {
        int n = s.N, rank = s.Rank;
        for (int k = 0; k < rank; k++)
        {
            int[,]? baseQ = null;
            for (int x = 0; x < n; x++)
                for (int y = 0; y < n; y++)
                {
                    if (s.Rel[x, y] != k) continue;
                    var qq = new int[rank, rank];
                    for (int z = 0; z < n; z++) qq[s.Rel[x, z], s.Rel[z, y]]++;
                    if (baseQ is null) baseQ = qq;
                    else { for (int i = 0; i < rank; i++) for (int j = 0; j < rank; j++) if (qq[i, j] != baseQ[i, j]) return false; }
                }
        }
        return true;
    }

    static bool Primitive(Scheme s)
    {
        for (int k = 1; k < s.Rank; k++)
        {
            var seen = new bool[s.N]; var st = new Stack<int>(); st.Push(0); seen[0] = true; int c = 1;
            while (st.Count > 0) { int x = st.Pop(); for (int y = 0; y < s.N; y++) if (!seen[y] && s.Rel[x, y] == k) { seen[y] = true; c++; st.Push(y); } }
            if (c != s.N) return false;
        }
        return true;
    }

    static HashSet<int> GeneratedClosedSubset(Scheme s, int k)
    {
        var I = new HashSet<int> { 0, k };
        bool grew = true;
        while (grew)
        {
            grew = false;
            var add = new List<int>();
            foreach (int i in I) foreach (int j in I)
                for (int m = 0; m < s.Rank; m++)
                    if (s.P[m, i, j] != 0 && !I.Contains(m)) add.Add(m);
            foreach (int m in add) if (I.Add(m)) grew = true;
        }
        return I;
    }

    static bool HasProperBlock(Scheme s)
    {
        for (int k = 1; k < s.Rank; k++)
            if (GeneratedClosedSubset(s, k).Count < s.Rank) return true;
        return false;
    }

    static bool EdgeGenerates(Scheme s, int j0)
    {
        var iso = new bool[s.Rank]; iso[0] = true; int count = 1;
        if (j0 != 0) { iso[j0] = true; count = 2; }
        bool progress = true;
        while (progress && count < s.Rank)
        {
            progress = false;
            var isoList = new List<int>(); for (int l = 0; l < s.Rank; l++) if (iso[l]) isoList.Add(l);
            string Sig(int i)
            {
                var sb = new StringBuilder();
                sb.Append(i == j0 ? '1' : '0');
                foreach (int l in isoList) { sb.Append(':'); sb.Append(s.P[i, l, j0]); }
                return sb.ToString();
            }
            var sig = new string[s.Rank];
            var seen = new Dictionary<string, int>();
            for (int i = 1; i < s.Rank; i++) { sig[i] = Sig(i); seen[sig[i]] = seen.GetValueOrDefault(sig[i], 0) + 1; }
            for (int i = 1; i < s.Rank; i++)
                if (!iso[i] && seen[sig[i]] == 1) { iso[i] = true; count++; progress = true; }
        }
        return count == s.Rank;
    }

    static bool Recovers(Scheme s) { for (int j0 = 1; j0 < s.Rank; j0++) if (EdgeGenerates(s, j0)) return true; return false; }

    static int[] Refine(Scheme s, List<int> ind)
    {
        int n = s.N;
        var color = new int[n];
        for (int i = 0; i < ind.Count; i++) color[ind[i]] = i + 1;
        int prev = color.Distinct().Count();
        while (true)
        {
            var sig = new (int, string)[n];
            for (int v = 0; v < n; v++)
            {
                var ms = new List<(int, int)>();
                for (int u = 0; u < n; u++) if (u != v) ms.Add((s.Rel[v, u], color[u]));
                ms.Sort();
                sig[v] = (color[v], string.Join(";", ms.Select(t => $"{t.Item1},{t.Item2}")));
            }
            var map = new Dictionary<(int, string), int>(); int next = 0; var nc = new int[n];
            foreach (var v in Enumerable.Range(0, n).OrderBy(v => sig[v].Item1).ThenBy(v => sig[v].Item2))
            { if (!map.TryGetValue(sig[v], out int c)) { c = next++; map[sig[v]] = c; } nc[v] = c; }
            int d2 = nc.Distinct().Count(); color = nc;
            if (d2 == prev) break;
            prev = d2;
        }
        return color;
    }

    static int WLDepth(Scheme s, int cap)
    {
        int n = s.N;
        var ind = new List<int>();
        for (int depth = 0; depth <= cap; depth++)
        {
            var color = Refine(s, ind);
            if (color.Distinct().Count() == n) return depth;
            var byColor = new Dictionary<int, List<int>>();
            for (int v = 0; v < n; v++) { if (!byColor.TryGetValue(color[v], out var lst)) { lst = new(); byColor[color[v]] = lst; } lst.Add(v); }
            int target = -1, best = 1;
            foreach (var kv in byColor) if (kv.Value.Count > best) { best = kv.Value.Count; target = kv.Value.Min(); }
            if (target < 0) return depth;
            ind.Add(target);
        }
        return cap + 1;
    }

    // NL-type SRG ⟺ the larger eigenvalue r and smaller s satisfy the negative-Latin
    // sign convention: r = g > 0, s = −(n−g) with v = n².  We classify from (v,k,λ,μ).
    static string SrgType(int v, int k, int lam, int mu)
    {
        double disc = (double)(lam - mu) * (lam - mu) + 4.0 * (k - mu);
        if (disc < 0) return "?";
        double root = Math.Sqrt(disc);
        double r = ((lam - mu) + root) / 2.0, sEig = ((lam - mu) - root) / 2.0;
        int n2 = (int)Math.Round(Math.Sqrt(v));
        if (n2 * n2 != v) return "?";
        // L_g(n): r=n−g, s=−g.  NL_g(n): r=g, s=−(n−g).
        if (Math.Abs(sEig + (n2 - r)) < 1e-6 && r > 0) return $"NL_{(int)Math.Round(r)}({n2})";
        if (Math.Abs(r - (n2 - (-sEig))) < 1e-6) return $"L_{(int)Math.Round(-sEig)}({n2})";
        return $"SRG r={r:0.##} s={sEig:0.##}";
    }

    // ── Search: all rank-(parts+1) equal-valency amorphic partitions of G\{0} into
    // `numClasses` PDS of size `size`.  Fully verified (PDS + coherent scheme). ───────
    static List<List<int[]>> FindAmorphicPartitions(Grp g, int numClasses, int size, int cap)
    {
        var pdsSets = new List<int[]>();
        var pdsKey = new List<long>();          // bitmask of membership (v ≤ 64)
        (int, int, int) targetParams = (-1, -1, -1);
        foreach (var d in SymmetricSubsets(g, size))
        {
            var pp = PdsParams(g, d);
            if (pp is null) continue;
            // require all classes share the SAME SRG params (interchangeable = amorphic gap)
            if (targetParams.Item1 < 0) targetParams = pp.Value;
            else if (pp.Value != targetParams) continue;
            long mask = 0; foreach (int x in d) mask |= 1L << x;
            pdsSets.Add(d); pdsKey.Add(mask);
        }
        var results = new List<List<int[]>>();
        long full = 0; for (int x = 1; x < g.V; x++) full |= 1L << x;
        // recursively pick numClasses disjoint PDS covering G\{0}, ordered by min element
        void Rec(long covered, int startIdx, List<int> chosen)
        {
            if (chosen.Count == numClasses) { if (covered == full) results.Add(chosen.Select(i => pdsSets[i]).ToList()); return; }
            if (results.Count >= cap) return;
            for (int i = startIdx; i < pdsSets.Count; i++)
            {
                if ((covered & pdsKey[i]) != 0) continue;
                chosen.Add(i); Rec(covered | pdsKey[i], i + 1, chosen); chosen.RemoveAt(chosen.Count - 1);
                if (results.Count >= cap) return;
            }
        }
        Rec(0, 0, new List<int>());
        return results;
    }

    // ── THE SELF-TEST: the search finds the AFFINE Clebsch amorphic scheme on Z2^4 ──
    [Fact]
    public void Probe_PdsSearch_SelfTest_Z2_4()
    {
        output.WriteLine("── PDS-search self-test: three-Clebsch amorphic scheme on Z2^4 (the affine anchor) ──");
        var g = MakeGroup("Z2^4", 2, 2, 2, 2);
        var parts = FindAmorphicPartitions(g, 3, 5, 50);
        output.WriteLine($"  Z2^4: found {parts.Count} rank-4 equal-valency amorphic partitions (3×SRG(16,5,0,2))");
        Assert.NotEmpty(parts);
        var s = BuildScheme(CayleyTable(g, parts[0]), g.V);
        Assert.NotNull(s);
        Assert.Equal(4, s!.Rank);
        Assert.True(FullyCoherent(s));
        var pp = PdsParams(g, parts[0][0])!.Value;
        output.WriteLine($"  class SRG params = (16,{pp.k},{pp.lam},{pp.mu}) = {SrgType(16, pp.k, pp.lam, pp.mu)}  (Clebsch = NL_1(4))");
        Assert.Equal((5, 0, 2), pp);
    }

    // ── THE PROBE: rank-4 amorphic NLS schemes on all groups of order 16 ────────────
    [Fact]
    public void Probe_AmorphicNLS_Order16()
    {
        output.WriteLine("── G2-B residue probe: rank-4 amorphic-NLS schemes on groups of order 16 ──");
        output.WriteLine("    the genuine Davis–Xiang shape: 3 interchangeable equal-valency Clebsch SRG(16,5,0,2)");
        output.WriteLine("    classes (the amorphic S3 gap) on NON-elementary-abelian 2-groups.");
        output.WriteLine($"    {"group",-10} {"elemAb",6} {"#amorph",8} {"rank",5} {"prim",5} {"srg",10} {"recov",6} {"WLdep",6} {"sepB",5}  verdict");

        var groups = new[]
        {
            MakeGroup("Z2^4", 2, 2, 2, 2),      // elementary abelian — the affine anchor
            MakeGroup("Z4xZ2^2", 4, 2, 2),      // non-elementary-abelian
            MakeGroup("Z4^2", 4, 4),            // non-elementary-abelian
            MakeGroup("Z8xZ2", 8, 2),           // non-elementary-abelian
        };

        int witnesses = 0, primitiveTested = 0, nonElemFound = 0;
        foreach (var g in groups)
        {
            bool elemAb = g.M.All(m => m == 2);
            var parts = FindAmorphicPartitions(g, 3, 5, 200);
            if (parts.Count == 0)
            {
                output.WriteLine($"    {g.Name,-10} {(elemAb ? "y" : "n"),6} {0,8}  — no rank-4 equal-valency amorphic partition exists on this group");
                continue;
            }
            // measure recovery on the first partition (all are isomorphic-flavoured; report one)
            var s = BuildScheme(CayleyTable(g, parts[0]), g.V);
            if (s is null || !FullyCoherent(s)) { output.WriteLine($"    {g.Name,-10}  built partition is not a coherent scheme (unexpected)"); continue; }
            bool prim = !HasProperBlock(s);
            var pp = PdsParams(g, parts[0][0])!.Value;
            string srg = SrgType(16, pp.k, pp.lam, pp.mu);
            bool recov = Recovers(s);
            int sepBound = (int)Math.Ceiling(Math.Log2(g.V)) + 2;
            int wl = WLDepth(s, sepBound + 10);
            if (!elemAb) nonElemFound++;

            string verdict;
            if (!prim) verdict = "imprimitive (→ hImprim, not G2-B)";
            else
            {
                primitiveTested++;
                bool separates = wl <= sepBound;
                if (separates) verdict = elemAb ? "RECOVERS (affine anchor, no witness)" : "RECOVERS (non-elem-ab amorphic, no witness)";
                else { verdict = "*** G2-B CANDIDATE (primitive amorphic, non-separating) ***"; witnesses++; }
            }
            output.WriteLine($"    {g.Name,-10} {(elemAb ? "y" : "n"),6} {parts.Count,8} {s.Rank,5} {(prim ? "y" : "n"),5} {srg,10} {(recov ? "y" : "n"),6} {wl,6} {sepBound,5}  {verdict}");
        }

        output.WriteLine($"── primitive amorphic schemes tested: {primitiveTested};  non-elem-abelian found: {nonElemFound};  G2-B witnesses: {witnesses} ──");
        output.WriteLine("    A primitive amorphic non-separating scheme = a seal counterexample (statement change).");
        output.WriteLine("    If the non-elementary-abelian groups yield NO amorphic partition, the rank-4 amorphic NLS");
        output.WriteLine("    residue genuinely starts at order ≥ 64 (the explicit Davis–Xiang construction is then next).");
        Assert.Equal(0, witnesses);
    }
}
