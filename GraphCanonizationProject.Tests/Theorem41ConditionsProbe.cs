using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Xunit;
using Xunit.Abstractions;

// ─────────────────────────────────────────────────────────────────────────────
// Theorem-4.1 HYPOTHESES probe — the Stage-3 gate for the general-CC separability
// build (docs/chain-descent-general-cc-separability.md §5 Stage 3.2, added 2026-06-12).
//
// CONTEXT.  The live build closes G2-B via Ponomarenko arXiv:2006.13592 Theorem 4.1
// (docs/papers/p4paper-arxiv-2006.13592.txt, line ~552): a coherent configuration X
// with a point µ satisfying
//   (i)  every Δ ⊆ Ω with |Δ| ≤ 4 is DOMINATED: ∃λ, Δ ← λ, where α ← λ means
//        c^{r(µ,λ)}_{r(µ,α), r(α,λ)} = 1                        (paper (9)/(11), §2.6)
//   (ii) every triple (α,β,γ) has an m-EXTENSION of its couple Qµ(α,β,γ) for some
//        m ∈ S with µm ≠ ∅: a triangle (x̄,ȳ,z̄) with x̄∈m*x, ȳ∈m*y, z̄∈m*z and
//        x̄*ȳ ∩ x*y = {r},  ȳ*z̄ ∩ y*z = {s},  z̄*x̄ ∩ z*x = {t}   (paper §3, (16)/(17))
// is SEPARABLE.  Route β proves the residue's ONE-POINT EXTENSION X_α separable via
// these conditions, then Lemma 2.6 ⟹ 2-separability of X.  All seven prior
// falsifiers tested the CONCLUSION (separates at bounded base); none tested these
// PREMISES.  This probe tests them, on the exact predicted-worst-case residue:
//
//   • POSITIVE CONTROL — cycle distance schemes C_n with 3ck(k−1) < n: the paper's
//     §5 (Lemmas 5.2/5.3) PROVES (i)+(ii) hold there, so the checker must say PASS
//     (this validates the checker's faithfulness; asserted).
//   • THE RESIDUE — the rank-4 amorphic-NLS Clebsch schemes on Z4^2 (the primitive
//     G2-B bullseye, PdsAmorphicSchemeProbe) and Z2^4 (the affine anchor):
//       X itself        — expected to FAIL (dense; §3.6's reasoning),
//       X_α (one-point extension, coherent closure with α individualized) — the
//                         DECISIVE Route-β check,
//       X0 = X_α \ {α}  — the paper's actual verification object (Lemma 2.5).
//
// VERDICT LOGIC.  Route β viable ⟺ ∃µ with (i) ∧ (ii) on X_α (equiv. X0).  Failure
// on every µ of the extension ⟹ Thm 4.1's sufficient condition does not reach the
// residue at m=1 and the build must escalate (2-extension / Route α) or reroute —
// better learned here than mid-Stage-3.  Residue outcomes are REPORTED, not
// asserted (either answer is a finding); only the control is asserted.
//
// Self-contained by probe convention (group/PDS/scheme code follows
// PdsAmorphicSchemeProbe).  No production code is touched.
// ─────────────────────────────────────────────────────────────────────────────
public class Theorem41ConditionsProbe(ITestOutputHelper output)
{
    // ── General coherent configuration (multi-fiber OK): stable pair colouring +
    //    fully-verified intersection numbers.  Rel values are dense 0..Rank-1 with
    //    NO assumption that the diagonal is class 0 (a general CC has several
    //    reflexive classes = fibers). ─────────────────────────────────────────────
    sealed class CC
    {
        public required int N;
        public required int Rank;
        public required int[,] Rel;
        public required byte[,,] C;       // C[t,a,b] = c^t_{a,b}  (counts ≤ N ≤ 255)
        public required int[] Trans;      // transpose class
        public required List<int>[,] Prod; // complex product: Prod[a,b] = {w : C[w,a,b] ≠ 0}
    }

    // Build + FULLY VERIFY a CC from a pair-class matrix (dense labels assumed).
    // Verifies: transpose well-defined; intersection numbers constant on every class
    // (per-pair check at the pair's nonzero cells + the Σ_{a,b} C[t,a,b] = N identity).
    static CC BuildCC(int n, int[,] rel)
    {
        int rank = 0;
        for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) rank = Math.Max(rank, rel[u, v] + 1);

        var trans = new int[rank]; for (int t = 0; t < rank; t++) trans[t] = -1;
        var c = new byte[rank, rank, rank];
        var haveRep = new bool[rank];
        for (int u = 0; u < n; u++)
            for (int v = 0; v < n; v++)
            {
                int t = rel[u, v];
                if (trans[t] < 0) trans[t] = rel[v, u];
                else Assert.Equal(trans[t], rel[v, u]);            // transpose well-defined
                if (haveRep[t]) continue;
                haveRep[t] = true;
                for (int w = 0; w < n; w++) c[t, rel[u, w], rel[w, v]]++;
            }

        // constancy: every pair's local counts match the representative's.
        var local = new int[rank * rank];
        var touched = new List<int>(n);
        for (int u = 0; u < n; u++)
            for (int v = 0; v < n; v++)
            {
                int t = rel[u, v];
                touched.Clear();
                for (int w = 0; w < n; w++)
                {
                    int idx = rel[u, w] * rank + rel[w, v];
                    if (local[idx] == 0) touched.Add(idx);
                    local[idx]++;
                }
                foreach (int idx in touched)
                {
                    Assert.Equal(c[t, idx / rank, idx % rank], (byte)local[idx]); // counts match
                    local[idx] = 0;
                }
                // touched cells cover all n intermediates and matched C exactly; since
                // Σ_{a,b} C[t,a,b] = n as well, the zero cells match too.
            }

        var prod = new List<int>[rank, rank];
        for (int a = 0; a < rank; a++) for (int b = 0; b < rank; b++) prod[a, b] = new List<int>();
        for (int w = 0; w < rank; w++)
            for (int a = 0; a < rank; a++)
                for (int b = 0; b < rank; b++)
                    if (c[w, a, b] != 0) prod[a, b].Add(w);

        return new CC { N = n, Rank = rank, Rel = rel, C = c, Trans = trans, Prod = prod };
    }

    // ── Coherent closure (WL on ordered pairs) of an initial pair colouring; the
    //    one-point extension X_T is the closure of (Rel, T-individualized). ────────
    static int[,] CoherentClosure(int n, Func<int, int, long> init)
    {
        var colour = new int[n, n];
        var map0 = new Dictionary<long, int>();
        for (int u = 0; u < n; u++)
            for (int v = 0; v < n; v++)
            {
                long k = init(u, v);
                if (!map0.TryGetValue(k, out int cc)) { cc = map0.Count; map0[k] = cc; }
                colour[u, v] = cc;
            }
        int classes = map0.Count;
        while (true)
        {
            var sigMap = new Dictionary<string, int>();
            var nc = new int[n, n];
            var sb = new StringBuilder();
            var arr = new (int a, int b)[n];
            for (int u = 0; u < n; u++)
                for (int v = 0; v < n; v++)
                {
                    for (int w = 0; w < n; w++) arr[w] = (colour[u, w], colour[w, v]);
                    Array.Sort(arr);
                    sb.Clear(); sb.Append(colour[u, v]);
                    foreach (var (a, b) in arr) { sb.Append('|'); sb.Append(a); sb.Append(','); sb.Append(b); }
                    string s = sb.ToString();
                    if (!sigMap.TryGetValue(s, out int cc)) { cc = sigMap.Count; sigMap[s] = cc; }
                    nc[u, v] = cc;
                }
            if (sigMap.Count == classes) return colour;  // stable (split-only ⟹ same count = same partition)
            colour = nc; classes = sigMap.Count;
        }
    }

    static CC OnePointExtension(CC x, int alpha) =>
        BuildCC(x.N, CoherentClosure(x.N, (u, v) =>
            (long)x.Rel[u, v] * 4 + (u == alpha ? 1 : 0) + (v == alpha ? 2 : 0)));

    // Lemma 2.5: delete the singleton fiber α; the restriction is a CC, separable
    // iff X_α is.  (Re-densify labels on the smaller point set.)
    static CC DeletePoint(CC x, int alpha)
    {
        int n = x.N - 1;
        var pts = Enumerable.Range(0, x.N).Where(p => p != alpha).ToArray();
        var map = new Dictionary<int, int>();
        var rel = new int[n, n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
            {
                int t = x.Rel[pts[i], pts[j]];
                if (!map.TryGetValue(t, out int cc)) { cc = map.Count; map[t] = cc; }
                rel[i, j] = cc;
            }
        return BuildCC(n, rel);
    }

    // ── Condition (i): every Δ ⊆ Ω, |Δ| ≤ 4 is dominated (∃λ ∀δ∈Δ: δ ← λ), w.r.t. µ.
    //    δ ← λ  ⟺  C[ r(µ,λ), r(µ,δ), r(δ,λ) ] = 1.  Checking |Δ| = 4 suffices
    //    (a dominator of a superset dominates every subset); n ≥ 5 throughout. ─────
    static bool Dominates(CC x, int mu, int delta, int lam) =>
        x.C[x.Rel[mu, lam], x.Rel[mu, delta], x.Rel[delta, lam]] == 1;

    static (bool ok, int[]? badDelta) CondI(CC x, int mu)
    {
        int n = x.N;
        var d = new int[4];
        for (d[0] = 0; d[0] < n; d[0]++)
            for (d[1] = d[0] + 1; d[1] < n; d[1]++)
                for (d[2] = d[1] + 1; d[2] < n; d[2]++)
                    for (d[3] = d[2] + 1; d[3] < n; d[3]++)
                    {
                        bool found = false;
                        for (int lam = 0; lam < n && !found; lam++)
                            found = Dominates(x, mu, d[0], lam) && Dominates(x, mu, d[1], lam)
                                 && Dominates(x, mu, d[2], lam) && Dominates(x, mu, d[3], lam);
                        if (!found) return (false, (int[])d.Clone());
                    }
        return (true, null);
    }

    // ── Condition (ii): ∀(α,β,γ) ∃m (µm ≠ ∅) with an m-extension of Qµ(α,β,γ).
    //    Fast path (paper Lemma 5.3's witness shape): the geometric triangle
    //    (r(λ,α), r(λ,β), r(λ,γ)) with m = r(µ,λ), scanned over λ.  Fallback: the
    //    full abstract search over m ∈ {row-µ classes} and (x̄,ȳ,z̄) ∈ candidate
    //    products — exhaustive, so a FAIL verdict is genuine. ──────────────────────
    sealed class CondIIResult
    {
        public long Geo, Abstract, Fail;
        public (int a, int b, int g)? FirstFail;
        public bool Pass => Fail == 0;
    }

    static bool UniqueIntersection(List<int> a, bool[] memB, int r)
    {
        // a ∩ B = {r}?  (memB is B's membership array)
        bool hasR = false;
        foreach (int w in a)
        {
            if (!memB[w]) continue;
            if (w != r) return false;
            hasR = true;
        }
        return hasR;
    }

    static CondIIResult CondII(CC x, int mu, int failCap = 25)
    {
        int n = x.N, rank = x.Rank;
        var res = new CondIIResult();
        var rowClasses = new List<int>();
        { var seen = new bool[rank]; for (int v = 0; v < n; v++) if (!seen[x.Rel[mu, v]]) { seen[x.Rel[mu, v]] = true; rowClasses.Add(x.Rel[mu, v]); } }

        var memXY = new bool[rank]; var memYZ = new bool[rank]; var memZX = new bool[rank];
        for (int al = 0; al < n; al++)
            for (int be = 0; be < n; be++)
                for (int ga = 0; ga < n; ga++)
                {
                    int xr = x.Rel[mu, al], yr = x.Rel[mu, be], zr = x.Rel[mu, ga];
                    int r = x.Rel[al, be], s = x.Rel[be, ga], t = x.Rel[ga, al];
                    var pXY = x.Prod[x.Trans[xr], yr]; foreach (int w in pXY) memXY[w] = true;
                    var pYZ = x.Prod[x.Trans[yr], zr]; foreach (int w in pYZ) memYZ[w] = true;
                    var pZX = x.Prod[x.Trans[zr], xr]; foreach (int w in pZX) memZX[w] = true;

                    bool ok = false;
                    // geometric λ-scan
                    for (int lam = 0; lam < n && !ok; lam++)
                    {
                        int xb = x.Rel[lam, al], yb = x.Rel[lam, be], zb = x.Rel[lam, ga];
                        ok = UniqueIntersection(x.Prod[x.Trans[xb], yb], memXY, r)
                          && UniqueIntersection(x.Prod[x.Trans[yb], zb], memYZ, s)
                          && UniqueIntersection(x.Prod[x.Trans[zb], xb], memZX, t);
                    }
                    if (ok) res.Geo++;
                    else
                    {
                        // exhaustive abstract search
                        foreach (int m in rowClasses)
                        {
                            int ms = x.Trans[m];
                            var cx = x.Prod[ms, xr]; var cy = x.Prod[ms, yr]; var cz = x.Prod[ms, zr];
                            foreach (int xb in cx)
                            {
                                foreach (int yb in cy)
                                {
                                    if (!UniqueIntersection(x.Prod[x.Trans[xb], yb], memXY, r)) continue;
                                    foreach (int zb in cz)
                                        if (UniqueIntersection(x.Prod[x.Trans[yb], zb], memYZ, s)
                                         && UniqueIntersection(x.Prod[x.Trans[zb], xb], memZX, t)) { ok = true; break; }
                                    if (ok) break;
                                }
                                if (ok) break;
                            }
                            if (ok) break;
                        }
                        if (ok) res.Abstract++;
                        else { res.Fail++; res.FirstFail ??= (al, be, ga); }
                    }

                    foreach (int w in pXY) memXY[w] = false;
                    foreach (int w in pYZ) memYZ[w] = false;
                    foreach (int w in pZX) memZX[w] = false;
                    if (res.Fail >= failCap) return res;   // enough to settle this µ
                }
        return res;
    }

    // ── Homogeneous-scheme diagnostics (context lines only) ───────────────────────
    static (int k, int c, bool sparse31, bool param51) HomogeneousParams(CC x)
    {
        int n = x.N;
        var val = new int[x.Rank];
        for (int v = 0; v < n; v++) val[x.Rel[0, v]]++;
        int diag = x.Rel[0, 0];
        int k = 0; for (int a = 0; a < x.Rank; a++) if (a != diag) k = Math.Max(k, val[a]);
        int c = 0;
        for (int r = 0; r < x.Rank; r++)
        {
            if (r == diag) continue;
            int cr = 0; for (int s = 0; s < x.Rank; s++) cr += x.C[r, s, x.Trans[s]];
            c = Math.Max(c, cr);
        }
        return (k, c, 2 * c * (k - 1) < n, 3 * c * k * (k - 1) < n);
    }

    // ── Cycle distance scheme C_n (P-polynomial; the §5 positive-control family) ──
    static CC CycleScheme(int n)
    {
        var rel = new int[n, n];
        for (int u = 0; u < n; u++)
            for (int v = 0; v < n; v++)
            { int d = Math.Abs(u - v); rel[u, v] = Math.Min(d, n - d); }
        return BuildCC(n, rel);
    }

    // ── Clebsch amorphic-NLS scheme construction (as in PdsAmorphicSchemeProbe) ───
    sealed class Grp
    {
        public required int V; public required int[] M; public required int[] Stride; public required string Name;
    }
    static Grp MakeGroup(string name, params int[] moduli)
    {
        int v = 1; var stride = new int[moduli.Length];
        for (int i = 0; i < moduli.Length; i++) { stride[i] = v; v *= moduli[i]; }
        return new Grp { V = v, M = moduli, Stride = stride, Name = name };
    }
    static int Digit(Grp g, int x, int i) => (x / g.Stride[i]) % g.M[i];
    static int Neg(Grp g, int x)
    {
        int r = 0;
        for (int i = 0; i < g.M.Length; i++) r += ((g.M[i] - Digit(g, x, i)) % g.M[i]) * g.Stride[i];
        return r;
    }
    static int Sub(Grp g, int x, int y)
    {
        int r = 0;
        for (int i = 0; i < g.M.Length; i++) r += ((Digit(g, x, i) - Digit(g, y, i) + g.M[i]) % g.M[i]) * g.Stride[i];
        return r;
    }

    static (int k, int lam, int mu)? PdsParams(Grp g, int[] d)
    {
        var inD = new bool[g.V];
        foreach (int e in d) { if (e == 0) return null; inD[e] = true; }
        foreach (int e in d) if (!inD[Neg(g, e)]) return null;
        var cnt = new int[g.V];
        foreach (int a in d) foreach (int b in d) cnt[Sub(g, a, b)]++;
        int lam = -1, mu = -1;
        for (int t = 1; t < g.V; t++)
        {
            if (inD[t]) { if (lam < 0) lam = cnt[t]; else if (cnt[t] != lam) return null; }
            else { if (mu < 0) mu = cnt[t]; else if (cnt[t] != mu) return null; }
        }
        return (lam < 0 || mu < 0) ? null : (d.Length, lam, mu);
    }

    static IEnumerable<int[]> Choose(int n, int k)
    {
        if (k < 0 || k > n) yield break;
        if (k == 0) { yield return Array.Empty<int>(); yield break; }
        var idx = Enumerable.Range(0, k).ToArray();
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

    static List<int[]> SymmetricSubsets(Grp g, int size)
    {
        var involutions = new List<int>(); var pairs = new List<(int, int)>(); var seen = new bool[g.V];
        for (int x = 1; x < g.V; x++)
        {
            if (seen[x]) continue;
            int nx = Neg(g, x);
            if (nx == x) involutions.Add(x); else { pairs.Add((x, nx)); seen[nx] = true; }
            seen[x] = true;
        }
        var result = new List<int[]>();
        for (int i = size % 2; i <= Math.Min(size, involutions.Count); i += 2)
        {
            int p = (size - i) / 2;
            if (p < 0 || p > pairs.Count) continue;
            foreach (var invSel in Choose(involutions.Count, i))
                foreach (var pairSel in Choose(pairs.Count, p))
                {
                    var d = new List<int>();
                    foreach (int ix in invSel) d.Add(involutions[ix]);
                    foreach (int ix in pairSel) { d.Add(pairs[ix].Item1); d.Add(pairs[ix].Item2); }
                    result.Add(d.ToArray());
                }
        }
        return result;
    }

    // first rank-4 equal-valency amorphic partition (3 × SRG(16,5,0,2)) on g, as a CC.
    static CC? ClebschScheme(Grp g)
    {
        var pds = new List<int[]>(); var keys = new List<long>();
        (int, int, int) target = (5, 0, 2);
        foreach (var d in SymmetricSubsets(g, 5))
        {
            var pp = PdsParams(g, d);
            if (pp is null || pp.Value != target) continue;
            long mask = 0; foreach (int x in d) mask |= 1L << x;
            pds.Add(d); keys.Add(mask);
        }
        long full = 0; for (int x = 1; x < g.V; x++) full |= 1L << x;
        for (int i = 0; i < pds.Count; i++)
            for (int j = i + 1; j < pds.Count; j++)
            {
                if ((keys[i] & keys[j]) != 0) continue;
                for (int k = j + 1; k < pds.Count; k++)
                {
                    if (((keys[i] | keys[j]) & keys[k]) != 0 || (keys[i] | keys[j] | keys[k]) != full) continue;
                    var classOf = new int[g.V];
                    foreach (int d in pds[i]) classOf[d] = 1;
                    foreach (int d in pds[j]) classOf[d] = 2;
                    foreach (int d in pds[k]) classOf[d] = 3;
                    var rel = new int[g.V, g.V];
                    for (int u = 0; u < g.V; u++) for (int v = 0; v < g.V; v++) rel[u, v] = (u == v) ? 0 : classOf[Sub(g, u, v)];
                    return BuildCC(g.V, rel);
                }
            }
        return null;
    }

    // PARAMETRIC generalisation of ClebschScheme: the first coherent rank-4 amorphic
    // 3-class scheme on g with EQUAL valency (V−1)/3 — auto-detecting the SRG params
    // (any λ,μ), not the hard-coded (5,0,2).  Builds the family the δ′ rainbow lemma
    // wants to bite on beyond order 16 (Z5^2 = 25, …).  Returns null if no coherent
    // equal-valency 3-class amorphic partition exists.
    static CC? AmorphicNLS3Scheme(Grp g)
    {
        int V = g.V;
        if (V < 4 || (V - 1) % 3 != 0) return null;
        int k = (V - 1) / 3;
        var pds = new List<int[]>(); var keys = new List<long>();
        foreach (var d in SymmetricSubsets(g, k))
        {
            if (PdsParams(g, d) is null) continue;
            long mask = 0; foreach (int x in d) mask |= 1L << x;
            pds.Add(d); keys.Add(mask);
        }
        long full = 0; for (int x = 1; x < V; x++) full |= 1L << x;
        for (int i = 0; i < pds.Count; i++)
            for (int j = i + 1; j < pds.Count; j++)
            {
                if ((keys[i] & keys[j]) != 0) continue;
                for (int kk = j + 1; kk < pds.Count; kk++)
                {
                    if (((keys[i] | keys[j]) & keys[kk]) != 0 || (keys[i] | keys[j] | keys[kk]) != full) continue;
                    var classOf = new int[V];
                    foreach (int d in pds[i]) classOf[d] = 1;
                    foreach (int d in pds[j]) classOf[d] = 2;
                    foreach (int d in pds[kk]) classOf[d] = 3;
                    var rel = new int[V, V];
                    for (int u = 0; u < V; u++) for (int v = 0; v < V; v++) rel[u, v] = (u == v) ? 0 : classOf[Sub(g, u, v)];
                    try { return BuildCC(V, rel); } catch { /* not coherent — keep searching */ }
                }
            }
        return null;
    }

    static bool PrimitiveScheme(CC s)
    {
        // connectivity of every non-diagonal class (homogeneous symmetric case)
        int diag = s.Rel[0, 0];
        for (int k = 0; k < s.Rank; k++)
        {
            if (k == diag) continue;
            var seen = new bool[s.N]; var st = new Stack<int>(); st.Push(0); seen[0] = true; int c = 1;
            while (st.Count > 0) { int x = st.Pop(); for (int y = 0; y < s.N; y++) if (!seen[y] && s.Rel[x, y] == k) { seen[y] = true; c++; st.Push(y); } }
            if (c != s.N) return false;
        }
        return true;
    }

    // run both conditions for every µ; print a table; return whether ∃µ passing both.
    bool ReportConditionsAllMu(string label, CC x)
    {
        output.WriteLine($"    {label}:  n={x.N}, rank={x.Rank}");
        output.WriteLine($"      {"µ",3} {"cond(i)",8} {"cond(ii)",9} {"geo",6} {"abs",5} {"fail",5}  first failure");
        bool anyMu = false;
        for (int mu = 0; mu < x.N; mu++)
        {
            var (okI, bad) = CondI(x, mu);
            var r2 = CondII(x, mu);
            bool both = okI && r2.Pass;
            anyMu |= both;
            string firsts = "";
            if (!okI) firsts += $"(i): Δ={{{string.Join(",", bad!)}}} undominated  ";
            if (!r2.Pass) firsts += $"(ii): (α,β,γ)=({r2.FirstFail!.Value.a},{r2.FirstFail.Value.b},{r2.FirstFail.Value.g}) no m-extension";
            output.WriteLine($"      {mu,3} {(okI ? "PASS" : "fail"),8} {(r2.Pass ? "PASS" : "fail"),9} {r2.Geo,6} {r2.Abstract,5} {r2.Fail,5}{(r2.Fail >= 25 ? "+" : " ")} {firsts}");
        }
        output.WriteLine($"      ⟹ {label}: Thm 4.1 conditions {(anyMu ? "HOLD for some µ — the sufficient condition APPLIES" : "FAIL for every µ — the sufficient condition does NOT apply")}");
        return anyMu;
    }

    // ── POSITIVE CONTROL: the checker must say PASS where the paper PROVES it ─────
    [Fact]
    public void Probe_Thm41Conditions_PositiveControl_Cycles()
    {
        output.WriteLine("── Thm 4.1 conditions probe — positive control: cycle distance schemes ──");
        output.WriteLine("   paper §5 (Lemmas 5.2/5.3): 3ck(k−1) < n ⟹ conditions (i)+(ii) hold (any µ).");
        foreach (int n in new[] { 17, 25 })
        {
            var x = CycleScheme(n);
            var (k, c, sparse, p51) = HomogeneousParams(x);
            output.WriteLine($"   C_{n}: rank={x.Rank} k={k} c={c}  2c(k−1)<n:{(sparse ? "y" : "n")}  3ck(k−1)<n:{(p51 ? "y" : "n")}");
            var (okI, bad) = CondI(x, 0);
            var r2 = CondII(x, 0);
            output.WriteLine($"      µ=0: cond(i) {(okI ? "PASS" : $"FAIL Δ={{{string.Join(",", bad ?? Array.Empty<int>())}}}")}, " +
                             $"cond(ii) {(r2.Pass ? "PASS" : "FAIL")} (geo {r2.Geo}, abs {r2.Abstract}, fail {r2.Fail})");
            if (p51)
            {
                Assert.True(okI, $"C_{n}: condition (i) must hold under 3ck(k−1)<n (Lemma 5.2)");
                Assert.True(r2.Pass, $"C_{n}: condition (ii) must hold under 3ck(k−1)<n (Lemma 5.3)");
            }
        }
        output.WriteLine("   control PASS — the checker is faithful where the paper proves the conditions.");
    }

    // ── THE PROBE: the rank-4 amorphic-NLS Clebsch residue, X / X_α / X0 ──────────
    [Fact]
    public void Probe_Thm41Conditions_ClebschResidue()
    {
        output.WriteLine("── Thm 4.1 conditions probe — the G2-B residue (rank-4 amorphic-NLS Clebsch) ──");
        output.WriteLine("   Route β stands on: Thm 4.1's (i)+(ii) hold on the ONE-POINT EXTENSION of the residue.");
        output.WriteLine("   (X itself is expected to fail — that is why the build needs the extension; §3.6.)");

        var verdicts = new List<(string grp, bool onX, bool onXa, bool onX0)>();
        foreach (var g in new[] { MakeGroup("Z4^2", 4, 4), MakeGroup("Z2^4", 2, 2, 2, 2) })
        {
            var x = ClebschScheme(g);
            Assert.NotNull(x);
            bool prim = PrimitiveScheme(x!);
            var (k, c, sparse, p51) = HomogeneousParams(x!);
            output.WriteLine($"");
            output.WriteLine($"   {g.Name}: rank={x!.Rank} primitive={(prim ? "y" : "n")} k={k} c={c}  " +
                             $"2c(k−1)<n:{(sparse ? "y" : "n")}  3ck(k−1)<n:{(p51 ? "y" : "n")}   (dense — both sparse routes closed, as recorded)");

            // X itself (vertex-transitive translation scheme ⟹ µ=0 represents all µ)
            var (okI, badI) = CondI(x, 0);
            var r2 = CondII(x, 0);
            bool onX = okI && r2.Pass;
            output.WriteLine($"    X itself (µ=0): cond(i) {(okI ? "PASS" : $"fail, Δ={{{string.Join(",", badI ?? Array.Empty<int>())}}}")}; " +
                             $"cond(ii) {(r2.Pass ? "PASS" : "fail")} (geo {r2.Geo}, abs {r2.Abstract}, fail {r2.Fail}{(r2.Fail >= 25 ? "+ (capped)" : "")})");

            // the one-point extension (vertex-transitive ⟹ wlog α = 0)
            var xa = OnePointExtension(x, 0);
            bool onXa = ReportConditionsAllMu($"X_α (α=0, coherent closure)", xa);

            // the paper's verification object (Lemma 2.5): X0 = X_α minus the singleton fiber
            var x0 = DeletePoint(xa, 0);
            bool onX0 = ReportConditionsAllMu($"X0 = X_α \\ {{α}} (Lemma 2.5 object)", x0);

            verdicts.Add((g.Name, onX, onXa, onX0));
        }

        output.WriteLine("");
        output.WriteLine("── VERDICT (Stage-3 gate, chain-descent-general-cc-separability.md §5 Stage 3.2) ──");
        foreach (var v in verdicts)
            output.WriteLine($"   {v.grp,-6}: X {(v.onX ? "PASS" : "fail")} | X_α {(v.onXa ? "PASS" : "FAIL")} | X0 {(v.onX0 ? "PASS" : "FAIL")}" +
                             $"  ⟹ Route β (Thm 4.1 on the one-point extension) {(v.onXa || v.onX0 ? "VIABLE on this residue" : "BLOCKED at m=1 on this residue — escalate (2-extension / Route α) or reroute")}");
        output.WriteLine("   (Outcomes are findings, not assertions: a FAIL here means the m=1 sufficient");
        output.WriteLine("    condition does not reach the residue — discovered for ~a day's probe instead of mid-Stage-3.)");
    }

    // ─────────────────────────────────────────────────────────────────────────────
    // STAGE-2.1 DIRECTION CHECK (build doc §5 Stage 1.2(c)/2.1 ⚠️, added 2026-06-12).
    //
    // The transport's load-bearing model bridge: the seal's twin lives in the 1-WL
    // vertex refinement (`warmRefine (schemeAdj S) … (individualizedColouring n T)`,
    // the SeparatesAtBoundedBase keying), while the substrate's objects are the
    // point extension X_T's FIBERS (pair-coherent closure, 2-WL-flavoured — never
    // coarser than 1-WL cells).  Two questions, checked on the exact residue:
    //
    //   (a) cells = fibers?   Are the 1-WL cells from T exactly X_T's fibers?
    //       (fibers ⊆ cells always; the content is the converse.)
    //   (b) twin ⟹ alg-iso?  For every same-1-WL-cell pair (u,u') off T, are the
    //       extensions X_{T∪{u}} and X_{T∪{u'}} WL-on-pairs-EQUIVALENT (canonical
    //       stable-colouring fingerprints equal)?  This is Stage 2.1's actual step
    //       — equivalence here is exactly what the Lean lemma must produce.
    //
    // Control: C_17 with T={0} (orbits = distance classes = cells = fibers; the ±d
    // reflection twins must give equivalent extensions) — asserted.  Residue
    // outcomes are findings, reported either way.
    // ─────────────────────────────────────────────────────────────────────────────

    // 1-WL vertex refinement mirroring the Lean model: edge labels = relation
    // indices (schemeAdj), trivial P, initial colours = individualizedColouring.
    static int[] WarmRefineCells(CC x, int[] t)
    {
        int n = x.N;
        var col = new int[n];
        for (int i = 0; i < t.Length; i++) col[t[i]] = i + 1;
        int classes = col.Distinct().Count();
        var sb = new StringBuilder();
        while (true)
        {
            var sigMap = new Dictionary<string, int>();
            var nc = new int[n];
            var arr = new (int cu, int rel)[n - 1];
            for (int v = 0; v < n; v++)
            {
                int j = 0;
                for (int u = 0; u < n; u++) if (u != v) arr[j++] = (col[u], x.Rel[v, u]);
                Array.Sort(arr);
                sb.Clear(); sb.Append(col[v]);
                foreach (var (cu, rel) in arr) { sb.Append('|'); sb.Append(cu); sb.Append(','); sb.Append(rel); }
                string s = sb.ToString();
                if (!sigMap.TryGetValue(s, out int cc)) { cc = sigMap.Count; sigMap[s] = cc; }
                nc[v] = cc;
            }
            if (sigMap.Count == classes) return col;   // split-only ⟹ same count = stable
            col = nc; classes = sigMap.Count;
        }
    }

    // Canonical WL-on-pairs: colour ids renamed each round by sorted signature
    // order, so the stable colouring's fingerprint is comparable ACROSS runs
    // (two initial configurations get equal fingerprints iff pair-WL cannot
    // distinguish them).  Returns the stable colour matrix + the fingerprint.
    static (int[,] colour, string fingerprint) CanonicalPairWL(int n, Func<int, int, long> init)
    {
        var colour = new int[n, n];
        {
            var keys = new SortedSet<long>();
            for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) keys.Add(init(u, v));
            var map0 = new Dictionary<long, int>(); int id = 0;
            foreach (long k in keys) map0[k] = id++;
            for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) colour[u, v] = map0[init(u, v)];
        }
        int classes = 0; { var s = new HashSet<int>(); foreach (int c in colour) s.Add(c); classes = s.Count; }
        var sb = new StringBuilder();
        var arr = new (int a, int b)[n];
        while (true)
        {
            var sigs = new string[n, n];
            var distinct = new SortedSet<string>(StringComparer.Ordinal);
            for (int u = 0; u < n; u++)
                for (int v = 0; v < n; v++)
                {
                    for (int w = 0; w < n; w++) arr[w] = (colour[u, w], colour[w, v]);
                    Array.Sort(arr);
                    sb.Clear(); sb.Append(colour[u, v]);
                    foreach (var (a, b) in arr) { sb.Append('|'); sb.Append(a); sb.Append(','); sb.Append(b); }
                    sigs[u, v] = sb.ToString();
                    distinct.Add(sigs[u, v]);
                }
            if (distinct.Count == classes)
            {
                // stable: fingerprint = sorted final signatures with multiplicities
                var counts = new SortedDictionary<string, int>(StringComparer.Ordinal);
                foreach (string s in sigs) counts[s] = counts.TryGetValue(s, out int k) ? k + 1 : 1;
                var fp = new StringBuilder();
                foreach (var kv in counts) { fp.Append(kv.Value); fp.Append('×'); fp.Append(kv.Key); fp.Append('\n'); }
                return (colour, fp.ToString());
            }
            var rename = new Dictionary<string, int>(StringComparer.Ordinal); int id = 0;
            foreach (string s in distinct) rename[s] = id++;
            for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) colour[u, v] = rename[sigs[u, v]];
            classes = distinct.Count;
        }
    }

    static long ExtInit(CC x, int[] pts, int u, int v)
    {
        long pu = 0, pv = 0;
        for (int i = 0; i < pts.Length; i++) { if (pts[i] == u) pu = i + 1; if (pts[i] == v) pv = i + 1; }
        return ((long)x.Rel[u, v] * 64 + pu) * 64 + pv;
    }

    // fibers of X_T: the diagonal classes of the pair-coherent closure
    static int[] FibersOf(CC x, int[] t)
    {
        var (colour, _) = CanonicalPairWL(x.N, (u, v) => ExtInit(x, t, u, v));
        var diag = new int[x.N];
        for (int v = 0; v < x.N; v++) diag[v] = colour[v, v];
        return diag;
    }

    static bool SamePartition(int[] a, int[] b)
    {
        for (int u = 0; u < a.Length; u++)
            for (int v = u + 1; v < a.Length; v++)
                if ((a[u] == a[v]) != (b[u] == b[v])) return false;
        return true;
    }

    static int NumCells(int[] a) => a.Distinct().Count();

    // (a) + (b) for one scheme and one base T; returns (cellsEqFibers, twinPairs, twinMismatches)
    (bool eq, int pairs, int mismatches) DirectionCheck(string label, CC x, int[] t)
    {
        var cells = WarmRefineCells(x, t);
        var fibers = FibersOf(x, t);
        bool eq = SamePartition(cells, fibers);
        string witness = "";
        if (!eq)
        {
            for (int u = 0; u < x.N && witness == ""; u++)
                for (int v = u + 1; v < x.N; v++)
                    if (cells[u] == cells[v] && fibers[u] != fibers[v]) { witness = $"  witness: cell-mates ({u},{v}) split by fibers"; break; }
        }
        output.WriteLine($"    {label} T={{{string.Join(",", t)}}}:  1-WL cells={NumCells(cells),3}  X_T fibers={NumCells(fibers),3}  " +
                         $"cells=fibers: {(eq ? "YES" : "NO")}{witness}");

        // (b) per same-cell pair off T: extension fingerprints must match
        var inT = new bool[x.N]; foreach (int p in t) inT[p] = true;
        var fp = new Dictionary<int, string>();
        int pairs = 0, mismatches = 0; string firstBad = "";
        for (int u = 0; u < x.N; u++)
            for (int v = u + 1; v < x.N; v++)
            {
                if (inT[u] || inT[v] || cells[u] != cells[v]) continue;
                foreach (int w in new[] { u, v })
                    if (!fp.ContainsKey(w))
                    {
                        var ext = t.Append(w).ToArray();
                        fp[w] = CanonicalPairWL(x.N, (a, b) => ExtInit(x, ext, a, b)).fingerprint;
                    }
                pairs++;
                if (fp[u] != fp[v]) { mismatches++; if (firstBad == "") firstBad = $"  FIRST MISMATCH: ({u},{v})"; }
            }
        output.WriteLine($"      twin⟹alg-iso: {pairs} same-cell pairs off T, extension-WL-equivalent: {pairs - mismatches}/{pairs}" +
                         $"{(mismatches > 0 ? $"  ⚠️ {mismatches} MISMATCHES{firstBad}" : "  — all twins give WL-equivalent extensions")}");
        return (eq, pairs, mismatches);
    }

    [Fact]
    public void Probe_Stage21_DirectionCheck_CellsVsFibers()
    {
        output.WriteLine("── Stage-2.1 direction check — 1-WL cells vs X_T fibers, twin ⟹ alg-iso ──");
        output.WriteLine("   (a) are warmRefine cells = point-extension fibers on the residue?");
        output.WriteLine("   (b) do same-cell twins give WL-equivalent one-point-further extensions?");
        output.WriteLine("");

        // control: C_17 — orbits = distance classes; cells, fibers, and twins all behave
        var c17 = CycleScheme(17);
        var (eqC, pairsC, misC) = DirectionCheck("C_17 (control)", c17, new[] { 0 });
        Assert.True(eqC, "C_17 control: 1-WL cells from {0} must equal X_{0} fibers");
        Assert.True(pairsC > 0 && misC == 0, "C_17 control: reflection twins must give WL-equivalent extensions");
        output.WriteLine("");

        // the residue
        var results = new List<(string grp, string t, bool eq, int pairs, int mis)>();
        foreach (var g in new[] { MakeGroup("Z4^2", 4, 4), MakeGroup("Z2^4", 2, 2, 2, 2) })
        {
            var x = ClebschScheme(g);
            Assert.NotNull(x);
            output.WriteLine($"   {g.Name} (rank-4 amorphic-NLS Clebsch, primitive={(PrimitiveScheme(x!) ? "y" : "n")}):");

            // representatives: z_i = first vertex with Rel[0,z]=i (one per non-diagonal class)
            var z = new int[4];
            for (int i = 1; i <= 3; i++) { for (int v = 1; v < x!.N; v++) if (x.Rel[0, v] == i) { z[i] = v; break; } }

            var bases = new List<int[]> { new[] { 0 } };
            for (int i = 1; i <= 3; i++) bases.Add(new[] { 0, z[i] });
            bases.Add(new[] { 0, z[1], z[2] });

            foreach (var t in bases)
            {
                var (eq, pairs, mis) = DirectionCheck(g.Name, x!, t);
                results.Add((g.Name, $"{{{string.Join(",", t)}}}", eq, pairs, mis));
            }
            output.WriteLine("");
        }

        output.WriteLine("── VERDICT (Stage 2.1 model bridge) ──");
        bool allEq = results.All(r => r.eq), allTwin = results.All(r => r.mis == 0);
        foreach (var r in results)
            output.WriteLine($"   {r.grp,-6} T={r.t,-12}: cells=fibers {(r.eq ? "YES" : "NO ")}  twins equiv {r.pairs - r.mis}/{r.pairs}");
        output.WriteLine($"   (a) cells = fibers on the residue: {(allEq ? "EVERYWHERE — the bridge is an equality; keep the warmRefine keying" : "NOT everywhere — fibers strictly finer somewhere; the twin keying caution (Stage 2.1 ⚠️) is LIVE")}");
        output.WriteLine($"   (b) twin ⟹ WL-equivalent extensions: {(allTwin ? "HOLDS on all tested pairs — Stage 2.1's statement is empirically sound as keyed" : "FAILS somewhere — re-key the seal-side twin on fibers before Lean investment")}");
    }

    // ─────────────────────────────────────────────────────────────────────────────
    // THE CATCH-UP PROBE-GATE (build doc STATUS item 5, added 2026-06-12).
    //
    // Stage 2 landed modulo ONE model statement, the catch-up `WarmTwinsAreFiberTwins
    // S T E`: same-warmRefine-cell pair (u,u') from T ⟹ same fiber of E = X_T.  The
    // direction check refuted it at arbitrary T (ℤ₄², T={0}: 4 cells vs 10 fibers)
    // and confirmed it at the few |T| ≥ 2 sets it sampled — but the assembly consumes
    // it at GROUP BASES T (`IsBase`: trivial pointwise stabilizer of Aut(X)), which
    // no probe has measured.  Two questions:
    //
    //   (a) THE GATE — does the catch-up hold at the assembly's actual bases?
    //       Compute Aut(X) exactly (backtracking), then sweep ALL subsets of sizes
    //       1..b(G): per T record base-ness, catch-up violations (same-cell pair
    //       split by fibers), 1-WL discreteness, extension completeness.  This also
    //       measures b(G) vs b(X) (the honest-accounting note: at a complete-
    //       extension base, catch-up ⟺ 1-WL discreteness — the conclusion itself).
    //   (b) THE ENGINE — does condition-(i)-style domination PROPAGATE?  The intended
    //       Lean discharge is B1–B5-shaped: δ pinned by a c=1 triangle against two
    //       determined points (`Dominates`, on the EXTENSION's classes) becomes
    //       determined.  Run that closure from T (i) on X's own classes (the landed
    //       scheme-level saAdj engine — expected to stall on the dense residue) and
    //       (ii) on E = X_T's pair-closure classes (the route's hope: the extension
    //       is where the dense scheme turns sparse-ish; Theorem41ConditionsProbe
    //       found its (i)-dominators there).  1-WL-SOUNDNESS is also measured: a
    //       B3-on-E lemma keyed on warm cells needs every E-closure-determined
    //       vertex to sit in a SINGLETON warm cell — violations refute that keying.
    //
    // Control: C₁₇ (sparse, PV-Thm-3.1 territory) — every pair is a base; catch-up,
    // discreteness, and both closures must succeed there (asserted).  Residue
    // outcomes (ℤ₄² bullseye, ℤ₂⁴ anchor) are findings, reported either way.
    // ─────────────────────────────────────────────────────────────────────────────

    // scheme automorphisms = Rel-preserving permutations, by pruned backtracking.
    static List<int[]> SchemeAut(CC x)
    {
        int n = x.N;
        var perms = new List<int[]>();
        var img = new int[n]; var used = new bool[n];
        void Rec(int v)
        {
            if (v == n) { perms.Add((int[])img.Clone()); return; }
            for (int w = 0; w < n; w++)
            {
                if (used[w] || x.Rel[v, v] != x.Rel[w, w]) continue;
                bool ok = true;
                for (int u = 0; u < v && ok; u++)
                    ok = x.Rel[u, v] == x.Rel[img[u], w] && x.Rel[v, u] == x.Rel[w, img[u]];
                if (!ok) continue;
                used[w] = true; img[v] = w;
                Rec(v + 1);
                used[w] = false;
            }
        }
        Rec(0);
        return perms;
    }

    // IsBase: no non-identity automorphism fixes T pointwise.
    static bool IsBaseSet(List<int[]> auts, int[] t)
    {
        foreach (var g in auts)
        {
            bool fixesT = true;
            foreach (int p in t) if (g[p] != p) { fixesT = false; break; }
            if (!fixesT) continue;
            for (int v = 0; v < g.Length; v++) if (g[v] != v) return false;
        }
        return true;
    }

    // fibers + the full stable pair colouring of X_T (the closure E's classes).
    static (int[] fibers, int[,] pairColour) ExtFibers(CC x, int[] t)
    {
        var (colour, _) = CanonicalPairWL(x.N, (u, v) => ExtInit(x, t, u, v));
        var diag = new int[x.N];
        for (int v = 0; v < x.N; v++) diag[v] = colour[v, v];
        return (diag, colour);
    }

    // The c=1 dominator closure (the B3/`Dominates` propagation shape): starting
    // from T determined, δ becomes determined when some determined (µ,λ) pins it —
    // #{w : col(µ,w) = col(µ,δ) ∧ col(w,λ) = col(δ,λ)} = 1.  `col` = X.Rel gives
    // the scheme-level (landed saAdj) engine; `col` = the pair-closure colouring
    // gives the extension-level engine the route hopes for.
    static bool[] DominatorClosure(int n, int[,] col, int[] t)
    {
        var det = new bool[n];
        foreach (int p in t) det[p] = true;
        bool changed = true;
        while (changed)
        {
            changed = false;
            for (int d = 0; d < n; d++)
            {
                if (det[d]) continue;
                bool pinned = false;
                for (int mu = 0; mu < n && !pinned; mu++)
                {
                    if (!det[mu]) continue;
                    for (int lam = 0; lam < n && !pinned; lam++)
                    {
                        if (!det[lam]) continue;
                        int cnt = 0;
                        for (int w = 0; w < n && cnt < 2; w++)
                            if (col[mu, w] == col[mu, d] && col[w, lam] == col[d, lam]) cnt++;
                        pinned = cnt == 1;
                    }
                }
                if (pinned) { det[d] = true; changed = true; }
            }
        }
        return det;
    }

    // Rank-EXTRACTING dominator closure: returns, per point, the BFS round it is
    // pinned at (0 = base, -1 = never) and the pinning pair (µ,λ) that did it.  A
    // point is pinned at round k+1 by two points of round ≤ k.  This is the explicit
    // construction a Lean closure proof must formalize (the "pinning rank" of
    // `dominatorReachable_of_rank`).
    static (int[] rank, (int mu, int lam)[] pinner) DominatorRank(int n, int[,] col, int[] t)
    {
        var rank = Enumerable.Repeat(-1, n).ToArray();
        var pinner = new (int, int)[n];
        foreach (int p in t) { rank[p] = 0; pinner[p] = (-1, -1); }
        int round = 0;
        bool changed = true;
        while (changed)
        {
            changed = false; round++;
            for (int d = 0; d < n; d++)
            {
                if (rank[d] >= 0) continue;
                bool found = false;
                for (int mu = 0; mu < n && !found; mu++)
                {
                    if (rank[mu] < 0 || rank[mu] >= round) continue;   // strictly-earlier round
                    for (int lam = 0; lam < n && !found; lam++)
                    {
                        if (rank[lam] < 0 || rank[lam] >= round) continue;
                        int cnt = 0;
                        for (int w = 0; w < n && cnt < 2; w++)
                            if (col[mu, w] == col[mu, d] && col[w, lam] == col[d, lam]) cnt++;
                        if (cnt == 1) { rank[d] = round; pinner[d] = (mu, lam); changed = true; found = true; }
                    }
                }
            }
        }
        return (rank, pinner);
    }

    // Dump the ℤ₄² Clebsch colour matrix as a Lean literal (for the concrete-route
    // feasibility spike: a hard-coded `AssociationScheme 16`).
    [Fact]
    public void Probe_DumpClebschMatrix()
    {
        var g = MakeGroup("Z4^2", 4, 4);
        var x = ClebschScheme(g)!;
        int n = x.N;
        output.WriteLine($"-- Z4^2 Clebsch colour matrix, n={n}, rank-4 (colours 0..3); col[v][w]");
        output.WriteLine("#eval -- rows:");
        for (int v = 0; v < n; v++)
        {
            var row = new int[n];
            for (int w = 0; w < n; w++) row[w] = x.Rel[v, w];
            output.WriteLine($"  ![{string.Join(",", row)}],");
        }
        // sanity: symmetric, diagonal=0, 4 colours
        bool sym = true, diag = true; var cols = new HashSet<int>();
        for (int v = 0; v < n; v++) for (int w = 0; w < n; w++)
        { if (x.Rel[v, w] != x.Rel[w, v]) sym = false; if (v == w && x.Rel[v, w] != 0) diag = false; cols.Add(x.Rel[v, w]); }
        output.WriteLine($"-- symmetric={sym}, diag0={diag}, colours={{{string.Join(",", cols.OrderBy(c => c))}}}");
        // dominator-closure rank for base {0,1} (the concrete-route pinning rank)
        var (rank, pinner) = DominatorRank(n, x.Rel, new[] { 0, 1 });
        output.WriteLine($"-- rank (base {{0,1}}): ![{string.Join(",", rank)}]");
        output.WriteLine($"-- complete? {rank.All(r => r >= 0)}; pinners:");
        for (int d = 0; d < n; d++)
            if (rank[d] > 0) output.WriteLine($"--   {d}: rank {rank[d]} pinned by ({pinner[d].mu},{pinner[d].lam})");
    }

    // ── IS RAINBOW-RIGIDITY PARAMETRIC? ────────────────────────────────────────────
    // The δ′ family lemma `dominatorReachable_of_rainbowRank` needs (a) the scheme is
    // `RainbowRigid` (distinct non-diagonal colours ⟹ ≤1 common neighbour) and (b) a
    // bounded base admits a rainbow rank.  Both are `decide`-checked on the order-16
    // bullseye; this probe asks whether they are a PARAMETRIC pattern by testing the
    // analogous amorphic-NLS 3-class scheme on n=25 (Z5^2) — the first prime-power
    // square beyond 16 — alongside the two order-16 instances.  RainbowRigid ⟺ for all
    // distinct nonzero i,j,k the intersection number C[k,i,j] ≤ 1.
    [Fact]
    public void Probe_RainbowRigidFamily()
    {
        output.WriteLine("── δ′ rainbow-rigidity: PARAMETRIC? (amorphic-NLS 3-class schemes, incl. n=25 beyond 16) ──");
        var groups = new[]
        {
            MakeGroup("Z4^2", 4, 4),          // n=16, the bullseye
            MakeGroup("Z2^4", 2, 2, 2, 2),    // n=16, char-2 anchor
            MakeGroup("Z5^2", 5, 5),          // n=25, BEYOND order 16
        };
        foreach (var g in groups)
        {
            var x = AmorphicNLS3Scheme(g);
            if (x is null)
            { output.WriteLine($"   {g.Name} (n={g.V}): no coherent equal-valency amorphic 3-class scheme found"); continue; }
            bool prim = PrimitiveScheme(x);
            // (a) rainbow rigidity: max common-neighbour count over distinct-colour triples
            int maxRainbow = 0; bool rigid = true;
            for (int i = 1; i < x.Rank; i++)
                for (int j = 1; j < x.Rank; j++)
                    for (int kk = 1; kk < x.Rank; kk++)
                        if (i != j && j != kk && i != kk)
                        { int c = x.C[kk, i, j]; maxRainbow = Math.Max(maxRainbow, c); if (c > 1) rigid = false; }
            var val = new int[x.Rank];
            for (int w = 0; w < x.N; w++) val[x.Rel[0, w]]++;
            // (b) smallest base {0,…,sz−1} whose forced-triangle closure exhausts Ω,
            //     and whether every pinning triangle is rainbow (distinct nonzero colours).
            int baseSize = -1; int[]? chosen = null;
            for (int sz = 2; sz <= 8 && baseSize < 0; sz++)
            {
                var bt = Enumerable.Range(0, sz).ToArray();
                var (rk, _) = DominatorRank(x.N, x.Rel, bt);
                if (rk.All(r => r >= 0)) { baseSize = sz; chosen = bt; }
            }
            int pinCount = 0, rainbowPins = 0;
            if (chosen != null)
            {
                var (rk, pn) = DominatorRank(x.N, x.Rel, chosen);
                for (int d = 0; d < x.N; d++)
                    if (rk[d] > 0)
                    {
                        pinCount++;
                        int a = x.Rel[pn[d].mu, d], b = x.Rel[d, pn[d].lam], cc = x.Rel[pn[d].mu, pn[d].lam];
                        if (a != 0 && b != 0 && cc != 0 && a != b && b != cc && a != cc) rainbowPins++;
                    }
            }
            // b(X): smallest consecutive base whose FULL coherent-closure (1-WL on pairs,
            // the actual recovery) discretizes — does it recover at all, even where the
            // scheme-level two-endpoint δ′ shortcut does not?
            int bX = -1;
            for (int sz = 1; sz <= 6 && bX < 0; sz++)
            {
                var T = Enumerable.Range(0, sz).ToHashSet();
                var col = CoherentClosure(x.N, (u, v) =>
                    (long)x.Rel[u, v] * 1000 + (T.Contains(u) ? u + 1 : 0) * 30 + (T.Contains(v) ? v + 1 : 0));
                var diag = new HashSet<int>(); bool disc = true;
                for (int u = 0; u < x.N && disc; u++) if (!diag.Add(col[u, u])) disc = false;
                if (disc) bX = sz;
            }
            // b₁(X): smallest consecutive base whose VERTEX 1-WL refinement (WarmRefineCells —
            // the actual seal model `warmRefine (schemeAdj S)`) discretizes.  THE WIRING SCOPE
            // QUESTION: is the seal's 1-WL recovery base the same as the 2-WL coherent base b(X)?
            //   b₁ == b(X)  ⟹ 1-WL reaches the 2-WL fiber partition at the base ⟹ the
            //                 `X_T-complete ⟹ warmRefine-discrete` wiring is residue-keyed, citation-free.
            //   b₁ >  b(X)  ⟹ the gap bites: 1-WL needs extra individualizations ⟹ the wiring must
            //                 carry the dimWL ±1 exchange (Chen–Ponomarenko / CFI Thm 5.2), a citation.
            int b1 = -1;
            for (int sz = 1; sz <= 8 && b1 < 0; sz++)
            {
                var cells = WarmRefineCells(x, Enumerable.Range(0, sz).ToArray());
                if (cells.Distinct().Count() == x.N) b1 = sz;
            }
            output.WriteLine($"   {g.Name} (n={x.N}, rank={x.Rank}, primitive={(prim ? "y" : "n")}): valencies={{{string.Join(",", val)}}}");
            output.WriteLine($"      WIRING-SCOPE: 2-WL base b(X)={(bX < 0 ? ">6" : bX.ToString())} vs 1-WL(warmRefine) base b₁={(b1 < 0 ? ">8" : b1.ToString())} ⟹ " +
                $"{(bX > 0 && b1 == bX ? "EQUAL — wiring residue-keyed/citation-free" : bX > 0 && b1 > bX ? "GAP BITES — wiring needs dimWL ±1 exchange (citation)" : "inconclusive")}");
            output.WriteLine($"      RAINBOW-RIGID={(rigid ? "YES" : "NO")} (max common-nbr over distinct-colour triples = {maxRainbow}); " +
                $"b(X)={(bX < 0 ? ">6" : bX.ToString())} (full WL recovers); " +
                $"scheme-level δ′ base = {(baseSize < 0 ? ">8 (does NOT close)" : baseSize.ToString())}; pins rainbow = {rainbowPins}/{pinCount}");
        }
        output.WriteLine("   ⟹ FINDING (2026-06-13): rainbow-rigidity is NOT parametric — YES at n=16 (cn=1), NO at n=25");
        output.WriteLine("      (cn=4); scheme-level δ′ likewise closes n=16 but NOT n=25. Yet n=25 RECOVERS at b(X)=2 via");
        output.WriteLine("      full WL ⟹ its recovery lives in the EXTENSION X_T's finer colours, not X's rank-4 colours.");
        output.WriteLine("      Redirect: lift the forced-triangle closure to the general-CC extension (the §1B c(X_T) route).");
    }

    // THE EXTRACTION PROBE: pull the explicit pinning-rank construction out of the
    // non-affine residue's forced-triangle closure.  Goal — reveal whether the
    // construction is UNIFORM/structural (⟹ a clean abstract Lean lemma exists) or
    // ad hoc, by reporting depth, layer sizes, whether intermediate points are
    // needed, and the distribution of pinning-triangle relation-types.
    [Fact]
    public void Probe_ExtractPinningRank()
    {
        output.WriteLine("── δ′ pinning-rank extraction — the non-affine residue's closure construction ──");
        foreach (var g in new[] { MakeGroup("Z4^2", 4, 4), MakeGroup("Z2^4", 2, 2, 2, 2) })
        {
            var x = ClebschScheme(g);
            if (x == null) { output.WriteLine($"   {g.Name}: no Clebsch scheme"); continue; }
            int n = x.N;
            output.WriteLine($"   {g.Name} (rank-4 amorphic-NLS, primitive={(PrimitiveScheme(x) ? "y" : "n")}, n={n}):");

            // every 2-point base {a,b} whose scheme-level c=1 closure completes
            var completingBases = new List<int[]>();
            for (int a = 0; a < n; a++)
                for (int b = a + 1; b < n; b++)
                    if (DominatorClosure(n, x.Rel, new[] { a, b }).All(z => z))
                        completingBases.Add(new[] { a, b });
            output.WriteLine($"      completing 2-bases: {completingBases.Count} of {n * (n - 1) / 2} pairs");
            if (completingBases.Count == 0) { output.WriteLine("      (no 2-base completes; needs larger base)"); continue; }

            // extract the construction from the first completing base, and aggregate
            // pinning-triangle types over ALL completing bases (uniformity test)
            var first = completingBases[0];
            var (rank, pinner) = DominatorRank(n, x.Rel, first);
            int depth = rank.Max();
            var layer = new int[depth + 1];
            foreach (int rk in rank) if (rk >= 0) layer[rk]++;
            output.WriteLine($"      sample base {{{string.Join(",", first)}}}: depth {depth} rounds, layers [{string.Join(",", layer)}]");

            int depthMax = 0; bool everNeedsIntermediate = false;
            var triples = new Dictionary<string, int>();
            foreach (var bt in completingBases)
            {
                var (rk, pn) = DominatorRank(n, x.Rel, bt);
                depthMax = Math.Max(depthMax, rk.Max());
                for (int d = 0; d < n; d++)
                {
                    if (rk[d] <= 0) continue;
                    var (mu, lam) = pn[d];
                    if (rk[mu] != 0 || rk[lam] != 0) everNeedsIntermediate = true;
                    string tri = $"({x.Rel[mu, d]},{x.Rel[d, lam]},{x.Rel[mu, lam]})";
                    triples[tri] = triples.TryGetValue(tri, out int c) ? c + 1 : 1;
                }
            }
            output.WriteLine($"      over all completing bases: max depth {depthMax}; " +
                             $"intermediate (non-base) pinners ever needed? {(everNeedsIntermediate ? "YES (genuine multi-round)" : "no (one-round in disguise)")}");
            output.WriteLine($"      pinning-triangle types (rel(µ,d),rel(d,λ),rel(µ,λ)) → count [uniformity signal]:");
            foreach (var kv in triples.OrderByDescending(kv => kv.Value))
                output.WriteLine($"         {kv.Key}: {kv.Value}");
        }
    }

    sealed class GateRow
    {
        public required int[] T; public required bool IsBase;
        public required int Cells, Fibers, CatchUpViol, N;
        public bool CatchUp => CatchUpViol == 0;
        public bool Discrete => Cells == N;
        public bool Complete => Fibers == N;
    }

    GateRow GateCheck(CC x, List<int[]> auts, int[] t)
    {
        var cells = WarmRefineCells(x, t);
        var (fibers, _) = ExtFibers(x, t);
        int viol = 0;
        for (int u = 0; u < x.N; u++)
            for (int v = u + 1; v < x.N; v++)
                if (cells[u] == cells[v] && fibers[u] != fibers[v]) viol++;
        return new GateRow
        {
            T = t, IsBase = IsBaseSet(auts, t), N = x.N,
            Cells = NumCells(cells), Fibers = NumCells(fibers), CatchUpViol = viol
        };
    }

    void MechanismCheck(string label, CC x, int[] t, bool isBase)
    {
        var cells = WarmRefineCells(x, t);
        var (_, pairColour) = ExtFibers(x, t);
        var detS = DominatorClosure(x.N, x.Rel, t);
        var detE = DominatorClosure(x.N, pairColour, t);
        var cellSize = new Dictionary<int, int>();
        foreach (int c in cells) cellSize[c] = cellSize.TryGetValue(c, out int k) ? k + 1 : 1;
        int viol = 0;
        for (int v = 0; v < x.N; v++) if (detE[v] && cellSize[cells[v]] > 1) viol++;
        output.WriteLine($"    {label} T={{{string.Join(",", t)}}}{(isBase ? " (base)" : " (NOT a base)")}: " +
                         $"scheme-c=1 closure {detS.Count(b => b)}/{x.N}; E-c=1 closure {detE.Count(b => b)}/{x.N}; " +
                         $"1-WL-soundness violations {viol}{(viol > 0 ? " ⚠️ (E-determined vertex in a non-singleton warm cell)" : "")}");
    }

    [Fact]
    public void Probe_CatchUpGate_BasesAndDominators()
    {
        output.WriteLine("── The catch-up probe-gate — WarmTwinsAreFiberTwins at the assembly's bases ──");
        output.WriteLine("   (a) gate: catch-up (same warm cell ⟹ same X_T fiber) at ALL group bases of size b(G);");
        output.WriteLine("   (b) engine: does the c=1 dominator closure (B3 shape) discretize — on X vs on E = X_T?");
        output.WriteLine("");

        // ── control: C₁₇ — sparse, every pair a base, everything must work ──
        {
            var x = CycleScheme(17);
            var auts = SchemeAut(x);
            output.WriteLine($"   C_17 (control): |Aut| = {auts.Count} (D₁₇ = 34 expected)");
            Assert.Equal(34, auts.Count);
            int bases = 0, catchUpOk = 0, discrete = 0;
            for (int a = 0; a < 17; a++)
                for (int b = a + 1; b < 17; b++)
                {
                    var row = GateCheck(x, auts, new[] { a, b });
                    if (row.IsBase) bases++;
                    if (row.CatchUp) catchUpOk++;
                    if (row.Discrete) discrete++;
                }
            output.WriteLine($"      size-2 sweep: {bases}/136 bases, catch-up {catchUpOk}/136, 1-WL discrete {discrete}/136");
            Assert.Equal(136, bases);     // every pair is a base (n odd: a reflection fixes one point)
            Assert.Equal(136, catchUpOk); // catch-up everywhere
            Assert.Equal(136, discrete);  // PV-sparse: every pair discretizes
            MechanismCheck("C_17", x, new[] { 0, 1 }, isBase: true);
            var detS = DominatorClosure(17, x.Rel, new[] { 0, 1 });
            Assert.Equal(17, detS.Count(b => b)); // the landed scheme-level engine succeeds on the sparse control
            output.WriteLine("");
        }

        // ── the residue ──
        var verdicts = new List<(string grp, int bG, int basesN, int basesCatchUp, int basesDiscrete,
                                 int basesComplete, bool engineAtBases, bool soundAtBases)>();
        foreach (var g in new[] { MakeGroup("Z4^2", 4, 4), MakeGroup("Z2^4", 2, 2, 2, 2) })
        {
            var x = ClebschScheme(g);
            Assert.NotNull(x);
            int n = x!.N;
            var auts = SchemeAut(x);
            output.WriteLine($"   {g.Name} (rank-4 amorphic-NLS Clebsch, primitive={(PrimitiveScheme(x) ? "y" : "n")}): |Aut| = {auts.Count}");

            // sweep sizes 1, 2, … until bases appear (b(G) = first size with a base)
            var rows = new List<GateRow>();
            int bG = -1;
            for (int size = 1; size <= 4 && bG < 0; size++)
            {
                var sizeRows = new List<GateRow>();
                foreach (var idx in Choose(n, size))
                    sizeRows.Add(GateCheck(x, auts, idx));
                rows.AddRange(sizeRows);
                if (sizeRows.Any(r => r.IsBase)) bG = size;

                // aggregate this size, keyed by the difference class for pairs
                if (size == 1)
                {
                    int cu = sizeRows.Count(r => r.CatchUp);
                    output.WriteLine($"    |T|=1 sweep ({sizeRows.Count} sets, {sizeRows.Count(r => r.IsBase)} bases): " +
                                     $"catch-up holds at {cu}/{sizeRows.Count}" +
                                     (cu < sizeRows.Count ? "  (the direction-check refutation, reproduced)" : ""));
                }
                else if (size == 2)
                {
                    output.WriteLine($"    |T|=2 sweep ({sizeRows.Count} sets) by difference class:");
                    foreach (var grp2 in sizeRows.GroupBy(r => x.Rel[r.T[0], r.T[1]]).OrderBy(q => q.Key))
                        output.WriteLine($"      class {grp2.Key}: {grp2.Count(),3} pairs | bases {grp2.Count(r => r.IsBase),3} | " +
                                         $"catch-up {grp2.Count(r => r.CatchUp),3} | 1-WL discrete {grp2.Count(r => r.Discrete),3} | " +
                                         $"ext complete {grp2.Count(r => r.Complete),3}");
                }
                else
                {
                    output.WriteLine($"    |T|={size} sweep ({sizeRows.Count} sets, {sizeRows.Count(r => r.IsBase)} bases): " +
                                     $"catch-up {sizeRows.Count(r => r.CatchUp)}, discrete {sizeRows.Count(r => r.Discrete)}");
                }
            }
            Assert.True(bG > 0, $"{g.Name}: no base of size ≤ 4 — unexpected for a small residual");

            var minBases = rows.Where(r => r.IsBase && r.T.Length == bG).ToList();
            int cuB = minBases.Count(r => r.CatchUp), dB = minBases.Count(r => r.Discrete), cB = minBases.Count(r => r.Complete);
            output.WriteLine($"    b(G) = {bG}; minimal bases: {minBases.Count}  →  catch-up {cuB}/{minBases.Count}, " +
                             $"1-WL discrete {dB}/{minBases.Count}, ext complete {cB}/{minBases.Count}");
            foreach (var r in minBases.Where(r => !r.CatchUp).Take(5))
                output.WriteLine($"      ⚠️ catch-up FAILS at base T={{{string.Join(",", r.T)}}}: cells={r.Cells}, fibers={r.Fibers}, {r.CatchUpViol} split pairs");

            // mechanism: the singleton anchor + up to 3 minimal bases spread across difference
            // classes + (if any) the first catch-up-failing base
            output.WriteLine($"    engine (c=1 dominator closures):");
            MechanismCheck(g.Name, x, new[] { 0 }, isBase: IsBaseSet(auts, new[] { 0 }));
            var mechBases = minBases.GroupBy(r => x.Rel[r.T[0], r.T[r.T.Length - 1]])
                                    .Select(q => q.First()).Take(3).ToList();
            var failing = minBases.FirstOrDefault(r => !r.CatchUp);
            if (failing != null && !mechBases.Contains(failing)) mechBases.Add(failing);
            bool engineOk = true, soundOk = true;
            foreach (var r in mechBases)
            {
                var (_, pc) = ExtFibers(x, r.T);
                var detE = DominatorClosure(n, pc, r.T);
                var cells = WarmRefineCells(x, r.T);
                var cellSize = new Dictionary<int, int>();
                foreach (int c in cells) cellSize[c] = cellSize.TryGetValue(c, out int k) ? k + 1 : 1;
                engineOk &= detE.Count(b => b) == n;
                for (int v = 0; v < n; v++) if (detE[v] && cellSize[cells[v]] > 1) soundOk = false;
                MechanismCheck(g.Name, x, r.T, isBase: true);
            }
            verdicts.Add((g.Name, bG, minBases.Count, cuB, dB, cB, engineOk, soundOk));
            output.WriteLine("");
        }

        output.WriteLine("── VERDICT (the catch-up gate, build doc STATUS item 5) ──");
        foreach (var v in verdicts)
        {
            output.WriteLine($"   {v.grp,-6}: b(G)={v.bG}, {v.basesN} minimal bases | catch-up {v.basesCatchUp}/{v.basesN}" +
                             $" | discrete {v.basesDiscrete}/{v.basesN} | complete {v.basesComplete}/{v.basesN}" +
                             $" | E-engine discretizes at tested bases: {(v.engineAtBases ? "YES" : "NO")}" +
                             $" | 1-WL-sound: {(v.soundAtBases ? "YES" : "NO")}");
        }
        bool gateGreen = verdicts.All(v => v.basesCatchUp == v.basesN);
        bool engineGreen = verdicts.All(v => v.engineAtBases && v.soundAtBases);
        output.WriteLine($"   (a) {(gateGreen ? "catch-up HOLDS at every minimal base — state `WarmTwinsAreFiberTwins` at `IsBase T` and the gate is green"
                                             : "catch-up FAILS at some minimal base — the assembly must move to base+O(1) (or re-key); see the failing T above")}");
        output.WriteLine($"   (b) {(engineGreen ? "the extension-level c=1 dominator closure discretizes from the tested bases with no 1-WL-soundness violations — the B3-on-E propagation is a viable discharge engine"
                                               : "the dominator engine stalls or is 1-WL-unsound at some base — the discharge needs the pair-WL model, not warm-cell-keyed B3-on-E")}");
    }

    // ════════════════════════════════════════════════════════════════════════════
    //  M1 (c(X_T) scoping) — measure the indistinguishing number across a DIVERSE
    //  residue family and test whether the X_T forced-triangle mechanism is uniform.
    //  See docs/chain-descent-cxt-scoping.md §3–§4.
    // ════════════════════════════════════════════════════════════════════════════

    //  c(X) = indistinguishing number = max over α≠β of #{γ : r(α,γ) = r(β,γ)}
    //  (the counting form of `Separability.indistinguishingNumber`; constant on each
    //  relation class, so the max over ordered pairs is c(X)).
    static int IndistinguishingNumber(int n, int[,] col)
    {
        int best = 0;
        for (int a = 0; a < n; a++)
            for (int b = 0; b < n; b++)
            {
                if (a == b) continue;
                int c = 0;
                for (int g = 0; g < n; g++) if (col[a, g] == col[b, g]) c++;
                if (c > best) best = c;
            }
        return best;
    }

    //  X_T colour matrix = coherent closure with the points of T individualized.
    static int[,] ExtensionColours(CC x, int[] T)
    {
        var inT = new bool[x.N]; foreach (int t in T) inT[t] = true;
        long B = x.N + 1;
        return CoherentClosure(x.N, (u, v) =>
            ((long)x.Rel[u, v] * B + (inT[u] ? u + 1 : 0)) * B + (inT[v] ? v + 1 : 0));
    }

    //  smallest consecutive base {0..sz-1} whose 2-WL coherent closure is discrete.
    static int MinBase(CC x, int maxSz)
    {
        for (int sz = 1; sz <= maxSz; sz++)
        {
            var col = ExtensionColours(x, Enumerable.Range(0, sz).ToArray());
            var diag = new HashSet<int>(); bool disc = true;
            for (int u = 0; u < x.N && disc; u++) if (!diag.Add(col[u, u])) disc = false;
            if (disc) return sz;
        }
        return -1;
    }

    //  Paley scheme on F_p (p prime, p ≡ 1 mod 4) — a rank-3 cyclotomic SRG; a
    //  small-aut primitive test point of a different rank/construction than amorphic-NLS.
    static CC PaleyScheme(int q)
    {
        var isQR = new bool[q];
        for (int x = 1; x < q; x++) isQR[(x * x) % q] = true;
        var rel = new int[q, q];
        for (int u = 0; u < q; u++)
            for (int v = 0; v < q; v++)
                rel[u, v] = (u == v) ? 0 : (isQR[((u - v) % q + q) % q] ? 1 : 2);
        return BuildCC(q, rel);
    }

    //  Petersen = Kneser K(5,2): a rank-3 primitive SRG(10,3,0,1) with |Aut| = S₅ —
    //  a genuinely NON-cyclotomic small primitive scheme (diversity beyond the field families).
    static CC PetersenScheme()
    {
        var subs = new List<(int a, int b)>();
        for (int a = 0; a < 5; a++) for (int b = a + 1; b < 5; b++) subs.Add((a, b));
        int n = subs.Count;
        var rel = new int[n, n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
            {
                if (i == j) { rel[i, j] = 0; continue; }
                var (a, b) = subs[i]; var (c, d) = subs[j];
                bool disjoint = a != c && a != d && b != c && b != d;
                rel[i, j] = disjoint ? 1 : 2;
            }
        return BuildCC(n, rel);
    }

    [Fact]
    public void Probe_CXT_ScopingM1()
    {
        output.WriteLine("── M1: c(X_T) across a DIVERSE residue family + the X_T mechanism (scoping the general c(X_T) work) ──");
        output.WriteLine("   does individualizing O(1) points drive the indistinguishing number c down to a SMALL value, uniformly?");
        var schemes = new List<(string tag, CC x)>();
        foreach (var (nm, mods) in new[] { ("Z4^2", new[] { 4, 4 }), ("Z2^4", new[] { 2, 2, 2, 2 }), ("Z5^2", new[] { 5, 5 }) })
        {
            var xx = AmorphicNLS3Scheme(MakeGroup(nm, mods));
            if (xx != null) schemes.Add(($"amorph-{nm}", xx));   // rank-4 amorphic-NLS (V≤25: PDS search feasible)
        }
        foreach (int q in new[] { 13, 17, 29, 37, 41 }) schemes.Add(($"Paley-{q}", PaleyScheme(q)));  // rank-3 cyclotomic
        schemes.Add(("Petersen", PetersenScheme()));                                                  // rank-3 non-cyclotomic

        foreach (var (tag, x) in schemes)
        {
            int n = x.N;
            int cX = IndistinguishingNumber(n, x.Rel);
            int c1 = IndistinguishingNumber(n, ExtensionColours(x, new[] { 0 }));
            int c2 = n > 2 ? IndistinguishingNumber(n, ExtensionColours(x, new[] { 0, 1 })) : 0;
            int bX = MinBase(x, 6);
            // Scheme-level δ′ at the min base {0..b(X)-1}: does the forced-triangle (c=1)
            // closure on X's OWN colours reach discreteness?  (NB: testing it on X_T's
            // colours is vacuous — X_T at a base is already discrete — so the meaningful
            // signal is this scheme-level test + the c-collapse, NOT a closure on X_T.)
            var bBase = bX > 0 ? Enumerable.Range(0, bX).ToArray() : new[] { 0, 1 };
            var (rkScheme, _) = DominatorRank(n, x.Rel, bBase);
            bool schemeCloses = rkScheme.All(r => r >= 0);
            string dom = n <= 26 ? (CondI(OnePointExtension(x, 0), 0).ok ? "PASS" : "fail") : "—(skip)";
            output.WriteLine(
                $"   {tag,-12} n={n,2} rk={x.Rank,3} {(PrimitiveScheme(x) ? "prim" : "imp ")} | " +
                $"c(X)={cX,3} → c(X₁)={c1,3} → c(X₂)={c2,3} | b(X)={(bX < 0 ? ">6" : bX.ToString()),2} | " +
                $"dom@Xα={dom,7} | scheme-δ′@b(X)={(schemeCloses ? "✓" : "✗")}");
        }
        output.WriteLine("   ⟹ READ (the §3 uniformity question — the c-collapse IS the forced-triangle abundance / domination precondition):");
        output.WriteLine("     • c(X) grows ~n/2 (dense, unbounded) but COLLAPSES to a small constant after O(1) points (c(X₁)/c(X₂)) — uniformly?");
        output.WriteLine("     • scheme-level δ′ fails for n≥25 (forced triangles vanish in X's own colours — the order-16 artifact ⟹ need X_T);");
        output.WriteLine("     • any scheme with c(X₁)/c(X₂) GROWING in n is a candidate seal-falsifier (unbounded-base residue).");
    }
}
