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
}
