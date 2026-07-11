using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;

// ─────────────────────────────────────────────────────────────────────────────
// RING-SOLVE PROBE (2026-07-11) — RM-5 algebraic core: the ring generalization of
// Option-2's SolveF2 + CosetMin (the D4/D5 emit primitives).
//
// The canonical-form emit needs two operations over a finite abelian A, the ring
// twins of the F₂ CanonicalForm's `SolveF2` and `CosetMin`:
//   · SolveA(M, target)   : solve M o = target over A^nW (unique when rigid) — the
//                           gauge-fixing "orientation" solve.
//   · CosetMinA(c, M)      : canonical (lex-min) representative of the coset
//                           c + im_A(M) — the iso-invariant twist-class (D-M2 twin);
//                           im_A(M) is exactly the translation gauge (shifting a
//                           segment's zero by t shifts the twist by M·t).
//   · TwistClassA(c, M)    : coset-min further quotiented by the unit/Aut gauge
//                           (min over ring units) — fully gauge-invariant twist class.
//
// Validated here at the algebraic level (brute over A^nW; production = extended
// Smith, whose invariant-factor form RM-4 already validated). Recognition-free
// reading of `c` from the graph + the state-ordered adjacency emit is the remaining
// RM-5 integration step (uses RM-3's per-segment group recovery to label states).
// ─────────────────────────────────────────────────────────────────────────────
public sealed class RingSolveProbe
{
    private readonly ITestOutputHelper _out;
    public RingSolveProbe(ITestOutputHelper o) => _out = o;

    private sealed class Ab
    {
        public readonly string Name; public readonly int[] Inv; public readonly int N;
        public Ab(string name, params int[] inv) { Name = name; Inv = inv; N = inv.Aggregate(1, (a, b) => a * b); }
        private int[] T(int idx) { var t = new int[Inv.Length]; for (int i = Inv.Length - 1; i >= 0; i--) { t[i] = idx % Inv[i]; idx /= Inv[i]; } return t; }
        private int Ix(int[] t) { int x = 0; for (int i = 0; i < Inv.Length; i++) x = x * Inv[i] + t[i]; return x; }
        public int Add(int a, int b) { var ta = T(a); var tb = T(b); var tc = new int[Inv.Length]; for (int i = 0; i < Inv.Length; i++) tc[i] = (ta[i] + tb[i]) % Inv[i]; return Ix(tc); }
        public int Scale(int a, int u) { var ta = T(a); var tc = new int[Inv.Length]; for (int i = 0; i < Inv.Length; i++) tc[i] = (int)(((long)ta[i] * u) % Inv[i]); return Ix(tc); }
    }

    // M o over A (result length = #rows).
    private static int[] MatVec(long[,] M, int[] o, Ab A)
    {
        int m = M.GetLength(0), nW = M.GetLength(1);
        var r = new int[m];
        for (int i = 0; i < m; i++) { int s = 0; for (int j = 0; j < nW; j++) if (M[i, j] != 0) for (int t = 0; t < (int)M[i, j]; t++) s = A.Add(s, o[j]); r[i] = s; }
        return r;
    }
    private static int[] VecAdd(int[] a, int[] b, Ab A) { var r = new int[a.Length]; for (int i = 0; i < a.Length; i++) r[i] = A.Add(a[i], b[i]); return r; }

    // brute enumerate o ∈ A^nW.
    private static IEnumerable<int[]> AllVectors(int nW, int n)
    {
        long total = 1; for (int i = 0; i < nW; i++) total *= n;
        for (long code = 0; code < total; code++)
        {
            var o = new int[nW]; long c = code; for (int j = 0; j < nW; j++) { o[j] = (int)(c % n); c /= n; }
            yield return o;
        }
    }

    // solve M o = target over A (brute; unique when rigid). null if unsatisfiable.
    private static int[]? SolveA(long[,] M, int[] target, Ab A, int nW)
    {
        foreach (var o in AllVectors(nW, A.N)) if (MatVec(M, o, A).SequenceEqual(target)) return o;
        return null;
    }

    // canonical lex-min representative of the coset c + im_A(M).
    private static int[] CosetMinA(int[] c, long[,] M, Ab A, int nW)
    {
        int[]? best = null;
        foreach (var o in AllVectors(nW, A.N))
        {
            var cand = VecAdd(c, MatVec(M, o, A), A);
            if (best == null || LexLess(cand, best)) best = cand;
        }
        return best!;
    }
    private static bool LexLess(int[] a, int[] b) { for (int i = 0; i < a.Length; i++) { if (a[i] != b[i]) return a[i] < b[i]; } return false; }

    // fully gauge-invariant twist class: coset-min further min'd over the ring units
    // (the scalar/Aut gauge that coset-min alone does not quotient). Cyclic units shown.
    private static string TwistClassA(int[] c, long[,] M, Ab A, int nW)
    {
        int[]? best = null;
        foreach (int u in CyclicUnits(A))
        {
            var cu = c.Select(x => A.Scale(x, u)).ToArray();
            var cm = CosetMinA(cu, M, A, nW);
            if (best == null || LexLess(cm, best)) best = cm;
        }
        return string.Join("", best!);
    }
    private static IEnumerable<int> CyclicUnits(Ab A) { if (A.Inv.Length != 1) { yield return 1; yield break; } int k = A.Inv[0]; for (int u = 1; u < k; u++) if (Gcd(u, k) == 1) yield return u; }
    private static int Gcd(int a, int b) { while (b != 0) { (a, b) = (b, a % b); } return a < 0 ? -a : a; }

    [Theory]
    [InlineData("Z2", 2)]
    [InlineData("Z4", 4)]
    [InlineData("Z2^2", 2, 2)]
    [InlineData("Z6", 6)]
    public void RM5_SolveAndCoset_OverRing_Correct(string name, params int[] inv)
    {
        var A = new Ab(name, inv);
        // triangle incidence — nontrivial coker over any A (det = 2), so the coset/twist
        // machinery is genuinely exercised (not a full-rank M where every coset collapses).
        long[,] M = { { 1, 1, 0 }, { 0, 1, 1 }, { 1, 0, 1 } };
        int nW = 3;

        // (1) SolveA recovers a genuine solution of M o = target.
        var o0 = new[] { 1, A.N - 1, 2 % A.N };
        var target = MatVec(M, o0, A);
        var o = SolveA(M, target, A, nW);
        Assert.NotNull(o);
        Assert.Equal(target, MatVec(M, o!, A));

        // (2) CosetMinA is constant on a coset (adding any M·o' leaves it unchanged) —
        //     exactly the translation-gauge invariance the emit needs.
        var c = new int[] { 1 % A.N, 0, 2 % A.N };
        var cmin = CosetMinA(c, M, A, nW);
        foreach (var oq in new[] { new[] { 2 % A.N, 1, 0 }, new[] { 0, 3 % A.N, 1 } })
        {
            var shifted = VecAdd(c, MatVec(M, oq, A), A);
            Assert.Equal(cmin, CosetMinA(shifted, M, A, nW));
        }

        // (3) CosetMinA SEPARATES distinct cosets: e_0 and 0 land in different classes iff e_0 ∉ im_A(M).
        var e0 = new int[] { 1, 0, 0 };
        var zero = new int[] { 0, 0, 0 };
        bool e0InImage = SolveA(M, e0, A, nW) != null;
        bool minsDiffer = !CosetMinA(e0, M, A, nW).SequenceEqual(CosetMinA(zero, M, A, nW));
        Assert.Equal(!e0InImage, minsDiffer);
        Assert.False(e0InImage);                 // triangle has nontrivial coker ⟹ separation is genuinely hit
        var twE0 = TwistClassA(e0, M, A, nW);
        Assert.NotEqual("000", twE0);            // e_0's twist-class is a nonzero coset rep

        // (4) TwistClassA is invariant under the unit gauge (scaling c by a unit).
        var twc = TwistClassA(c, M, A, nW);
        foreach (int u in CyclicUnits(A))
            Assert.Equal(twc, TwistClassA(c.Select(x => A.Scale(x, u)).ToArray(), M, A, nW));

        _out.WriteLine($"{name,-6} solve✓ coset-invariant✓ separates(e0∈im={e0InImage})✓ twist(e0)={twE0} unit-gauge-inv✓");
    }
}
