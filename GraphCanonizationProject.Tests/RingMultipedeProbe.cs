using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit;
using Xunit.Abstractions;

// ─────────────────────────────────────────────────────────────────────────────
// RING-MULTIPEDE PROBE (2026-07-11) — the native-A-multipede generator + the
// graph-level realization of the degree<->budget bridge (the ring twin of D-M1).
//
// Confirms two things the algebraic RingInferenceProbe could only assume:
//  (1) The FORCING MECHANISM: in a degree-k gadget Σ_{i} x_i = 0, pinning j peers to
//      a common value v and the rest to 0 FORCES the last = -(j·v). So forcing exposes
//      the multiples { (0..k-1)·v } — recognition-free (only sum-zero propagation, no
//      arithmetic peeking). Hence the annihilator counts c_m = |{a:m·a=0}| are
//      recoverable for m ≤ k-1, and a same-order ring pair splits exactly at gadget
//      degree = exp+1. This is RingInferenceProbe test 2, now on the actual mechanism.
//  (2) The native-A-multipede GRAPH generator is well-formed: segment-state vertices
//      (p,a) + gadget-tuple vertices (one per A-tuple summing to 0), each gadget vertex
//      joined to its k segment-states whose values sum to 0 in A. The substrate B1's D1
//      runs on; F₂ (A=Z/2) is the case MultipedeGenerator already builds.
//
// Layer B (1-WL forcing == unit-prop over A) lets us work at the propagation level.
// ─────────────────────────────────────────────────────────────────────────────
public sealed class RingMultipedeProbe
{
    private static readonly string LogPath =
        "/tmp/claude-1000/-workspace/59f34b56-7c75-41c7-b064-94cd43f98d92/scratchpad/ring_multipede.log";

    private readonly ITestOutputHelper _out;
    public RingMultipedeProbe(ITestOutputHelper o) => _out = o;
    private void Log(string s) { _out.WriteLine(s); File.AppendAllText(LogPath, s + "\n"); }

    // ── finite abelian group ⊕ Z/d_i, elements as mixed-radix indices ─────────────
    private sealed class Ab
    {
        public readonly string Name; public readonly int[] Inv; public readonly int N;
        public Ab(string name, params int[] inv) { Name = name; Inv = inv; N = inv.Aggregate(1, (a, b) => a * b); }
        private int[] T(int idx) { var t = new int[Inv.Length]; for (int i = Inv.Length - 1; i >= 0; i--) { t[i] = idx % Inv[i]; idx /= Inv[i]; } return t; }
        private int Ix(int[] t) { int x = 0; for (int i = 0; i < Inv.Length; i++) x = x * Inv[i] + t[i]; return x; }
        public int Add(int a, int b) { var ta = T(a); var tb = T(b); var tc = new int[Inv.Length]; for (int i = 0; i < Inv.Length; i++) tc[i] = (ta[i] + tb[i]) % Inv[i]; return Ix(tc); }
        public int Neg(int a) { var ta = T(a); var tc = new int[Inv.Length]; for (int i = 0; i < Inv.Length; i++) tc[i] = (Inv[i] - ta[i]) % Inv[i]; return Ix(tc); }
        public int Order(int a) { int o = 1, x = a; while (x != 0) { x = Add(x, a); o++; } return o; }
        public int Annih(int m) { int c = 0; for (int a = 0; a < N; a++) { int x = 0; for (int i = 0; i < m; i++) x = Add(x, a); if (x == 0) c++; } return c; }
        public int Exponent() { int e = 1; for (int a = 0; a < N; a++) e = Lcm(e, Order(a)); return e; }
    }
    private static int Gcd(int a, int b) { while (b != 0) { (a, b) = (b, a % b); } return a < 0 ? -a : a; }
    private static int Lcm(int a, int b) => a / Gcd(a, b) * b;

    // ── unit-propagation over A: constraints (var-index lists) each summing to 0 ──
    private static void Propagate(Ab A, List<int[]> cons, Dictionary<int, int> asn)
    {
        bool changed = true;
        while (changed)
        {
            changed = false;
            foreach (var c in cons)
            {
                var unknown = c.Where(v => !asn.ContainsKey(v)).ToList();
                if (unknown.Count == 1)
                {
                    int sum = 0; foreach (var v in c) if (asn.TryGetValue(v, out var val)) sum = A.Add(sum, val);
                    asn[unknown[0]] = A.Neg(sum); changed = true;
                }
            }
        }
    }

    // Recognition-free observation: a degree-k gadget forces -(j·v). Read the multiple j·v of value v.
    private static int ObserveMultiple(Ab A, int k, int v, int j)
    {
        var cons = new List<int[]> { Enumerable.Range(0, k).ToArray() };
        var asn = new Dictionary<int, int>();
        for (int i = 1; i <= j; i++) asn[i] = v;          // j peers pinned to v
        for (int i = j + 1; i < k; i++) asn[i] = 0;       // the rest to identity
        Propagate(A, cons, asn);
        return A.Neg(asn[0]);                              // asn[0] = -(j·v); undo the sign to read j·v
    }

    // Annihilator counts recovered FROM FORCING ALONE (m·a read via ObserveMultiple), m=1..k-1.
    private static int[] RecoveredAnnih(Ab A, int k)
    {
        var res = new int[Math.Max(0, k - 1)];
        for (int m = 1; m <= k - 1; m++)
        {
            int c = 0;
            for (int a = 0; a < A.N; a++) if (ObserveMultiple(A, k, a, m) == 0) c++;  // m·a == 0 ?
            res[m - 1] = c;
        }
        return res;
    }

    private static bool SepAtDegree(Ab x, Ab y, int k) => !RecoveredAnnih(x, k).SequenceEqual(RecoveredAnnih(y, k));

    [Fact]
    public void RingMultipede_ForcingExposesMultiplesUpToDegreeMinusOne()
    {
        Log("");
        Log("=== RING-MULTIPEDE PROBE (2026-07-11) — forcing exposes multiples up to (degree-1) ===");

        var z4 = new Ab("Z4", 4);
        var z2z8 = new Ab("Z2xZ8", 2, 8); var z4z4 = new Ab("Z4xZ4", 4, 4);
        var z9 = new Ab("Z9", 9); var z33 = new Ab("Z3^2", 3, 3);

        // (a) forcing recovers c_m EXACTLY (cross-check the mechanism vs the ground-truth arithmetic).
        var recZ4 = RecoveredAnnih(z4, 5);
        for (int m = 1; m <= 4; m++) Assert.Equal(z4.Annih(m), recZ4[m - 1]);
        Assert.Equal(new[] { 1, 2, 1, 4 }, recZ4);   // Z4 fully seen at degree 5 (budget 4 ≥ exp 4)
        Log($"Z4 recovered-by-forcing c_1..c_4 = [{string.Join(",", RecoveredAnnih(z4, 5))}]  (matches ground truth 1,2,1,4)");

        // (b) a same-order pair splits under FORCING exactly at gadget degree = exp+1.
        Log($"Z2xZ8 | Z4xZ4 (exp 4): sep@deg4={SepAtDegree(z2z8, z4z4, 4)}  sep@deg5={SepAtDegree(z2z8, z4z4, 5)}");
        Assert.False(SepAtDegree(z2z8, z4z4, 4));   // degree 4 (budget 3) — indistinguishable
        Assert.True(SepAtDegree(z2z8, z4z4, 5));    // degree 5 = exp+1 — split
        Assert.Equal(5, z4z4.Exponent() + 1);

        Log($"Z9 | Z3^2 (exp 3): sep@deg3={SepAtDegree(z9, z33, 3)}  sep@deg4={SepAtDegree(z9, z33, 4)}");
        Assert.False(SepAtDegree(z9, z33, 3));      // degree 3 (budget 2) — odd rings show nothing at 2-torsion
        Assert.True(SepAtDegree(z9, z33, 4));       // degree 4 = exp+1 — split
        Assert.Equal(4, z33.Exponent() + 1);

        Log("FINDING: the forcing MECHANISM realizes budget = degree-1; a ring pins exactly at gadget degree exp(A)+1.");
    }

    // ── native-A-multipede graph generator ────────────────────────────────────────
    // Base incidence = points × lines. Vertices: segment-states (p,a) [color 0] and
    // gadget-tuples (ℓ, tuple) [color 1]; a gadget-tuple joins the k segment-states its
    // tuple selects, and every tuple sums to 0 in A.
    private static IEnumerable<int[]> TuplesSumZero(Ab A, int d)
    {
        int free = d - 1, total = 1; for (int i = 0; i < free; i++) total *= A.N;
        for (int code = 0; code < total; code++)
        {
            var t = new int[d]; int c = code, sum = 0;
            for (int i = 0; i < free; i++) { t[i] = c % A.N; c /= A.N; sum = A.Add(sum, t[i]); }
            t[d - 1] = A.Neg(sum);
            yield return t;
        }
    }

    [Fact]
    public void RingMultipede_GraphGenerator_WellFormed()
    {
        Log("");
        Log("=== RING-MULTIPEDE PROBE — native-A-multipede graph generator well-formedness ===");
        var A = new Ab("Z4", 4);
        int nPoints = 4;
        var lines = new List<int[]> { new[] { 0, 1, 2 }, new[] { 1, 2, 3 } };  // two degree-3 gadgets

        // vertex ids: segment-states 0 .. nPoints*|A|-1 ; gadget-tuples appended after.
        int segCount = nPoints * A.N;
        var edges = new List<(int u, int v)>();
        int gadgetCount = 0;
        foreach (var ln in lines)
        {
            foreach (var t in TuplesSumZero(A, ln.Length))
            {
                int gv = segCount + gadgetCount++;
                int s = 0;
                for (int i = 0; i < ln.Length; i++)
                {
                    int seg = ln[i] * A.N + t[i];       // vertex (point ln[i], value t[i])
                    edges.Add((gv, seg));
                    s = A.Add(s, t[i]);
                }
                Assert.Equal(0, s);                      // every gadget-tuple sums to 0 in A
            }
        }

        int expectedGadgets = lines.Sum(ln => (int)Math.Pow(A.N, ln.Length - 1));
        Assert.Equal(expectedGadgets, gadgetCount);      // |gadget vertices| = Σ |A|^(deg-1)
        Assert.Equal(nPoints * A.N, segCount);
        // every gadget vertex has degree = its line's degree
        var deg = new Dictionary<int, int>();
        foreach (var (u, _) in edges) deg[u] = deg.GetValueOrDefault(u) + 1;
        Assert.All(deg.Values, d => Assert.Contains(d, new[] { 3 }));  // all lines here are degree 3

        Log($"A=Z4, points={nPoints}, lines={lines.Count} (deg 3): seg-verts={segCount}, gadget-verts={gadgetCount} (= Σ|A|^(deg-1)={expectedGadgets}), edges={edges.Count}.");
        Log("FINDING: generator well-formed — every gadget-tuple sums to 0 in A; the native-A substrate B1's D1 runs on.");
    }
}
