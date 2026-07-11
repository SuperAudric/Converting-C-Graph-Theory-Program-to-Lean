using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit;
using Xunit.Abstractions;

// ─────────────────────────────────────────────────────────────────────────────
// RING-INFERENCE PROBE (2026-07-11) — the fresh, in-repo replacement for the
// evaporated /tmp/ring_infer_probe.py. Anchors the ring design (IR doc §11.13a)
// before B1: can the value group A be recovered CANONICALLY from the extracted
// gadget relation, and is the negation-relation 2-torsion (the §11.13
// discriminator) sufficient in general, or is the full order-profile required?
//
// Algebraic level — no graph/WL. The Z4 probe already established that native
// A-multipede 1-WL forcing == the algebra over A (same forcing number as F2), so
// the OPEN question is purely group-theoretic: which invariant of A does the
// extracted state relation have to compute to canonically pin the ring?
//
//   A            = a finite abelian group by invariant factors [d1|d2|...].
//   order-profile= the multiset {ord(a) : a in A}  (a group invariant; = the
//                  solution counts of m*a=0 per m | exp A). The canonical A-fingerprint.
//   2-torsion    = |{a : 2a = 0}| = |fix N|, N = {(a,-a)} the negation relation
//                  (the §11.13 deg-2-gadget discriminator).
//
// FINDING (codified): order-profile separates every same-order abelian group;
// 2-torsion separates Z4|Z2^2 but NOT Z2xZ8|Z4xZ4 (both order 16, 2-torsion 4).
// => canonical ring inference must read the FULL order-profile => D1 must extract
// higher-degree gadget relations, not only the deg-2 negation relation.
// ─────────────────────────────────────────────────────────────────────────────
public sealed class RingInferenceProbe
{
    private static readonly string LogPath =
        "/tmp/claude-1000/-workspace/59f34b56-7c75-41c7-b064-94cd43f98d92/scratchpad/ring_infer.log";

    private readonly ITestOutputHelper _out;
    public RingInferenceProbe(ITestOutputHelper o) => _out = o;

    private void Log(string line)
    {
        _out.WriteLine(line);
        File.AppendAllText(LogPath, line + "\n");
    }

    // A finite abelian group ⊕ Z/d_i by invariant factors; element = mixed-radix index 0..N-1.
    private sealed class Ab
    {
        public readonly string Name;
        public readonly int[] Inv;
        public readonly int N;
        public Ab(string name, params int[] inv) { Name = name; Inv = inv; N = inv.Aggregate(1, (a, b) => a * b); }

        public int[] Tuple(int idx)
        {
            var t = new int[Inv.Length];
            for (int i = Inv.Length - 1; i >= 0; i--) { t[i] = idx % Inv[i]; idx /= Inv[i]; }
            return t;
        }

        // additive order of an element = lcm_i ( d_i / gcd(a_i, d_i) )
        public int Order(int idx)
        {
            var t = Tuple(idx);
            int o = 1;
            for (int i = 0; i < Inv.Length; i++) { int di = Inv[i]; o = Lcm(o, di / Gcd(t[i], di)); }
            return o;
        }

        public SortedDictionary<int, int> OrderProfile()
        {
            var d = new SortedDictionary<int, int>();
            for (int i = 0; i < N; i++) { int o = Order(i); d[o] = d.TryGetValue(o, out var c) ? c + 1 : 1; }
            return d;
        }

        public int TwoTorsion() { int c = 0; for (int i = 0; i < N; i++) if (Order(i) <= 2) c++; return c; }

        public string Fingerprint() => string.Join(",", OrderProfile().Select(kv => $"{kv.Key}^{kv.Value}"));
    }

    private static int Gcd(int a, int b) { while (b != 0) { (a, b) = (b, a % b); } return a < 0 ? -a : a; }
    private static int Lcm(int a, int b) => a / Gcd(a, b) * b;

    [Fact]
    public void RingInference_OrderProfile_SeparatesSameOrderGroups_TwoTorsionInsufficient()
    {
        Log("");
        Log("=== RING-INFERENCE PROBE (2026-07-11) — canonical A-fingerprint: order-profile vs 2-torsion ===");
        Log(string.Format("{0,-10} {1,4} {2,8}   {3}", "group", "|A|", "2-tors", "order-profile (the canonical fingerprint)"));
        Log(new string('-', 78));

        var groups = new[]
        {
            new Ab("Z2", 2),
            new Ab("Z4", 4), new Ab("Z2^2", 2, 2),
            new Ab("Z8", 8), new Ab("Z2xZ4", 2, 4), new Ab("Z2^3", 2, 2, 2),
            new Ab("Z6", 6),
            new Ab("Z9", 9), new Ab("Z3^2", 3, 3),
            new Ab("Z2xZ8", 2, 8), new Ab("Z4xZ4", 4, 4),
        };

        foreach (var g in groups)
            Log(string.Format("{0,-10} {1,4} {2,8}   [{3}]", g.Name, g.N, g.TwoTorsion(), g.Fingerprint()));
        Log("");

        // (a) The order-profile separates every same-order pair of distinct type.
        foreach (var byOrder in groups.GroupBy(g => g.N))
        {
            var fps = byOrder.Select(g => g.Fingerprint()).ToList();
            Assert.Equal(fps.Count, fps.Distinct().Count());
        }

        // (b) Classic case: Z4 vs Z2^2 separated by 2-torsion (2 vs 4).
        var z4 = groups.First(g => g.Name == "Z4");
        var z22 = groups.First(g => g.Name == "Z2^2");
        Assert.Equal(z4.N, z22.N);
        Assert.NotEqual(z4.TwoTorsion(), z22.TwoTorsion());

        // (c) 2-torsion INSUFFICIENT in general: Z2xZ8 and Z4xZ4 share order (16) AND
        //     2-torsion (4) yet differ in type — separated only by the full order-profile.
        var a = groups.First(g => g.Name == "Z2xZ8");
        var b = groups.First(g => g.Name == "Z4xZ4");
        Assert.Equal(a.N, b.N);                        // same order
        Assert.Equal(a.TwoTorsion(), b.TwoTorsion());  // same 2-torsion
        Assert.NotEqual(a.Fingerprint(), b.Fingerprint()); // order-profile still separates

        Log($"(b) Z4 2-tors={z4.TwoTorsion()} vs Z2^2 2-tors={z22.TwoTorsion()}  -> 2-torsion separates the order-4 pair.");
        Log($"(c) Z2xZ8 & Z4xZ4: |A|={a.N}, 2-tors={a.TwoTorsion()} (EQUAL) but profiles [{a.Fingerprint()}] vs [{b.Fingerprint()}] (DIFFER).");
        Log("FINDING: 2-torsion (deg-2 negation relation) is NOT a sufficient ring discriminator in general;");
        Log("         canonical inference needs the FULL order-profile => D1 must extract higher-degree gadget relations.");
    }

    // Annihilator count c_m(A) = |{ a : m·a = 0 }| = |{ a : ord(a) | m }|.
    // This is exactly what an "observe m·a" probe reads: at observation budget B you know c_1..c_B.
    // A degree-d gadget observes the multiple (d-1) [force d-1 peers equal, read the sum], so budget B <-> degree B+1.
    private static int Annih(Ab g, int m) { int c = 0; for (int i = 0; i < g.N; i++) if (m % g.Order(i) == 0) c++; return c; }
    private static int Exponent(Ab g) { int e = 1; for (int i = 0; i < g.N; i++) e = Lcm(e, g.Order(i)); return e; }

    // First budget m at which the annihilator sequences of two groups diverge (-1 = never, up to max exponent).
    private static int MinSepBudget(Ab x, Ab y)
    {
        int hi = Math.Max(Exponent(x), Exponent(y));
        for (int m = 1; m <= hi; m++) if (Annih(x, m) != Annih(y, m)) return m;
        return -1;
    }

    [Fact]
    public void RingInference_ObservationBudget_WorstCaseIsTheExponent()
    {
        Log("");
        Log("=== RING-INFERENCE PROBE (2026-07-11) — observation budget (gadget degree) to pin A ===");
        Log("annihilator sequence c_m = |{a : m·a=0}|, m=1..exp; budget B <-> gadget degree B+1.");
        Log(string.Format("{0,-10} {1,4} {2,4}   {3}", "group", "|A|", "exp", "c_1 c_2 c_3 ... c_exp"));
        Log(new string('-', 66));

        var z4 = new Ab("Z4", 4); var z22 = new Ab("Z2^2", 2, 2);
        var z8 = new Ab("Z8", 8); var z2z4 = new Ab("Z2xZ4", 2, 4);
        var z2z8 = new Ab("Z2xZ8", 2, 8); var z4z4 = new Ab("Z4xZ4", 4, 4);
        var z9 = new Ab("Z9", 9); var z33 = new Ab("Z3^2", 3, 3);

        foreach (var g in new[] { z4, z22, z8, z2z4, z2z8, z4z4, z9, z33 })
        {
            int e = Exponent(g);
            var seq = string.Join(" ", Enumerable.Range(1, e).Select(m => Annih(g, m).ToString()));
            Log(string.Format("{0,-10} {1,4} {2,4}   {3}", g.Name, g.N, e, seq));
        }
        Log("");

        // Some same-order pairs separate EARLY (well below the exponent) — bounded budget suffices there.
        int sep_8 = MinSepBudget(z8, z2z4);         // Z8 vs Z2xZ4: 2-torsion already differs (2 vs 4)
        Assert.Equal(2, sep_8);
        Assert.True(sep_8 < Math.Min(Exponent(z8), Exponent(z2z4)));  // 2 < 4 < 8

        // But there are WORST-CASE pairs that agree on every c_m below the exponent and split only AT it:
        int sep_16 = MinSepBudget(z2z8, z4z4);       // agree through c_3, split at c_4
        Assert.Equal(4, sep_16);
        Assert.Equal(Exponent(z4z4), sep_16);        // = the lower exponent (4)

        int sep_9 = MinSepBudget(z9, z33);           // odd groups: NO 2-torsion signal at all; split at c_3
        Assert.Equal(3, sep_9);
        Assert.Equal(Exponent(z33), sep_9);          // = the lower exponent (3)

        int sep_4 = MinSepBudget(z4, z22);           // the classic order-4 pair, at c_2
        Assert.Equal(2, sep_4);

        Log($"Z8 | Z2xZ4     split at budget {sep_8} (early: 2-torsion, << exp 8)");
        Log($"Z2xZ8 | Z4xZ4  split at budget {sep_16} = exp(Z4xZ4) (agree on c_1..c_3, split only at c_4)");
        Log($"Z9 | Z3^2      split at budget {sep_9} = exp(Z3^2) (no 2-torsion signal; needs the 3-torsion)");
        Log("FINDING: the WORST-CASE observation budget to canonically pin A is its EXPONENT => gadget degree ~ exp(A)+1.");
        Log("         Bounded gadget degree => only bounded-exponent rings inferable (= §11.6 ring-varying / unbounded-arity");
        Log("         flag floor). For a FIXED ring (bounded exp) it is bounded degree = poly.");
    }
}
