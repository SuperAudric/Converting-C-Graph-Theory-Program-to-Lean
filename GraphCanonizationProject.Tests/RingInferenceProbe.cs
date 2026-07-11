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
}
