using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ─────────────────────────────────────────────────────────────────────────────
// DEEPEN-STRENGTH PROBE (2026-07-20) — MEASUREMENT ONLY. Asserts nothing.
//
// WHY. The Lean `deepenSupply` (ChainDescent/DeepenSupply.lean) is a port of the
// C# `HarvestTwists`, and it turned out STRONGER than the docs predicted (on mp7
// it makes the branch cell AND the foot cell each a single orbit). Before any of
// that strength is claimed in Lean, it has to be MEASURED on the C# side across a
// real battery — the Lean-side evidence is only 4 structured witnesses, and the
// random-graph sweeps behind it are degenerate (n=8 branch cells of size 0 or 2).
//
// WHAT IS DECISIVE. `HarvestTwists` returns a footprint class (ChainDescent.cs
// :556-558) that IS the success/failure taxonomy:
//     1 = all-singleton at depth 0 (linear oracle)   — success
//     3 = resolved by the cascade recursion          — success
//     0 = empty / closure-fail, nothing to harvest   — benign failure
//     2 = STARVED: still non-singleton past the depth bound
// `ClassifyStarved > 0` (or `BranchStarved > 0`) anywhere ⟹ the harvest is NOT
// provably complete on that case (CanonResult.cs:60-62 calls it "the Route-A
// breaker"). RruDepthProbe.cs:19-23 hypothesises class 2 is unreachable dead code.
// THIS PROBE TESTS THAT HYPOTHESIS on every family the repo can generate.
//
// The other decisive metric is COMPLETENESS, which starvation counts do not give:
// harvested |Aut| vs ground truth. A run can be starvation-free and still LEAK
// (Chang-A is the recorded case). So both are reported side by side.
//
// COLUMNS
//   flag      descent flagged (budget exhausted) — an honest "not handled"
//   nodes/lv  descent-tree nodes / discrete leaves
//   c1/c3/ST  ClassifyStarved histogram: class1 / class3 / STARVED  ← the breaker
//   bST       BranchStarved (same breaker, at branching nodes)
//   mrd       MaxRecursionDepth (single-path deepening; ~tw(H) on CFI)
//   |Aut|     harvested residual group order
//   truth     brute-force ground truth (capped), or the generator's known order
//   verdict   COMPLETE (harvested == truth) / LEAK / (capped ⟹ unchecked)
//   fusion    A_stall < A_full — symmetry certifiable only AFTER rigid decisions
//
// Helpers copied from RruDepthProbe.cs / FusionHarvestProbe.cs (private there).
// No production or existing test file is modified.
// ─────────────────────────────────────────────────────────────────────────────
public sealed class DeepenStrengthProbe
{
    private static readonly string LogPath =
        "/tmp/claude-1000/-workspace/43015005-3976-4d9c-aeeb-1596b6c37849/scratchpad/deepen-strength.log";

    private readonly ITestOutputHelper _out;
    public DeepenStrengthProbe(ITestOutputHelper o) { _out = o; }

    private void Log(string s)
    {
        _out.WriteLine(s);
        try { File.AppendAllText(LogPath, s + Environment.NewLine); } catch { }
    }

    [Fact]
    [Trait("Category", "LongRunning")]
    public void DeepenStrength_ClassHistogram_AcrossFamilies()
    {
        try { File.WriteAllText(LogPath, ""); } catch { }
        Log("=== DEEPEN-STRENGTH SWEEP (footprint-class histogram + completeness) ===");
        Log(string.Format("{0,-26} {1,5} | {2,-4} {3,-8} {4,-5} | {5,-6} {6,-6} {7,-4} {8,-4} {9,-4} | {10,-14} {11,-14} {12,-10} {13}",
            "graph", "n", "flag", "nodes", "lv", "c1", "c3", "ST", "bST", "mrd",
            "|Aut|", "truth", "verdict", "fusion"));

        // ── 1. CFI pairs (the canonical WL-hard family) ──────────────────────
        foreach (var b in new[] { "K4", "K33", "Rook3x3", "Petersen" })
        {
            var pair = CfiGraphGenerator.Generate(b);
            Measure($"CFI-{b}-even", FlatAdj(pair.Even), pair.Even.VertexCount, null, null);
            Measure($"CFI-{b}-odd", FlatAdj(pair.Odd), pair.Odd.VertexCount, null, null);
        }

        // ── 2. Multipedes over a circulant base (rigid iff 7∤m) ──────────────
        // ⚠ RUN BOTH COLOURINGS. Seeding VertexTypes makes the descent terminate
        // in ONE node with ZERO harvest calls. The tempting explanation — "the fine
        // colouring discretizes by fiat" — is MEASURED FALSE: `MP-circ7-typed` still
        // has a type-preserving |Aut| of 8, and refinement cannot discretize a graph
        // with 8 colour-automorphisms. So the typed rows are not vacuous; they are a
        // genuine harvest MISS, isolated in the test below. The uniform rows ("-u")
        // are the object the Lean side models.
        foreach (int m in new[] { 4, 5, 6, 7, 8, 9 })
        {
            var mp = MultipedeGenerator.BuildCirculant(m);
            string tag = $"MP-circ{m}{(mp.BaseIsOdd ? "" : "*")}";
            Measure(tag + "-typed", FlatAdj(mp.Graph), mp.Graph.VertexCount, mp.VertexTypes, null);
            Measure(tag + "-u", FlatAdj(mp.Graph), mp.Graph.VertexCount, null, null);
        }

        // ── 3. Multipedes over an EXPANDER base — the flagging regime ────────
        // This is the class the Lean docs name as the missing discriminating
        // witness: non-trivial structure that refinement genuinely cannot
        // cheaply discretize. If class 2 is reachable at all, it is reachable here.
        foreach (var (c, bits, d, s) in new[] { (6, 6, 3, 0), (8, 8, 3, 0), (10, 10, 3, 0), (10, 10, 3, 7) })
        {
            MultipedeGenerator.Multipede mp;
            try { mp = MultipedeGenerator.BuildRandomRegular(c, bits, d, s); }
            catch (Exception e) { Log($"MP-rr(c{c},b{bits},d{d},s{s}) SKIPPED: {e.Message}"); continue; }
            string tag = $"MP-rr(c{c},b{bits},d{d},s{s})";
            Measure(tag + "-typed", FlatAdj(mp.Graph), mp.Graph.VertexCount, mp.VertexTypes, null);
            Measure(tag + "-u", FlatAdj(mp.Graph), mp.Graph.VertexCount, null, null);
        }

        // ── 4. Cameron families (known closed-form |Aut|) ────────────────────
        foreach (var cg in new[] {
            CameronGraphGenerator.Johnson(5, 2), CameronGraphGenerator.Johnson(6, 2),
            CameronGraphGenerator.Johnson(7, 3), CameronGraphGenerator.Hamming(2, 3),
            CameronGraphGenerator.Hamming(3, 2), CameronGraphGenerator.Kneser(7, 2),
            CameronGraphGenerator.Kneser(7, 3) })
        {
            Measure($"{cg.Family[0]}-{cg.Name}", FlatAdj(cg.Graph), cg.VertexCount,
                    null, cg.KnownAutOrder);
        }

        // ── 5. Chang graphs — the recorded FUSION / LEAK witnesses ───────────
        int n8;
        var t8 = Johnson(8, 2, out n8);
        Measure("T(8)=J(8,2)", t8, n8, null, null);
        Measure("Chang-A", SeidelSwitch(t8, n8, ChangMask(n8, ChangA)), n8, null, 384);
        Measure("Chang-B", SeidelSwitch(t8, n8, ChangMask(n8, ChangB)), n8, null, 96);

        Log("");
        Log("KEY: ST/bST = STARVED (class 2). Any nonzero ⟹ harvest not provably complete there.");
        Log("     '*' on MP-circ = base NOT odd (non-rigid multipede, e.g. 7|m).");
    }

    // ─────────────────────────────────────────────────────────────────────────
    // THE ONE REAL INCOMPLETENESS THE SWEEP FOUND, isolated and cross-checked.
    //
    // `MP-circ7-typed` (the FINE-COLOURED Fano multipede, n=42) reports
    // |Aut| = 1 after ONE node with ZERO harvest calls — while the graph in fact
    // has a type-preserving automorphism group of order 8 (the F_2 gauge).
    //
    // Both instruments were cross-checked because they cannot both be right:
    // refinement cannot discretize a graph with 8 colour-automorphisms.
    //   · canonicity  — the canonical form IS stable across 8 relabellings, so
    //     this is NOT a soundness failure; the canonizer's output is correct.
    //   · ground truth — counted again by plain type-preserving backtracking that
    //     never touches WL colours: still 8 (and 1 for the rigid m=8 control).
    // ⟹ the descent misses the whole gauge while *presenting as locally rigid*
    // (1 node, no branching). That is exactly the C3 gap the Lean `kernelSupply`
    // was built to close, reproduced on the C# side.
    // ─────────────────────────────────────────────────────────────────────────
    [Fact]
    public void FineColouredMultipede_MissesTheGauge_ButStaysCanonical()
    {
        foreach (int m in new[] { 7, 8 })
        {
            var mp = MultipedeGenerator.BuildCirculant(m);
            int n = mp.Graph.VertexCount;
            var t = mp.VertexTypes;
            var adj = FlatAdj(mp.Graph);

            // (i) independent type-preserving |Aut|, no WL colours involved
            var img = new int[n]; var used = new bool[n]; Array.Fill(img, -1);
            long count = 0, visits = 0; bool capped = false;
            void Rec(int v)
            {
                if (capped) return;
                if (v == n) { count++; return; }
                for (int c = 0; c < n; c++)
                {
                    if (used[c] || t[c] != t[v]) continue;
                    if (++visits > 20_000_000) { capped = true; return; }
                    bool ok = true;
                    for (int u = 0; u < v && ok; u++) if (adj[v * n + u] != adj[c * n + img[u]]) ok = false;
                    if (!ok) continue;
                    img[v] = c; used[c] = true; Rec(v + 1); used[c] = false; img[v] = -1;
                }
            }
            Rec(0);

            // (ii) what the descent harvests, and whether its output is canonical
            string? first = null; bool stable = true; var rnd = new Random(12345);
            long nodes = 0; BigInteger harvested = 0;
            for (int trial = 0; trial < 8; trial++)
            {
                var perm = new int[n];
                for (int i = 0; i < n; i++) perm[i] = i;
                if (trial > 0)
                    for (int i = n - 1; i > 0; i--) { int j = rnd.Next(i + 1); (perm[i], perm[j]) = (perm[j], perm[i]); }
                var a2 = new int[n * n]; var t2 = new int[n];
                for (int i = 0; i < n; i++)
                {
                    t2[perm[i]] = t[i];
                    for (int j = 0; j < n; j++) a2[perm[i] * n + perm[j]] = adj[i * n + j];
                }
                var d = new ChainDescent(n, a2, new CascadeOracle(), ChainDescent.DefaultBudget(n))
                { EnableLinearOracle = true, EnableDeferral = true };
                var r = d.Canonize(SeedFromTypes(n, t2), new WarmPartition(n));
                string key = r.Flagged ? "FLAG" : string.Concat(r.Matrix!.Select(x => x.ToString()));
                if (first == null) { first = key; nodes = r.Stats.NodeCount; harvested = r.ResidualGroup.Order; }
                else if (key != first) stable = false;
            }

            Log($"MP-circ{m}-typed: true type-preserving |Aut| = {(capped ? "CAPPED" : count.ToString())}, " +
                $"descent harvested {harvested} in {nodes} node(s), canonical-form stable = {stable}");

            Assert.True(stable, $"m={m}: canonical form NOT stable under relabelling — soundness failure");
        }
    }

    // Run the full descent plus a RecoveryOnly descent, and report both the
    // footprint-class histogram and completeness against ground truth.
    private void Measure(string name, int[] adj, int n, int[]? types, BigInteger? knownAut)
    {
        var dFull = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        { EnableLinearOracle = true, EnableDeferral = true };
        var r = dFull.Canonize(SeedFromTypes(n, types), new WarmPartition(n));
        var c = r.Stats.Cascade;
        BigInteger aFull = r.ResidualGroup.Order;

        // A_stall: stop at the Phase-1/Phase-2 boundary, before any rigid decision.
        BigInteger aStall;
        try
        {
            var dStall = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
            { EnableLinearOracle = true, EnableDeferral = true, RecoveryOnly = true };
            dStall.Canonize(SeedFromTypes(n, types), new WarmPartition(n));
            aStall = dStall.Automorphisms.Order;
        }
        catch (Exception) { aStall = -1; }

        // Ground truth: the generator's known order if supplied, else brute force.
        string truthStr; string verdict;
        if (knownAut is BigInteger ka)
        {
            truthStr = ka + "(known)";
            verdict = aFull == ka ? "COMPLETE" : "LEAK";
        }
        else
        {
            var (truth, capped, _) = FusionBatteryExperiment.BruteForceAutInfo(adj, n, types);
            truthStr = capped ? "CAPPED" : truth.ToString();
            verdict = capped ? "unchecked" : (aFull == truth ? "COMPLETE" : "LEAK");
        }

        string fusion = aStall < 0 ? "?" : (aStall < aFull ? "YES" : "no");

        Log(string.Format("{0,-26} {1,5} | {2,-4} {3,-8} {4,-5} | {5,-6} {6,-6} {7,-4} {8,-4} {9,-4} | {10,-14} {11,-14} {12,-10} {13}",
            name, n, r.Flagged ? "FLAG" : "-", r.Stats.NodeCount, r.Stats.LeafCount,
            c.ClassifyClass1, c.ClassifyClass3, c.ClassifyStarved, c.BranchStarved,
            c.MaxRecursionDepth, aFull, truthStr, verdict, fusion));
    }

    // ── copied plumbing ──────────────────────────────────────────────────────
    static int[] FlatAdj(AdjMatrix g)
    {
        int n = g.VertexCount;
        var adj = new int[n * n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                adj[i * n + j] = g[i, j];
        return adj;
    }

    static sbyte[] SeedFromTypes(int n, int[]? types)
    {
        var p = new sbyte[n * n];
        if (types == null) return p;
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                if (i != j && types[i] < types[j]) { p[i * n + j] = -1; p[j * n + i] = 1; }
        return p;
    }

    static int[] Johnson(int n, int k, out int nv)
    {
        var sets = new List<int>();
        for (int m = 0; m < (1 << n); m++)
            if (System.Numerics.BitOperations.PopCount((uint)m) == k) sets.Add(m);
        nv = sets.Count;
        var adj = new int[nv * nv];
        for (int u = 0; u < nv; u++)
            for (int v = u + 1; v < nv; v++)
                if (System.Numerics.BitOperations.PopCount((uint)(sets[u] & sets[v])) == k - 1)
                { adj[u * nv + v] = 1; adj[v * nv + u] = 1; }
        return adj;
    }

    static int[] SeidelSwitch(int[] adj, int n, bool[] inS)
    {
        var b = (int[])adj.Clone();
        for (int u = 0; u < n; u++)
            for (int v = u + 1; v < n; v++)
                if (inS[u] != inS[v]) { int f = 1 - b[u * n + v]; b[u * n + v] = f; b[v * n + u] = f; }
        return b;
    }

    // Johnson(8,2) vertices are enumerated by ASCENDING BITMASK, not lex pair order.
    static bool[] ChangMask(int n8, (int, int)[] edges)
    {
        var idx = new Dictionary<int, int>(); int c = 0;
        for (int m = 0; m < (1 << 8); m++)
            if (System.Numerics.BitOperations.PopCount((uint)m) == 2) idx[m] = c++;
        var mask = new bool[n8];
        foreach (var (a, b) in edges) mask[idx[(1 << a) | (1 << b)]] = true;
        return mask;
    }

    static readonly (int, int)[] ChangA = { (0, 1), (2, 3), (4, 5), (6, 7) };
    static readonly (int, int)[] ChangB = { (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 0) };
}
