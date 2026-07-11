using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ─────────────────────────────────────────────────────────────────────────────
// FUSION-HARVEST PROBE (2026-07-11) — MEASUREMENT ONLY. Asserts nothing.
//
// Quantifies the "rigid decisions expose hidden symmetry" (fusion) mechanism by
// driving the REAL cascade-first descent and reading how much automorphism
// symmetry is harvested BEFORE vs AFTER the rigid (Phase-2) decisions.
//
//   A_stall = |harvested Aut subgroup| at the Phase-1/Phase-2 boundary, BEFORE any
//             rigid decision. Instrument = RecoveryOnly=true (ChainDescent.cs:176):
//             the descent consumes only symmetric cells and STOPS at the first
//             node where every cell is a real decision, leaving `Automorphisms`
//             = the symmetry-only harvest.
//   A_full  = |harvested Aut group| by the FULL normal descent
//             (RecoveryOnly=false, cascade + deferral on): r.ResidualGroup.Order.
//   |Aut|   = brute-force ground truth (FusionBatteryExperiment.BruteForceAutInfo,
//             capped at 3e6 node-visits; known values quoted where capped).
//   #rigid  = CascadeStats.Phase2Nodes on the full run (nodes where every cell was
//             a real decision — the deferred rigid residue that had to be branched).
//   nodes   = full-run descent-tree node count.
//
// Fusion signature = A_stall < A_full (== |Aut|). Control A_stall == A_full anchors.
//
// Helpers (FlatAdj, SeedFromTypes, OrbitProfile, Johnson, SeidelSwitch, ChangMask,
// ChangA/ChangB) are copied from RruDepthProbe.cs (private there). No production or
// existing test file is modified.
// ─────────────────────────────────────────────────────────────────────────────
public sealed class FusionHarvestProbe
{
    private static readonly string LogPath =
        "/tmp/claude-1000/-workspace/59f34b56-7c75-41c7-b064-94cd43f98d92/scratchpad/fusion.log";

    private readonly ITestOutputHelper _out;
    public FusionHarvestProbe(ITestOutputHelper o) => _out = o;

    private void Log(string line)
    {
        _out.WriteLine(line);
        File.AppendAllText(LogPath, line + "\n");
    }

    [Fact]
    public void FusionHarvest_StallVsFull()
    {
        Log("");
        Log("=== FUSION-HARVEST PROBE (2026-07-11) — A_stall (before rigid decisions) vs A_full (after) ===");
        Log(string.Format("{0,-24} {1,4} | {2,-12} {3,-12} {4,-14} | {5,-7} {6,-6} {7,-6} | {8}",
            "fixture", "n", "A_stall", "A_full", "|Aut| truth", "#rigid", "nodes", "orb(stall)", "A_stall<A_full?"));
        Log(new string('-', 130));

        // 1. Chang-A (n=28, |Aut|=384 = 2^7·3) — the ¬NoFusion case of interest.
        {
            int n; var t8 = Johnson(8, 2, out n);
            Measure("Chang-A (matching)", SeidelSwitch(t8, n, ChangMask(n, ChangA)), n, null, "known 384");
        }
        // 2. Chang-B (n=28, |Aut|=96).
        {
            int n; var t8 = Johnson(8, 2, out n);
            Measure("Chang-B (8-cycle)", SeidelSwitch(t8, n, ChangMask(n, ChangB)), n, null, "known 96");
        }
        // 3. CFI(K4) even (|Aut|=192) — the not-VT CFI.
        {
            var pair = CfiGraphGenerator.Generate("K4");
            Measure("CFI(K4) even", FlatAdj(pair.Even), pair.Even.VertexCount, null, "known 192");
        }
        // 4. rigid multipede control — expect |Aut|=1, A_stall==A_full==1.
        {
            var mp = MultipedeGenerator.BuildRandomRegular(8, 6, 3, seed: 0);
            MultipedeGenerator.AssertRigid(mp);
            Measure($"RigidMultipede({mp.BaseName})", FlatAdj(mp.Graph), mp.Graph.VertexCount,
                    mp.VertexTypes, "expect 1");
        }
        // 5. T(8) = J(8,2), n=28, |Aut|=|S8|=40320 — VT high-symmetry control.
        {
            int n; var t8 = Johnson(8, 2, out n);
            Measure("T(8) = J(8,2)", t8, n, null, "known 40320=|S8|");
        }
    }

    // Run RecoveryOnly (A_stall) and full (A_full) descents and log raw numbers.
    private void Measure(string name, int[] adj, int n, int[]? types, string autNote)
    {
        // A_stall: defer every real decision, stop at the Phase-1/Phase-2 boundary.
        var dStall = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        { EnableLinearOracle = true, EnableDeferral = true, RecoveryOnly = true };
        dStall.Canonize(SeedFromTypes(n, types), new WarmPartition(n));
        BigInteger aStall = dStall.Automorphisms.Order;
        var (orbStall, _) = OrbitProfile(dStall.Automorphisms, n);
        bool stuck = dStall.StuckResidual;

        // A_full: normal descent (cascade + deferral on, RecoveryOnly off).
        var dFull = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        { EnableLinearOracle = true, EnableDeferral = true };
        var r = dFull.Canonize(SeedFromTypes(n, types), new WarmPartition(n));
        BigInteger aFull = r.ResidualGroup.Order;
        long rigid = r.Stats.Cascade.Phase2Nodes;
        long nodes = r.Stats.NodeCount;
        bool flagged = r.Flagged;

        // |Aut| ground truth (brute force, capped).
        var (truth, capped, _) = FusionBatteryExperiment.BruteForceAutInfo(adj, n, types);
        string truthStr = capped ? "CAPPED" : truth.ToString();

        string fused = aStall < aFull ? "YES (fusion)" : (aStall == aFull ? "no" : "A_stall>A_full?!");

        Log(string.Format("{0,-24} {1,4} | {2,-12} {3,-12} {4,-14} | {5,-7} {6,-6} {7,-6} | orb(stall)={8} stuck={9} flag={10} | {11}  [{12}]",
            name, n, aStall, aFull, truthStr, rigid, nodes, "", orbStall, stuck ? "Y" : "n", flagged ? "Y" : "n", fused, autNote));
    }

    // ── copied plumbing (RruDepthProbe.cs private helpers) ────────────────────
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

    static (int orbits, int maxOrbit) OrbitProfile(PermutationGroup g, int n)
    {
        var seen = new bool[n]; int orbits = 0, max = 0;
        for (int i = 0; i < n; i++)
        {
            if (seen[i]) continue;
            var orb = g.Orbit(i);
            orbits++; if (orb.Length > max) max = orb.Length;
            foreach (var x in orb) seen[x] = true;
        }
        return (orbits, max);
    }

    static int[] Johnson(int n, int k, out int nv)
    {
        var sets = new List<int>();
        for (int m = 0; m < (1 << n); m++) if (System.Numerics.BitOperations.PopCount((uint)m) == k) sets.Add(m);
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
