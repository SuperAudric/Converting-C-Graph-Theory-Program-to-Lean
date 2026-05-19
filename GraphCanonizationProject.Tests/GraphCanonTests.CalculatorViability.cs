using Xunit;
using Canonizer;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using VertexType = int;
using EdgeType = int;

// Measurement-only tests for the §11.10 dependency-calculator viability study.
// For each input family, run the flip-validation canonizer with branch
// instrumentation enabled and report per-primary distinct-canonical counts.
//
// Hypothesis under test:
//   Route 1 (equivalence-detection sharing) is polynomial iff the per-primary
//   distinct-canonical count stays polynomial in n across all input families.
//   The naive cascade size is the *product* across primaries; route 1's
//   speedup comes from collapsing pair-orbit-equivalent branches at each
//   primary to a single representative. If max-distinct-per-primary blows
//   up on some family, route 1 cannot be polynomial regardless of how the
//   sharing is implemented.
//
// Output: one row per input graph with
//   prims        — number of primary positions visited (across all sweeps)
//   branches     — total non-baseline branches enumerated
//   maxDistinct  — max over primaries of distinct canonical outcomes
//   sumDistinct  — sum over primaries of distinct canonical outcomes
//   ratio        — sumDistinct / branches (low = lots of sharing opportunity)
//   timeMs       — wall-clock for the whole Run()
public partial class GraphCanonTests
{
    [Fact]
    public void CalculatorViability_DistinctBranchCount_AcrossFamilies()
    {
        var inputs = new List<(string name, EdgeType[,] adj)>();

        // Complete graphs: 1 pair-orbit per state, expect maxDistinct = 1.
        for (int n = 3; n <= 7; n++) inputs.Add(($"K_{n}", CompleteGraph(n)));

        // Simple cycles: ⌊n/2⌋ pair-orbits initially (distance classes).
        for (int n = 4; n <= 8; n++) inputs.Add(($"C_{n}", CycleGraph(n)));

        // Circulants (cycle + k-nearest-neighbour edges): more pair-orbits.
        inputs.Add(("C_6(1,2)",   CirculantGraph(6, 2)));
        inputs.Add(("C_8(1,2)",   CirculantGraph(8, 2)));
        inputs.Add(("C_8(1,2,3)", CirculantGraph(8, 3)));

        // Disjoint complete graphs: 2 pair-orbits (same-copy, cross-copy).
        inputs.Add(("2·K_3", DisjointGraph(CompleteGraph(3), CompleteGraph(3))));
        inputs.Add(("3·K_3", DisjointGraph(DisjointGraph(CompleteGraph(3), CompleteGraph(3)), CompleteGraph(3))));
        inputs.Add(("2·K_4", DisjointGraph(CompleteGraph(4), CompleteGraph(4))));

        // Path: low symmetry baseline.
        inputs.Add(("P_6", PathGraph(6)));
        inputs.Add(("P_8", PathGraph(8)));

        // Random graph: trivial Aut almost surely, 1-WL distinguishes quickly.
        var rand = GenerateRandomAdjacencyMatrix(7, 0.5f, seed: 12345);
        inputs.Add(("Random(n=7,p=0.5)", rand));

        // CFI(Cycle_k): the acid test for route 1. If maxDistinct explodes
        // as k grows here, route 1 falls over on the family the algorithm
        // cares about most. We test k = 3, 4, 5 to see the trend.
        foreach (int k in new[] { 3, 4, 5 })
        {
            var cfi = CfiGraphGenerator.Generate($"Cycle{k}");
            inputs.Add(($"CFI(Cycle{k}) Even", AdjToFlat(cfi.Even)));
            inputs.Add(($"CFI(Cycle{k}) Odd",  AdjToFlat(cfi.Odd)));
        }

        output.WriteLine(
            $"{"Graph",-22} {"n",4} {"prims",6} {"maxCa",6} {"maxCb",6} {"branches",10} {"maxDist",8} {"sumDist",8} {"ratio",6} {"timeMs",8}");

        foreach (var (name, adj) in inputs)
        {
            var canonizer = new CanonGraphOrdererFlipValidation { CollectBranchStats = true };
            int n = adj.GetLength(0);
            var verts = new VertexType[n];

            var sw = Stopwatch.StartNew();
            canonizer.Run_ToString(verts, adj);
            sw.Stop();

            var stats = canonizer.LastBranchStats!;
            int prims         = stats.Count;
            int totalBranches = stats.Sum(s => s.BranchCount);
            int maxCellA      = stats.Count > 0 ? stats.Max(s => s.CellSizeA) : 0;
            int maxCellB      = stats.Count > 0 ? stats.Max(s => s.CellSizeB) : 0;
            int maxDistinct   = stats.Count > 0 ? stats.Max(s => s.DistinctCanonicalCount) : 0;
            int sumDistinct   = stats.Sum(s => s.DistinctCanonicalCount);
            double ratio      = totalBranches > 0 ? (double)sumDistinct / totalBranches : 0;

            output.WriteLine(
                $"{name,-22} {n,4} {prims,6} {maxCellA,6} {maxCellB,6} {totalBranches,10} {maxDistinct,8} {sumDistinct,8} {ratio,6:F2} {sw.ElapsedMilliseconds,8}");
        }
    }

    // ── Graph generators ────────────────────────────────────────────────────

    private static EdgeType[,] CompleteGraph(int n)
    {
        var m = new EdgeType[n, n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                if (i != j) m[i, j] = 1;
        return m;
    }

    private static EdgeType[,] CycleGraph(int n)
    {
        var m = new EdgeType[n, n];
        for (int i = 0; i < n; i++)
            m[i, (i + 1) % n] = m[(i + 1) % n, i] = 1;
        return m;
    }

    private static EdgeType[,] CirculantGraph(int n, int k)
    {
        var m = new EdgeType[n, n];
        for (int i = 0; i < n; i++)
            for (int d = 1; d <= k; d++)
                m[i, (i + d) % n] = m[(i + d) % n, i] = 1;
        return m;
    }

    // C_n with edges at specific distances rather than 1..k inclusive.
    // Distinguishes "C_n(1,3)" from "C_n(1,2,3)".
    private static EdgeType[,] CirculantGraphAtDistances(int n, int[] distances)
    {
        var m = new EdgeType[n, n];
        for (int i = 0; i < n; i++)
            foreach (int d in distances)
                m[i, (i + d) % n] = m[(i + d) % n, i] = 1;
        return m;
    }

    private static EdgeType[,] DisjointGraph(EdgeType[,] a, EdgeType[,] b)
    {
        int na = a.GetLength(0);
        int nb = b.GetLength(0);
        int n  = na + nb;
        var m  = new EdgeType[n, n];
        for (int i = 0; i < na; i++)
            for (int j = 0; j < na; j++)
                m[i, j] = a[i, j];
        for (int i = 0; i < nb; i++)
            for (int j = 0; j < nb; j++)
                m[na + i, na + j] = b[i, j];
        return m;
    }

    private static EdgeType[,] PathGraph(int n)
    {
        var m = new EdgeType[n, n];
        for (int i = 0; i < n - 1; i++)
            m[i, i + 1] = m[i + 1, i] = 1;
        return m;
    }

    // Direct test of the disjoint-component-multiplies-state-space concern.
    // If state count for k disjoint copies of G scales linearly in k (~k·|S_G|),
    // the algorithm processes components sequentially and the DP memo is
    // additive. If it scales as |S_G|^k, the user's concern is correct and
    // the DP fails on disjoint-union inputs.
    [Fact]
    public void StateCount_DisjointComponents_ScalingTrend()
    {
        var inputs = new List<(string name, EdgeType[,] adj)>();

        // Baseline: single components.
        inputs.Add(("K_4 (single)",  CompleteGraph(4)));
        inputs.Add(("K_5 (single)",  CompleteGraph(5)));
        inputs.Add(("C_5 (single)",  CycleGraph(5)));
        inputs.Add(("C_6 (single)",  CycleGraph(6)));

        // Disjoint unions of K_4. Each K_4 alone has tiny state space; if
        // disjoint unions multiply, this becomes |S_K_4|^k.
        for (int k = 2; k <= 4; k++)
            inputs.Add(($"{k}·K_4", DisjointK(k, CompleteGraph(4))));
        for (int k = 2; k <= 4; k++)
            inputs.Add(($"{k}·K_5", DisjointK(k, CompleteGraph(5))));

        // Disjoint unions of cycles — slightly richer per-component state.
        for (int k = 2; k <= 3; k++)
            inputs.Add(($"{k}·C_5", DisjointK(k, CycleGraph(5))));
        for (int k = 2; k <= 3; k++)
            inputs.Add(($"{k}·C_6", DisjointK(k, CycleGraph(6))));

        // Disjoint unions of a CFI(Cycle3) "module" — the canonical hard case.
        // 1·CFI(Cycle3) had 40k states; if multiplicative, 2·CFI(Cycle3) → 1.6B.
        // Cap at 2 copies for feasibility.
        var cfi3 = CfiGraphGenerator.Generate("Cycle3");
        inputs.Add(("CFI(Cycle3) (single)", AdjToFlat(cfi3.Even)));
        inputs.Add(("2·CFI(Cycle3)", DisjointGraph(AdjToFlat(cfi3.Even), AdjToFlat(cfi3.Even))));

        // Mixed: K_4 ⊕ K_5 (non-isomorphic disjoint components).
        inputs.Add(("K_4 ⊕ K_5", DisjointGraph(CompleteGraph(4), CompleteGraph(5))));
        inputs.Add(("K_4 ⊕ C_5", DisjointGraph(CompleteGraph(4), CycleGraph(5))));
        inputs.Add(("K_4 ⊕ K_5 ⊕ C_6",
            DisjointGraph(DisjointGraph(CompleteGraph(4), CompleteGraph(5)), CycleGraph(6))));

        output.WriteLine(
            $"{"Graph",-25} {"n",4} {"prims",6} {"sweeps",7} {"states",10} {"states/n²",10} {"timeMs",10}");

        foreach (var (name, adj) in inputs)
        {
            var canonizer = new CanonGraphOrdererFlipValidation { CollectStateCount = true };
            int n = adj.GetLength(0);
            var verts = new VertexType[n];

            var sw = Stopwatch.StartNew();
            canonizer.Run_ToString(verts, adj);
            sw.Stop();

            int prims  = canonizer.LastPrimaryCount;
            int sweeps = canonizer.LastSweepCount;
            int states = canonizer.LastDistinctStateCount;
            double normalized = (double)states / (n * n);

            output.WriteLine(
                $"{name,-25} {n,4} {prims,6} {sweeps,7} {states,10} {normalized,10:F2} {sw.ElapsedMilliseconds,10}");
        }
    }

    // Build a necklace of k CFI(Cycle3) copies, connected by single bridge
    // edges from vertex 1 of copy i to vertex 0 of copy (i+1). With
    // `closed=true`, an extra bridge closes the necklace into a cycle.
    // Modular decomposition does NOT detect the components here because
    // bridges are between specific vertices, not modules. Each component's
    // local parity choices remain ~independent; if the algorithm processes
    // them independently in its state space, state count multiplies → the
    // adversarial case route 1 should fail on.
    private static EdgeType[,] NecklaceOfCfi(int k, string baseName, bool closed)
    {
        var cfi = CfiGraphGenerator.Generate(baseName);
        var component = AdjToFlat(cfi.Even);
        int componentSize = component.GetLength(0);
        int n = componentSize * k;
        var m = new EdgeType[n, n];

        // Copy each component into its offset block.
        for (int copy = 0; copy < k; copy++)
        {
            int offset = copy * componentSize;
            for (int i = 0; i < componentSize; i++)
                for (int j = 0; j < componentSize; j++)
                    m[offset + i, offset + j] = component[i, j];
        }

        // Bridges: vertex 1 of copy i — vertex 0 of copy (i+1).
        int bridgeCount = closed ? k : k - 1;
        for (int i = 0; i < bridgeCount; i++)
        {
            int from = i * componentSize + 1;
            int to   = ((i + 1) % k) * componentSize + 0;
            m[from, to] = 1;
            m[to, from] = 1;
        }

        return m;
    }

    // Necklace-of-CFI test: the structurally hardest adversarial case for
    // route 1. Modular decomposition can't factor this graph (bridges are
    // single edges between specific vertices, not modules). If state count
    // grows multiplicatively with k, route 1 is exponential.
    [Fact]
    public void StateCount_NecklaceOfCfi_ExponentTest()
    {
        var inputs = new List<(string name, EdgeType[,] adj)>
        {
            ("CFI(C3) (single)",      AdjToFlat(CfiGraphGenerator.Generate("Cycle3").Even)),
            ("2·CFI(C3) disjoint",    DisjointGraph(
                AdjToFlat(CfiGraphGenerator.Generate("Cycle3").Even),
                AdjToFlat(CfiGraphGenerator.Generate("Cycle3").Even))),
            ("Necklace(2, Cycle3) open",   NecklaceOfCfi(2, "Cycle3", closed: false)),
            ("Necklace(2, Cycle3) closed", NecklaceOfCfi(2, "Cycle3", closed: true)),
            ("Necklace(3, Cycle3) open",   NecklaceOfCfi(3, "Cycle3", closed: false)),
        };

        output.WriteLine(
            $"{"Graph",-30} {"n",4} {"prims",6} {"sweeps",7} {"states",10} {"states/n²",10} {"timeMs",10}");

        foreach (var (name, adj) in inputs)
        {
            var canonizer = new CanonGraphOrdererFlipValidation { CollectStateCount = true };
            int n = adj.GetLength(0);
            var verts = new VertexType[n];

            var sw = Stopwatch.StartNew();
            canonizer.Run_ToString(verts, adj);
            sw.Stop();

            int prims  = canonizer.LastPrimaryCount;
            int sweeps = canonizer.LastSweepCount;
            int states = canonizer.LastDistinctStateCount;
            double normalized = (double)states / (n * n);

            output.WriteLine(
                $"{name,-30} {n,4} {prims,6} {sweeps,7} {states,10} {normalized,10:F2} {sw.ElapsedMilliseconds,10}");
        }
    }

    // Build k disjoint copies of the same graph g.
    private static EdgeType[,] DisjointK(int k, EdgeType[,] g)
    {
        var result = g;
        for (int i = 1; i < k; i++)
            result = DisjointGraph(result, g);
        return result;
    }

    // L4.3-memo-polynomial verification. For each input, run the algorithm
    // with state-count collection enabled; report distinct intermediate
    // P-state count alongside primary count, sweep count, and time. The DP
    // calculator's memo size is bounded above by this count, so if it stays
    // polynomial in n across the problematic families (C_n(1,2), CFI), the
    // DP design is structurally viable.
    [Fact]
    public void StateCount_MemoSizeBound_AcrossFamilies()
    {
        var inputs = new List<(string name, EdgeType[,] adj)>();

        // Focus on the families where the L4.3 single-sweep test mismatched
        // (C_n(1,2)) plus the CFI cascade-rich family. K_n included as a
        // baseline (expect tiny state counts).
        for (int n = 3; n <= 7; n++) inputs.Add(($"K_{n}", CompleteGraph(n)));
        foreach (int n in new[] { 6, 8, 10, 12, 14, 16, 20, 24 })
            inputs.Add(($"C_{n}(1,2)", CirculantGraph(n, 2)));
        foreach (int n in new[] { 8, 10, 12, 16, 20 })
            inputs.Add(($"C_{n}(1,2,3)", CirculantGraph(n, 3)));
        foreach (int k in new[] { 3, 4, 5 })
        {
            var cfi = CfiGraphGenerator.Generate($"Cycle{k}");
            inputs.Add(($"CFI(Cycle{k}) Even", AdjToFlat(cfi.Even)));
        }

        output.WriteLine(
            $"{"Graph",-22} {"n",4} {"prims",6} {"sweeps",7} {"states",8} {"states/n²",10} {"timeMs",8}");

        foreach (var (name, adj) in inputs)
        {
            var canonizer = new CanonGraphOrdererFlipValidation { CollectStateCount = true };
            int n = adj.GetLength(0);
            var verts = new VertexType[n];

            var sw = Stopwatch.StartNew();
            canonizer.Run_ToString(verts, adj);
            sw.Stop();

            int prims  = canonizer.LastPrimaryCount;
            int sweeps = canonizer.LastSweepCount;
            int states = canonizer.LastDistinctStateCount;
            double normalized = (double)states / (n * n);

            output.WriteLine(
                $"{name,-22} {n,4} {prims,6} {sweeps,7} {states,8} {normalized,10:F2} {sw.ElapsedMilliseconds,8}");
        }
    }

    // L4.3 (single-pass equivalence) verification. For each input, run with
    // and without fixpoint iteration; compare canonicals. If they always
    // match, the deeper primaries' decisions are determined by shallower +
    // branch (the local-cascade-dependence conjecture). That's the structural
    // claim that lets the calculator be a single-pass evaluator.
    //
    // The "sweeps" column on the fixpoint side shows how many sweeps were
    // actually needed; if always 1, single-pass holds trivially. Values
    // greater than 1 indicate the fixpoint is doing real work — those are
    // the diagnostic cases.
    [Fact]
    public void LocalCascadeDependence_SingleSweep_MatchesFixpoint()
    {
        var inputs = new List<(string name, EdgeType[,] adj)>();

        // Same battery as CalculatorViability_DistinctBranchCount, minus the
        // slow CFI cases (K4 is its own test).
        for (int n = 3; n <= 7; n++) inputs.Add(($"K_{n}", CompleteGraph(n)));
        for (int n = 4; n <= 8; n++) inputs.Add(($"C_{n}", CycleGraph(n)));
        // Circulants: the C_8(1,2) counterexample lives here. Scan more
        // to see if sweep count grows with n or stays bounded.
        foreach (int n in new[] { 6, 7, 8, 9, 10, 11, 12, 14, 16, 20, 24 })
            inputs.Add(($"C_{n}(1,2)", CirculantGraph(n, 2)));
        foreach (int n in new[] { 8, 9, 10, 11, 12, 14, 16, 20 })
            inputs.Add(($"C_{n}(1,2,3)", CirculantGraph(n, 3)));
        foreach (int n in new[] { 10, 12, 14, 16 })
            inputs.Add(($"C_{n}(1,3)", CirculantGraphAtDistances(n, [1, 3])));
        foreach (int n in new[] { 10, 12, 14, 16 })
            inputs.Add(($"C_{n}(1,4)", CirculantGraphAtDistances(n, [1, 4])));
        inputs.Add(("2·K_3", DisjointGraph(CompleteGraph(3), CompleteGraph(3))));
        inputs.Add(("3·K_3", DisjointGraph(DisjointGraph(CompleteGraph(3), CompleteGraph(3)), CompleteGraph(3))));
        inputs.Add(("2·K_4", DisjointGraph(CompleteGraph(4), CompleteGraph(4))));
        inputs.Add(("P_6", PathGraph(6)));
        inputs.Add(("P_8", PathGraph(8)));
        // Random graphs at various densities and sizes.
        for (int seed = 0; seed < 5; seed++)
            inputs.Add(($"Random(n=8,p=0.5,seed={seed})", GenerateRandomAdjacencyMatrix(8, 0.5f, seed: seed)));

        // CFI inputs — the cases where pair-orbit ambiguity is densest.
        foreach (int k in new[] { 3, 4, 5 })
        {
            var cfi = CfiGraphGenerator.Generate($"Cycle{k}");
            inputs.Add(($"CFI(Cycle{k}) Even", AdjToFlat(cfi.Even)));
            inputs.Add(($"CFI(Cycle{k}) Odd",  AdjToFlat(cfi.Odd)));
        }

        output.WriteLine(
            $"{"Graph",-22} {"n",4} {"sweeps",7} {"singleSweep",13} {"fixpoint",10} {"match",6}");

        int mismatches = 0;
        foreach (var (name, adj) in inputs)
        {
            int n = adj.GetLength(0);
            var verts = new VertexType[n];

            var fp = new CanonGraphOrdererFlipValidation();
            string fpResult = fp.Run_ToString(verts, adj);

            var ss = new CanonGraphOrdererFlipValidation { SkipFixpoint = true };
            string ssResult = ss.Run_ToString(verts, adj);

            bool match = fpResult == ssResult;
            if (!match) mismatches++;

            output.WriteLine(
                $"{name,-22} {n,4} {fp.LastSweepCount,7} {Hash8(ssResult),13} {Hash8(fpResult),10} {(match ? "yes" : "NO"),6}");
        }

        output.WriteLine($"Mismatches: {mismatches} / {inputs.Count}");
        // No assertion — this is exploratory. The mismatch count is the
        // headline number.
    }

    private static string Hash8(string s)
    {
        ulong h = 14695981039346656037UL;
        foreach (char c in s) { h ^= c; h *= 1099511628211UL; }
        return h.ToString("x8")[..8];
    }

    // Separate slow test for richer CFI bases. K4 (40 vertices) is the
    // smallest "non-cycle" base; the n^5-ish trend on Cycle_k predicts ~2
    // minutes per case. Run on demand: it's gated by a separate filter.
    [Fact]
    public void CalculatorViability_DistinctBranchCount_CfiK4()
    {
        var cfi = CfiGraphGenerator.Generate("K4");
        var inputs = new[]
        {
            ("CFI(K4) Even", AdjToFlat(cfi.Even)),
            ("CFI(K4) Odd",  AdjToFlat(cfi.Odd)),
        };

        output.WriteLine(
            $"{"Graph",-22} {"n",4} {"prims",6} {"maxCa",6} {"maxCb",6} {"branches",10} {"maxDist",8} {"sumDist",8} {"ratio",6} {"timeMs",8}");

        foreach (var (name, adj) in inputs)
        {
            var canonizer = new CanonGraphOrdererFlipValidation { CollectBranchStats = true };
            int n = adj.GetLength(0);
            var verts = new VertexType[n];

            var sw = Stopwatch.StartNew();
            canonizer.Run_ToString(verts, adj);
            sw.Stop();

            var stats = canonizer.LastBranchStats!;
            int prims         = stats.Count;
            int totalBranches = stats.Sum(s => s.BranchCount);
            int maxCellA      = stats.Count > 0 ? stats.Max(s => s.CellSizeA) : 0;
            int maxCellB      = stats.Count > 0 ? stats.Max(s => s.CellSizeB) : 0;
            int maxDistinct   = stats.Count > 0 ? stats.Max(s => s.DistinctCanonicalCount) : 0;
            int sumDistinct   = stats.Sum(s => s.DistinctCanonicalCount);
            double ratio      = totalBranches > 0 ? (double)sumDistinct / totalBranches : 0;

            output.WriteLine(
                $"{name,-22} {n,4} {prims,6} {maxCellA,6} {maxCellB,6} {totalBranches,10} {maxDistinct,8} {sumDistinct,8} {ratio,6:F2} {sw.ElapsedMilliseconds,8}");
        }
    }

    private static EdgeType[,] AdjToFlat(AdjMatrix a)
    {
        int n = a.VertexCount;
        var m = new EdgeType[n, n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                m[i, j] = a[i, j];
        return m;
    }
}
