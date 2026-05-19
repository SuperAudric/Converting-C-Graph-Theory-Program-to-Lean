using Xunit;
using Xunit.Abstractions;
using Canonizer;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using VertexType = int;
using EdgeType = int;

// Phase 1 measurement tests for the rotation-coupling calculator.
//
// These tests do not assert correctness of the canonical; they run the
// single-flip probing instrumentation (CanonGraphOrdererFlipValidation
// .ProbeRotationsSingleFlip) and emit a report to the test output. The
// purpose is empirical measurement of the load-bearing assumption that
// powers the layered-DAG calculator design (see
// docs/flip-validation-calculator.md, T-C):
//
//   The boolean functions arising from per-layer constraint substitution
//   stay in AND-of-XOR (linear over Z₂) — equivalently, the rotation-
//   variable couplings on every P entry fit XOR structure.
//
// Phase 1 surfaces the raw data Phase 2 (XOR-fit) would consume: which
// rotation alternatives change the baseline P (the "false symmetries")
// and how many P entries get moved by multiple alternatives ("coupling
// candidates").
//
// Light assertions guard the instrumentation itself; the diagnostic
// value is the reports.
public partial class GraphCanonTests
{
    private readonly CanonGraphOrdererFlipValidation _calcFv = new();

    // ── Small worked cases ─────────────────────────────────────────────────

    [Fact]
    public void CV_Probe_TwoDisjointPair()
    {
        var edges = BuildGraph((0, 1), (2, 3));
        RunProbe("2K2 (size 4)", EmptyVerts(edges), edges);
    }

    [Fact]
    public void CV_Probe_K4()
    {
        var edges = BuildGraph((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3));
        RunProbe("K4 (size 4)", EmptyVerts(edges), edges);
    }

    [Fact]
    public void CV_Probe_C4()
    {
        var edges = BuildGraph((0, 1), (1, 2), (2, 3), (3, 0));
        RunProbe("C4 (size 4)", EmptyVerts(edges), edges);
    }

    [Fact]
    public void CV_Probe_C4_Plus_K2()
    {
        // C4 + K2 — the smallest graph in the corpus with a multi-orbit cell,
        // and the specific structure that originally failed §6.5 before
        // pair rotation was implemented.
        var edges = BuildGraph((0, 1), (1, 2), (2, 3), (3, 0), (4, 5));
        RunProbe("C4 + K2 (size 6)", EmptyVerts(edges), edges);
    }

    [Fact]
    public void CV_Probe_3Cycle_Plus_3Cycle()
    {
        // Two disjoint triangles — like 2K2 but with internal pair-orbit
        // structure in each component.
        var edges = BuildGraph((0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3));
        RunProbe("C3 + C3 (size 6)", EmptyVerts(edges), edges);
    }

    // ── CFI: the load-bearing case ─────────────────────────────────────────

    [Fact]
    public void CV_Probe_CFI_Cycle3_Even()
    {
        var pair = CfiGraphGenerator.Generate("Cycle3");
        RunProbe($"CFI(Cycle3) even — {pair.VertexRoles.Length} vertices", new VertexType[pair.Even.VertexCount], pair.Even);
    }

    [Fact]
    public void CV_Probe_CFI_Cycle3_Odd()
    {
        var pair = CfiGraphGenerator.Generate("Cycle3");
        RunProbe($"CFI(Cycle3) odd — {pair.VertexRoles.Length} vertices", new VertexType[pair.Odd.VertexCount], pair.Odd);
    }

    // ── Phase 2: XOR-fit per coupling-candidate entry ──────────────────────

    [Fact]
    public void CV_XorFit_TwoDisjointPair()
    {
        var edges = BuildGraph((0, 1), (2, 3));
        RunXorFit("2K2 (size 4)", EmptyVerts(edges), edges);
    }

    [Fact]
    public void CV_XorFit_K4()
    {
        var edges = BuildGraph((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3));
        RunXorFit("K4 (size 4)", EmptyVerts(edges), edges);
    }

    [Fact]
    public void CV_XorFit_C4()
    {
        var edges = BuildGraph((0, 1), (1, 2), (2, 3), (3, 0));
        RunXorFit("C4 (size 4)", EmptyVerts(edges), edges);
    }

    [Fact]
    public void CV_XorFit_C4_Plus_K2()
    {
        var edges = BuildGraph((0, 1), (1, 2), (2, 3), (3, 0), (4, 5));
        RunXorFit("C4 + K2 (size 6)", EmptyVerts(edges), edges);
    }

    [Fact]
    public void CV_XorFit_CFI_Cycle3_Even()
    {
        var pair = CfiGraphGenerator.Generate("Cycle3");
        RunXorFit($"CFI(Cycle3) even — {pair.Even.VertexCount} vertices",
                  new VertexType[pair.Even.VertexCount], pair.Even);
    }

    [Fact]
    public void CV_XorFit_CFI_Cycle3_Odd()
    {
        var pair = CfiGraphGenerator.Generate("Cycle3");
        RunXorFit($"CFI(Cycle3) odd — {pair.Odd.VertexCount} vertices",
                  new VertexType[pair.Odd.VertexCount], pair.Odd);
    }

    // ── Aggregate sweep on a small corpus ──────────────────────────────────

    [Fact]
    public void CV_Probe_KnownGraphs_Size6_Summary()
    {
        var graphs = ConvertJaggedArrayType<EdgeType>(UniqueGraphsBySize.graphsBySize[6]);
        var rows = new List<string>();
        for (int i = 0; i < graphs.Length; i++)
        {
            var verts = new VertexType[6];
            var report = _calcFv.ProbeRotationsSingleFlip(verts, new AdjMatrix(graphs[i]));
            rows.Add(FormatSummaryRow(i, report));
        }
        output.WriteLine($"Size 6 corpus, {graphs.Length} graphs. Columns:");
        output.WriteLine("  graph#  primaries  totalProbes  falseSym  trueSym  maxAff  couplingCands  avgAff(FS)");
        foreach (var r in rows) output.WriteLine(r);
    }

    // ── Helpers ────────────────────────────────────────────────────────────

    private void RunProbe(string label, VertexType[] types, EdgeType[,] edges)
    {
        var report = _calcFv.ProbeRotationsSingleFlip(types, new AdjMatrix(edges));
        EmitReport(label, report);
    }

    private void RunProbe(string label, VertexType[] types, AdjMatrix g)
    {
        var report = _calcFv.ProbeRotationsSingleFlip(types, g);
        EmitReport(label, report);
    }

    private void RunXorFit(string label, VertexType[] types, EdgeType[,] edges)
    {
        var report = _calcFv.ProbeXorCouplings(types, new AdjMatrix(edges));
        EmitFitReport(label, report);
    }

    private void RunXorFit(string label, VertexType[] types, AdjMatrix g)
    {
        var report = _calcFv.ProbeXorCouplings(types, g);
        EmitFitReport(label, report);
    }

    private void EmitFitReport(string label, CouplingFitReport report)
    {
        var sb = new StringBuilder();
        sb.AppendLine();
        sb.AppendLine($"=== XOR-fit: {label} ===");
        sb.AppendLine($"  N                          = {report.N}");
        sb.AppendLine($"  PrimaryCount               = {report.PrimaryCount}");
        sb.AppendLine($"  CouplingCandidatesTested   = {report.CouplingCandidatesTested}");
        sb.AppendLine($"  ForwardPassesRun           = {report.ForwardPassesRun}");
        sb.AppendLine($"  FitCount                   = {report.FitCount}");
        sb.AppendLine($"  NonFitCount                = {report.NonFitCount}");
        sb.AppendLine($"  FitRate                    = {report.FitRate:P2}");
        sb.AppendLine($"  MaxVariablesPerEntry       = {report.MaxVariablesPerEntry}");
        sb.AppendLine($"  AvgVariablesPerEntry       = {report.AvgVariablesPerEntry:F2}");

        // Distribution of variable counts among fitted entries.
        var byKvars = report.Fits.GroupBy(f => f.InvolvedPrimaries.Length).OrderBy(g => g.Key);
        sb.AppendLine("  Per-k breakdown (k vars: total, fit, non-fit):");
        foreach (var g in byKvars)
        {
            int fits = g.Count(f => f.FitsXor);
            int nonFits = g.Count() - fits;
            sb.AppendLine($"    k={g.Key,2}: {g.Count(),4} total, {fits,4} fit, {nonFits,4} non-fit");
        }

        // For non-fits, show pair-match rates (how close they were).
        if (report.NonFitCount > 0)
        {
            var pairStats = report.Fits.Where(f => !f.FitsXor)
                                       .Select(f => f.PairsChecked == 0 ? 0.0 : (double)f.PairsMatched / f.PairsChecked)
                                       .ToList();
            sb.AppendLine($"  Non-fit pair-match rates: min={pairStats.Min():P2} max={pairStats.Max():P2} avg={pairStats.Average():P2}");
        }

        Assert.True(report.N > 0);
        Assert.True(report.PrimaryCount >= 0);

        output.WriteLine(sb.ToString());
    }

    private void EmitReport(string label, RotationProbingReport report)
    {
        var sb = new StringBuilder();
        sb.AppendLine();
        sb.AppendLine($"=== {label} ===");
        sb.AppendLine($"  N                       = {report.N}");
        sb.AppendLine($"  PrimaryCount            = {report.PrimaryCount}");
        sb.AppendLine($"  TotalProbes             = {report.TotalProbes}");
        sb.AppendLine($"  TrueSymmetryProbes      = {report.TrueSymmetryProbes}");
        sb.AppendLine($"  FalseSymmetryProbes     = {report.FalseSymmetryProbes}");
        sb.AppendLine($"  MaxAffectedEntries      = {report.MaxAffectedEntries}");
        sb.AppendLine($"  CouplingCandidateEntries= {report.CouplingCandidateEntries}");
        sb.AppendLine($"  AvgAffectedEntries(FS)  = {report.AvgAffectedEntriesOverFalseSymProbes:F2}");

        // Per-layer breakdown.
        var byLayer = report.Probes
            .GroupBy(p => p.LayerId)
            .OrderBy(g => g.Key)
            .ToList();
        sb.AppendLine("  Per-layer (layer: total, falseSym, maxAff):");
        foreach (var g in byLayer)
        {
            int fs = g.Count(p => p.AffectedEntries.Length > 0);
            int maxAff = g.Max(p => p.AffectedEntries.Length);
            sb.AppendLine($"    layer {g.Key,2}: {g.Count(),4} total, {fs,4} falseSym, maxAff={maxAff}");
        }

        // Sanity assertions.
        Assert.True(report.N > 0);
        Assert.True(report.PrimaryCount >= 0);
        Assert.True(report.TotalProbes >= 0);

        output.WriteLine(sb.ToString());
    }

    private static string FormatSummaryRow(int idx, RotationProbingReport r) =>
        $"  {idx,6}  {r.PrimaryCount,9}  {r.TotalProbes,11}  {r.FalseSymmetryProbes,8}  {r.TrueSymmetryProbes,7}  {r.MaxAffectedEntries,6}  {r.CouplingCandidateEntries,13}  {r.AvgAffectedEntriesOverFalseSymProbes,10:F2}";
}
