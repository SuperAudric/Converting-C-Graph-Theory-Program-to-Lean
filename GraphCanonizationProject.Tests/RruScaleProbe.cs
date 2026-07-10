using System;
using System.Diagnostics;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// SCALING PROBE (2026-07-10). The user's claim: even a SMALL-Aut rigid obstruction has
// nonpolynomial LEAF COUNT, so Phase 1 does not resolve it in poly time and handing it to
// the IR phase is not enough. Test directly: as multipede size grows, do NODES / LEAVES
// stay bounded (single-path Phase-1 resolution) or blow up? A blow-up in leaves = the
// rigid obstruction is genuinely exponential in the descent; bounded = Phase 1 resolves it.
// Written to a flushed log so partial results survive a timeout on the largest case.
public class RruScaleProbe
{
    private readonly ITestOutputHelper _out;
    public RruScaleProbe(ITestOutputHelper o) => _out = o;
    static readonly string Log = "/tmp/claude-1000/-workspace/b076ebb8-96fc-4efb-bf83-7f5c0b04a3f8/scratchpad/scale.log";
    void Emit(string s) { _out.WriteLine(s); System.IO.File.AppendAllText(Log, s + "\n"); }

    static int[] FlatAdj(AdjMatrix g)
    { int n = g.VertexCount; var a = new int[n * n];
      for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) a[i * n + j] = g[i, j]; return a; }
    static sbyte[] Seed(int n, int[]? t)
    { var p = new sbyte[n * n]; if (t == null) return p;
      for (int i = 0; i < n; i++) for (int j = 0; j < n; j++)
        if (i != j && t[i] < t[j]) { p[i * n + j] = -1; p[j * n + i] = 1; } return p; }

    void Row(string name, int[] adj, int n, int[]? types)
    {
        long budget = 50L * n * n * n; // generous poly budget
        var d = new ChainDescent(n, adj, new CascadeOracle(), budget)
        { EnableLinearOracle = true, EnableDeferral = true };
        var sw = Stopwatch.StartNew();
        CanonResult r;
        try { r = d.Canonize(Seed(n, types), new WarmPartition(n)); }
        catch (Exception e) { Emit($"{name,-26} n={n,4} | EXCEPTION {e.GetType().Name}"); return; }
        sw.Stop();
        var c = r.Stats.Cascade;
        Emit($"{name,-26} n={n,4} | {(r.Flagged ? "FLAG" : "CANON"),-5} " +
             $"nodes={r.Stats.NodeCount,-8} leaves={r.Stats.LeafCount,-8} maxDepth={r.Stats.MaxDepth,-4} " +
             $"budget={budget,-11} | time={sw.Elapsed.TotalMilliseconds,8:F0}ms maxRecDepth={c.MaxRecursionDepth,3} " +
             $"phase2Nodes={c.Phase2Nodes,-6} |Aut|={r.ResidualGroup.Order}");
    }

    static int[] VO(int q, int dim, Func<int[], int> Q)
        => FormsGraphBuilder.StandardCayleyGraph(q, dim, dd => Q(dd) == 0);

    [Fact]
    public void Scaling()
    {
        System.IO.File.WriteAllText(Log, "");
        Emit("### RIGID multipedes (circulant, odd base) — does leaf/node count blow up with size?");
        foreach (int m in new[] { 5, 8, 11, 13, 16, 20, 25, 30, 40, 50 })
        {
            var mp = MultipedeGenerator.BuildCirculant(m);
            Row($"Multipede(circ {m})", FlatAdj(mp.Graph), mp.Graph.VertexCount, mp.VertexTypes);
        }

        Emit("");
        Emit("### RIGID multipedes (random-regular base) — the harder rigid family");
        foreach (var (nc, deg, sd) in new[] { (10, 3, 1), (14, 3, 2), (18, 3, 3), (24, 3, 4), (30, 3, 5), (30, 4, 6) })
        {
            var mp = MultipedeGenerator.BuildRandomRegular(nc, nc, deg, sd);
            Row($"Multipede(rr {nc},{deg},s{sd})", FlatAdj(mp.Graph), mp.Graph.VertexCount, mp.VertexTypes);
        }

        Emit("");
        Emit("### NODE-4 forms graphs — for contrast (VT, Cameron)");
        Row("VO^-_4(2)", VO(2, 4, d => (d[0]*d[1] + d[2]*d[2] + d[2]*d[3] + d[3]*d[3]) % 2), 16, null);
        Row("VO^-_6(2)", VO(2, 6, d => (d[0]*d[1] + d[2]*d[3] + d[4]*d[4] + d[4]*d[5] + d[5]*d[5]) % 2), 64, null);
        Row("VO^-_4(3)", VO(3, 4, d => (d[0]*d[1] + d[2]*d[2] + d[3]*d[3]) % 3), 81, null);
    }
}
