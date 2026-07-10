using System;
using System.Diagnostics;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// COST DECOMPOSITION PROBE (2026-07-10). Is the descent's cost on (a) node-4/Cameron
// families and (b) rigid obstructions driven by ORACLE WORK PER NODE, or by NODE COUNT
// (branching)? The oracle (HarvestTwists) is O(reps × depth × refine) = polynomial by
// inspection; the exponential can only enter via node count. Measure both separately.
public class RruCostProbe
{
    private readonly ITestOutputHelper _out;
    public RruCostProbe(ITestOutputHelper o) => _out = o;

    static int[] FlatAdj(AdjMatrix g)
    { int n = g.VertexCount; var a = new int[n * n];
      for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) a[i * n + j] = g[i, j]; return a; }

    static sbyte[] Seed(int n, int[]? t)
    { var p = new sbyte[n * n]; if (t == null) return p;
      for (int i = 0; i < n; i++) for (int j = 0; j < n; j++)
        if (i != j && t[i] < t[j]) { p[i * n + j] = -1; p[j * n + i] = 1; } return p; }

    void Row(string name, int[] adj, int n, int[]? types, long budget)
    {
        var d = new ChainDescent(n, adj, new CascadeOracle(), budget)
        { EnableLinearOracle = true, EnableDeferral = true };
        var sw = Stopwatch.StartNew();
        var r = d.Canonize(Seed(n, types), new WarmPartition(n));
        sw.Stop();
        var c = r.Stats.Cascade;
        double perNode = r.Stats.NodeCount > 0 ? sw.Elapsed.TotalMilliseconds / r.Stats.NodeCount : 0;
        _out.WriteLine($"{name,-24} n={n,4} | {(r.Flagged ? "FLAG " + r.FlagReason : "CANON"),-22} " +
                       $"| nodes={r.Stats.NodeCount,-9} leaves={r.Stats.LeafCount,-7} " +
                       $"| time={sw.Elapsed.TotalMilliseconds,9:F1}ms  ms/node={perNode,8:F3} " +
                       $"| maxRecDepth={c.MaxRecursionDepth,3} phase2Nodes={c.Phase2Nodes,-7} |Aut|={r.ResidualGroup.Order}");
    }

    static int[] VO(int q, int dim, Func<int[], int> Q)
        => FormsGraphBuilder.StandardCayleyGraph(q, dim, dd => Q(dd) == 0);

    [Fact]
    public void CostDecomposition()
    {
        long big = 2_000_000L;
        _out.WriteLine("### NODE-4 / Cameron forms graphs — cost should be HIGH ms/node (deep harvest), LOW node count");
        Row("VO^-_4(2)  Clebsch", VO(2, 4, d => (d[0]*d[1] + d[2]*d[2] + d[2]*d[3] + d[3]*d[3]) % 2), 16, null, big);
        Row("VO^-_6(2)", VO(2, 6, d => (d[0]*d[1] + d[2]*d[3] + d[4]*d[4] + d[4]*d[5] + d[5]*d[5]) % 2), 64, null, big);
        Row("VO^-_8(2)", VO(2, 8, d => (d[0]*d[1] + d[2]*d[3] + d[4]*d[5] + d[6]*d[6] + d[6]*d[7] + d[7]*d[7]) % 2), 256, null, big);
        Row("VO^-_4(3)", VO(3, 4, d => (d[0]*d[1] + d[2]*d[2] + d[3]*d[3]) % 3), 81, null, big);
        Row("VO^-_6(3)", VO(3, 6, d => (d[0]*d[1] + d[2]*d[3] + d[4]*d[4] + d[5]*d[5]) % 3), 729, null, big);

        _out.WriteLine("");
        _out.WriteLine("### RIGID obstructions (multipedes) — is the cost in ms/node, or in node count?");
        foreach (int m in new[] { 5, 8, 12, 16, 20, 24, 28 })
        {
            var mp = MultipedeGenerator.BuildCirculant(m);
            Row($"Multipede(circ {m})", FlatAdj(mp.Graph), mp.Graph.VertexCount, mp.VertexTypes, big);
        }

        _out.WriteLine("");
        _out.WriteLine("### RIGID, harder: random-regular multipede bases");
        foreach (var (nc, nb, deg, sd) in new[] { (10, 10, 3, 1), (14, 14, 3, 2), (18, 18, 3, 3), (22, 22, 3, 4) })
        {
            var mp = MultipedeGenerator.BuildRandomRegular(nc, nb, deg, sd);
            Row($"Multipede(rr {nc},{deg},s{sd})", FlatAdj(mp.Graph), mp.Graph.VertexCount, mp.VertexTypes, big);
        }

        _out.WriteLine("");
        _out.WriteLine("### CFI (abelian Aut, small by threshold)");
        foreach (var b in new[] { "K6", "K7" })
        { var p = CfiGraphGenerator.Generate(b); Row($"CFI({b}) even", FlatAdj(p.Even), p.Even.VertexCount, null, big); }
    }
}
