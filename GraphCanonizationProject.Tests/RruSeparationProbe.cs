using System;
using System.Diagnostics;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// SEPARATION PROBE (2026-07-10). The overarching design question: can rigid and symmetric
// work be separated so NEITHER's exponential leaks into the other before it is resolved?
// Concretely = the "sum not product" property. Test with a graph that forces BOTH kinds in
// ONE descent: disjoint union of A = rigid multipede (many Phase-2 nodes, 2^k leaves) and
// B = symmetric forms graph (expensive per-node harvest, fully consumed by Phase 1).
//
//   CLEAN (deferral ON): B's symmetry hoisted ABOVE A's rigid branching, consumed ONCE.
//     union_leaves ≈ A_leaves ; union_harvest ≈ A_harv + B_harv ; union_time ≈ A_time + B_time.
//   PRODUCT (deferral OFF): B re-harvested inside each of A's 2^k rigid branches.
//     union_harvest / time scale with A_leaves × B_cost.
//
// If ON is sum and OFF is product, the design achieves the separation the user asks for
// (on the refinement-separable case; the entangled case is the fusion-battery "no third
// species" result — symmetry and rigidity provably do not 1-WL-entangle except as a Cameron
// section, which confinement consumes wholesale).
public class RruSeparationProbe
{
    private readonly ITestOutputHelper _out;
    public RruSeparationProbe(ITestOutputHelper o) => _out = o;
    static readonly string Log = "/tmp/claude-1000/-workspace/b076ebb8-96fc-4efb-bf83-7f5c0b04a3f8/scratchpad/sep2.log";
    void Emit(string s) { _out.WriteLine(s); System.IO.File.AppendAllText(Log, s + "\n"); }

    static int[] FlatAdj(AdjMatrix g)
    { int n = g.VertexCount; var a = new int[n * n];
      for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) a[i * n + j] = g[i, j]; return a; }
    static sbyte[] Seed(int n, int[]? t)
    { var p = new sbyte[n * n]; if (t == null) return p;
      for (int i = 0; i < n; i++) for (int j = 0; j < n; j++)
        if (i != j && t[i] < t[j]) { p[i * n + j] = -1; p[j * n + i] = 1; } return p; }
    static int[] VO(int q, int dim, Func<int[], int> Q)
        => FormsGraphBuilder.StandardCayleyGraph(q, dim, dd => Q(dd) == 0);

    // Block-diagonal disjoint union of two flat adjacencies.
    static int[] Union(int[] a, int na, int[] b, int nb)
    {
        int n = na + nb; var u = new int[n * n];
        for (int i = 0; i < na; i++) for (int j = 0; j < na; j++) u[i * n + j] = a[i * na + j];
        for (int i = 0; i < nb; i++) for (int j = 0; j < nb; j++) u[(na + i) * n + (na + j)] = b[i * nb + j];
        return u;
    }

    (long nodes, long leaves, long harv, double ms, int maxRec) Run(int[] adj, int n, int[]? types, bool defer)
    {
        var d = new ChainDescent(n, adj, new CascadeOracle(), 500L * n * n * n)
        { EnableLinearOracle = true, EnableDeferral = defer };
        var sw = Stopwatch.StartNew();
        var r = d.Canonize(Seed(n, types), new WarmPartition(n));
        sw.Stop();
        return (r.Stats.NodeCount, r.Stats.LeafCount, r.Stats.Cascade.GeneratorsHarvested,
                sw.Elapsed.TotalMilliseconds, r.Stats.Cascade.MaxRecursionDepth);
    }

    void Line(string tag, (long nodes, long leaves, long harv, double ms, int maxRec) x)
        => Emit($"    {tag,-18} nodes={x.nodes,-7} leaves={x.leaves,-7} harvested={x.harv,-7} maxRec={x.maxRec,-3} time={x.ms,9:F0}ms");

    [Fact]
    public void SumNotProduct()
    {
        System.IO.File.WriteAllText(Log, "");

        // A = rigid multipede (2^k Phase-2 leaves). B = symmetric forms graph (per-node harvest).
        var mp = MultipedeGenerator.BuildRandomRegular(10, 10, 3, 1); // rr10: 16 leaves, keeps OFF-product tractable
        int nA = mp.Graph.VertexCount; var A = FlatAdj(mp.Graph); var tA = mp.VertexTypes;
        int nB = 64; var B = VO(2, 6, d => (d[0]*d[1] + d[2]*d[3] + d[4]*d[4] + d[4]*d[5] + d[5]*d[5]) % 2);

        int tmax = 0; foreach (var t in tA) tmax = Math.Max(tmax, t);
        int nU = nA + nB;
        var U = Union(A, nA, B, nB);
        var tU = new int[nU];
        for (int i = 0; i < nA; i++) tU[i] = tA[i];
        for (int i = 0; i < nB; i++) tU[nA + i] = tmax + 1;   // B one uniform colour

        foreach (bool defer in new[] { true, false })
        {
            Emit($"### deferral {(defer ? "ON " : "OFF")} — A=rigid multipede(rr18, n={nA}), B=VO^-_6(2) (n={nB})");
            var a = Run(A, nA, tA, defer);
            var b = Run(B, nB, null, defer);
            var u = Run(U, nU, tU, defer);
            Line("A alone (rigid)", a);
            Line("B alone (symm)", b);
            Line("A + B (sum)", (a.nodes + b.nodes, a.leaves + b.leaves, a.harv + b.harv, a.ms + b.ms, Math.Max(a.maxRec, b.maxRec)));
            Line("A ⊔ B (union)", u);
            double prod = a.leaves * Math.Max(1, b.harv);
            Emit($"    → union harvested={u.harv}  vs  sum={a.harv + b.harv}  vs  product-estimate(A_leaves×B_harv)={prod:F0}");
            Emit("");
        }
    }
}
