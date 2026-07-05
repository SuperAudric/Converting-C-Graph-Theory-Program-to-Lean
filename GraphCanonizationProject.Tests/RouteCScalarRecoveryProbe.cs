using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — the scalar-recovery experiment (2026-07-05). Given a FRAME (o + axis point e), do the
// graph incidences separate 2e / 3e / 4e on the line o-e? We fix the frame, run 1-WL color refinement
// (the incidence engine), and read the final cells of 2e,3e,4e. Also: how big must the frame be to
// separate them? This pinpoints exactly which scalar step is recoverable from incidences and which
// needs the additive structure (2 = 1+1).
public class RouteCScalarRecoveryProbe
{
    private readonly ITestOutputHelper _out;
    public RouteCScalarRecoveryProbe(ITestOutputHelper o) => _out = o;

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    // 1-WL color refinement with a given initial coloring; returns stable colors.
    static int[] Refine(int[] adj, int n, int[] init)
    {
        var color = (int[])init.Clone();
        while (true)
        {
            var sig = new (int, string)[n];
            for (int v = 0; v < n; v++)
            {
                var nb = new List<int>();
                for (int w = 0; w < n; w++) if (adj[v * n + w] == 1) nb.Add(color[w]);
                nb.Sort();
                sig[v] = (color[v], string.Join(",", nb));
            }
            var rank = sig.Select((s, v) => (s, v)).GroupBy(t => t.s).OrderBy(g => g.Key)
                          .SelectMany((g, i) => g.Select(t => (t.v, i))).ToDictionary(t => t.v, t => t.i);
            var next = new int[n];
            for (int v = 0; v < n; v++) next[v] = rank[v];
            if (next.SequenceEqual(color)) return color;
            color = next;
        }
    }

    [Theory]
    [InlineData(5, -1)]
    [InlineData(3, -1)]
    public void ScalarSeparation_ByFrameSize(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim);
        var (adj, vec, enc) = RouteCVO4.Build(q, eps);

        // an isotropic axis point e (Q(e)=0): e = (1,0,0,0) is isotropic for VO with a hyperbolic first pair
        int e1 = enc(new[] { 1, 0, 0, 0 });
        Assert.True(adj[0 * n + e1] == 1, "e must be isotropic (adjacent to o)");
        var mult = new int[q];   // mult[k] = vertex k*e
        for (int k = 0; k < q; k++) mult[k] = enc(new[] { k, 0, 0, 0 });

        // pick a second independent isotropic axis f for larger frames (partner in another position)
        int f1 = enc(new[] { 0, 0, 1, 0 });   // may or may not be isotropic; find an isotropic independent one
        for (int cand = 1; cand < n; cand++)
            if (adj[0 * n + cand] == 1 && !Dependent(vec(cand), vec(e1), q, dim)) { f1 = cand; break; }

        // try frames of increasing size: {o,e}, {o,e,f}, {o,e,f,2e}, then individualize a spanning set
        var frames = new List<(string name, int[] pts)>
        {
            ("{o,e}", new[] { 0, e1 }),
            ("{o,e,f}", new[] { 0, e1, f1 }),
        };
        // a spanning isotropic frame (o + up to dim independent isotropic axes)
        var span = new List<int> { 0, e1 };
        for (int cand = 1; cand < n && span.Count < dim + 1; cand++)
            if (adj[0 * n + cand] == 1 && IndependentOfAll(vec(cand), span.Skip(1).Select(vec).ToList(), q, dim)) span.Add(cand);
        frames.Add(($"spanning({span.Count})", span.ToArray()));

        foreach (var (name, pts) in frames)
        {
            var init = new int[n];
            // each framed point gets its own singleton color; the rest share color 0
            int c = 1; foreach (int p in pts) init[p] = c++;
            var col = Refine(adj, n, init);
            var cells = mult.Skip(1).Select(v => col[v]).ToArray();   // colors of e,2e,3e,4e (skip 0*e=o)
            int distinct = cells.Distinct().Count();
            int totalCells = col.Distinct().Count();                  // whole-graph discretization
            _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_4({q}) frame {name}: line-scalars distinct={distinct}/{q - 1}; WHOLE-GRAPH cells={totalCells}/{n} {(totalCells == n ? "DISCRETIZED ✓" : "NOT discrete")}");
        }
    }

    // GREEDY coordinate-free discretization: individualize o, refine; then repeatedly individualize the
    // first vertex of the first non-singleton cell and refine, until discrete. Counts individualizations.
    // If this is O(d), harvest-free coordinatization via frame+WL is cheap (poly).
    [Theory]
    [InlineData(3, -1, 4)]   // VO^-_4(3) n=81,   d=4
    [InlineData(5, -1, 4)]   // VO^-_4(5) n=625,  d=4
    [InlineData(3, -1, 6)]   // VO^-_6(3) n=729,  d=6
    [InlineData(3, +1, 6)]   // VO^+_6(3) n=729,  d=6
    [InlineData(7, -1, 4)]   // VO^-_4(7) n=2401, d=4
    public void GreedyDiscretization_FrameSize(int q, int eps, int d)
    {
        int n = IPow(q, d);
        var (adj, _, _) = BuildVO(q, eps, d);

        var color = new int[n];
        color[0] = 1;                       // individualize o
        color = Refine(adj, n, color);
        int indiv = 1;
        int nextColor = n + 5;
        while (color.Distinct().Count() < n && indiv < n)
        {
            // first vertex of the first non-singleton cell
            var groups = Enumerable.Range(0, n).GroupBy(v => color[v]).Where(g => g.Count() > 1).ToList();
            if (groups.Count == 0) break;
            int pick = groups.OrderBy(g => g.Key).First().OrderBy(v => v).First();
            color[pick] = nextColor++;
            color = Refine(adj, n, color);
            indiv++;
        }
        int cells = color.Distinct().Count();
        _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_{d}({q}) n={n}: greedy individualizations to discretize = {indiv} (d+1={d + 1}); cells={cells}/{n} {(cells == n ? "✓" : "STUCK")}");
    }

    // VO^eps_d(q) Cayley graph for general even d (standard form: hyperbolic pairs + anisotropic tail for eps=-1)
    static (int[] adj, Func<int, int[]> vec, Func<int[], int> enc) BuildVO(int q, int eps, int d)
    {
        int m = d / 2, n = IPow(q, d);
        int bb = 0, cc = 0;
        if (eps == -1)
        {
            bool found = false;
            for (int b = 0; b < q && !found; b++) for (int c = 0; c < q && !found; c++)
            {
                bool an = true;
                for (int y = 0; y < q && an; y++) for (int z = 0; z < q; z++)
                { if (y == 0 && z == 0) continue; if (((y * y + b * y % q * z) % q + c * (z * z % q)) % q == 0) { an = false; break; } }
                if (an) { bb = b; cc = c; found = true; }
            }
        }
        int[] Vec(int v) { var x = new int[d]; for (int i = 0; i < d; i++) { x[i] = v % q; v /= q; } return x; }
        int Enc(int[] x) { int v = 0, pw = 1; for (int i = 0; i < d; i++) { v += (((x[i] % q) + q) % q) * pw; pw *= q; } return v; }
        int Q(int[] x)
        {
            int s = 0, hyp = eps == -1 ? m - 1 : m;
            for (int i = 0; i < hyp; i++) s = (s + x[2 * i] * x[2 * i + 1]) % q;
            if (eps == -1) { int y = x[2 * (m - 1)], z = x[2 * (m - 1) + 1]; s = (s + (y * y + bb * y % q * z) % q + cc * (z * z % q)) % q; }
            return ((s % q) + q) % q;
        }
        var vecs = new int[n][]; for (int v = 0; v < n; v++) vecs[v] = Vec(v);
        var adj = new int[n * n]; var dd = new int[d];
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++)
        { for (int i = 0; i < d; i++) dd[i] = ((vecs[u][i] - vecs[v][i]) % q + q) % q; if (Q(dd) == 0) { adj[u * n + v] = 1; adj[v * n + u] = 1; } }
        return (adj, Vec, Enc);
    }

    static bool Dependent(int[] x, int[] y, int q, int d)
    {
        for (int c = 0; c < q; c++) if (Enumerable.Range(0, d).All(k => (c * x[k]) % q == ((y[k] % q) + q) % q)) return true;
        for (int c = 0; c < q; c++) if (Enumerable.Range(0, d).All(k => (c * y[k]) % q == ((x[k] % q) + q) % q)) return true;
        return false;
    }
    static bool IndependentOfAll(int[] v, List<int[]> basis, int q, int d)
    {
        // v independent of span(basis) over F_q (append-and-rank)
        var rows = new List<int[]>(basis) { v };
        return Rank(rows, q, d) == basis.Count + 1;
    }
    static int Rank(List<int[]> vs, int q, int d)
    {
        var A = vs.Select(r => r.Select(x => ((x % q) + q) % q).ToArray()).ToList();
        int rank = 0;
        for (int col = 0; col < d && rank < A.Count; col++)
        {
            int piv = -1; for (int i = rank; i < A.Count; i++) if (A[i][col] % q != 0) { piv = i; break; }
            if (piv < 0) continue;
            (A[rank], A[piv]) = (A[piv], A[rank]);
            int inv = 1; for (int i = 0; i < q - 2; i++) inv = inv * A[rank][col] % q;
            for (int cc = 0; cc < d; cc++) A[rank][cc] = A[rank][cc] * inv % q;
            for (int i = 0; i < A.Count; i++) if (i != rank && A[i][col] % q != 0)
                { int fct = A[i][col]; for (int cc = 0; cc < d; cc++) A[i][cc] = (((A[i][cc] - fct * A[rank][cc]) % q) + q * q) % q; }
            rank++;
        }
        return rank;
    }
}
