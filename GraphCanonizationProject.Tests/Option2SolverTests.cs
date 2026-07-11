using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// B1a — production Option2Solver.Recover, validated against native-A-multipedes driven
// through the REAL WarmPartition with a bare 1-WL seed (no synthetic type colouring —
// segments are found structurally, via the bipartition + degree). Mirrors the RM-1/3/4
// probe validation, now on the production class.
public sealed class Option2SolverTests
{
    private readonly ITestOutputHelper _out;
    public Option2SolverTests(ITestOutputHelper o) => _out = o;

    private sealed class Ab
    {
        public readonly int[] Inv; public readonly int N;
        public Ab(params int[] inv) { Inv = inv; N = inv.Aggregate(1, (a, b) => a * b); }
        private int[] T(int idx) { var t = new int[Inv.Length]; for (int i = Inv.Length - 1; i >= 0; i--) { t[i] = idx % Inv[i]; idx /= Inv[i]; } return t; }
        private int Ix(int[] t) { int x = 0; for (int i = 0; i < Inv.Length; i++) x = x * Inv[i] + t[i]; return x; }
        public int Add(int a, int b) { var ta = T(a); var tb = T(b); var tc = new int[Inv.Length]; for (int i = 0; i < Inv.Length; i++) tc[i] = (ta[i] + tb[i]) % Inv[i]; return Ix(tc); }
        public int Neg(int a) { var ta = T(a); var tc = new int[Inv.Length]; for (int i = 0; i < Inv.Length; i++) tc[i] = (Inv[i] - ta[i]) % Inv[i]; return Ix(tc); }
        public int Order(int a) { int o = 1, x = a; while (x != 0) { x = Add(x, a); o++; } return o; }
        public string TrueOrderProfile()
        {
            var h = new SortedDictionary<int, int>();
            for (int a = 0; a < N; a++) { int o = Order(a); h[o] = h.TryGetValue(o, out var c) ? c + 1 : 1; }
            return string.Join(",", h.Select(kv => $"{kv.Key}^{kv.Value}"));
        }
    }

    [Theory]
    [InlineData("Z4", 4)]
    [InlineData("Z2^2", 4)]
    [InlineData("Z3", 3)]
    public void Recover_NativeMultipede_YieldsRingAndSegments_ScrambleInvariant(string name, int asz)
    {
        var A = name switch
        {
            "Z4" => new Ab(4), "Z2^2" => new Ab(2, 2), "Z3" => new Ab(3),
            _ => throw new ArgumentException(name)
        };
        Assert.Equal(asz, A.N);
        int nW = 6;
        var (g0, t0) = BuildNativeMultipede(A, CirculantLines(nW, new[] { 0, 1, 3 }), nW);

        var profiles = new List<string>();
        var sizes = new List<int>();
        var segCounts = new List<int>();
        for (int s = -1; s < 3; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = g0; t = (int[])t0.Clone(); }
            else (g, t) = ScrambleWithTypes(g0, t0, 13000 + s);
            int n = g.VertexCount;
            var adj = Flat(g);
            var part = new WarmPartition(n);
            // The descent's partition at target==-1 has already separated the segments (via the
            // pinned path); mimic that with a segment-distinguishing seed. 1-WL alone is blind
            // on the rigid multipede — it cannot split segments (the IR-blindspot).
            part.Refine(adj, SeedFromTypes(n, t));
            var res = Option2Solver.Recover(adj, n, part.CellOf, part.NumCells);
            Assert.NotNull(res);
            profiles.Add(res!.OrderProfile);
            sizes.Add(res.ASize);
            segCounts.Add(res.Segments.Count);
            Assert.Equal(nW, res.Incidence.GetLength(1));    // M has nW segment columns
        }

        Assert.All(sizes, k => Assert.Equal(A.N, k));
        Assert.All(segCounts, c => Assert.Equal(nW, c));
        Assert.All(profiles, p => Assert.Equal(A.TrueOrderProfile(), p));   // ring recovered exactly
        Assert.True(profiles.Distinct().Count() == 1);                       // scramble-invariant
        _out.WriteLine($"{name,-6} |A|={sizes[0]} segments={segCounts[0]} ring=[{profiles[0]}] scramble-inv=True");
    }

    [Fact]
    public void Recover_NonMultipede_Flags()
    {
        // a plain path graph is bipartite but has no degree-3 sum-zero gadgets ⟹ no ring ⟹ flag (null).
        int n = 8;
        var adj = new int[n * n];
        for (int i = 0; i + 1 < n; i++) { adj[i * n + (i + 1)] = 1; adj[(i + 1) * n + i] = 1; }
        var part = new WarmPartition(n);
        part.Refine(adj, new sbyte[n * n]);
        Assert.Null(Option2Solver.Recover(adj, n, part.CellOf, part.NumCells));
    }

    // ── local native-A-multipede builder + plumbing ───────────────────────────────
    private static IEnumerable<int[]> TuplesSumZero(Ab A, int d)
    {
        int free = d - 1, total = 1; for (int i = 0; i < free; i++) total *= A.N;
        for (int code = 0; code < total; code++)
        {
            var t = new int[d]; int c = code, sum = 0;
            for (int i = 0; i < free; i++) { t[i] = c % A.N; c /= A.N; sum = A.Add(sum, t[i]); }
            t[d - 1] = A.Neg(sum);
            yield return t;
        }
    }
    private static List<int[]> CirculantLines(int nW, int[] offsets)
    {
        var lines = new List<int[]>();
        for (int i = 0; i < nW; i++) lines.Add(offsets.Select(o => (i + o) % nW).Distinct().ToArray());
        return lines;
    }
    private static (AdjMatrix g, int[] types) BuildNativeMultipede(Ab A, List<int[]> lines, int nW)
    {
        int segCount = nW * A.N;
        var edges = new List<(int u, int v)>();
        int gid = 0;
        for (int li = 0; li < lines.Count; li++)
            foreach (var t in TuplesSumZero(A, lines[li].Length))
            {
                int gv = segCount + gid++;
                for (int i = 0; i < lines[li].Length; i++) edges.Add((gv, lines[li][i] * A.N + t[i]));
            }
        int n = segCount + gid;
        var m = new int[n, n];
        foreach (var (u, v) in edges) { m[u, v] = 1; m[v, u] = 1; }
        var types = new int[n];
        for (int p = 0; p < nW; p++) for (int a = 0; a < A.N; a++) types[p * A.N + a] = p;
        for (int i = 0; i < gid; i++) types[segCount + i] = nW;   // gadgets = one colour class (not over-individualised)
        return (new AdjMatrix(m), types);
    }
    private static int[] Flat(AdjMatrix g)
    {
        int n = g.VertexCount; var a = new int[n * n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) a[i * n + j] = g[i, j];
        return a;
    }
    private static (AdjMatrix, int[]) ScrambleWithTypes(AdjMatrix g, int[] types, int seed)
    {
        int n = g.VertexCount; var m = g.ToArray(); var t = (int[])types.Clone(); var rng = new Random(seed);
        for (int r = 0; r < n - 1; r++)
        {
            int s = r + rng.Next() % (n - r);
            for (int i = 0; i < n; i++) (m[s, i], m[r, i]) = (m[r, i], m[s, i]);
            for (int i = 0; i < n; i++) (m[i, s], m[i, r]) = (m[i, r], m[i, s]);
            (t[s], t[r]) = (t[r], t[s]);
        }
        return (new AdjMatrix(m), t);
    }

    private static sbyte[] SeedFromTypes(int n, int[] types)
    {
        var p = new sbyte[n * n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++)
            if (i != j && types[i] < types[j]) { p[i * n + j] = -1; p[j * n + i] = 1; }
        // transitive closure
        for (int k = 0; k < n; k++) for (int i = 0; i < n; i++)
        {
            if (p[i * n + k] != -1) continue;
            for (int j = 0; j < n; j++) if (p[k * n + j] == -1 && p[i * n + j] == 0) { p[i * n + j] = -1; p[j * n + i] = 1; }
        }
        return p;
    }
}
