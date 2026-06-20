using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ─────────────────────────────────────────────────────────────────────────────
// Option-2 / Layer-D milestone D-M1 — F2 extraction in C#, driven by the REAL
// canonizer refinement (WarmPartition = the descent's 1-WL).
//
// The IR-blindspot solver (docs/chain-descent-ir-blindspot-solver.md §11) reads
// the multipede's F2 constraint matrix H (= the base biadjacency A_G) from the
// descent's *forcing* behaviour alone — no gadget recognition — then Gaussian-
// eliminates to recover dim ker (= |Aut_F2-gauge| exponent; 0 for a rigid/odd
// multipede). Layers A/B/C validated this on a Python matrix model and a Python
// 1-WL port; D-M0 validated the whole pipeline from raw scrambled adjacency.
// D-M1 ports the EXTRACTION to C# against the genuine WarmPartition refinement,
// so the test exercises Layer B (WL == unit-propagation) and the Layer-C
// extraction together in the real machinery.
//
// The forcing oracle (RefinementFootprint's mechanism, §11.10 D2): individualize
// one vertex of a segment pair below its cellmate — exactly the p-pin the descent
// uses (ChainDescent.Individualize) — warm-refine, and read which OTHER segment
// pairs have split. A minimal set of segments that force each other is a row of H.
//
// Assertions (the D-M1 deliverable): extracted dim ker == ground truth
// (nW − rank_F2(A_G)), and it is scramble-invariant. Recognition-free: segments
// are identified as the size-2 stable cells (the D1 rule), cross-checked == nW.
// ─────────────────────────────────────────────────────────────────────────────
public sealed class Option2ExtractionProbe
{
    private const sbyte LESS = -1, UNKNOWN = 0, GREATER = 1;
    private readonly ITestOutputHelper output;
    public Option2ExtractionProbe(ITestOutputHelper o) => output = o;

    [Theory]
    [InlineData(6, 4)]   // circulant, odd (7∤6) ⟹ rigid, dim ker 0
    [InlineData(8, 4)]   // odd ⟹ dim ker 0
    [InlineData(9, 4)]   // odd ⟹ dim ker 0
    [InlineData(7, 4)]   // 7|7 ⟹ NOT odd ⟹ dim ker > 0 (near-rigid extraction)
    public void Extraction_RecoversDimKer_Circulant(int m, int D)
    {
        var biadj = MultipedeGenerator.CirculantBiadjacency(m, new[] { 0, 1, 3 });
        RunCase($"Circulant{m}", biadj, D);
    }

    [Fact]
    public void Extraction_RecoversDimKer_RandomRegular()
    {
        // an odd random-regular base with nV>nW (the genuine high-treewidth
        // IR-blindspot regime; coker>0 but still rigid since odd ⟹ dim ker 0).
        int[,]? biadj = null;
        for (int seed = 0; seed < 200; seed++)
        {
            var b = RandomRegularBiadjacency(8, 6, 3, seed);
            if (ColRankF2(b) == 6) { biadj = b; break; }
        }
        Assert.NotNull(biadj);
        RunCase("RandReg(8,6,3)", biadj!, D: 4);
    }

    // ── the case runner ──────────────────────────────────────────────────────
    private void RunCase(string name, int[,] biadj, int D)
    {
        int nW = biadj.GetLength(1);
        int trueKer = nW - ColRankF2(biadj);

        var mp = MultipedeGenerator.BuildMultipede(biadj, name);
        MultipedeGenerator.AssertWellFormed(mp);

        var kers = new List<int>();
        var ranks = new List<int>();
        // original + several scrambles
        var (g0, t0) = (mp.Graph, mp.VertexTypes);
        for (int s = -1; s < 4; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = g0; t = (int[])t0.Clone(); }
            else (g, t) = ScrambleWithTypes(g0, t0, seed: 4100 + s);

            int n = g.VertexCount;
            int[] adj = ExtractAdj(g);
            sbyte[] pBase = SeedFromTypes(n, t);

            var segs = RecoverSegments(n, adj, pBase);
            Assert.Equal(nW, segs.Count);   // D1: size-2 cells == segments

            var rows = ExtractRows(n, adj, pBase, segs, D);
            int rank = RankF2(rows);
            kers.Add(segs.Count - rank);
            ranks.Add(rank);
        }

        // (D-M1 deliverable) extracted dim ker == ground truth, every run.
        foreach (var k in kers)
            Assert.Equal(trueKer, k);
        // scramble-invariant rank too.
        Assert.True(ranks.Distinct().Count() == 1);

        output.WriteLine(
            $"{name,-16} n={mp.Graph.VertexCount,3} nW={nW} nV={biadj.GetLength(0)} " +
            $"odd={ColRankF2(biadj) == nW,-5} extracted dim ker={kers[0]} (true {trueKer}) " +
            $"rank={ranks[0]} scramble-inv={kers.Distinct().Count() == 1 && ranks.Distinct().Count() == 1}");
    }

    // ── D1: segments = size-2 stable cells of the real refinement ─────────────
    private static List<int[]> RecoverSegments(int n, int[] adj, sbyte[] pBase)
    {
        var part = new WarmPartition(n);
        part.Refine(adj, pBase);
        var byCell = new Dictionary<int, List<int>>();
        for (int v = 0; v < n; v++)
        {
            if (!byCell.TryGetValue(part.CellOf[v], out var l)) byCell[part.CellOf[v]] = l = new List<int>();
            l.Add(v);
        }
        return byCell.Values.Where(c => c.Count == 2).Select(c => { c.Sort(); return c.ToArray(); }).ToList();
    }

    // ── D2: the forcing oracle (RefinementFootprint mechanism) ────────────────
    // Individualize one vertex of each fixed segment below its cellmate (the
    // descent's p-pin), warm-refine, return the indices of segments that SPLIT.
    private static HashSet<int> ForcingClosure(
        int n, int[] adj, sbyte[] pBase, List<int[]> segs, IEnumerable<int> fixedSegs)
    {
        var p = (sbyte[])pBase.Clone();
        foreach (int si in fixedSegs)
        {
            int a = segs[si][0], b = segs[si][1];
            p[a * n + b] = LESS; p[b * n + a] = GREATER;
        }
        if (!TransitiveClose(p, n)) return new HashSet<int>();   // contradiction ⟹ no info
        var part = new WarmPartition(n);
        part.Refine(adj, p);
        var forced = new HashSet<int>();
        for (int si = 0; si < segs.Count; si++)
            if (part.CellOf[segs[si][0]] != part.CellOf[segs[si][1]]) forced.Add(si);
        return forced;
    }

    private static bool IsForcingCircuit(
        int n, int[] adj, sbyte[] pBase, List<int[]> segs, int[] W)
    {
        foreach (int w in W)
        {
            var rest = W.Where(x => x != w);
            if (!ForcingClosure(n, adj, pBase, segs, rest).Contains(w)) return false;
        }
        return true;
    }

    // ── Layer C: cumulative MINIMAL forcing-circuits up to arity D → rows ──────
    private static List<ulong> ExtractRows(
        int n, int[] adj, sbyte[] pBase, List<int[]> segs, int D)
    {
        int nW = segs.Count;
        var minimalMasks = new List<ulong>();
        var rows = new List<ulong>();
        for (int size = 2; size <= D; size++)
        {
            foreach (var W in Combinations(nW, size))
            {
                ulong mask = 0; foreach (int w in W) mask |= 1UL << w;
                // minimality: skip if a known minimal circuit's support is a PROPER subset
                if (minimalMasks.Any(mc => (mc & mask) == mc && mc != mask)) continue;
                if (IsForcingCircuit(n, adj, pBase, segs, W))
                {
                    minimalMasks.Add(mask);
                    rows.Add(mask);
                }
            }
        }
        return rows;
    }

    // ── F2 linear algebra ─────────────────────────────────────────────────────
    private static int RankF2(List<ulong> rows)
    {
        var pivots = new List<ulong>();
        foreach (var r0 in rows)
        {
            ulong cur = r0;
            foreach (var p in pivots) cur = Math.Min(cur, cur ^ p);
            if (cur != 0) pivots.Add(cur);
        }
        return pivots.Count;
    }

    // column rank over F2 of a |V|×|W| 0/1 matrix (== nW iff "odd"/rigid)
    private static int ColRankF2(int[,] b)
    {
        int nV = b.GetLength(0), nW = b.GetLength(1);
        var rows = new List<ulong>();
        for (int v = 0; v < nV; v++)
        {
            ulong r = 0;
            for (int w = 0; w < nW; w++) if ((b[v, w] & 1) != 0) r |= 1UL << w;
            rows.Add(r);
        }
        return RankF2(rows);
    }

    // ── plumbing replicated from CanonGraphOrdererChainDescent (private there) ─
    private static int[] ExtractAdj(AdjMatrix g)
    {
        int n = g.VertexCount;
        var adj = new int[n * n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                adj[i * n + j] = g[i, j];
        return adj;
    }

    private static sbyte[] SeedFromTypes(int n, int[] types)
    {
        var p = new sbyte[n * n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                if (i != j && types[i] < types[j]) { p[i * n + j] = LESS; p[j * n + i] = GREATER; }
        TransitiveClose(p, n);
        return p;
    }

    private static bool TransitiveClose(sbyte[] p, int n)
    {
        for (int k = 0; k < n; k++)
            for (int i = 0; i < n; i++)
            {
                if (p[i * n + k] != LESS) continue;
                for (int j = 0; j < n; j++)
                {
                    if (p[k * n + j] != LESS) continue;
                    if (i == j) return false;
                    sbyte cur = p[i * n + j];
                    if (cur == GREATER) return false;
                    if (cur == UNKNOWN) { p[i * n + j] = LESS; p[j * n + i] = GREATER; }
                }
            }
        return true;
    }

    // ── small helpers ─────────────────────────────────────────────────────────
    private static IEnumerable<int[]> Combinations(int nW, int size)
    {
        var idx = new int[size];
        for (int i = 0; i < size; i++) idx[i] = i;
        while (true)
        {
            yield return (int[])idx.Clone();
            int k = size - 1;
            while (k >= 0 && idx[k] == nW - size + k) k--;
            if (k < 0) yield break;
            idx[k]++;
            for (int j = k + 1; j < size; j++) idx[j] = idx[j - 1] + 1;
        }
    }

    private static int[,] RandomRegularBiadjacency(int nV, int nW, int degree, int seed)
    {
        var rng = new Random(seed);
        var b = new int[nV, nW];
        for (int v = 0; v < nV; v++)
        {
            var chosen = new HashSet<int>();
            while (chosen.Count < degree) chosen.Add(rng.Next(nW));
            foreach (var w in chosen) b[v, w] = 1;
        }
        return b;
    }

    private static (AdjMatrix, int[]) ScrambleWithTypes(AdjMatrix g, int[] types, int seed)
    {
        int n = g.VertexCount;
        var m = g.ToArray();
        var t = (int[])types.Clone();
        var rng = new Random(seed);
        for (int r = 0; r < n - 1; r++)
        {
            int s = r + rng.Next() % (n - r);
            for (int i = 0; i < n; i++) (m[s, i], m[r, i]) = (m[r, i], m[s, i]);
            for (int i = 0; i < n; i++) (m[i, s], m[i, r]) = (m[i, r], m[i, s]);
            (t[s], t[r]) = (t[r], t[s]);
        }
        return (new AdjMatrix(m), t);
    }
}
