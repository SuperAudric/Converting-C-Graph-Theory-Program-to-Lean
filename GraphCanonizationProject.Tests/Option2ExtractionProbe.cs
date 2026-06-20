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

    // ─────────────────────────────────────────────────────────────────────────
    // D-M2 — F2 Gaussian solve + the canonical twist-class, in C#.
    //
    // The iso-invariant twist content is the coker(A_G) class c + im(A_G) (D-M0
    // finding: c itself is gauge/orientation-dependent), taken as a canonical
    // coset representative over the canonical base order. The canonical order is
    // free: WarmPartition assigns iso-invariant canonical cell-ids, and the fine
    // colouring makes the base WL-discrete at the cell level (each segment its own
    // 2-cell, each gadget its own cell), so ordering cells by CellOf id IS the
    // canonical variable order (scope (b), realised directly — no brute base canon).
    //
    // Deliverable: the twist-class is scramble-invariant AND SEPARATING — twisted
    // vs untwisted multipedes get different classes exactly when their coker
    // classes differ (matching base-level ground truth). Non-vacuous.
    // ─────────────────────────────────────────────────────────────────────────
    [Fact]
    public void TwistClass_Invariant_And_Separating()
    {
        // an odd base with nV>nW so coker(A_G) is nontrivial (twins can differ).
        int[,]? biadj = null;
        for (int seed = 0; seed < 200; seed++)
        {
            var b = RandomRegularBiadjacency(8, 6, 3, seed);
            if (ColRankF2(b) == 6) { biadj = b; break; }
        }
        Assert.NotNull(biadj);
        int nV = biadj!.GetLength(0), nW = biadj.GetLength(1);
        int cokerDim = nV - ColRankF2(biadj);
        Assert.True(cokerDim > 0, "need coker>0 for a meaningful separation test");

        // ground-truth: twist of gadget set T is isomorphic to untwisted iff
        //   e_T in im(A_G) = col-space. Build the column space in ORIGINAL order.
        var colsOrig = new List<ulong>();
        for (int w = 0; w < nW; w++)
        {
            ulong col = 0;
            for (int v = 0; v < nV; v++) if ((biadj[v, w] & 1) != 0) col |= 1UL << v;
            colsOrig.Add(col);
        }

        var untw = BuildMultipedeLocal(biadj, new HashSet<int>());
        var classUntw = CanonicalTwistClassRuns(untw.Item1, untw.Item2);
        Assert.True(classUntw.inv, "untwisted twist-class not scramble-invariant");
        Assert.Equal(0, classUntw.dimKer);   // rigid

        // (a) CORRECTNESS — every single-gadget twist: pipeline differs ⟺ e_g ∉ im(A_G).
        int separated = 0;
        for (int g = 0; g < nV; g++)
        {
            var tw = BuildMultipedeLocal(biadj, new HashSet<int> { g });
            var classTw = CanonicalTwistClassRuns(tw.Item1, tw.Item2);
            Assert.True(classTw.inv, $"twist{{{g}}} class not scramble-invariant");

            bool pipelineDiffers = classTw.cls != classUntw.cls;
            bool gtDiffers = CosetMin(1UL << g, colsOrig) != 0;   // e_g ∉ im(A_G)
            Assert.Equal(gtDiffers, pipelineDiffers);             // pipeline == ground truth
            if (pipelineDiffers) separated++;
        }

        // (b) a GUARANTEED-MERGED twin (non-vacuity, base-robust): twisting the
        //     gadget-set supp(col_w) = the gauge flip of segment w ⟹ e_T ∈ im(A_G)
        //     ⟹ ISOMORPHIC to untwisted ⟹ same canonical class.
        var Tmerged = new HashSet<int>();
        for (int v = 0; v < nV; v++) if ((biadj[v, 0] & 1) != 0) Tmerged.Add(v);
        ulong eMerged = 0; foreach (int v in Tmerged) eMerged |= 1UL << v;
        Assert.Equal(0UL, CosetMin(eMerged, colsOrig));          // GT: gauge ⟹ in im
        var mClass = CanonicalTwistClassRuns(BuildMultipedeLocal(biadj, Tmerged).Item1,
                                             BuildMultipedeLocal(biadj, Tmerged).Item2);
        Assert.True(mClass.inv);
        Assert.Equal(classUntw.cls, mClass.cls);                 // MERGED with untwisted

        // (c) a GUARANTEED-SEPARATING twin exists since coker>0; pipeline separates it.
        Assert.True(separated > 0, "coker>0 but no single-gadget separation found");

        output.WriteLine(
            $"TwistClass nV={nV} nW={nW} cokerDim={cokerDim}: " +
            $"{separated}/{nV} single-gadget twists give a DISTINCT class (e_g∉im A_G), " +
            $"the constructed gauge twin (supp col_0) MERGES; all scramble-invariant, all match ground truth.");
    }

    private (ulong cls, bool inv, int dimKer) CanonicalTwistClassRuns(AdjMatrix g0, int[] t0)
    {
        var classes = new List<ulong>();
        int dimKer = -1;
        for (int s = -1; s < 4; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = g0; t = (int[])t0.Clone(); }
            else (g, t) = ScrambleWithTypes(g0, t0, seed: 5200 + s);
            var (cls, dk) = CanonicalTwistClass(g, t);
            classes.Add(cls); dimKer = dk;
        }
        return (classes[0], classes.Distinct().Count() == 1, dimKer);
    }

    // D3 (read c, recognition-free) + D4 (coset_min over the canonical base order).
    private static (ulong cls, int dimKer) CanonicalTwistClass(AdjMatrix g, int[] types)
    {
        int n = g.VertexCount;
        int[] adj = ExtractAdj(g);
        sbyte[] p = SeedFromTypes(n, types);
        var part = new WarmPartition(n);
        part.Refine(adj, p);

        var byCell = new Dictionary<int, List<int>>();
        for (int v = 0; v < n; v++)
        {
            if (!byCell.TryGetValue(part.CellOf[v], out var l)) byCell[part.CellOf[v]] = l = new List<int>();
            l.Add(v);
        }
        // canonical order = ascending WarmPartition cell-id (iso-invariant).
        var segCells = byCell.Where(kv => kv.Value.Count == 2)
                             .OrderBy(kv => kv.Key).Select(kv => kv.Value).ToList();
        var gadCells = byCell.Where(kv => kv.Value.Count > 2)
                             .OrderBy(kv => kv.Key).Select(kv => kv.Value).ToList();
        int nW = segCells.Count, nV = gadCells.Count;

        var des = new int[nW];                 // orientation reference per segment (gauge — modded out)
        var vseg = new Dictionary<int, int>();
        for (int sr = 0; sr < nW; sr++)
        {
            des[sr] = segCells[sr].Min();
            foreach (int v in segCells[sr]) vseg[v] = sr;
        }

        var cols = new ulong[nW];              // A_G columns over canonical gadget-rank bits
        ulong cvec = 0;
        for (int gr = 0; gr < nV; gr++)
        {
            int m = gadCells[gr].Min();        // any middle: all share the gadget's parity
            int hit = 0;
            for (int u = 0; u < n; u++)
            {
                if (adj[m * n + u] == 0) continue;
                if (!vseg.TryGetValue(u, out int sr)) continue;
                cols[sr] |= 1UL << gr;         // gadget gr incident to segment sr
                if (u == des[sr]) hit ^= 1;
            }
            if (hit == 1) cvec |= 1UL << gr;
        }
        ulong cls = CosetMin(cvec, cols);
        int dimKer = nW - RankF2(cols.ToList());
        return (cls, dimKer);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // D-M3 — the Phase-2 pre-processor: canonize the rigid multipede END-TO-END,
    // no F2-layer IR. Base order from WarmPartition cell-ids (D-M2); the unique
    // orientation from the twist solve A_G·o = c ⊕ coset_min(c) (rigid ⟹ ker=0 ⟹
    // unique o); middles ordered by subset under that orientation. Emits a full
    // canonical adjacency matrix.
    //
    // Deliverable: iso-invariant (scrambles ⟹ byte-identical matrix) AND complete
    // — the GAUGE twin (isomorphic to untwisted) canonicalises to the SAME matrix,
    // a SEPARATING twin to a different one. That the gauge twin maps to the same
    // matrix is the proof the twist-solve canonicalises (not merely classifies).
    // ─────────────────────────────────────────────────────────────────────────
    [Fact]
    public void CanonizeEndToEnd_Invariant_And_Complete()
    {
        int[,]? biadj = null;
        for (int seed = 0; seed < 200; seed++)
        {
            var b = RandomRegularBiadjacency(8, 6, 3, seed);
            if (ColRankF2(b) == 6) { biadj = b; break; }
        }
        Assert.NotNull(biadj);
        int nV = biadj!.GetLength(0), nW = biadj.GetLength(1);

        var colsOrig = new List<ulong>();
        for (int w = 0; w < nW; w++)
        {
            ulong col = 0;
            for (int v = 0; v < nV; v++) if ((biadj[v, w] & 1) != 0) col |= 1UL << v;
            colsOrig.Add(col);
        }

        var untw = BuildMultipedeLocal(biadj, new HashSet<int>());
        string cf0 = CanonFormRuns(untw.Item1, untw.Item2, out bool inv0);
        Assert.True(inv0, "untwisted canonical form not scramble-invariant");

        // GAUGE twin (segment-0 flip = twist supp(col_0)) — ISOMORPHIC to untwisted.
        var Tg = new HashSet<int>();
        for (int v = 0; v < nV; v++) if ((biadj[v, 0] & 1) != 0) Tg.Add(v);
        Assert.Equal(0UL, CosetMin(GadgetSetMask(Tg), colsOrig));     // GT: ∈ im
        var gauge = BuildMultipedeLocal(biadj, Tg);
        string cfG = CanonFormRuns(gauge.Item1, gauge.Item2, out bool invG);
        Assert.True(invG);
        Assert.Equal(cf0, cfG);          // ★ isomorphic ⟹ IDENTICAL canonical matrix

        // SEPARATING twin (some e_g ∉ im) — NON-isomorphic.
        int sepG = -1;
        for (int g = 0; g < nV; g++) if (CosetMin(1UL << g, colsOrig) != 0) { sepG = g; break; }
        Assert.True(sepG >= 0);
        var sep = BuildMultipedeLocal(biadj, new HashSet<int> { sepG });
        string cfS = CanonFormRuns(sep.Item1, sep.Item2, out bool invS);
        Assert.True(invS);
        Assert.NotEqual(cf0, cfS);       // non-isomorphic ⟹ different canonical matrix

        output.WriteLine(
            $"CanonizeEndToEnd nV={nV} nW={nW}: untwisted form scramble-invariant; " +
            $"GAUGE twin (supp col_0) → SAME canonical matrix (twist-solve canonicalises); " +
            $"SEPARATING twin (gadget {sepG}) → different matrix. Complete + iso-invariant, no F2-layer IR.");
    }

    // coker=0 regime (square odd circulant): EVERY twist is isomorphic to
    // untwisted, so all must canonicalise to one identical form — a strong
    // completeness stress test (m distinct graphs collapse to a single canonical).
    [Theory]
    [InlineData(6)]
    [InlineData(8)]
    public void CanonizeEndToEnd_Circulant_AllTwistsMerge(int m)
    {
        var biadj = MultipedeGenerator.CirculantBiadjacency(m, new[] { 0, 1, 3 });
        Assert.Equal(m, ColRankF2(biadj));   // square, full rank ⟹ coker = 0
        var untw = BuildMultipedeLocal(biadj, new HashSet<int>());
        string cf0 = CanonFormRuns(untw.Item1, untw.Item2, out bool inv0);
        Assert.True(inv0);
        for (int g = 0; g < m; g++)
        {
            var tw = BuildMultipedeLocal(biadj, new HashSet<int> { g });
            string cf = CanonFormRuns(tw.Item1, tw.Item2, out bool inv);
            Assert.True(inv, $"circulant{m} twist{{{g}}} not scramble-invariant");
            Assert.Equal(cf0, cf);           // coker=0 ⟹ isomorphic ⟹ same canonical form
        }
        output.WriteLine($"CanonizeEndToEnd Circulant{m} (coker=0): all {m} single-gadget twists " +
                         $"canonicalise to the SAME form as untwisted; scramble-invariant.");
    }

    private static ulong GadgetSetMask(HashSet<int> s)
    {
        ulong m = 0; foreach (int v in s) m |= 1UL << v; return m;
    }

    private string CanonFormRuns(AdjMatrix g0, int[] t0, out bool invariant)
    {
        var forms = new List<string>();
        for (int s = -1; s < 4; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = g0; t = (int[])t0.Clone(); }
            else (g, t) = ScrambleWithTypes(g0, t0, seed: 6300 + s);
            forms.Add(CanonicalForm(g, t));
        }
        invariant = forms.Distinct().Count() == 1;
        return forms[0];
    }

    // The end-to-end canonical labelling → canonical adjacency, as a string.
    private static string CanonicalForm(AdjMatrix g, int[] types)
    {
        int n = g.VertexCount;
        int[] adj = ExtractAdj(g);
        sbyte[] p = SeedFromTypes(n, types);
        var part = new WarmPartition(n);
        part.Refine(adj, p);

        var byCell = new Dictionary<int, List<int>>();
        for (int v = 0; v < n; v++)
        {
            if (!byCell.TryGetValue(part.CellOf[v], out var l)) byCell[part.CellOf[v]] = l = new List<int>();
            l.Add(v);
        }
        var segCells = byCell.Where(kv => kv.Value.Count == 2)
                             .OrderBy(kv => kv.Key).Select(kv => kv.Value).ToList();
        var gadCells = byCell.Where(kv => kv.Value.Count > 2)
                             .OrderBy(kv => kv.Key).Select(kv => kv.Value).ToList();
        int nW = segCells.Count, nV = gadCells.Count;

        var vseg = new Dictionary<int, int>();
        var desV = new int[nW]; var othV = new int[nW];
        for (int sr = 0; sr < nW; sr++)
        {
            desV[sr] = segCells[sr].Min(); othV[sr] = segCells[sr].Max();
            foreach (int v in segCells[sr]) vseg[v] = sr;
        }

        // columns of A_G + raw c over the canonical gadget order (D-M2).
        var cols = new ulong[nW]; ulong cRaw = 0;
        for (int gr = 0; gr < nV; gr++)
        {
            int m = gadCells[gr].Min(); int hit = 0;
            for (int u = 0; u < n; u++)
            {
                if (adj[m * n + u] == 0 || !vseg.TryGetValue(u, out int sr)) continue;
                cols[sr] |= 1UL << gr;
                if (u == desV[sr]) hit ^= 1;
            }
            if (hit == 1) cRaw |= 1UL << gr;
        }
        ulong cStar = CosetMin(cRaw, cols);
        ulong o = SolveF2(cols.ToList(), cRaw ^ cStar)
                  ?? throw new InvalidOperationException("twist target not in im(A_G)");

        // canonical orientation: first[sr] = oriented "0" vertex of segment sr.
        var first = new int[nW]; var second = new int[nW];
        for (int sr = 0; sr < nW; sr++)
        {
            bool flip = ((o >> sr) & 1) != 0;
            first[sr] = flip ? othV[sr] : desV[sr];
            second[sr] = flip ? desV[sr] : othV[sr];
        }

        // canonical vertex order: segments (first,second) then gadgets' middles
        // ordered by their subset bitmask under the canonical orientation.
        var order = new List<int>(n);
        for (int sr = 0; sr < nW; sr++) { order.Add(first[sr]); order.Add(second[sr]); }
        for (int gr = 0; gr < nV; gr++)
        {
            var mids = gadCells[gr];
            ulong Key(int m)
            {
                ulong k = 0;
                for (int u = 0; u < n; u++)
                    if (adj[m * n + u] != 0 && vseg.TryGetValue(u, out int sr) && u == first[sr])
                        k |= 1UL << sr;
                return k;
            }
            order.AddRange(mids.OrderBy(Key));
        }

        // canonical adjacency in this order, serialised.
        var sb = new System.Text.StringBuilder(n * n);
        for (int i = 0; i < order.Count; i++)
            for (int j = 0; j < order.Count; j++)
                sb.Append(adj[order[i] * n + order[j]] != 0 ? '1' : '0');
        return sb.ToString();
    }

    // solve  XOR_{sr ∈ S} cols[sr] = target  over F2; return S as a bitmask
    // (the unique solution when cols have full column rank), or null if no solution.
    private static ulong? SolveF2(List<ulong> cols, ulong target)
    {
        var pivot = new Dictionary<int, (ulong val, ulong tag)>();
        for (int sr = 0; sr < cols.Count; sr++)
        {
            ulong cur = cols[sr], tag = 1UL << sr;
            while (cur != 0)
            {
                int lb = System.Numerics.BitOperations.Log2(cur);
                if (pivot.TryGetValue(lb, out var b)) { cur ^= b.val; tag ^= b.tag; }
                else { pivot[lb] = (cur, tag); break; }
            }
        }
        ulong ccur = target, otag = 0;
        while (ccur != 0)
        {
            int lb = System.Numerics.BitOperations.Log2(ccur);
            if (pivot.TryGetValue(lb, out var b)) { ccur ^= b.val; otag ^= b.tag; }
            else return null;
        }
        return otag;
    }

    private static List<ulong> ReducedBasis(IEnumerable<ulong> vecs)
    {
        var basis = new List<ulong>();
        foreach (var v in vecs)
        {
            ulong cur = v;
            foreach (var b in basis) cur = Math.Min(cur, cur ^ b);
            if (cur != 0)
            {
                for (int i = 0; i < basis.Count; i++) basis[i] = Math.Min(basis[i], basis[i] ^ cur);
                basis.Add(cur);
            }
        }
        return basis;
    }

    // canonical (lex-min) representative of c + span(cols) over F2.
    private static ulong CosetMin(ulong c, IEnumerable<ulong> cols)
    {
        var basis = ReducedBasis(cols);
        basis.Sort((a, b) => b.CompareTo(a));   // by leading bit, descending
        ulong cur = c;
        bool changed = true;
        while (changed)
        {
            changed = false;
            foreach (var b in basis)
                if ((cur ^ b) < cur) { cur ^= b; changed = true; }
        }
        return cur;
    }

    // local twisted-multipede builder (MultipedeGenerator has no twist param):
    // gadget v in `twist` uses ODD-cardinality subsets (the CFI flip).
    private static (AdjMatrix, int[]) BuildMultipedeLocal(int[,] biadj, HashSet<int> twist)
    {
        int nV = biadj.GetLength(0), nW = biadj.GetLength(1);
        var nbr = new List<int>[nV];
        for (int v = 0; v < nV; v++)
        {
            nbr[v] = new List<int>();
            for (int w = 0; w < nW; w++) if (biadj[v, w] != 0) nbr[v].Add(w);
        }
        var aIdx = new int[nW]; var bIdx = new int[nW];
        int idx = 0;
        for (int w = 0; w < nW; w++) { aIdx[w] = idx++; bIdx[w] = idx++; }
        var mids = new List<(int v, int bm)>();
        for (int v = 0; v < nV; v++)
        {
            int d = nbr[v].Count, want = twist.Contains(v) ? 1 : 0;
            for (int bm = 0; bm < (1 << d); bm++)
                if (System.Numerics.BitOperations.PopCount((uint)bm) % 2 == want)
                    mids.Add((v, bm));
        }
        var midIdx = new int[mids.Count];
        for (int i = 0; i < mids.Count; i++) midIdx[i] = idx++;
        int n = idx;
        var adj = new int[n, n];
        for (int i = 0; i < mids.Count; i++)
        {
            var (v, bm) = mids[i]; int mi = midIdx[i]; int d = nbr[v].Count;
            for (int k = 0; k < d; k++)
            {
                int w = nbr[v][k];
                int target = ((bm >> k) & 1) != 0 ? aIdx[w] : bIdx[w];
                adj[mi, target] = 1; adj[target, mi] = 1;
            }
        }
        var types = new int[n];
        for (int w = 0; w < nW; w++) { types[aIdx[w]] = w; types[bIdx[w]] = w; }
        for (int i = 0; i < mids.Count; i++) types[midIdx[i]] = nW + mids[i].v;
        return (new AdjMatrix(adj), types);
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
