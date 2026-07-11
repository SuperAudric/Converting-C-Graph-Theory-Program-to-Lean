using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ─────────────────────────────────────────────────────────────────────────────
// FUSION-RESOLUTION PROBE (2026-07-11) — measurement only.
//
// Two architecture questions:
//   (Q1) Does the rigid solver's F2-kernel extraction DE-FUSE hidden symmetry —
//        i.e. on a residue whose gauge the cascade DEFERRED (linear oracle off),
//        does dim ker recover that gauge, and do the extracted kernel elements
//        VERIFY as genuine automorphisms of the input graph?
//   (Q2) Does the extraction stay STRUCTURAL (scramble-invariant) on FUSED
//        residues (WL cells coarser than orbits — CFI-deferred, Chang-A)?
//
// This probe is mistargeted, as it checks if the rigid core can be consumed before the symmetries have been removed, which no, it cannot
// This probe ASSERTS nothing about Q1/Q2 (that is the measurement). The only
// Assert is scramble-invariance of the rigid-multipede control, which is already
// an established invariant (Option2ExtractionProbe). Everything else is logged.
//
// Extraction pipeline (RecoverSegments / ExtractRows / RankF2) and the Chang /
// Johnson builders are copied byte-for-byte from Option2ExtractionProbe.cs and
// RruDepthProbe.cs (they are private there). NullSpaceBasis + BuildSwapPerm +
// VerifyAut are new: they turn an extracted kernel element into the permutation
// it implies (segment endpoint-swap on the swap-set X, middles remapped by
// signature XOR (X ∩ incident-segments)) and check adjacency-preservation.
// ─────────────────────────────────────────────────────────────────────────────
public sealed class FusionResolutionProbe
{
    private const sbyte LESS = -1, UNKNOWN = 0, GREATER = 1;
    private const int D = 4;
    private static readonly string LogPath =
        "/tmp/claude-1000/-workspace/59f34b56-7c75-41c7-b064-94cd43f98d92/scratchpad/fusion.log";

    private readonly ITestOutputHelper output;
    public FusionResolutionProbe(ITestOutputHelper o) => output = o;

    private void Log(string line)
    {
        output.WriteLine(line);
        File.AppendAllText(LogPath, line + "\n");
    }

    // ── FIXTURE 1: CFI with linear oracle OFF (deferred gauge) ────────────────
    [Fact]
    public void Fixture1_CFI_LinearOracleOff_KernelRecoversGauge()
    {
        Log("");
        Log("=== FIXTURE 1: CFI, linear oracle OFF (deferred gauge) — does the F2-kernel recover it? ===");
        foreach (var bg in new[] { "Cycle3", "Cycle4", "K4" })
        {
            var pair = CfiGraphGenerator.Generate(bg);
            var g = pair.Even;
            int n = g.VertexCount;
            int[] adj = ExtractAdj(g);

            // (a) descent with the LINEAR ORACLE OFF: gauge is deferred, not consumed.
            var (offOrder, offFlag, offOrb, offVT) = Harvest(n, adj, null, linOracle: false);
            // (b) full descent (oracle on) = ground-truth harvested gauge order → k = log2.
            var (fullOrder, fullFlag, fullOrb, fullVT) = Harvest(n, adj, null, linOracle: true);
            int kKnown = fullOrder > BigInteger.Zero ? (int)BigInteger.Log(fullOrder, 2) + (IsPow2(fullOrder) ? 0 : 0) : -1;
            int betti = BettiOfBase(bg);

            // (c) option-2 extraction pipeline.
            var ex = RunExtraction(n, adj, null);
            var (verOk, verTotal, verNote) = VerifyKernel(n, adj, ex);

            Log($"CFI({bg}) n={n} nW(segs)={ex.nW} rowRank={ex.rank} dimKer={ex.dimKer} " +
                $"| gauge: betti(|E|-|V|+1)={betti} fullDescent|Aut|={fullOrder} (flag={fullFlag},orb={fullOrb},VT={fullVT}) " +
                $"| oracleOFF|Aut|={offOrder} (flag={offFlag},orb={offOrb},VT={offVT}) " +
                $"| kernel-elems-verifying-as-Aut={verOk}/{verTotal} {verNote} " +
                $"| WLcells[{CellHisto(n, adj, null)}]");
        }
    }

    // ── FIXTURE 2: Chang-A ────────────────────────────────────────────────────
    [Fact]
    public void Fixture2_ChangA_KernelVisibility()
    {
        Log("");
        Log("=== FIXTURE 2: Chang-A (SRG(28,12,6,4), |Aut|=384=2^7·3) — does the F2-kernel see any symmetry? ===");
        int n; var t8 = Johnson(8, 2, out n);
        int[] changA = SeidelSwitch(t8, n, ChangMask(n, ChangA));

        var (order, flag, orb, vt) = Harvest(n, changA, null, linOracle: true);
        int cellHisto0Size2 = CountCellsOfSize(n, changA, null, 2);
        var ex = RunExtraction(n, changA);
        var (verOk, verTotal, verNote) = VerifyKernel(n, changA, ex);

        Log($"Chang-A n={n} | normal descent |Aut|={order} (flag={flag}, orbits={orb}, VT={vt}) " +
            $"[ground truth |Aut(Chang-A)|=384=2^7·3] | WL size-2 cells={cellHisto0Size2} " +
            $"| extraction nW(segs)={ex.nW} rowspaceRank={ex.rank} dimKer={ex.dimKer} " +
            $"| kernel-elems-verifying-as-Aut={verOk}/{verTotal} {verNote} " +
            $"| WLcells[{CellHisto(n, changA, null)}]");
    }

    // ── FIXTURE 3: scramble-invariance of extraction on FUSED residues ────────
    [Fact]
    public void Fixture3_ScrambleInvariance_OnFusedResidues()
    {
        Log("");
        Log("=== FIXTURE 3: scramble-invariance of extraction (dim ker, rowspace rank) over 5 relabelings ===");

        // (a) CFI (linear-oracle-off residue) — FUSED, do NOT assert.
        foreach (var bg in new[] { "Cycle3", "K4" })
        {
            var g = CfiGraphGenerator.Generate(bg).Even;
            ScrambleReport($"CFI({bg})", ExtractAdj(g), g.VertexCount, null, assertInvariant: false);
        }

        // (b) Chang-A — FUSED, do NOT assert.
        {
            int n; var t8 = Johnson(8, 2, out n);
            ScrambleReport("Chang-A", SeidelSwitch(t8, n, ChangMask(n, ChangA)), n, null, assertInvariant: false);
        }

        // (c) rigid multipede control — established invariant, ASSERT.
        {
            var mp = MultipedeGenerator.BuildRandomRegular(8, 6, 3, seed: 0);
            MultipedeGenerator.AssertRigid(mp);
            ScrambleReport($"RigidMultipede({mp.BaseName})", ExtractAdj(mp.Graph), mp.Graph.VertexCount,
                           mp.VertexTypes, assertInvariant: true);
        }
    }

    private void ScrambleReport(string name, int[] adj0, int n, int[]? types0, bool assertInvariant)
    {
        var kers = new List<int>();
        var ranks = new List<int>();
        var nWs = new List<int>();
        for (int s = 0; s < 5; s++)
        {
            var (adj, types) = ScrambleFlat(adj0, n, types0, seed: 9100 + s);
            var ex = RunExtraction(n, adj, types);
            kers.Add(ex.dimKer); ranks.Add(ex.rank); nWs.Add(ex.nW);
        }
        bool kerInv = kers.Distinct().Count() == 1;
        bool rankInv = ranks.Distinct().Count() == 1;
        bool nWInv = nWs.Distinct().Count() == 1;
        Log($"{name,-22} n={n,4} | nW={string.Join(",", nWs)} (inv={nWInv}) " +
            $"| dimKer={string.Join(",", kers)} (inv={kerInv}) " +
            $"| rank={string.Join(",", ranks)} (inv={rankInv})");
        if (assertInvariant)
        {
            Assert.True(kerInv, $"{name}: dim ker not scramble-invariant");
            Assert.True(rankInv, $"{name}: rowspace rank not scramble-invariant");
        }
    }

    // ── extraction driver ─────────────────────────────────────────────────────
    private readonly struct Extraction
    {
        public readonly int nW, rank, dimKer;
        public readonly List<int[]> segs;
        public readonly List<ulong> rows;
        public Extraction(int nW, int rank, int dimKer, List<int[]> segs, List<ulong> rows)
        { this.nW = nW; this.rank = rank; this.dimKer = dimKer; this.segs = segs; this.rows = rows; }
    }

    private static Extraction RunExtraction(int n, int[] adj, int[]? types = null)
    {
        sbyte[] pBase = SeedFromTypes(n, types);
        var segs = RecoverSegments(n, adj, pBase);
        var rows = ExtractRows(n, adj, pBase, segs, D);
        int rank = RankF2(rows);
        return new Extraction(segs.Count, rank, segs.Count - rank, segs, rows);
    }

    // Build every null-space basis element, turn it into the permutation it
    // implies, and count how many verify as genuine automorphisms of adj.
    private (int ok, int total, string note) VerifyKernel(int n, int[] adj, Extraction ex)
    {
        if (ex.nW == 0) return (0, 0, "(no segments ⟹ no kernel elements)");
        var basis = NullSpaceBasis(ex.rows, ex.nW);
        if (basis.Count == 0) return (0, 0, "(dim ker 0)");
        var part = new WarmPartition(n);
        part.Refine(adj, SeedFromTypes(n, null));   // cells for the middle remap
        int ok = 0, unbuildable = 0;
        foreach (var x in basis)
        {
            var perm = BuildSwapPerm(n, adj, ex.segs, part, x);
            if (perm == null) { unbuildable++; continue; }
            if (VerifyAut(n, adj, perm)) ok++;
        }
        string note = unbuildable > 0 ? $"({unbuildable} unbuildable)" : "";
        return (ok, basis.Count, note);
    }

    // The permutation implied by swap-set X: swap the two endpoints of each
    // segment in X; every non-segment vertex m (a "middle") maps within its WL
    // cell to the vertex whose a-signature = sig(m) XOR (X ∩ incident-segments(m)).
    private static int[]? BuildSwapPerm(int n, int[] adj, List<int[]> segs, WarmPartition part, ulong X)
    {
        int nW = segs.Count;
        var aEnd = new int[nW]; var bEnd = new int[nW];
        var segOf = new int[n]; for (int i = 0; i < n; i++) segOf[i] = -1;
        for (int sr = 0; sr < nW; sr++)
        {
            aEnd[sr] = segs[sr][0]; bEnd[sr] = segs[sr][1];
            segOf[segs[sr][0]] = sr; segOf[segs[sr][1]] = sr;
        }

        ulong Sig(int m)
        {
            ulong k = 0;
            for (int u = 0; u < n; u++)
                if (adj[m * n + u] != 0 && segOf[u] != -1 && u == aEnd[segOf[u]]) k |= 1UL << segOf[u];
            return k;
        }
        ulong Inc(int m)
        {
            ulong k = 0;
            for (int u = 0; u < n; u++)
                if (adj[m * n + u] != 0 && segOf[u] != -1) k |= 1UL << segOf[u];
            return k;
        }

        var perm = new int[n];
        for (int i = 0; i < n; i++) perm[i] = i;
        for (int sr = 0; sr < nW; sr++)
            if (((X >> sr) & 1) != 0) { perm[aEnd[sr]] = bEnd[sr]; perm[bEnd[sr]] = aEnd[sr]; }

        // per-cell signature index over the non-segment vertices.
        var cellSig = new Dictionary<int, Dictionary<ulong, int>>();
        for (int m = 0; m < n; m++)
        {
            if (segOf[m] != -1) continue;
            int cell = part.CellOf[m];
            ulong sig = Sig(m);
            if (!cellSig.TryGetValue(cell, out var d)) cellSig[cell] = d = new Dictionary<ulong, int>();
            if (d.ContainsKey(sig)) return null;   // duplicate sig in a cell ⟹ ambiguous
            d[sig] = m;
        }
        for (int m = 0; m < n; m++)
        {
            if (segOf[m] != -1) continue;
            ulong target = Sig(m) ^ (X & Inc(m));
            if (!cellSig[part.CellOf[m]].TryGetValue(target, out int mp)) return null;
            perm[m] = mp;
        }

        // must be a bijection.
        var seen = new bool[n];
        foreach (int v in perm) { if (v < 0 || v >= n || seen[v]) return null; seen[v] = true; }
        return perm;
    }

    private static bool VerifyAut(int n, int[] adj, int[] perm)
    {
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                if (adj[i * n + j] != adj[perm[i] * n + perm[j]]) return false;
        return true;
    }

    // null-space basis of the rows over F2^nW.
    private static List<ulong> NullSpaceBasis(List<ulong> rows, int nW)
    {
        var basisRows = new List<(int pivot, ulong row)>();
        foreach (var r in rows)
        {
            ulong cur = r;
            foreach (var (pc, br) in basisRows) if (((cur >> pc) & 1) != 0) cur ^= br;
            if (cur == 0) continue;
            int p = System.Numerics.BitOperations.TrailingZeroCount(cur);
            for (int i = 0; i < basisRows.Count; i++)
                if (((basisRows[i].row >> p) & 1) != 0)
                    basisRows[i] = (basisRows[i].pivot, basisRows[i].row ^ cur);
            basisRows.Add((p, cur));
        }
        var pivotCols = new HashSet<int>(basisRows.Select(b => b.pivot));
        var basis = new List<ulong>();
        for (int f = 0; f < nW; f++)
        {
            if (pivotCols.Contains(f)) continue;
            ulong x = 1UL << f;
            foreach (var (pc, br) in basisRows) if (((br >> f) & 1) != 0) x |= 1UL << pc;
            basis.Add(x);
        }
        return basis;
    }

    // ── driving the descent to harvest |Aut| ──────────────────────────────────
    private static (BigInteger order, bool flagged, int orbits, bool vt) Harvest(
        int n, int[] adj, int[]? types, bool linOracle)
    {
        var d = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        { EnableLinearOracle = linOracle, EnableDeferral = true };
        var r = d.Canonize(SeedFromTypes(n, types), new WarmPartition(n));
        var (orbits, maxOrb) = OrbitProfile(r.ResidualGroup, n);
        return (r.ResidualGroup.Order, r.Flagged, orbits, orbits == 1 && maxOrb == n);
    }

    private static (int orbits, int maxOrbit) OrbitProfile(PermutationGroup g, int n)
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

    private static int CountCellsOfSize(int n, int[] adj, int[]? types, int size)
    {
        var part = new WarmPartition(n);
        part.Refine(adj, SeedFromTypes(n, types));
        var byCell = new Dictionary<int, int>();
        for (int v = 0; v < n; v++)
        {
            byCell.TryGetValue(part.CellOf[v], out int c);
            byCell[part.CellOf[v]] = c + 1;
        }
        return byCell.Values.Count(c => c == size);
    }

    // WL cell-size histogram (raw, no coloring): "count×sizeK, ..." — shows why
    // segment recovery (size-2 stable cells) finds what it finds.
    private static string CellHisto(int n, int[] adj, int[]? types)
    {
        var part = new WarmPartition(n);
        part.Refine(adj, SeedFromTypes(n, types));
        var byCell = new Dictionary<int, int>();
        for (int v = 0; v < n; v++)
        {
            byCell.TryGetValue(part.CellOf[v], out int c);
            byCell[part.CellOf[v]] = c + 1;
        }
        return string.Join(",", byCell.Values.GroupBy(x => x).OrderBy(g => g.Key)
            .Select(g => $"{g.Count()}×size{g.Key}"));
    }

    private static bool IsPow2(BigInteger x) => x > 0 && (x & (x - 1)) == 0;
    private static int BettiOfBase(string bg) => bg switch
    {
        "Cycle3" => 1, "Cycle4" => 1, "K4" => 3, "K33" => 4, _ => -1
    };

    // ─────────────────────────────────────────────────────────────────────────
    // Copied byte-for-byte from Option2ExtractionProbe.cs (private helpers there)
    // ─────────────────────────────────────────────────────────────────────────
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

    private static HashSet<int> ForcingClosure(
        int n, int[] adj, sbyte[] pBase, List<int[]> segs, IEnumerable<int> fixedSegs)
    {
        var p = (sbyte[])pBase.Clone();
        foreach (int si in fixedSegs)
        {
            int a = segs[si][0], b = segs[si][1];
            p[a * n + b] = LESS; p[b * n + a] = GREATER;
        }
        if (!TransitiveClose(p, n)) return new HashSet<int>();
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

    private static int[] ExtractAdj(AdjMatrix g)
    {
        int n = g.VertexCount;
        var adj = new int[n * n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                adj[i * n + j] = g[i, j];
        return adj;
    }

    // null types ⟹ all-UNKNOWN seed (RruDepthProbe convention).
    private static sbyte[] SeedFromTypes(int n, int[]? types)
    {
        var p = new sbyte[n * n];
        if (types == null) return p;
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

    private static IEnumerable<int[]> Combinations(int nW, int size)
    {
        if (size > nW) yield break;
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

    // scramble a flat adjacency (+optional types); mirrors ScrambleWithTypes.
    private static (int[] adj, int[]? types) ScrambleFlat(int[] adj0, int n, int[]? types0, int seed)
    {
        var perm = Enumerable.Range(0, n).ToArray();
        var rng = new Random(seed);
        for (int r = n - 1; r > 0; r--) { int s = rng.Next(r + 1); (perm[r], perm[s]) = (perm[s], perm[r]); }
        // new[perm[i]] = old[i]
        var adj = new int[n * n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                adj[perm[i] * n + perm[j]] = adj0[i * n + j];
        int[]? types = null;
        if (types0 != null) { types = new int[n]; for (int i = 0; i < n; i++) types[perm[i]] = types0[i]; }
        return (adj, types);
    }

    // ── Chang / Johnson builders (copied from RruDepthProbe.cs) ───────────────
    private static int[] Johnson(int n, int k, out int nv)
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

    private static int[] SeidelSwitch(int[] adj, int n, bool[] inS)
    {
        var b = (int[])adj.Clone();
        for (int u = 0; u < n; u++)
            for (int v = u + 1; v < n; v++)
                if (inS[u] != inS[v]) { int f = 1 - b[u * n + v]; b[u * n + v] = f; b[v * n + u] = f; }
        return b;
    }

    private static bool[] ChangMask(int n8, (int, int)[] edges)
    {
        var idx = new Dictionary<int, int>(); int c = 0;
        for (int m = 0; m < (1 << 8); m++)
            if (System.Numerics.BitOperations.PopCount((uint)m) == 2) idx[m] = c++;
        var mask = new bool[n8];
        foreach (var (a, b) in edges) mask[idx[(1 << a) | (1 << b)]] = true;
        return mask;
    }

    private static readonly (int, int)[] ChangA = { (0, 1), (2, 3), (4, 5), (6, 7) };
}
