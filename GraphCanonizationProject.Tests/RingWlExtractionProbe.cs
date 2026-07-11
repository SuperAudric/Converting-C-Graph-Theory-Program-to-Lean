using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ─────────────────────────────────────────────────────────────────────────────
// RING WL-EXTRACTION PROBE (2026-07-11) — the ring twin of Option-2 D-M1.
// Drives the REAL canonizer refinement (WarmPartition = the descent's 1-WL) on a
// native-A-multipede, generalizing Option2ExtractionProbe from F₂ (2-state
// segments, size-2 cells) to a finite abelian A (|A|-state segments, size-|A| cells).
//
// STAGE RM-1 (this file): recognition-free SEGMENT RECOGNITION + cold WL-fusion.
//   Build the native-A-multipede as an AdjMatrix + VertexTypes, scramble it, run
//   the genuine WarmPartition, and confirm the |A| states of each segment fuse into
//   ONE size-|A| cell (the ring twin of the "cold 1-WL sees fused |A|-cells" finding,
//   §11.11 Z₄ probe) — recovered as the size-|A| cells among the segment-coloured
//   vertices, count == nW, scramble-invariant.
//   (RM-2 forcing==A-unit-prop, RM-3 ring inference, RM-4 kernel — follow-ons.)
// ─────────────────────────────────────────────────────────────────────────────
public sealed class RingWlExtractionProbe
{
    private const sbyte LESS = -1, UNKNOWN = 0, GREATER = 1;
    private readonly ITestOutputHelper _out;
    public RingWlExtractionProbe(ITestOutputHelper o) => _out = o;

    // ── finite abelian group ⊕ Z/d_i ──────────────────────────────────────────
    private sealed class Ab
    {
        public readonly string Name; public readonly int[] Inv; public readonly int N;
        public Ab(string name, params int[] inv) { Name = name; Inv = inv; N = inv.Aggregate(1, (a, b) => a * b); }
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

    // ── native-A-multipede in production format (AdjMatrix + VertexTypes) ──────
    // segment-state (p,a) -> vertex p*|A|+a, coloured by segment p (type p < nW).
    // gadget-tuple vertices appended, coloured by line (type nW+lineId). Bipartite:
    // each gadget-tuple joins the |line| segment-states its (sum-zero) tuple selects.
    private static (AdjMatrix g, int[] types, int nW) BuildNativeMultipede(Ab A, List<int[]> lines, int nW)
    {
        int segCount = nW * A.N;
        var edges = new List<(int u, int v)>();
        var gTypes = new List<int>();
        int gid = 0;
        for (int li = 0; li < lines.Count; li++)
            foreach (var t in TuplesSumZero(A, lines[li].Length))
            {
                int gv = segCount + gid++; gTypes.Add(nW + li);
                for (int i = 0; i < lines[li].Length; i++)
                    edges.Add((gv, lines[li][i] * A.N + t[i]));
            }
        int n = segCount + gid;
        var m = new int[n, n];
        foreach (var (u, v) in edges) { m[u, v] = 1; m[v, u] = 1; }
        var types = new int[n];
        for (int p = 0; p < nW; p++) for (int a = 0; a < A.N; a++) types[p * A.N + a] = p;
        for (int i = 0; i < gid; i++) types[segCount + i] = gTypes[i];
        return (new AdjMatrix(m), types, nW);
    }

    // circulant base incidence: nW points, nW lines, line i = { i+off (mod nW) : off in offsets }.
    private static List<int[]> CirculantLines(int nW, int[] offsets)
    {
        var lines = new List<int[]>();
        for (int i = 0; i < nW; i++) lines.Add(offsets.Select(o => (i + o) % nW).Distinct().ToArray());
        return lines;
    }

    [Theory]
    [InlineData("Z2", 2)]     // sanity: reproduces the F₂ 2-state segment structure
    [InlineData("Z4", 4)]
    [InlineData("Z2^2", 4)]
    [InlineData("Z3", 3)]
    public void RM1_SegmentsRecognizedAsSizeA_ColdFused_ScrambleInvariant(string name, int asz)
    {
        var A = name switch
        {
            "Z2" => new Ab("Z2", 2),
            "Z4" => new Ab("Z4", 4),
            "Z2^2" => new Ab("Z2^2", 2, 2),
            "Z3" => new Ab("Z3", 3),
            _ => throw new ArgumentException(name)
        };
        Assert.Equal(asz, A.N);   // |A| == the declared segment (cell) size
        int nW = 6;
        var lines = CirculantLines(nW, new[] { 0, 1, 3 });   // degree-3 gadgets
        var (g0, t0, _) = BuildNativeMultipede(A, lines, nW);

        var counts = new List<int>();
        for (int s = -1; s < 4; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = g0; t = (int[])t0.Clone(); }
            else (g, t) = ScrambleWithTypes(g0, t0, seed: 7700 + s);

            int n = g.VertexCount;
            int[] adj = ExtractAdj(g);
            sbyte[] pBase = SeedFromTypes(n, t);

            var segs = RecoverSegmentsA(n, adj, pBase, t, nW, A.N);
            counts.Add(segs.Count);

            // every recovered segment is exactly |A| vertices, all the same segment colour.
            Assert.All(segs, c => Assert.Equal(A.N, c.Length));
            Assert.All(segs, c => Assert.True(c.All(v => t[v] == t[c[0]] && t[v] < nW)));
        }

        // (RM-1 deliverable) segments recognised == nW, cold-fused into size-|A| cells, scramble-invariant.
        Assert.All(counts, c => Assert.Equal(nW, c));
        Assert.True(counts.Distinct().Count() == 1);

        _out.WriteLine($"{name,-6} |A|={A.N} nW={nW} n={g0.VertexCount,4}  segments(size-|A| cells)={counts[0]} (== nW) scramble-inv={counts.Distinct().Count() == 1}");
    }

    // ── RM-3: ring inference recognition-free from a degree-3 gadget relation ──
    // A degree-3 sum-zero gadget's full tuple-relation is a group Latin square; by
    // Albert's theorem it determines A up to isomorphism. The order-profile falls out
    // of the row-permutation cycle structure: R_x ∘ R_{x'}⁻¹ = translation by (x'−x),
    // whose cycle length = ord(x'−x). That multiset is isotopy-invariant ⟹ recovered
    // recognition-free (states only locally labelled) and scramble-invariant. Degree 3
    // suffices for the FULL profile (stronger than the forcing-only budget=exp bound —
    // reading the whole relation beats pin-a-peer observation), for any A with exp ≤ n.
    [Theory]
    [InlineData("Z4", 4)]
    [InlineData("Z2^2", 4)]     // the classic discriminator: Z4 (1,2,4) vs Z2² (1,2)
    [InlineData("Z2xZ4", 8)]    // higher: still pinned from one degree-3 gadget
    public void RM3_RingInferred_FromGadgetRelation_ScrambleInvariant(string name, int asz)
    {
        var A = name switch
        {
            "Z4" => new Ab("Z4", 4),
            "Z2^2" => new Ab("Z2^2", 2, 2),
            "Z2xZ4" => new Ab("Z2xZ4", 2, 4),
            _ => throw new ArgumentException(name)
        };
        Assert.Equal(asz, A.N);
        int nW = 6;
        var lines = CirculantLines(nW, new[] { 0, 1, 3 });
        var (g0, t0, _) = BuildNativeMultipede(A, lines, nW);

        var profiles = new List<string>();
        for (int s = -1; s < 3; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = g0; t = (int[])t0.Clone(); }
            else (g, t) = ScrambleWithTypes(g0, t0, seed: 9900 + s);
            int n = g.VertexCount;
            profiles.Add(InferOrderProfile(n, ExtractAdj(g), t, nW, A.N));
        }

        // (RM-3 deliverable) recovered ring order-profile == ground truth, scramble-invariant.
        Assert.True(profiles.Distinct().Count() == 1);
        Assert.Equal(A.TrueOrderProfile(), profiles[0]);
        _out.WriteLine($"{name,-8} recovered-from-graph order-profile=[{profiles[0]}] (== ground truth) scramble-inv={profiles.Distinct().Count() == 1}");
    }

    // Read one degree-3 gadget's tuple-relation, build the group Latin square, and
    // return the order-profile via the row-permutation cycle structure. Recognition-free:
    // only segment identity (RM-1) + adjacency; states locally labelled per segment.
    private static string InferOrderProfile(int n, int[] adj, int[] types, int nW, int Asz)
    {
        var pBase = SeedFromTypes(n, types);
        var segs = RecoverSegmentsA(n, adj, pBase, types, nW, Asz);
        var segOf = new int[n]; Array.Fill(segOf, -1);
        var localOf = new int[n];
        for (int si = 0; si < segs.Count; si++)
            for (int k = 0; k < segs[si].Length; k++) { segOf[segs[si][k]] = si; localOf[segs[si][k]] = k; }

        // group gadget vertices (segOf==-1) by their incident-segment set; a degree-3 line has |A|² tuples.
        var byLine = new Dictionary<string, List<int>>();
        for (int v = 0; v < n; v++)
        {
            if (segOf[v] != -1) continue;
            var segSet = new SortedSet<int>();
            for (int w = 0; w < n; w++) if (adj[v * n + w] == 1 && segOf[w] != -1) segSet.Add(segOf[w]);
            if (segSet.Count != 3) continue;
            var key = string.Join(",", segSet);
            if (!byLine.TryGetValue(key, out var l)) byLine[key] = l = new List<int>();
            l.Add(v);
        }

        foreach (var kv in byLine)
        {
            if (kv.Value.Count != Asz * Asz) continue;   // a full degree-3 line
            var sids = kv.Key.Split(',').Select(int.Parse).ToArray();
            int s0 = sids[0], s1 = sids[1], s2 = sids[2];
            var L = new int[Asz, Asz];
            var filled = new bool[Asz, Asz];
            bool ok = true;
            foreach (int gv in kv.Value)
            {
                int x = -1, y = -1, z = -1;
                for (int w = 0; w < n; w++)
                {
                    if (adj[gv * n + w] != 1 || segOf[w] == -1) continue;
                    if (segOf[w] == s0) x = localOf[w]; else if (segOf[w] == s1) y = localOf[w]; else if (segOf[w] == s2) z = localOf[w];
                }
                if (x < 0 || y < 0 || z < 0 || filled[x, y]) { ok = false; break; }
                L[x, y] = z; filled[x, y] = true;
            }
            if (!ok) continue;

            // order histogram over pairs x≠x': cycle length of R_x ∘ R_{x'}⁻¹ = ord(x'−x).
            var hist = new SortedDictionary<int, int>();
            for (int x = 0; x < Asz; x++)
                for (int xp = 0; xp < Asz; xp++)
                {
                    if (x == xp) continue;
                    var rinv = new int[Asz]; for (int y = 0; y < Asz; y++) rinv[L[xp, y]] = y;
                    var perm = new int[Asz]; for (int z = 0; z < Asz; z++) perm[z] = L[x, rinv[z]];
                    int ord = PermOrder(perm);
                    hist[ord] = hist.TryGetValue(ord, out var c) ? c + 1 : 1;
                }

            // each nonzero group element g appears |A| times as (x'−x); divide out. Add the identity.
            var parts = new List<string> { "1^1" };
            foreach (var kv2 in hist) parts.Add($"{kv2.Key}^{kv2.Value / Asz}");
            return string.Join(",", parts);
        }
        return "NO-DEGREE-3-GADGET";
    }

    private static int PermOrder(int[] perm)
    {
        int n = perm.Length; var seen = new bool[n]; int ord = 1;
        for (int i = 0; i < n; i++)
        {
            if (seen[i]) continue;
            int len = 0, j = i;
            while (!seen[j]) { seen[j] = true; j = perm[j]; len++; }
            ord = Lcm(ord, len);
        }
        return ord;
    }
    private static int GcdI(int a, int b) { while (b != 0) { (a, b) = (b, a % b); } return a < 0 ? -a : a; }
    private static int Lcm(int a, int b) => a / GcdI(a, b) * b;

    // ── RM-2: graph WL-forcing == A-unit-propagation (Layer B over A) ─────────
    // Pin a base S (individualize one state per pinned segment) and refine: the graph
    // fully discretizes the segments IFF unit-propagation on the constraint system
    // resolves every segment from S. Resolution is ring-INDEPENDENT (a constraint
    // forces its last unknown over any A), so the correspondence is tested on the
    // support alone — matching the ring-design split (extraction/support ⊥ ring).
    [Theory]
    [InlineData("Z4", 4, new[] { 0, 1 }, true)]    // base {0,1} unit-prop-resolves all ⟹ graph discretizes
    [InlineData("Z4", 4, new[] { 0 }, false)]      // base {0} resolves only {0} ⟹ graph stays non-discrete
    [InlineData("Z2^2", 4, new[] { 0, 1 }, true)]  // same support ⟹ same resolution, any A
    [InlineData("Z3", 3, new[] { 0 }, false)]
    public void RM2_GraphForcing_MatchesUnitPropagation(string name, int asz, int[] baseSegs, bool expectAllResolved)
    {
        var A = name switch
        {
            "Z4" => new Ab("Z4", 4),
            "Z2^2" => new Ab("Z2^2", 2, 2),
            "Z3" => new Ab("Z3", 3),
            _ => throw new ArgumentException(name)
        };
        Assert.Equal(asz, A.N);
        int nW = 6;
        var lines = CirculantLines(nW, new[] { 0, 1, 3 });

        // (ground truth) unit-propagation on the constraint system, from S.
        int algResolved = UnitPropResolvedCount(lines, nW, baseSegs);
        Assert.Equal(expectAllResolved, algResolved == nW);

        var (g0, t0, _) = BuildNativeMultipede(A, lines, nW);
        var discreteFlags = new List<bool>();
        for (int s = -1; s < 3; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = g0; t = (int[])t0.Clone(); }
            else (g, t) = ScrambleWithTypes(g0, t0, seed: 8800 + s);
            int n = g.VertexCount;
            int[] adj = ExtractAdj(g);
            discreteFlags.Add(GraphDiscretizesSegments(n, adj, t, nW, A.N, baseSegs));
        }

        // (RM-2 deliverable) graph discretizes-all ⟺ unit-prop resolves-all, scramble-invariant.
        Assert.All(discreteFlags, f => Assert.Equal(expectAllResolved, f));
        _out.WriteLine($"{name,-6} base=[{string.Join(",", baseSegs)}] unit-prop resolved={algResolved}/{nW} graph-discretizes-all={discreteFlags[0]} (expect {expectAllResolved}) scramble-inv={discreteFlags.Distinct().Count() == 1}");
    }

    // unit-propagation on the constraint system: a line with one unresolved segment forces it.
    private static int UnitPropResolvedCount(List<int[]> lines, int nW, int[] baseSegs)
    {
        var resolved = new bool[nW];
        foreach (int b in baseSegs) resolved[b] = true;
        bool changed = true;
        while (changed)
        {
            changed = false;
            foreach (var ln in lines)
            {
                var unk = ln.Where(p => !resolved[p]).ToList();
                if (unk.Count == 1) { resolved[unk[0]] = true; changed = true; }
            }
        }
        return resolved.Count(r => r);
    }

    // pin S (individualize one state per pinned segment) then refine; return true iff every
    // segment's |A| states land in distinct cells (segments fully discretized).
    private static bool GraphDiscretizesSegments(int n, int[] adj, int[] types, int nW, int Asz, int[] baseSegs)
    {
        // segment p's state-vertices = { v : types[v] == p }.
        var statesOf = new List<int>[nW];
        for (int p = 0; p < nW; p++) statesOf[p] = new List<int>();
        for (int v = 0; v < n; v++) if (types[v] < nW) statesOf[types[v]].Add(v);

        var p2 = new sbyte[n * n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++)
            if (i != j && types[i] < types[j]) { p2[i * n + j] = LESS; p2[j * n + i] = GREATER; }
        // pin: individualize the min-id state of each based segment below its cellmates.
        foreach (int b in baseSegs)
        {
            var st = statesOf[b].OrderBy(x => x).ToList();
            int s0 = st[0];
            foreach (int x in st) if (x != s0) { p2[s0 * n + x] = LESS; p2[x * n + s0] = GREATER; }
        }
        if (!TransitiveClose(p2, n)) return false;
        var part = new WarmPartition(n);
        part.Refine(adj, p2);
        for (int p = 0; p < nW; p++)
        {
            // "resolved" = the fused |A|-cell has BROKEN (value identified): 1-WL distinguishes the
            // value state but leaves the |A|-1 non-value states symmetric, so the analog of unit-prop
            // "value known" is that the segment's states span ≥ 2 cells (not that they all singleton).
            var cells = statesOf[p].Select(v => part.CellOf[v]).Distinct().Count();
            if (cells < 2) return false;                 // still one fused cell ⟹ unresolved
        }
        return true;
    }

    // ── segments = size-|A| stable cells among segment-coloured (type < nW) vertices ──
    private static List<int[]> RecoverSegmentsA(int n, int[] adj, sbyte[] pBase, int[] types, int nW, int Asz)
    {
        var part = new WarmPartition(n);
        part.Refine(adj, pBase);
        var byCell = new Dictionary<int, List<int>>();
        for (int v = 0; v < n; v++)
        {
            if (types[v] >= nW) continue;                 // gadget-coloured: not a segment
            if (!byCell.TryGetValue(part.CellOf[v], out var l)) byCell[part.CellOf[v]] = l = new List<int>();
            l.Add(v);
        }
        return byCell.Values.Where(c => c.Count == Asz).Select(c => { c.Sort(); return c.ToArray(); }).ToList();
    }

    // ── plumbing (mirrors Option2ExtractionProbe) ─────────────────────────────
    private static int[] ExtractAdj(AdjMatrix g)
    {
        int n = g.VertexCount; var adj = new int[n * n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) adj[i * n + j] = g[i, j];
        return adj;
    }

    private static sbyte[] SeedFromTypes(int n, int[] types)
    {
        var p = new sbyte[n * n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++)
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

    private static (AdjMatrix, int[]) ScrambleWithTypes(AdjMatrix g, int[] types, int seed)
    {
        int n = g.VertexCount; var m = g.ToArray(); var t = (int[])types.Clone();
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
