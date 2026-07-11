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
        public int Annih(long d) { int c = 0; for (int a = 0; a < N; a++) if (d % Order(a) == 0) c++; return c; }
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

    // ── RM-4: kernel-module / rigidity from the extracted incidence (dim ker twin) ──
    // Extract the incidence M (which segments each gadget constrains) recognition-free,
    // then the kernel-module {x ∈ A^nW : Mx=0} via integer SMITH NORMAL FORM:
    //   ker size = Π_i annih_A(d_i) · |A|^(nW−rank),  d_i = invariant factors of M.
    // Rigid ⟺ ker size = 1. The nontrivial kernel is the hidden abelian symmetry the
    // stepwise engine consumes (de-fusion). Validated against brute force over A^nW,
    // scramble-invariant. Smith is the production D4 solve, exercised here.
    [Theory]
    [InlineData("Z2", 2, 6)]      // Circulant(6,{0,1,3}) — F₂-rigid ⟹ ker 1
    [InlineData("Z4", 4, 6)]
    [InlineData("Z2^2", 4, 6)]
    [InlineData("Z2", 2, 7)]      // Circulant(7,{0,1,3}) — F₂ non-rigid (ker > 1), a contrast
    [InlineData("Z4", 4, 7)]
    public void RM4_KernelModule_RigidityFromForcing_ScrambleInvariant(string name, int asz, int nW)
    {
        var A = name switch
        {
            "Z2" => new Ab("Z2", 2),
            "Z4" => new Ab("Z4", 4),
            "Z2^2" => new Ab("Z2^2", 2, 2),
            _ => throw new ArgumentException(name)
        };
        Assert.Equal(asz, A.N);
        var lines = CirculantLines(nW, new[] { 0, 1, 3 });
        var (g0, t0, _) = BuildNativeMultipede(A, lines, nW);

        var kers = new List<long>();
        for (int s = -1; s < 3; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = g0; t = (int[])t0.Clone(); }
            else (g, t) = ScrambleWithTypes(g0, t0, seed: 10500 + s);
            int n = g.VertexCount;
            var M = ExtractIncidence(n, ExtractAdj(g), t, nW, A.N);

            long viaSmith = KerSizeOverA(A, SmithInvariantFactors(M), nW);
            long viaBrute = BruteKerSizeOverA(A, M, nW);
            Assert.Equal(viaBrute, viaSmith);          // Smith solve == ground truth on the extracted M
            kers.Add(viaSmith);
        }

        // (RM-4 deliverable) recovered kernel-module size scramble-invariant.
        Assert.True(kers.Distinct().Count() == 1);
        _out.WriteLine($"{name,-6} nW={nW} ker-module size={kers[0],4} rigid={kers[0] == 1} scramble-inv={kers.Distinct().Count() == 1}");
    }

    // incidence M (nLines × nW), recognition-free: gadget vertices grouped by their segment set.
    private static long[,] ExtractIncidence(int n, int[] adj, int[] types, int nW, int Asz)
    {
        var pBase = SeedFromTypes(n, types);
        var segs = RecoverSegmentsA(n, adj, pBase, types, nW, Asz);
        var segOf = new int[n]; Array.Fill(segOf, -1);
        for (int si = 0; si < segs.Count; si++) foreach (int v in segs[si]) segOf[v] = si;

        var seen = new HashSet<string>();
        var rows = new List<int[]>();
        for (int v = 0; v < n; v++)
        {
            if (segOf[v] != -1) continue;
            var set = new SortedSet<int>();
            for (int w = 0; w < n; w++) if (adj[v * n + w] == 1 && segOf[w] != -1) set.Add(segOf[w]);
            if (set.Count < 2) continue;
            var key = string.Join(",", set);
            if (seen.Add(key)) rows.Add(set.ToArray());
        }
        var M = new long[rows.Count, nW];
        for (int r = 0; r < rows.Count; r++) foreach (int j in rows[r]) M[r, j] = 1;
        return M;
    }

    // integer Smith normal form → nonzero invariant factors (|d_1|,…,|d_r|), d_i | d_{i+1}.
    private static List<long> SmithInvariantFactors(long[,] M0)
    {
        int m = M0.GetLength(0), nn = M0.GetLength(1);
        var M = (long[,])M0.Clone();
        var factors = new List<long>();
        int t = 0;
        while (t < Math.Min(m, nn))
        {
            // pivot: any nonzero entry in the [t..,t..] submatrix.
            int pi = -1, pj = -1;
            for (int i = t; i < m && pi < 0; i++) for (int j = t; j < nn; j++) if (M[i, j] != 0) { pi = i; pj = j; break; }
            if (pi < 0) break;
            SwapRows(M, t, pi, nn); SwapCols(M, t, pj, m);

            bool clean = false;
            while (!clean)
            {
                clean = true;
                for (int i = t + 1; i < m; i++)
                    if (M[i, t] != 0)
                    {
                        long q = M[i, t] / M[t, t];
                        for (int k = 0; k < nn; k++) M[i, k] -= q * M[t, k];
                        if (M[i, t] != 0) { SwapRows(M, t, i, nn); clean = false; }   // smaller residual ⟹ re-pivot
                    }
                for (int j = t + 1; j < nn; j++)
                    if (M[t, j] != 0)
                    {
                        long q = M[t, j] / M[t, t];
                        for (int k = 0; k < m; k++) M[k, j] -= q * M[k, t];
                        if (M[t, j] != 0) { SwapCols(M, t, j, m); clean = false; }
                    }
            }
            // ensure M[t,t] divides the rest; else fold an offending row in and redo.
            bool div = true;
            for (int i = t + 1; i < m && div; i++)
                for (int j = t + 1; j < nn && div; j++)
                    if (M[i, j] % M[t, t] != 0) { for (int k = 0; k < nn; k++) M[t, k] += M[i, k]; div = false; }
            if (!div) continue;

            factors.Add(Math.Abs(M[t, t]));
            t++;
        }
        return factors;
    }
    private static void SwapRows(long[,] M, int a, int b, int cols) { if (a == b) return; for (int k = 0; k < cols; k++) (M[a, k], M[b, k]) = (M[b, k], M[a, k]); }
    private static void SwapCols(long[,] M, int a, int b, int rows) { if (a == b) return; for (int k = 0; k < rows; k++) (M[k, a], M[k, b]) = (M[k, b], M[k, a]); }

    private static long KerSizeOverA(Ab A, List<long> factors, int nW)
    {
        long size = 1;
        for (int i = 0; i < nW - factors.Count; i++) size *= A.N;
        foreach (var d in factors) size *= A.Annih(d);
        return size;
    }

    // brute force |{x ∈ A^nW : Mx = 0 over A}| (ground truth; small nW,|A|).
    private static long BruteKerSizeOverA(Ab A, long[,] M, int nW)
    {
        int rows = M.GetLength(0);
        long total = 1; for (int i = 0; i < nW; i++) total *= A.N;
        long count = 0;
        var x = new int[nW];
        for (long code = 0; code < total; code++)
        {
            long c = code; for (int j = 0; j < nW; j++) { x[j] = (int)(c % A.N); c /= A.N; }
            bool ok = true;
            for (int r = 0; r < rows && ok; r++)
            {
                int s = 0;
                for (int j = 0; j < nW; j++) if (M[r, j] != 0) s = A.Add(s, x[j]);
                if (s != 0) ok = false;
            }
            if (ok) count++;
        }
        return count;
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

    // ── RM-5 + RM-6: canonical-form emit == verify-by-reconstruction ───────────
    // A state-labelling φ (states → A) that makes every gadget's neighbours sum to 0
    // is exactly a valid trivialisation of the (untwisted) native-A-multipede. Search
    // for one from a resolving base (rigid ⟹ the base determines the rest by unit-prop);
    // EMIT the canonical adjacency under the min such labelling. If NO consistent
    // complete labelling exists, the input is not that multipede structure → FLAG (null).
    // So the emit is self-verifying: success is the reconstruction certificate (B3).
    // (Untwisted case; the twisted case fixes the per-gadget constant via CosetMinA — RingSolveProbe.)
    [Theory]
    [InlineData("Z2", 2)]
    [InlineData("Z4", 4)]
    [InlineData("Z2^2", 4)]
    [InlineData("Z3", 3)]
    public void RM5_CanonicalForm_EmitAndSelfVerify_ScrambleInvariant(string name, int asz)
    {
        var A = name switch
        {
            "Z2" => new Ab("Z2", 2), "Z4" => new Ab("Z4", 4),
            "Z2^2" => new Ab("Z2^2", 2, 2), "Z3" => new Ab("Z3", 3),
            _ => throw new ArgumentException(name)
        };
        Assert.Equal(asz, A.N);
        int nW = 6;
        var lines = CirculantLines(nW, new[] { 0, 1, 3 });
        var (g0, t0, _) = BuildNativeMultipede(A, lines, nW);

        var forms = new List<string?>();
        for (int s = -1; s < 3; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = g0; t = (int[])t0.Clone(); }
            else (g, t) = ScrambleWithTypes(g0, t0, seed: 12000 + s);
            forms.Add(BuildCanonicalFormOrFlag(g.VertexCount, ExtractAdj(g), t, nW, A));
        }

        Assert.All(forms, f => Assert.NotNull(f));          // valid multipede ⟹ self-verifies (non-flag)
        Assert.True(forms.Distinct().Count() == 1);         // canonical form is scramble-invariant
        _out.WriteLine($"{name,-6} canonical-form len={forms[0]!.Length} scramble-inv={forms.Distinct().Count() == 1} (self-verified)");
    }

    [Fact]
    public void RM6_VerifyByReconstruction_FlagsCorruptedStructure_AndSeparatesTwins()
    {
        var A = new Ab("Z4", 4);
        int nW = 6;
        var lines = CirculantLines(nW, new[] { 0, 1, 3 });
        var (g0, t0, _) = BuildNativeMultipede(A, lines, nW);
        int n = g0.VertexCount;

        // valid ⟹ verifies (non-null).
        var good = BuildCanonicalFormOrFlag(n, ExtractAdj(g0), (int[])t0.Clone(), nW, A);
        Assert.NotNull(good);

        // corrupt: redirect one gadget-vertex edge to a different state of the same segment,
        // so its tuple no longer sums to 0 ⟹ NO consistent labelling ⟹ verify FLAGS (null).
        var adj = ExtractAdj(g0);
        int segCount = nW * A.N;
        int gv = segCount;                                   // first gadget vertex
        int oldNbr = -1; for (int w = 0; w < n; w++) if (adj[gv * n + w] == 1) { oldNbr = w; break; }
        int seg = oldNbr / A.N; int newNbr = seg * A.N + (oldNbr % A.N + 1) % A.N;  // sibling state, same segment
        adj[gv * n + oldNbr] = 0; adj[oldNbr * n + gv] = 0;
        adj[gv * n + newNbr] = 1; adj[newNbr * n + gv] = 1;
        var flagged = BuildCanonicalFormOrFlag(n, adj, (int[])t0.Clone(), nW, A);
        Assert.Null(flagged);                                // verify-by-reconstruction rejects it

        // completeness: same base + same |A| but a DIFFERENT ring (Z4 vs Z2²) is a
        // non-isomorphic graph ⟹ a different canonical form (both rigid, both verify).
        var B = new Ab("Z2^2", 2, 2);
        var (gB, tB, _) = BuildNativeMultipede(B, lines, nW);
        var other = BuildCanonicalFormOrFlag(gB.VertexCount, ExtractAdj(gB), tB, nW, B);
        Assert.NotNull(other);
        Assert.NotEqual(good, other);                        // Z4-multipede ≠ Z2²-multipede

        _out.WriteLine($"RM-6: valid✓ corrupt→FLAG✓ (self-verify rejects non-multipede) ring-separation(Z4≠Z2²)✓");
    }

    // canonical form or flag (null) — the untwisted D-M3 assembly, self-verifying.
    private static string? BuildCanonicalFormOrFlag(int n, int[] adj, int[] types, int nW, Ab A)
    {
        int Asz = A.N;
        var pBase = SeedFromTypes(n, types);
        var part = new WarmPartition(n); part.Refine(adj, pBase);
        var byCell = new Dictionary<int, List<int>>();
        for (int v = 0; v < n; v++)
        {
            if (types[v] >= nW) continue;
            if (!byCell.TryGetValue(part.CellOf[v], out var l)) byCell[part.CellOf[v]] = l = new List<int>();
            l.Add(v);
        }
        var segCells = byCell.Where(kv => kv.Value.Count == Asz).OrderBy(kv => kv.Key)
                             .Select(kv => { kv.Value.Sort(); return kv.Value; }).ToList();
        if (segCells.Count != nW) return null;
        var segOf = new int[n]; Array.Fill(segOf, -1);
        for (int si = 0; si < nW; si++) foreach (int v in segCells[si]) segOf[v] = si;

        var gVerts = new List<int>(); var gNbr = new List<List<(int seg, int v)>>();
        for (int v = 0; v < n; v++)
        {
            if (segOf[v] != -1) continue;
            var nb = new List<(int, int)>();
            for (int w = 0; w < n; w++) if (adj[v * n + w] == 1 && segOf[w] != -1) nb.Add((segOf[w], w));
            if (nb.Count >= 2) { gVerts.Add(v); gNbr.Add(nb); }
        }

        // resolving base = the first 2 segments (cell-id order); enumerate labellings, propagate.
        var perms = Permutations(Asz);
        string? best = null;
        foreach (var p0 in perms)
            foreach (var p1 in perms)
            {
                var phi = new int[n]; Array.Fill(phi, -1);
                for (int k = 0; k < Asz; k++) { phi[segCells[0][k]] = p0[k]; phi[segCells[1][k]] = p1[k]; }
                if (!Propagate(phi, gVerts, gNbr, A)) continue;
                if (!LabellingComplete(phi, segCells, Asz)) continue;
                var form = EmitForm(n, adj, segCells, gVerts, gNbr, phi, nW);
                if (best == null || string.CompareOrdinal(form, best) < 0) best = form;
            }
        return best;
    }

    // unit-propagation of φ: a gadget with one unknown neighbour forces it = −(sum); all-known must sum to 0.
    private static bool Propagate(int[] phi, List<int> gVerts, List<List<(int seg, int v)>> gNbr, Ab A)
    {
        bool changed = true;
        while (changed)
        {
            changed = false;
            for (int gi = 0; gi < gVerts.Count; gi++)
            {
                var nb = gNbr[gi];
                int unknownV = -1, unknownCnt = 0, s = 0;
                foreach (var x in nb) { if (phi[x.v] == -1) { unknownCnt++; unknownV = x.v; } else s = A.Add(s, phi[x.v]); }
                if (unknownCnt == 0) { if (s != 0) return false; }
                else if (unknownCnt == 1) { phi[unknownV] = A.Neg(s); changed = true; }
            }
        }
        return true;
    }

    private static bool LabellingComplete(int[] phi, List<List<int>> segCells, int Asz)
    {
        foreach (var seg in segCells)
        {
            var vals = seg.Select(v => phi[v]).ToList();
            if (vals.Any(x => x == -1) || vals.Distinct().Count() != Asz) return false;
        }
        return true;
    }

    // canonical vertex order: segments (cell-id) × states (by φ-value), then gadgets by φ-tuple key.
    private static string EmitForm(int n, int[] adj, List<List<int>> segCells, List<int> gVerts,
                                   List<List<(int seg, int v)>> gNbr, int[] phi, int nW)
    {
        var order = new List<int>(n);
        foreach (var seg in segCells) order.AddRange(seg.OrderBy(v => phi[v]));
        var keyed = new List<(string key, int v)>();
        for (int gi = 0; gi < gVerts.Count; gi++)
        {
            var key = string.Join("|", gNbr[gi].OrderBy(x => x.seg).Select(x => $"{x.seg}:{phi[x.v]}"));
            keyed.Add((key, gVerts[gi]));
        }
        foreach (var kv in keyed.OrderBy(x => x.key, StringComparer.Ordinal)) order.Add(kv.v);

        var sb = new System.Text.StringBuilder(order.Count * order.Count);
        for (int i = 0; i < order.Count; i++)
            for (int j = 0; j < order.Count; j++)
                sb.Append(adj[order[i] * n + order[j]] != 0 ? '1' : '0');
        return sb.ToString();
    }

    private static List<int[]> Permutations(int k)
    {
        var res = new List<int[]>(); var a = Enumerable.Range(0, k).ToArray();
        void Rec(int i)
        {
            if (i == k) { res.Add((int[])a.Clone()); return; }
            for (int j = i; j < k; j++) { (a[i], a[j]) = (a[j], a[i]); Rec(i + 1); (a[i], a[j]) = (a[j], a[i]); }
        }
        Rec(0); return res;
    }
}
