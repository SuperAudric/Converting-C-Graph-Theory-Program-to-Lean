using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ─────────────────────────────────────────────────────────────────────────────
// Non-abelian-CFI WITNESS PROBE — does a rigid graph with NO linear (F-variable)
// structure exist that is still WL-hard?  (docs/chain-descent-ir-blindspot-solver.md
// §11.14 / chain-descent-cameron-entanglement.md — the structure/non-linear cell
// of the 2×2; the open node-4 wall seen from the rigid side.)
//
// The setup (the reframe).  For a SCHURIAN scheme the individualization/WL base
// equals the group base (gap ≡ 0): rigid + schurian ⟹ WL-discrete.  So a rigid
// graph that resists WL must be NON-schurian — its WL-closure carries "fake twins"
// that are not orbits.  In every KNOWN such graph (CFI / multipede / Lichter
// Z_{2^k}) the fake twins are a coset of a LINEAR / abelian gauge, and that group
// structure is exactly what makes the hardness survive individualization
// (b_WL = Ω(n)).  The open question: must the gauge be abelian/linear?  i.e. can a
// NON-abelian gauge produce WL-hardness, or does WL "see" the non-abelian
// structure and collapse it?
//
// This probe is the test.  Generalize the CFI / multipede gadget from F₂ to an
// arbitrary finite group Γ:
//   * SEGMENT for each base column w ∈ W: |Γ| value-vertices val(w,g), g ∈ Γ,
//     all one colour (so WL cannot tell the values apart by colour).
//   * GADGET for each base row v ∈ V with ordered neighbourhood (w₁,…,w_d):
//     one tuple-vertex per (g₁,…,g_d) ∈ Γ^d with ORDERED PRODUCT g₁·…·g_d = c_v
//     (homogeneous: c_v = e), all one colour; |Γ|^{d-1} of them.
//   * EDGES: tuple-vertex (g₁,…,g_d) — val(w_i, g_i).
// Γ = Z₂ reproduces the Neuen–Schweitzer multipede exactly (segment {a,b} =
// val(w,1)/val(w,0); product-=-e tuples = even subsets), so it is the linear
// baseline.  The non-abelian groups (S₃, D₄) are the witness candidates.
//
// Step 1–2 (this probe): the generator + the WL-HARDNESS measurement.  For each
// (Γ, base) report:
//   * segFused   — do the |Γ| values of every segment stay in ONE 1-WL cell
//                  (WL is stuck / "fake twins" present)?  This is the precondition
//                  for WL-hardness; if NO, WL already separated the group values
//                  ⟹ the non-abelian structure is visible ⟹ collapses.
//   * b_WL       — greedy individualizations to reach a discrete colouring.
//   * collapse   — segments-still-fused after each pin (the forcing cascade =
//                  "what causes their collapse").
//   * |Aut|      — harvested by the real canonizer (small budget): rigid (1) vs
//                  symmetric, and whether it FLAGS (the IR-blindspot signature).
// Witness criterion: a non-abelian Γ with segFused=yes, b_WL>0, |Aut| small/flag
// behaves like the F₂ multipede ⟹ rigid non-abelian structural WL-hardness =
// a non-linear witness.  Collapse (segFused=no, b_WL≈0) ⟹ supports "no
// non-abelian gauge".  The extraction discriminator (is the surviving hardness
// linear-over-a-ring?) is the NEXT probe.
//
// Self-contained: groups are built from permutation generators (associativity
// free), the CFI-over-Γ builder is local, and only the public AdjMatrix /
// CanonGraphOrdererChainDescent and the internal WarmPartition (the descent's
// 1-WL, via InternalsVisibleTo) are reused.  The main project is untouched.
// ─────────────────────────────────────────────────────────────────────────────
public sealed class NonAbelianCfiProbe
{
    private const sbyte LESS = -1, UNKNOWN = 0, GREATER = 1;
    private readonly ITestOutputHelper output;
    public NonAbelianCfiProbe(ITestOutputHelper o) => output = o;

    // ── a finite group as a Cayley table, built from permutation generators ────
    private sealed class Grp
    {
        public readonly string Name;
        public readonly int N;          // order |Γ|
        public readonly int[,] Mul;     // Mul[i,j] = i·j   (identity = index 0)
        public readonly int[] Inv;      // Inv[i] = i⁻¹
        public readonly bool Abelian;
        public Grp(string name, int[,] mul, int[] inv, bool ab)
        { Name = name; N = mul.GetLength(0); Mul = mul; Inv = inv; Abelian = ab; }
    }

    // Closure of <gens> ⊆ S_deg, as a Cayley table.  Group op = permutation
    // composition (a∘b)[i] = a[b[i]] — associative by construction; identity
    // (the trivial perm) is added first so it is index 0.
    private static Grp GroupFromPerms(string name, int deg, List<int[]> gens)
    {
        static string Key(int[] p) => string.Join(",", p);
        int[] Comp(int[] a, int[] b) { var r = new int[deg]; for (int i = 0; i < deg; i++) r[i] = a[b[i]]; return r; }

        int[] id = Enumerable.Range(0, deg).ToArray();
        var index = new Dictionary<string, int>();
        var elems = new List<int[]>();
        void Add(int[] p) { var k = Key(p); if (!index.ContainsKey(k)) { index[k] = elems.Count; elems.Add(p); } }

        Add(id);
        var queue = new Queue<int[]>();
        queue.Enqueue(id);
        while (queue.Count > 0)
        {
            var p = queue.Dequeue();
            foreach (var g in gens)
            {
                var nq = Comp(g, p);
                if (!index.ContainsKey(Key(nq))) { Add(nq); queue.Enqueue(nq); }
            }
        }

        int n = elems.Count;
        var mul = new int[n, n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                mul[i, j] = index[Key(Comp(elems[i], elems[j]))];

        var inv = new int[n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                if (mul[i, j] == 0) { inv[i] = j; break; }

        bool ab = true;
        for (int i = 0; i < n && ab; i++)
            for (int j = 0; j < n; j++)
                if (mul[i, j] != mul[j, i]) { ab = false; break; }

        return new Grp(name, mul, inv, ab);
    }

    private static Grp Zn(int n)
    {
        var c = Enumerable.Range(0, n).Select(i => (i + 1) % n).ToArray();   // n-cycle
        return GroupFromPerms($"Z{n}", n, new List<int[]> { c });
    }
    private static Grp Klein() =>   // Z₂ × Z₂ = two disjoint transpositions
        GroupFromPerms("Z2xZ2", 4, new List<int[]> { new[] { 1, 0, 2, 3 }, new[] { 0, 1, 3, 2 } });
    private static Grp S3() =>      // ⟨(0 1),(1 2)⟩ = full symmetric group on 3 pts
        GroupFromPerms("S3", 3, new List<int[]> { new[] { 1, 0, 2 }, new[] { 0, 2, 1 } });
    private static Grp D4() =>      // ⟨(0 1 2 3),(1 3)⟩ = dihedral of order 8
        GroupFromPerms("D4", 4, new List<int[]> { new[] { 1, 2, 3, 0 }, new[] { 0, 3, 2, 1 } });

    // ── CFI / multipede over a group Γ ────────────────────────────────────────
    private sealed class GroupCfi
    {
        public AdjMatrix Graph = null!;
        public int[] Types = null!;
        public int N;
        public int[][] SegVerts = null!;   // SegVerts[w][g] = value-vertex for w ↦ g
        public int[] Gadget0Tuples = null!; // tuple-vertex indices of gadget 0
        public int[] Gadget0Segs = null!;   // the (ordered) segment columns gadget 0 touches
    }

    // All tuples (g₁,…,g_d) ∈ Γ^d with ordered product = cv: enumerate the first
    // d-1 coordinates freely, force the last (g_d = (g₁…g_{d-1})⁻¹ · cv).
    private static IEnumerable<int[]> TuplesWithProduct(Grp G, int d, int cv)
    {
        int q = G.N;
        var t = new int[d];
        var ctr = new int[d - 1];
        while (true)
        {
            int P = 0;                                   // running product (identity)
            for (int k = 0; k < d - 1; k++) { t[k] = ctr[k]; P = G.Mul[P, t[k]]; }
            t[d - 1] = G.Mul[G.Inv[P], cv];
            yield return (int[])t.Clone();

            int kk = 0;
            while (kk < d - 1) { ctr[kk]++; if (ctr[kk] < q) break; ctr[kk] = 0; kk++; }
            if (kk == d - 1) break;
        }
    }

    private static GroupCfi BuildGroupCfi(Grp G, int[,] biadj, bool anchorSeg0 = false)
    {
        int nV = biadj.GetLength(0), nW = biadj.GetLength(1), q = G.N;
        var nbr = new int[nV][];
        for (int v = 0; v < nV; v++)
        {
            var l = new List<int>();
            for (int w = 0; w < nW; w++) if (biadj[v, w] != 0) l.Add(w);
            if (l.Count < 2) throw new ArgumentException($"gadget {v} has degree {l.Count} < 2");
            nbr[v] = l.ToArray();
        }

        // layout: all segment value-vertices, then all gadget tuple-vertices.
        var segVerts = new int[nW][];
        int idx = 0;
        for (int w = 0; w < nW; w++) { segVerts[w] = new int[q]; for (int g = 0; g < q; g++) segVerts[w][g] = idx++; }

        var gadTuples = new List<(int v, int[] tuple)>();
        for (int v = 0; v < nV; v++)
            foreach (var t in TuplesWithProduct(G, nbr[v].Length, 0)) gadTuples.Add((v, t));
        int firstMid = idx;
        idx += gadTuples.Count;
        int n = idx;

        var adj = new int[n, n];
        for (int gi = 0; gi < gadTuples.Count; gi++)
        {
            var (v, t) = gadTuples[gi];
            int mv = firstMid + gi;
            for (int k = 0; k < nbr[v].Length; k++)
            {
                int tgt = segVerts[nbr[v][k]][t[k]];
                adj[mv, tgt] = 1; adj[tgt, mv] = 1;
            }
        }

        // fine colouring: one colour per segment (shared by all |Γ| values), one
        // colour per gadget (shared by all its tuples).  If anchorSeg0, segment 0's
        // |Γ| values get DISTINCT colours — individualizing it, which kills the
        // global Γ-gauge (the extrinsic rigidification; the residue should be rigid
        // if the base is "odd enough"), so we can test whether the WL-hardness
        // survives into the rigid residue rather than being the consumable gauge.
        var types = new int[n];
        for (int w = 0; w < nW; w++) for (int g = 0; g < q; g++) types[segVerts[w][g]] = (q + 1) + w;
        for (int gi = 0; gi < gadTuples.Count; gi++) types[firstMid + gi] = (q + 1) + nW + gadTuples[gi].v;
        if (anchorSeg0) for (int g = 0; g < q; g++) types[segVerts[0][g]] = g;   // distinct, < q+1

        var g0tuples = new List<int>();
        for (int gi = 0; gi < gadTuples.Count; gi++) if (gadTuples[gi].v == 0) g0tuples.Add(firstMid + gi);

        return new GroupCfi
        {
            Graph = new AdjMatrix(adj), Types = types, N = n, SegVerts = segVerts,
            Gadget0Tuples = g0tuples.ToArray(), Gadget0Segs = nbr[0]
        };
    }

    // ── WL-hardness measurement ───────────────────────────────────────────────
    private static int FusedSegments(WarmPartition part, int[][] segVerts) =>
        segVerts.Count(s => s.Select(v => part.CellOf[v]).Distinct().Count() == 1);

    // Greedy individualization to discreteness: pin the min vertex of the
    // lowest-id non-singleton cell, refine, repeat.  Returns b_WL, the initial
    // 1-WL cell count, whether segments start fused, and the per-pin
    // fused-segment trace (the forcing cascade).
    private (int bWL, int initCells, bool segFused, List<int> fusedTrace) MeasureWL(
        int n, int[] adj, int[] types, int[][] segVerts)
    {
        sbyte[] p = SeedFromTypes(n, types);
        var part = new WarmPartition(n);
        part.Refine(adj, p);
        int initCells = part.NumCells;
        int nSeg = segVerts.Length;
        bool segFused = FusedSegments(part, segVerts) == nSeg;

        var trace = new List<int>();
        int count = 0;
        while (part.NumCells < n && count <= n + 2)
        {
            // lowest-id non-singleton cell
            var size = new Dictionary<int, int>();
            for (int v = 0; v < n; v++) { size.TryGetValue(part.CellOf[v], out int c); size[part.CellOf[v]] = c + 1; }
            int targetCell = size.Where(kv => kv.Value > 1).Min(kv => kv.Key);
            int pin = -1;
            for (int v = 0; v < n; v++) if (part.CellOf[v] == targetCell) { pin = v; break; }

            for (int u = 0; u < n; u++)
                if (u != pin && part.CellOf[u] == targetCell) { p[pin * n + u] = LESS; p[u * n + pin] = GREATER; }
            if (!TransitiveClose(p, n)) break;

            int before = part.NumCells;
            part = new WarmPartition(n);
            part.Refine(adj, p);
            count++;
            trace.Add(FusedSegments(part, segVerts));
            if (part.NumCells == before) break;   // no progress (safety)
        }
        return (count, initCells, segFused, trace);
    }

    private string MeasureAut(AdjMatrix g, int[] types, long budget)
    {
        var orderer = new CanonGraphOrdererChainDescent { BudgetOverride = budget };
        try
        {
            orderer.Run(types, g);
            return $"|Aut|={orderer.LastAutomorphismGroupOrder} nodes={orderer.LastNodeCount} branch={orderer.LastBranchingNodes}";
        }
        catch (CanonizationFlaggedException)
        {
            return $"FLAG(|res|={orderer.LastAutomorphismGroupOrder},{orderer.LastFlagKind},nodes={orderer.LastNodeCount})";
        }
    }

    // ── the probe ─────────────────────────────────────────────────────────────
    [Fact]
    public void Probe_NonAbelianCfi_WLHardness()
    {
        var groups = new[] { Zn(2), Zn(3), Zn(4), Klein(), S3(), D4() };
        int[] ms = { 5, 6, 7 };   // circulant base on Z_m, offsets {0,1,3} (degree 3)

        output.WriteLine("Non-abelian-CFI WL-hardness witness probe — homogeneous, circulant base offsets {0,1,3}");
        output.WriteLine("Γ=Z2 is the multipede baseline (linear); S3/D4 are the non-abelian witness candidates.");
        output.WriteLine($"{"grp",-7} {"|G|",3} {"ab",2}  {"m",2} {"n",5} {"#seg",4} {"initCells",9} {"segFused",8} {"b_WL",4}  collapse(fused/pin)   aut");
        foreach (var G in groups)
        {
            foreach (int m in ms)
            {
                var biadj = MultipedeGenerator.CirculantBiadjacency(m, new[] { 0, 1, 3 });
                var cfi = BuildGroupCfi(G, biadj);
                int n = cfi.N;
                int[] adj = FlatAdj(cfi.Graph);

                var (bWL, initCells, segFused, trace) = MeasureWL(n, adj, cfi.Types, cfi.SegVerts);
                string aut = n <= 300 ? MeasureAut(cfi.Graph, cfi.Types, budget: 10_000) : "(skipped n>300)";
                string traceStr = string.Join(",", trace.Take(12)) + (trace.Count > 12 ? "…" : "");

                output.WriteLine(
                    $"{G.Name,-7} {G.N,3} {(G.Abelian ? "y" : "n"),2}  {m,2} {n,5} {m,4} {initCells,9} " +
                    $"{(segFused ? "yes" : "NO"),8} {bWL,4}  {traceStr,-20} {aut}");
            }
        }
    }

    // ── the rigidified probe: kill the global Γ-gauge, does WL-hardness survive? ─
    // Same construction, but segment 0 is anchored (its |Γ| values individualized),
    // which removes the global gauge.  If the residue is then rigid (|Aut| small)
    // yet still needs pins (b_WL > 0) with a forcing cascade, that is a RIGID
    // (non-abelian, for S3/D4) WL-hard instance — a witness candidate for the
    // structure cell.  Run on the thin circulant (rigidity test) and a
    // high-treewidth random-regular base (genuine large-b_WL hardness).
    [Fact]
    public void Probe_NonAbelianCfi_Rigidified()
    {
        // Ordered for the decisive comparison: Z6 vs S3 (both order 6), Z8 vs D4
        // (both order 8) — same order, abelian vs non-abelian, identical base. If
        // the non-abelian one matches its abelian twin, WL only sees |Γ| (the
        // non-abelian structure is invisible); if it differs, non-abelian matters.
        var groups = new[] { Zn(2), Zn(3), Zn(4), Klein(), Zn(6), S3(), Zn(8), D4() };

        output.WriteLine("Rigidified group-CFI — segment 0 anchored (global Γ-gauge killed).");
        output.WriteLine("Does the WL-hardness survive into the RIGID residue?  (witness = |Aut| small AND b_WL>0 with forcing)");
        output.WriteLine($"{"grp",-7} {"|G|",3} {"ab",2}  {"base",-16} {"n",5} {"segFused",8} {"b_WL",4}  collapse(fused/pin)        aut");

        var bases = new (string name, int[,] biadj)[]
        {
            ("Circ6",          MultipedeGenerator.CirculantBiadjacency(6, new[] { 0, 1, 3 })),
            ("RandReg(8,6,3)", OddRandomRegular(8, 6, 3)),
            ("RandReg(10,7,3)",OddRandomRegular(10, 7, 3)),
        };

        foreach (var G in groups)
            foreach (var (bname, biadj) in bases)
            {
                var cfi = BuildGroupCfi(G, biadj, anchorSeg0: true);
                int n = cfi.N;
                if (n > 900) { output.WriteLine($"{G.Name,-7} {G.N,3} {(G.Abelian ? "y" : "n"),2}  {bname,-16} {n,5} (skipped n>900)"); continue; }
                int[] adj = FlatAdj(cfi.Graph);

                var (bWL, _, segFused, trace) = MeasureWL(n, adj, cfi.Types, cfi.SegVerts);
                string aut = n <= 320 ? MeasureAut(cfi.Graph, cfi.Types, budget: 20_000) : "(aut skipped n>320)";
                string traceStr = string.Join(",", trace.Take(14)) + (trace.Count > 14 ? "…" : "");

                output.WriteLine(
                    $"{G.Name,-7} {G.N,3} {(G.Abelian ? "y" : "n"),2}  {bname,-16} {n,5} " +
                    $"{(segFused ? "yes" : "NO"),8} {bWL,4}  {traceStr,-24} {aut}");
            }
    }

    // Are the S3-CFI and Z6-CFI actually DISTINCT graphs (so the identical
    // WL-hardness is the real finding: WL can't see non-abelian structure), or
    // are they isomorphic (construction is group-blind, a trivial identity)?
    // Canonize both (anchored, so rigid) and compare canonical forms.
    [Fact]
    public void Probe_S3_vs_Z6_DistinctButWLEqual()
    {
        var biadj = MultipedeGenerator.CirculantBiadjacency(6, new[] { 0, 1, 3 });
        string Canon(Grp G)
        {
            var cfi = BuildGroupCfi(G, biadj, anchorSeg0: true);
            var orderer = new CanonGraphOrdererChainDescent { BudgetOverride = 2_000_000 };
            var canon = orderer.Run(cfi.Types, cfi.Graph);
            return canon.ToString();
        }
        string z6 = Canon(Zn(6)), s3 = Canon(S3());
        output.WriteLine($"S3-CFI and Z6-CFI canonical forms equal? {z6 == s3}");
        output.WriteLine(z6 == s3
            ? "⟹ construction is group-blind (isomorphic graphs) — the WL identity is trivial."
            : "⟹ DISTINCT non-isomorphic graphs with IDENTICAL WL-hardness — WL is blind to the non-abelian structure (the finding).");
        Assert.True(z6.Length > 0);
    }

    // ── the EXTRACTION DISCRIMINATOR ──────────────────────────────────────────
    // Is the rigid group-CFI's structure LINEAR OVER AN ABELIAN RING (what
    // option-2's Smith-normal-form / ring route can canonize) or genuinely
    // non-abelian (no abelian module fits ⟹ ring inference fails ⟹ option-2
    // flags)?  Recover the gadget relation R_v from the GRAPH (its tuple-vertices'
    // segment-neighbours = the consistent value-triples), then test whether R_v is
    // ISOTOPIC to an abelian group.  By Albert's theorem (isotopic groups are
    // isomorphic) this holds iff Γ is abelian — and isotopy of a ternary relation =
    // ISOMORPHISM of its colour-parted incidence graph, which we settle with the
    // project's own canonizer.  So: recover R_v ⟹ canonize its relation-graph ⟹
    // compare to the abelian groups of order |Γ|.
    [Fact]
    public void Probe_ExtractionDiscriminator()
    {
        var groups = new[] { Zn(2), Zn(3), Zn(4), Klein(), Zn(6), S3(), Zn(8), D4() };
        var biadj = MultipedeGenerator.CirculantBiadjacency(5, new[] { 0, 1, 3 });

        output.WriteLine("Extraction discriminator — is the rigid group-CFI structure linear-over-an-ABELIAN-ring?");
        output.WriteLine("Recover gadget relation R_v from the graph; test isotopy-to-abelian (Albert) via relation-graph canon.");
        output.WriteLine($"{"grp",-7} {"|G|",3} {"ab",2}  {"recovered==Γ?",13}  {"abelian-isotope?",16}  verdict");

        foreach (var G in groups)
        {
            var cfi = BuildGroupCfi(G, biadj);
            int q = G.N;

            // recover R_v from the graph: each gadget-0 tuple-vertex → its 3
            // segment-neighbours → (local value index per segment).
            var seg0 = cfi.Gadget0Segs;
            var posOf = new Dictionary<int, int>(); // value-vertex → (segIndexInGadget, localValue) packed
            for (int s = 0; s < seg0.Length; s++)
                for (int gv = 0; gv < q; gv++) posOf[cfi.SegVerts[seg0[s]][gv]] = s * q + gv;

            var R = new List<(int, int, int)>();
            int[] adj = FlatAdj(cfi.Graph);
            foreach (int tv in cfi.Gadget0Tuples)
            {
                var coord = new int[seg0.Length];
                for (int u = 0; u < cfi.N; u++)
                    if (adj[tv * cfi.N + u] != 0 && posOf.TryGetValue(u, out int packed))
                        coord[packed / q] = packed % q;
                R.Add((coord[0], coord[1], coord[2]));
            }

            string recovered = RelationCanon(R, q);
            string gammaRef = RelationCanon(GroupRelation(G), q);
            var abelianRefs = AbelianRefs(q).Select(A => RelationCanon(GroupRelation(A), q)).ToHashSet();
            bool isAbelianIsotope = abelianRefs.Contains(recovered);

            string verdict = isAbelianIsotope
                ? "abelian-linear ⟹ option-2 ring route HANDLES it"
                : "NON-abelian ⟹ no abelian module fits ⟹ option-2 ring route FLAGS it";
            output.WriteLine(
                $"{G.Name,-7} {q,3} {(G.Abelian ? "y" : "n"),2}  {(recovered == gammaRef ? "yes" : "NO"),13}  " +
                $"{(isAbelianIsotope ? "yes" : "NO"),16}  {verdict}");

            Assert.Equal(gammaRef, recovered);                  // extraction recovered Γ's actual relation
            Assert.Equal(G.Abelian, isAbelianIsotope);          // abelian-isotope ⟺ Γ abelian (Albert)
        }
    }

    private static List<(int, int, int)> GroupRelation(Grp G)
    {
        var R = new List<(int, int, int)>();
        for (int i = 0; i < G.N; i++)
            for (int j = 0; j < G.N; j++)
                R.Add((i, j, G.Inv[G.Mul[i, j]]));   // i·j·k = e ⟺ k = (i·j)⁻¹
        return R;
    }

    // isotopy class of a ternary relation = canonical form of its colour-parted
    // incidence graph (parts A/B/C distinct colours; one vertex per triple).
    private string RelationCanon(List<(int, int, int)> R, int q)
    {
        int nT = R.Count, n = 3 * q + nT;
        var adj = new int[n, n];
        var types = new int[n];
        for (int i = 0; i < q; i++) { types[i] = 0; types[q + i] = 1; types[2 * q + i] = 2; }
        for (int t = 0; t < nT; t++)
        {
            types[3 * q + t] = 3;
            int tv = 3 * q + t;
            void E(int u) { adj[tv, u] = 1; adj[u, tv] = 1; }
            E(R[t].Item1); E(q + R[t].Item2); E(2 * q + R[t].Item3);
        }
        var orderer = new CanonGraphOrdererChainDescent { BudgetOverride = 20_000_000 };
        return orderer.Run(types, new AdjMatrix(adj)).ToString();
    }

    private static List<Grp> AbelianRefs(int q) => q switch
    {
        2 => new() { Zn(2) },
        3 => new() { Zn(3) },
        4 => new() { Zn(4), Klein() },
        6 => new() { Zn(6) },
        8 => new() { Zn(8),
                     GroupFromPerms("Z4xZ2", 6, new List<int[]> { new[] { 1, 2, 3, 0, 4, 5 }, new[] { 0, 1, 2, 3, 5, 4 } }),
                     GroupFromPerms("Z2^3", 6, new List<int[]> { new[] { 1, 0, 2, 3, 4, 5 }, new[] { 0, 1, 3, 2, 4, 5 }, new[] { 0, 1, 2, 3, 5, 4 } }) },
        _ => new() { Zn(q) },
    };

    // an F₂-odd random-regular biadjacency (nV>nW, high treewidth) — the genuine
    // IR-hard regime; oddness is the F₂ rigidity heuristic (the Γ-gauge is killed
    // by the anchor, not by oddness, but oddness gives a non-degenerate base).
    private static int[,] OddRandomRegular(int nV, int nW, int degree)
    {
        for (int seed = 0; seed < 5000; seed++)
        {
            var rng = new Random(seed);
            var b = new int[nV, nW];
            for (int v = 0; v < nV; v++)
            {
                var chosen = new HashSet<int>();
                while (chosen.Count < degree) chosen.Add(rng.Next(nW));
                foreach (var w in chosen) b[v, w] = 1;
            }
            if (MultipedeGenerator.IsOdd(b)) return b;
        }
        throw new InvalidOperationException("no odd random-regular base found");
    }

    // ── plumbing (replicated from CanonGraphOrdererChainDescent / Option2 probe) ─
    private static int[] FlatAdj(AdjMatrix g)
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
}
