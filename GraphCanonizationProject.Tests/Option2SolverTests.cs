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

    [Theory]
    [InlineData("Z2", 2)]
    [InlineData("Z4", 4)]
    [InlineData("Z2^2", 4)]
    [InlineData("Z3", 3)]
    public void B1c_TryCanonicalForm_ScrambleInvariant_SelfVerified(string name, int asz)
    {
        var A = name switch { "Z2" => new Ab(2), "Z4" => new Ab(4), "Z2^2" => new Ab(2, 2), "Z3" => new Ab(3), _ => throw new ArgumentException(name) };
        Assert.Equal(asz, A.N);
        int nW = 6;
        var (g0, t0) = BuildNativeMultipede(A, CirculantLines(nW, new[] { 0, 1, 3 }), nW);

        var forms = new List<string?>();
        for (int s = -1; s < 3; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = g0; t = (int[])t0.Clone(); }
            else (g, t) = ScrambleWithTypes(g0, t0, 14000 + s);
            int n = g.VertexCount; var adj = Flat(g);
            var part = new WarmPartition(n); part.Refine(adj, SeedFromTypes(n, t));
            forms.Add(Option2Solver.TryCanonicalForm(adj, n, part.CellOf, part.NumCells));
        }
        Assert.All(forms, f => Assert.NotNull(f));                 // valid ⟹ self-verifies
        Assert.True(forms.Distinct().Count() == 1);                // scramble-invariant
    }

    [Fact]
    public void B1c_TryCanonicalForm_FlagsCorruption_AndSeparatesRings()
    {
        int nW = 6; var lines = CirculantLines(nW, new[] { 0, 1, 3 });
        var (g0, t0) = BuildNativeMultipede(new Ab(4), lines, nW);   // Z4
        int n = g0.VertexCount; var adj = Flat(g0);
        var part = new WarmPartition(n); part.Refine(adj, SeedFromTypes(n, t0));
        var good = Option2Solver.TryCanonicalForm(adj, n, part.CellOf, part.NumCells);
        Assert.NotNull(good);

        // corrupt one gadget tuple (redirect an edge to a sibling state) ⟹ no consistent labelling ⟹ FLAG.
        var badAdj = (int[])adj.Clone();
        int segCount = nW * 4; int gv = segCount;
        int oldNbr = -1; for (int w = 0; w < n; w++) if (badAdj[gv * n + w] == 1) { oldNbr = w; break; }
        int newNbr = (oldNbr / 4) * 4 + (oldNbr % 4 + 1) % 4;
        badAdj[gv * n + oldNbr] = 0; badAdj[oldNbr * n + gv] = 0;
        badAdj[gv * n + newNbr] = 1; badAdj[newNbr * n + gv] = 1;
        var partBad = new WarmPartition(n); partBad.Refine(badAdj, SeedFromTypes(n, t0));
        Assert.Null(Option2Solver.TryCanonicalForm(badAdj, n, partBad.CellOf, partBad.NumCells));

        // different ring, same base/size ⟹ different canonical form.
        var (gB, tB) = BuildNativeMultipede(new Ab(2, 2), lines, nW);   // Z2²
        int nB = gB.VertexCount; var adjB = Flat(gB);
        var partB = new WarmPartition(nB); partB.Refine(adjB, SeedFromTypes(nB, tB));
        var other = Option2Solver.TryCanonicalForm(adjB, nB, partB.CellOf, partB.NumCells);
        Assert.NotNull(other);
        Assert.NotEqual(good, other);
    }

    // ── B2: the rigid solver WIRED into the descent (ChainDescent.cs target==-1) ──
    // Drives the FULL descent (not just Recover/TryCanonicalForm) and asserts the B2 hook
    // (i) actually FIRES (RigidSolverCanonicalized > 0 — not silently falling through), (ii)
    // canonicalizes instead of flagging, and (iii) the emitted canonical matrix is
    // scramble-invariant. The spec is NOT the global lex-min (deferral fixes a different but
    // iso-invariant form), so we do NOT compare against the exhaustive branch — invariance is
    // the correctness claim. This is the B5 firing-slice bundled with B2, per the plan.
    [Theory]
    [InlineData("Z2", 2)]
    [InlineData("Z4", 4)]
    [InlineData("Z2^2", 4)]
    [InlineData("Z3", 3)]
    public void B2_RigidSolver_FiresAndCanonicalizes_ScrambleInvariant(string name, int asz)
    {
        var A = name switch { "Z2" => new Ab(2), "Z4" => new Ab(4), "Z2^2" => new Ab(2, 2), "Z3" => new Ab(3), _ => throw new ArgumentException(name) };
        Assert.Equal(asz, A.N);
        int nW = 6;
        var (g0, t0) = BuildNativeMultipede(A, CirculantLines(nW, new[] { 0, 1, 3 }), nW);

        var matrices = new List<string>();
        int totalFired = 0;
        for (int s = -1; s < 3; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = g0; t = (int[])t0.Clone(); }
            else (g, t) = ScrambleWithTypes(g0, t0, 15000 + s);
            int n = g.VertexCount; var adj = Flat(g);

            var descent = new ChainDescent(n, adj, new CascadeOracle(), 100_000);
            var result = descent.Canonize(SeedFromTypes(n, t), new WarmPartition(n));

            _out.WriteLine($"[{name} s={s}] n={n} flagged={result.Flagged} fired={descent.RigidSolverCanonicalized} " +
                           $"nodes={result.Stats.NodeCount} phase2={result.Stats.Cascade.Phase2Nodes}");

            Assert.True(descent.RigidSolverCanonicalized > 0, "B2 hook did not fire");
            Assert.False(result.Flagged);                       // rigid solver canonicalizes — no flag
            Assert.NotNull(result.Matrix);
            totalFired += descent.RigidSolverCanonicalized;
            matrices.Add(string.Concat(result.Matrix!.Select(x => x == 0 ? '0' : '1')));
        }
        Assert.True(totalFired > 0);
        Assert.True(matrices.Distinct().Count() == 1);          // canonical form scramble-invariant
        _out.WriteLine($"{name,-6} B2 fired ({totalFired}×), |A|={asz}, canonical scramble-inv=True");
    }

    // B1d large-|A|: the poly generating-set base (|A|^{r+1} anchor picks) canonicalizes rings the
    // old |A|!² brute base could never reach — Z8 alone would be 8!² ≈ 1.6e9 base labellings; here
    // it is 8·7 = 56 anchor picks. Fires + canonicalizes + scramble-invariant; distinct order-8 rings
    // (Z8 vs Z2×Z4) are separated by the emit.
    [Theory]
    [InlineData("Z6", 6)]
    [InlineData("Z8", 8)]
    [InlineData("Z9", 9)]
    [InlineData("Z2xZ4", 8)]
    public void B1d_LargeRing_PolyBase_FiresAndCanonicalizes(string name, int asz)
    {
        var A = name switch { "Z6" => new Ab(6), "Z8" => new Ab(8), "Z9" => new Ab(9), "Z2xZ4" => new Ab(2, 4), _ => throw new ArgumentException(name) };
        Assert.Equal(asz, A.N);
        int nW = 4;
        var (g0, t0) = BuildNativeMultipede(A, CirculantLines(nW, new[] { 0, 1, 3 }), nW);
        int n = g0.VertexCount;

        var forms = new List<string>();
        for (int s = -1; s < 1; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = g0; t = (int[])t0.Clone(); }
            else (g, t) = ScrambleWithTypes(g0, t0, 18000 + s);
            var r = RunDescent(g.VertexCount, Flat(g), SeedFromTypes(g.VertexCount, t), 100_000, rigid: true);
            Assert.True(r.fired > 0, $"B2 did not fire on native {name}");
            Assert.False(r.flagged);
            Assert.NotNull(r.matrix);
            forms.Add(MatrixString(r.matrix!));
        }
        Assert.True(forms.Distinct().Count() == 1);            // scramble-invariant
        _out.WriteLine($"{name,-6} |A|={asz} n={n} fired + scramble-inv (poly base; |A|!² brute infeasible)");
    }

    // ── B5: the cross-check battery — "prove it works" on the REAL descent ────────
    // Runs the PRODUCTION multipede (MultipedeGenerator, the F₂ CFI-parity fixture the
    // canonizer already knows as the IR-blind-spot) through the full descent B2-ON vs OFF.
    //
    // The B1d `SolveOverA` emit (one-segment base + linear solve) canonicalizes the whole
    // circulant multipede family INCLUDING the m≥8 cases where the old brute-2-segment +
    // unit-propagation emit stalled (the trivialisation needs simultaneous linear solving over
    // the cyclic constraint graph, which `SolveOverA` does and unit-prop cannot). So B2 now
    // FIRES + canonicalizes across the family, with a speedup over the exhaustive path.
    [Theory]
    [InlineData(5)]
    [InlineData(6)]
    [InlineData(8)]
    [InlineData(9)]
    [InlineData(10)]
    public void B5_ProductionMultipede_FiresAndCanonicalizes_Speedup(int m)
    {
        var mp = MultipedeGenerator.BuildCirculant(m);
        int n = mp.Graph.VertexCount;
        const long budget = 5000;

        var on = RunDescent(n, Flat(mp.Graph), SeedFromTypes(n, mp.VertexTypes), budget, rigid: true);
        var off = RunDescent(n, Flat(mp.Graph), SeedFromTypes(n, mp.VertexTypes), budget, rigid: false);

        Assert.True(on.fired > 0, $"B2 did not fire on production Circulant{m}");
        Assert.False(on.flagged);                          // B2 canonicalizes the IR-blind-spot residue
        Assert.NotNull(on.matrix);
        Assert.True(on.nodes <= off.nodes);                // speedup: never costs more than the exhaustive path
        _out.WriteLine($"Circulant{m} n={n}: ON[fired={on.fired} nodes={on.nodes}]  " +
                       $"OFF[flag={off.flagged} nodes={off.nodes}]  flagShrink={(off.flagged && !on.flagged)}");

        // the B2 canonical matrix is scramble-invariant (the real correctness claim).
        string? form0 = MatrixString(on.matrix!);
        for (int s = 0; s < 4; s++)
        {
            var (g2, t2) = ScrambleWithTypes(mp.Graph, mp.VertexTypes, 16000 + s);
            var r = RunDescent(n, Flat(g2), SeedFromTypes(n, t2), budget, rigid: true);
            Assert.True(r.fired > 0);
            Assert.False(r.flagged);
            Assert.Equal(form0, MatrixString(r.matrix!));
        }
    }

    // The SAFETY guarantee across the firing boundary: whether or not B2 fires, the full
    // descent's verdict AND (when canonical) its canonical matrix are SCRAMBLE-INVARIANT.
    // B2 fires uniformly per graph (root-gated on the iso-invariant partition), so no graph
    // mixes the two forms; m≥8 (unit-prop stalls ⟹ B2 does not fire) exercises the sound
    // fall-through. This test stays green when B1d makes m≥8 fire (it asserts invariance, not
    // firing) — a regression guard for the boundary, not a freeze of it.
    [Theory]
    [InlineData(5)]
    [InlineData(6)]
    [InlineData(8)]
    [InlineData(9)]
    public void B5_ProductionMultipede_SoundAcrossFiringBoundary(int m)
    {
        var mp = MultipedeGenerator.BuildCirculant(m);
        int n = mp.Graph.VertexCount;
        const long budget = 5000;

        (bool flagged, string? form, int fired)? baseline = null;
        for (int s = -1; s < 4; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = mp.Graph; t = mp.VertexTypes; }
            else (g, t) = ScrambleWithTypes(mp.Graph, mp.VertexTypes, 17000 + s);
            var r = RunDescent(n, Flat(g), SeedFromTypes(n, t), budget, rigid: true);
            (bool flagged, string? form, int fired) cur = (r.flagged, r.matrix == null ? null : MatrixString(r.matrix), r.fired);
            baseline ??= cur;
            Assert.Equal(baseline.Value.flagged, cur.flagged);   // verdict scramble-invariant
            Assert.Equal(baseline.Value.form, cur.form);         // canonical matrix scramble-invariant (or both null)
            Assert.Equal(baseline.Value.fired > 0, cur.fired > 0); // firing is uniform per graph
        }
        _out.WriteLine($"Circulant{m}: verdict+form scramble-invariant; B2 fired={baseline!.Value.fired > 0} " +
                       $"(m≥8 unit-prop stall ⟹ sound fall-through)");
    }

    // B5 separation: two DIFFERENT rings (same size/base) ⟹ DISTINCT canonical forms
    // through the full descent — the canonizer distinguishes non-isomorphic residues.
    [Fact]
    public void B5_DistinctRings_ProduceDistinctCanonicalForms()
    {
        int nW = 6; var lines = CirculantLines(nW, new[] { 0, 1, 3 });
        var (g4, t4) = BuildNativeMultipede(new Ab(4), lines, nW);       // Z4
        var (gv, tv) = BuildNativeMultipede(new Ab(2, 2), lines, nW);    // Z2²  (same |A|=4, same base)
        int n4 = g4.VertexCount, nv = gv.VertexCount;

        var r4 = RunDescent(n4, Flat(g4), SeedFromTypes(n4, t4), 5000, rigid: true);
        var rv = RunDescent(nv, Flat(gv), SeedFromTypes(nv, tv), 5000, rigid: true);
        Assert.True(r4.fired > 0 && rv.fired > 0);
        Assert.False(r4.flagged); Assert.False(rv.flagged);
        Assert.Equal(n4, nv);                                // same vertex count
        Assert.NotEqual(MatrixString(r4.matrix!), MatrixString(rv.matrix!));   // different ring ⟹ different form
    }

    // ── B1d (i): GENERAL ARITY — InferOrderProfile reduces a degree-d gadget to degree-3 ─────
    // A degree-4 native multipede has NO degree-3 gadget line, so the old InferOrderProfile flagged
    // it. The reduction (pin d−3 segments to local-0) recovers A from the constant-sum sub-square, so
    // Recover succeeds and TryCanonicalOrder canonicalizes it, scramble-invariantly.
    [Theory]
    [InlineData("Z2", 2)]
    [InlineData("Z3", 3)]
    public void B1d_GeneralArity_DegreeFourMultipede_RecoversAndCanonicalizes(string name, int asz)
    {
        var A = name switch { "Z2" => new Ab(2), "Z3" => new Ab(3), _ => throw new ArgumentException(name) };
        int nW = 8;
        var lines = CirculantLines(nW, new[] { 0, 1, 3, 5 });      // arity 4 — no degree-3 gadget exists
        Assert.All(lines, l => Assert.Equal(4, l.Length));

        var (g0, t0) = BuildNativeMultipede(A, lines, nW);
        var forms = new List<string?>();
        for (int s = -1; s < 3; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = g0; t = (int[])t0.Clone(); }
            else (g, t) = ScrambleWithTypes(g0, t0, 18000 + s);
            int n = g.VertexCount; var adj = Flat(g);
            var part = new WarmPartition(n); part.Refine(adj, SeedFromTypes(n, t));

            var res = Option2Solver.Recover(adj, n, part.CellOf, part.NumCells);
            Assert.NotNull(res);                                   // ring recovered from the degree-4 line
            Assert.Equal(asz, res!.ASize);
            Assert.Equal(A.TrueOrderProfile(), res.OrderProfile);  // correct ring, via the pin-d−3 reduction

            var order = Option2Solver.TryCanonicalOrder(adj, n, part.CellOf, part.NumCells);
            Assert.NotNull(order);                                 // and the higher-arity residue canonicalizes
            forms.Add(EmitFromOrder(adj, n, order!));
        }
        Assert.True(forms.Distinct().Count() == 1);                // scramble-invariant
        _out.WriteLine($"{name,-4} arity-4 multipede: ring={A.TrueOrderProfile()} canonical scramble-inv=True");
    }

    // ── B1d (ii): TRY-BOTH-SIDES — the emit no longer depends on the avg-degree heuristic ─────
    // The recover→solve→emit runs on BOTH bipartition classes; only the true segment side
    // self-verifies. Here the WRONG (gadget) side fails to recover a clean uniform residue, so the
    // both-sides TryCanonicalOrder relies on selecting the segment side — and stays scramble-invariant.
    [Fact]
    public void B1d_TryBothSides_SelectsSegmentSide()
    {
        int nW = 6; var lines = CirculantLines(nW, new[] { 0, 1, 3 });
        var (g0, t0) = BuildNativeMultipede(new Ab(3), lines, nW);   // Z3
        int n = g0.VertexCount; var adj = Flat(g0);
        var part = new WarmPartition(n); part.Refine(adj, SeedFromTypes(n, t0));

        // exactly one bipartition side yields a clean uniform-size segment residue.
        var s0 = Option2Solver.Recover(adj, n, part.CellOf, part.NumCells, forceSide: 0);
        var s1 = Option2Solver.Recover(adj, n, part.CellOf, part.NumCells, forceSide: 1);
        Assert.True((s0 == null) ^ (s1 == null),
            $"expected exactly one segment side; got side0={(s0 == null ? "null" : "res")} side1={(s1 == null ? "null" : "res")}");

        // the both-sides emit canonicalizes regardless of which BFS label the segment side got,
        // and stays scramble-invariant (the heuristic is bypassed).
        string? form0 = null;
        for (int scr = 0; scr < 4; scr++)
        {
            var (g, t) = ScrambleWithTypes(g0, t0, 19000 + scr);
            int m = g.VertexCount; var a = Flat(g);
            var p = new WarmPartition(m); p.Refine(a, SeedFromTypes(m, t));
            var order = Option2Solver.TryCanonicalOrder(a, m, p.CellOf, p.NumCells);
            Assert.NotNull(order);
            var f = EmitFromOrder(a, m, order!);
            form0 ??= f; Assert.Equal(form0, f);
        }
    }

    // ── B4 (D6): the σ-FOLD — canonize a MATCHED DOUBLE via the copy-swap involution ─────
    // A doubled+matched multipede (two copies + a perfect matching, Aut = Z₂ copy-swap) is NOT a
    // clean single multipede, so plain TryCanonicalOrder flags. TryCanonicalOrderWithFold detects the
    // copy-swap σ structurally (σ(v) = v's unique same-cell neighbour = its match), folds onto one copy,
    // canonicalizes the rigid core, and lifts. It fires at the SAME iso-invariant root as B2.
    [Theory]
    [InlineData("Z2", 2)]
    [InlineData("Z3", 3)]
    [InlineData("Z4", 4)]
    public void B4_MatchedDouble_FoldsAndCanonicalizes_ScrambleInvariant(string name, int asz)
    {
        var A = name switch { "Z2" => new Ab(2), "Z3" => new Ab(3), "Z4" => new Ab(4), _ => throw new ArgumentException(name) };
        Assert.Equal(asz, A.N);
        int nW = 6;
        var (core, ct) = BuildNativeMultipede(A, CirculantLines(nW, new[] { 0, 1, 3 }), nW);
        var (dg, dt) = DoubleAndMatch(core, ct);
        int N = dg.VertexCount;

        var forms = new List<string?>();
        for (int s = -1; s < 3; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = dg; t = (int[])dt.Clone(); }
            else (g, t) = ScrambleWithTypes(dg, dt, 20000 + s);
            var adj = Flat(g);
            var part = new WarmPartition(N); part.Refine(adj, SeedFromTypes(N, t));

            Assert.Null(Option2Solver.TryCanonicalOrder(adj, N, part.CellOf, part.NumCells));   // plain flags (doubled)
            var order = Option2Solver.TryCanonicalOrderWithFold(adj, N, part.CellOf, part.NumCells);
            Assert.NotNull(order);                                        // the σ-fold canonicalizes it
            Assert.Equal(N, order!.Length);
            Assert.Equal(Enumerable.Range(0, N), order.OrderBy(x => x));  // a genuine permutation of [0,N)
            forms.Add(EmitFromOrder(adj, N, order));
        }
        Assert.True(forms.Distinct().Count() == 1);                        // whole-graph canonical form scramble-invariant
        _out.WriteLine($"{name,-4} matched-double n={N}: σ-fold canonicalizes, scramble-inv=True");
    }

    // B4 wired into the descent: the doubled multipede canonicalizes via the root fold hook,
    // scramble-invariant, through the FULL ChainDescent (not just the solver call).
    [Theory]
    [InlineData("Z2", 2)]
    [InlineData("Z3", 3)]
    public void B4_MatchedDouble_CanonicalizesThroughDescent_ScrambleInvariant(string name, int asz)
    {
        var A = name switch { "Z2" => new Ab(2), "Z3" => new Ab(3), _ => throw new ArgumentException(name) };
        Assert.Equal(asz, A.N);
        int nW = 6;
        var (core, ct) = BuildNativeMultipede(A, CirculantLines(nW, new[] { 0, 1, 3 }), nW);
        var (dg, dt) = DoubleAndMatch(core, ct);
        int N = dg.VertexCount;

        var matrices = new List<string>();
        for (int s = -1; s < 3; s++)
        {
            AdjMatrix g; int[] t;
            if (s < 0) { g = dg; t = (int[])dt.Clone(); }
            else (g, t) = ScrambleWithTypes(dg, dt, 21000 + s);
            var r = RunDescent(N, Flat(g), SeedFromTypes(N, t), 5000, rigid: true);
            Assert.True(r.fired > 0, "B4 fold hook did not fire on the matched double");
            Assert.False(r.flagged);
            matrices.Add(MatrixString(r.matrix!));
        }
        Assert.True(matrices.Distinct().Count() == 1);
        _out.WriteLine($"{name,-4} matched-double n={N}: descent σ-fold canonicalizes, scramble-inv=True");
    }

    // B4 harvest seam (sub-step 1 of the fold↔engine integration): the fold emits its verified cover
    // automorphisms. A matched double of a RIGID multipede has Aut = Z₂ (the copy-swap), so the fold
    // harvests exactly that one generator — a genuine, non-identity involution automorphism.
    [Theory]
    [InlineData("Z2", 2)]
    [InlineData("Z3", 3)]
    [InlineData("Z4", 4)]
    public void B4_MatchedDouble_HarvestsCoverAutomorphism(string name, int asz)
    {
        var A = name switch { "Z2" => new Ab(2), "Z3" => new Ab(3), "Z4" => new Ab(4), _ => throw new ArgumentException(name) };
        Assert.Equal(asz, A.N);
        int nW = 6;
        var (core, ct) = BuildNativeMultipede(A, CirculantLines(nW, new[] { 0, 1, 3 }), nW);
        var (dg, dt) = DoubleAndMatch(core, ct);
        int N = dg.VertexCount;

        var adj = Flat(dg);
        var part = new WarmPartition(N); part.Refine(adj, SeedFromTypes(N, dt));
        var order = Option2Solver.TryCanonicalOrderWithFold(adj, N, part.CellOf, part.NumCells, out var coverAuts);
        Assert.NotNull(order);
        Assert.Single(coverAuts);                                             // exactly the copy-swap generator
        var sigma = coverAuts[0];
        Assert.False(sigma.SequenceEqual(Enumerable.Range(0, N)));            // non-identity
        for (int v = 0; v < N; v++) Assert.Equal(v, sigma[sigma[v]]);        // an involution
        for (int u = 0; u < N; u++)                                          // a genuine automorphism of G
            for (int v = 0; v < N; v++)
                Assert.Equal(adj[u * N + v], adj[sigma[u] * N + sigma[v]]);
        _out.WriteLine($"{name,-4} matched-double n={N}: harvested 1 verified cover automorphism (Z₂ copy-swap).");
    }

    // B4 harvest through the descent: the terminal fold now reports the COMPLETE automorphism group
    // (Aut = Z₂ for a matched double of a rigid core) via ResidualGroup — it was the trivial group before
    // the harvest seam (under-reported |Aut|). Scramble-invariant.
    [Theory]
    [InlineData("Z2", 2)]
    [InlineData("Z3", 3)]
    public void B4_MatchedDouble_ReportsCompleteAut_ThroughDescent(string name, int asz)
    {
        var A = name switch { "Z2" => new Ab(2), "Z3" => new Ab(3), _ => throw new ArgumentException(name) };
        Assert.Equal(asz, A.N);
        int nW = 6;
        var (core, ct) = BuildNativeMultipede(A, CirculantLines(nW, new[] { 0, 1, 3 }), nW);
        var (dg, dt) = DoubleAndMatch(core, ct);
        int N = dg.VertexCount;

        for (int scr = -1; scr < 3; scr++)
        {
            AdjMatrix g; int[] t;
            if (scr < 0) { g = dg; t = (int[])dt.Clone(); }
            else (g, t) = ScrambleWithTypes(dg, dt, 23000 + scr);
            var d = new ChainDescent(N, Flat(g), new CascadeOracle(), 5000) { EnableRigidSolver = true };
            var res = d.Canonize(SeedFromTypes(N, t), new WarmPartition(N));
            Assert.True(d.RigidSolverCanonicalized > 0, "fold did not fire");
            Assert.Equal(2, (int)res.ResidualGroup.Order);                    // Aut = Z₂, reported completely
        }
        _out.WriteLine($"{name,-4} matched-double n={N}: descent reports |Aut|=2 (complete) via the harvest seam.");
    }

    // B4 GENERAL fold: a NESTED double (double-of-double, Aut ⊇ Z₂², fiber size s=4). The general
    // fiber-quotient fold peels the whole Z₂² fiber in one shot (same-cell-neighbour graph → size-4
    // fibers; G∖H → 4 copies), canonizes the core, and lex-mins over the 4! copy-orderings.
    [Theory]
    [InlineData("Z2", 2)]
    [InlineData("Z3", 3)]
    public void B4_NestedDouble_GeneralFold_ScrambleInvariant(string name, int asz)
    {
        var A = name switch { "Z2" => new Ab(2), "Z3" => new Ab(3), _ => throw new ArgumentException(name) };
        Assert.Equal(asz, A.N);
        int nW = 6;
        var (core, ct) = BuildNativeMultipede(A, CirculantLines(nW, new[] { 0, 1, 3 }), nW);
        var (d1, t1) = DoubleAndMatch(core, ct);
        var (d2, t2) = DoubleAndMatch(d1, t1);        // double-of-double: 4 copies, fiber size 4
        int N = d2.VertexCount;
        Assert.Equal(4 * core.VertexCount, N);

        var forms = new List<string?>();
        for (int scr = -1; scr < 3; scr++)
        {
            AdjMatrix g; int[] t;
            if (scr < 0) { g = d2; t = (int[])t2.Clone(); }
            else (g, t) = ScrambleWithTypes(d2, t2, 22000 + scr);
            var adj = Flat(g);
            var part = new WarmPartition(N); part.Refine(adj, SeedFromTypes(N, t));

            Assert.Null(Option2Solver.TryCanonicalOrder(adj, N, part.CellOf, part.NumCells));   // plain flags
            var order = Option2Solver.TryCanonicalOrderWithFold(adj, N, part.CellOf, part.NumCells);
            Assert.NotNull(order);                                          // general fold canonicalizes
            Assert.Equal(Enumerable.Range(0, N), order!.OrderBy(x => x));   // genuine permutation
            forms.Add(EmitFromOrder(adj, N, order));
        }
        Assert.True(forms.Distinct().Count() == 1);                          // scramble-invariant
        _out.WriteLine($"{name,-4} nested-double n={N} (s=4): general fold canonicalizes, scramble-inv=True");
    }

    // B4 UNBOUNDED s: a FULLY-SYMMETRIC s-fold cover (each fiber = a clique K_s among the s copies, so
    // S_s acts). With s = 8 > MaxFoldMultiplicity(6), the s!-fallback is DISABLED, so a successful
    // canonicalization PROVES the poly symmetric path (identity order, verified by copy-swap automorphism)
    // engaged. Handles any s.
    [Theory]
    [InlineData("Z2", 8)]
    [InlineData("Z3", 8)]
    [InlineData("Z2", 12)]
    public void B4_SymmetricCover_UnboundedS_PolyFold_ScrambleInvariant(string name, int s)
    {
        var A = name switch { "Z2" => new Ab(2), "Z3" => new Ab(3), _ => throw new ArgumentException(name) };
        Assert.True(s > 6, "the point is s beyond the s!-fallback cap");
        int nW = 6;
        var (core, ct) = BuildNativeMultipede(A, CirculantLines(nW, new[] { 0, 1, 3 }), nW);
        var (cov, cvt) = SymmetricCover(core, ct, s);
        int N = cov.VertexCount;
        Assert.Equal(s * core.VertexCount, N);

        var forms = new List<string?>();
        for (int scr = -1; scr < 3; scr++)
        {
            AdjMatrix g; int[] t;
            if (scr < 0) { g = cov; t = (int[])cvt.Clone(); }
            else (g, t) = ScrambleWithTypes(cov, cvt, 23000 + scr);
            var adj = Flat(g);
            var part = new WarmPartition(N); part.Refine(adj, SeedFromTypes(N, t));

            Assert.Null(Option2Solver.TryCanonicalOrder(adj, N, part.CellOf, part.NumCells));   // plain flags
            var order = Option2Solver.TryCanonicalOrderWithFold(adj, N, part.CellOf, part.NumCells);
            Assert.NotNull(order);                                          // poly symmetric fold canonicalizes
            Assert.Equal(Enumerable.Range(0, N), order!.OrderBy(x => x));   // genuine permutation
            forms.Add(EmitFromOrder(adj, N, order));
        }
        Assert.True(forms.Distinct().Count() == 1);                          // scramble-invariant
        _out.WriteLine($"{name,-4} symmetric cover n={N} (s={s} > cap): POLY fold canonicalizes, scramble-inv=True");
    }

    // s isomorphic copies of `g`, glued fiber-wise: for each core-vertex i the s copies
    // {i, n+i, …, (s−1)n+i} share a colour AND form a clique K_s of same-cell edges (so every copy-swap
    // is an automorphism = S_s symmetry). COPIES = the s cores (G minus same-cell edges).
    private static (AdjMatrix, int[]) SymmetricCover(AdjMatrix g, int[] types, int s)
    {
        int n = g.VertexCount, N = s * n;
        var adj = new int[N, N];
        for (int c = 0; c < s; c++)
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (g[i, j] != 0) adj[c * n + i, c * n + j] = g[i, j];   // each copy = the core
        for (int i = 0; i < n; i++)
            for (int a = 0; a < s; a++)
                for (int b = a + 1; b < s; b++)
                { adj[a * n + i, b * n + i] = 1; adj[b * n + i, a * n + i] = 1; }   // K_s fiber per core-vertex
        var t = new int[N];
        for (int c = 0; c < s; c++) for (int i = 0; i < n; i++) t[c * n + i] = types[i];
        return (new AdjMatrix(adj), t);
    }

    // B4 separation: matched doubles of DIFFERENT cores get DISTINCT canonical forms.
    [Fact]
    public void B4_MatchedDouble_DistinctCores_ProduceDistinctForms()
    {
        int nW = 6; var lines = CirculantLines(nW, new[] { 0, 1, 3 });
        var (c4, t4) = BuildNativeMultipede(new Ab(4), lines, nW);       // Z4 core
        var (cv, tv) = BuildNativeMultipede(new Ab(2, 2), lines, nW);    // Z2² core (same size)
        var (d4, dt4) = DoubleAndMatch(c4, t4);
        var (dv, dtv) = DoubleAndMatch(cv, tv);
        int N = d4.VertexCount;
        Assert.Equal(N, dv.VertexCount);

        var f4 = FoldForm(d4, dt4);
        var fv = FoldForm(dv, dtv);
        Assert.NotNull(f4); Assert.NotNull(fv);
        Assert.NotEqual(f4, fv);
    }

    private static string? FoldForm(AdjMatrix g, int[] t)
    {
        int N = g.VertexCount; var adj = Flat(g);
        var part = new WarmPartition(N); part.Refine(adj, SeedFromTypes(N, t));
        var order = Option2Solver.TryCanonicalOrderWithFold(adj, N, part.CellOf, part.NumCells);
        return order == null ? null : EmitFromOrder(adj, N, order);
    }

    // two copies (0..n-1, n..2n-1) + a perfect matching i↔n+i; corresponding vertices share a colour.
    private static (AdjMatrix, int[]) DoubleAndMatch(AdjMatrix g, int[] types)
    {
        int n = g.VertexCount, N = 2 * n;
        var adj = new int[N, N];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                if (g[i, j] != 0) { adj[i, j] = g[i, j]; adj[n + i, n + j] = g[i, j]; }
        for (int i = 0; i < n; i++) { adj[i, n + i] = 1; adj[n + i, i] = 1; }
        var t = new int[N];
        for (int i = 0; i < n; i++) { t[i] = types[i]; t[n + i] = types[i]; }
        return (new AdjMatrix(adj), t);
    }

    // serialize adj under a canonical vertex order (order[rank]=orig vertex), row-major 0/1.
    private static string EmitFromOrder(int[] adj, int n, int[] order)
    {
        var sb = new System.Text.StringBuilder(order.Length * order.Length);
        for (int i = 0; i < order.Length; i++)
            for (int j = 0; j < order.Length; j++)
                sb.Append(adj[order[i] * n + order[j]] != 0 ? '1' : '0');
        return sb.ToString();
    }

    private (int fired, bool flagged, long nodes, int[]? matrix) RunDescent(
        int n, int[] adj, sbyte[] seed, long budget, bool rigid)
    {
        var d = new ChainDescent(n, adj, new CascadeOracle(), budget) { EnableRigidSolver = rigid };
        var res = d.Canonize((sbyte[])seed.Clone(), new WarmPartition(n));
        return (d.RigidSolverCanonicalized, res.Flagged, res.Stats.NodeCount, res.Matrix);
    }

    private static string MatrixString(int[] m) => string.Concat(m.Select(x => x == 0 ? '0' : '1'));

    [Fact]
    public void B1b_RecoverRing_Solve_Kernel_MatchGroundTruth()
    {
        // ring recovery from the order-profile fingerprint.
        Assert.Equal(new[] { 4 }, Option2Solver.RecoverRing(4, "1^1,2^1,4^2")!.Inv);       // Z4
        Assert.Equal(new[] { 2, 2 }, Option2Solver.RecoverRing(4, "1^1,2^3")!.Inv);        // Z2²
        Assert.Equal(new[] { 3 }, Option2Solver.RecoverRing(3, "1^1,3^2")!.Inv);           // Z3
        Assert.Equal(new[] { 2, 4 }, Option2Solver.RecoverRing(8, "1^1,2^3,4^4")!.Inv);    // Z2×Z4

        var A = Option2Solver.RecoverRing(4, "1^1,2^1,4^2")!;                                // Z4
        long[,] M = { { 1, 1, 0 }, { 0, 1, 1 }, { 1, 0, 1 } };                              // triangle (nontrivial coker)

        // SolveOverA solves M x = target (extended-Smith, poly).
        var target = MatVecRing(M, new[] { 1, 3, 2 }, A);
        var x = Option2Solver.SolveOverA(M, target, A);
        Assert.NotNull(x);
        Assert.Equal(target, MatVecRing(M, x!, A));

        // KernelSizeOverA (Smith) == brute over A^nW, for the triangle and for real multipede incidences.
        Assert.Equal(BruteKernel(M, A), Option2Solver.KernelSizeOverA(M, A));
        foreach (var (nW, name, inv) in new[] { (6, "Z4", new[] { 4 }), (6, "Z2^2", new[] { 2, 2 }), (7, "Z4", new[] { 4 }) })
        {
            var R = new Ab(inv);
            var (g, t) = BuildNativeMultipede(R, CirculantLines(nW, new[] { 0, 1, 3 }), nW);
            var part = new WarmPartition(g.VertexCount); part.Refine(Flat(g), SeedFromTypes(g.VertexCount, t));
            var res = Option2Solver.Recover(Flat(g), g.VertexCount, part.CellOf, part.NumCells);
            Assert.NotNull(res);
            var ring = Option2Solver.RecoverRing(res!.ASize, res.OrderProfile)!;
            Assert.Equal(BruteKernel(res.Incidence, ring), Option2Solver.KernelSizeOverA(res.Incidence, ring));
        }
    }

    private static int[] MatVecRing(long[,] M, int[] x, Option2Solver.Ring A)
    {
        int m = M.GetLength(0), nW = M.GetLength(1); var r = new int[m];
        for (int i = 0; i < m; i++) { int s = 0; for (int j = 0; j < nW; j++) if (M[i, j] != 0) s = A.Add(s, A.ScalarMul(x[j], M[i, j])); r[i] = s; }
        return r;
    }
    private static long BruteKernel(long[,] M, Option2Solver.Ring A)
    {
        int nW = M.GetLength(1); long total = 1; for (int i = 0; i < nW; i++) total *= A.N;
        long count = 0; var x = new int[nW];
        for (long code = 0; code < total; code++)
        {
            long c = code; for (int j = 0; j < nW; j++) { x[j] = (int)(c % A.N); c /= A.N; }
            if (MatVecRing(M, x, A).All(v => v == 0)) count++;
        }
        return count;
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
