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

    // ── B5: the cross-check battery — "prove it works" on the REAL descent ────────
    // Runs the PRODUCTION multipede (MultipedeGenerator, the F₂ CFI-parity fixture the
    // canonizer already knows as the IR-blind-spot) through the full descent B2-ON vs OFF.
    //
    // ⚠ B5 FINDING (the emit's completeness boundary): B2 v1's emit fixes a 2-SEGMENT base
    // and UNIT-PROPAGATES the sum-zero constraints. That completes only when propagation
    // from 2 segments reaches every segment; for the circulant it does at m=5,6 but STALLS
    // at m≥8 (the trivialisation is unique but needs simultaneous linear solving — Gaussian /
    // the already-built `SolveOverA` Smith gauge-fix — which unit-prop cannot do). So B2 FIRES
    // where unit-prop completes and FALLS THROUGH (sound) elsewhere. Wiring `SolveOverA` into
    // the emit closes this (B1d) — it is needed for COMPLETENESS, not only large |A|.
    [Theory]
    [InlineData(5)]
    [InlineData(6)]
    public void B5_ProductionMultipede_FiresWhereUnitPropCompletes_Speedup(int m)
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
