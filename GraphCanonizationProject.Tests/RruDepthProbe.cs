using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ─────────────────────────────────────────────────────────────────────────────
// RRU DEPTH PROBE (2026-07-10) — does an observable separate "rigid, correctly
// deferred" from "node-4/Cameron, must be assume-VT-consumed"?
//
// THE QUESTION. RRU ("Phase 1 reaches the rigid core unconditionally") needs a
// trigger for the assume-VT prune that is (a) computable and (b) sound, i.e.
//     trigger  ⟹  |Aut_D| large  (⟹ Cameron via G3 ⟹ classical ⟹ cell transitive).
// A trigger that also fires on a RIGID residue would assume-VT-prune a cell that
// is not one orbit — a correctness bug. Two candidates:
//     • ClassifyStarved (cls == 2) — the current "starvation" signal.
//     • MaxRecursionDepth (DeepenAnchor's `seq.Count`) — harvest deepening depth.
//
// THE PREDICTION UNDER TEST.
//   H1  ClassifyStarved == 0 everywhere (cls==2 is dead code: DeepenAnchor
//       individualizes one FRESH vertex per level, so the non-singleton footprint
//       shrinks each iteration and `depth == _n` is unreachable; the only other
//       exit is a TransitiveClose contradiction, which cannot happen when a rep is
//       placed below its own cellmates). If so, starvation is NOT an observable.
//   H2  MaxRecursionDepth stays BOUNDED on rigid / small-Aut residues (multipedes,
//       CFI, Chang) and GROWS on node-4/Cameron families (Johnson, Hamming, the
//       affine-polar forms graphs). If so, `MaxRecursionDepth > baseMax(n)` is a
//       sound, computable trigger and RRU is unconditional.
//       If a rigid residue also drives the depth up, H2 fails ⟹ no observable
//       separates ⟹ RRU must be stated conditionally (reaches rigid ∨ UnhandledResidue).
//
// READINGS (per graph): n, flagged?, harvested |Aut| + #orbits (VT?),
//   MaxRecursionDepth, ResolvedByRecursion, ClassifyStarved/BranchStarved,
//   Phase2Nodes, ConsumedSymmetric, NodeCount. Plus the RecoveryOnly (Phase-1-only,
//   defer-all-reals) run: StuckResidual + the Phase-1 harvest's orbit profile.
//
// This probe ASSERTS nothing about H2 (that is the measurement); it asserts only
// the invariants that must hold regardless (iso-invariance is covered elsewhere).
public class RruDepthProbe
{
    private readonly ITestOutputHelper _out;
    public RruDepthProbe(ITestOutputHelper output) => _out = output;

    // ── plumbing ────────────────────────────────────────────────────────────
    static int[] FlatAdj(AdjMatrix g)
    {
        int n = g.VertexCount;
        var adj = new int[n * n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                adj[i * n + j] = g[i, j];
        return adj;
    }

    static sbyte[] SeedFromTypes(int n, int[]? types)
    {
        var p = new sbyte[n * n];
        if (types == null) return p;
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                if (i != j && types[i] < types[j]) { p[i * n + j] = -1; p[j * n + i] = 1; }
        return p;
    }

    static (int orbits, int maxOrbit) OrbitProfile(PermutationGroup g, int n)
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

    // baseMax n = (log2 n)^2 — the Lean confinement threshold the trigger is compared against.
    static int BaseMax(int n) { int l = 0; while ((1 << (l + 1)) <= n) l++; return l * l; }

    void Report(string name, int[] adj, int n, int[]? types, string expect)
    {
        var d = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        { EnableLinearOracle = true, EnableDeferral = true };
        var r = d.Canonize(SeedFromTypes(n, types), new WarmPartition(n));
        var c = r.Stats.Cascade;
        var (orbits, maxOrb) = OrbitProfile(r.ResidualGroup, n);

        // Phase-1 only: defer every real decision, stop at the boundary.
        var d1 = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        { EnableLinearOracle = true, EnableDeferral = true, RecoveryOnly = true };
        d1.Canonize(SeedFromTypes(n, types), new WarmPartition(n));
        var (o1, m1) = OrbitProfile(d1.Automorphisms, n);

        _out.WriteLine(
            $"{name,-22} n={n,4} baseMax={BaseMax(n),2} | " +
            $"{(r.Flagged ? "FLAG" : "CANON"),-5} |Aut|={r.ResidualGroup.Order,-12} orb={orbits,-4} " +
            $"VT={(orbits == 1 && maxOrb == n ? "Y" : "n")} | " +
            $"MAXRECDEPTH={c.MaxRecursionDepth,3}  starved(cls/br)={c.ClassifyStarved}/{c.BranchStarved}  " +
            $"resolvedByRec={c.ResolvedByRecursion,-6} | " +
            $"nodes={r.Stats.NodeCount,-7} phase2Nodes={c.Phase2Nodes,-5} consumed={c.ConsumedSymmetric,-5} | " +
            $"P1: stuck={(d1.StuckResidual ? "Y" : "n")} |H|={d1.Automorphisms.Order,-12} orb={o1,-4} | {expect}");
    }

    // ── graph builders ──────────────────────────────────────────────────────
    static int[] Johnson(int n, int k, out int nv)
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

    static int[] Hamming(int d, int q, out int nv)
    {
        nv = (int)Math.Pow(q, d);
        var vec = new int[nv][];
        for (int v = 0; v < nv; v++) { var x = new int[d]; int t = v; for (int i = 0; i < d; i++) { x[i] = t % q; t /= q; } vec[v] = x; }
        var adj = new int[nv * nv];
        for (int u = 0; u < nv; u++)
            for (int v = u + 1; v < nv; v++)
            {
                int diff = 0; for (int i = 0; i < d; i++) if (vec[u][i] != vec[v][i]) diff++;
                if (diff == 1) { adj[u * nv + v] = 1; adj[v * nv + u] = 1; }
            }
        return adj;
    }

    // T(8) = J(8,2), and the Chang graphs = Seidel switch of T(8) w.r.t. a regular set.
    static int[] SeidelSwitch(int[] adj, int n, bool[] inS)
    {
        var b = (int[])adj.Clone();
        for (int u = 0; u < n; u++)
            for (int v = u + 1; v < n; v++)
                if (inS[u] != inS[v]) { int f = 1 - b[u * n + v]; b[u * n + v] = f; b[v * n + u] = f; }
        return b;
    }

    // Vertices of my Johnson(8,2) are enumerated by ASCENDING BITMASK, not lex pair
    // order — build the switching mask in that same order or you switch w.r.t. the
    // wrong 4-set and get a graph that is not a Chang graph.
    static bool[] ChangMask(int n8, (int, int)[] edges)
    {
        var idx = new Dictionary<int, int>(); int c = 0;
        for (int m = 0; m < (1 << 8); m++)
            if (System.Numerics.BitOperations.PopCount((uint)m) == 2) idx[m] = c++;
        var mask = new bool[n8];
        foreach (var (a, b) in edges) mask[idx[(1 << a) | (1 << b)]] = true;
        return mask;
    }

    static readonly (int, int)[] ChangA = { (0, 1), (2, 3), (4, 5), (6, 7) };            // perfect matching
    static readonly (int, int)[] ChangB = { (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 0) }; // 8-cycle

    // Affine-polar VO^ε_m(q): Cayley graph on F_q^dim, u~v iff Q(u-v)=0, Q ≠ 0.
    static int[] AffinePolar(int q, int dim, Func<int[], int> Q, out int nv)
    {
        int n = 1; for (int i = 0; i < dim; i++) n *= q;
        nv = n;
        return FormsGraphBuilder.StandardCayleyGraph(q, dim, dvec => Q(dvec) == 0);
    }

    [Fact]
    public void RRU_TriggerObservable_Separation()
    {
        _out.WriteLine("H1: is ClassifyStarved ever > 0?   H2: does MAXRECDEPTH separate rigid from Cameron?");
        _out.WriteLine(new string('-', 200));

        _out.WriteLine("### RIGID / small-Aut residues — the trigger MUST NOT fire here (else assume-VT is unsound)");
        foreach (int m in new[] { 5, 6, 8, 9, 10, 12 })
        {
            var mp = MultipedeGenerator.BuildCirculant(m);
            MultipedeGenerator.AssertRigid(mp);
            Report($"Multipede(circ {m})", FlatAdj(mp.Graph), mp.Graph.VertexCount, mp.VertexTypes, "rigid (odd base)");
        }

        foreach (var bg in new[] { "K4", "K33", "Rook3x3", "Petersen", "K6", "K7" })
        {
            var pair = CfiGraphGenerator.Generate(bg);
            Report($"CFI({bg}) even", FlatAdj(pair.Even), pair.Even.VertexCount, null, "CFI, abelian Aut");
        }

        {
            int n; var t8 = Johnson(8, 2, out n);
            Report("Chang-A (matching)", SeidelSwitch(t8, n, ChangMask(n, ChangA)), n, null, "small-Aut NON-VT SRG(28,12,6,4)");
            Report("Chang-B (8-cycle)", SeidelSwitch(t8, n, ChangMask(n, ChangB)), n, null, "small-Aut NON-VT SRG(28,12,6,4)");
        }

        _out.WriteLine("");
        _out.WriteLine("### NODE-4 / CAMERON (VT) residues — the trigger SHOULD fire here");
        foreach (var (nn, kk) in new[] { (7, 2), (8, 2), (9, 2), (10, 2), (9, 3), (10, 3) })
        {
            int n; var g = Johnson(nn, kk, out n);
            Report($"Johnson J({nn},{kk})", g, n, null, "Cameron, VT");
        }
        foreach (var (dd, qq) in new[] { (2, 5), (3, 3), (2, 7), (3, 4), (4, 3) })
        {
            int n; var g = Hamming(dd, qq, out n);
            Report($"Hamming H({dd},{qq})", g, n, null, "Cameron, VT");
        }

        _out.WriteLine("");
        _out.WriteLine("### AFFINE-POLAR forms graphs (the node-4 residue Route C seals)");
        // VO^-_4(3): Q = x0*x1 + x2^2 + x3^2  (x^2+y^2 anisotropic over F_3)
        {
            int n; var g = AffinePolar(3, 4, d => (d[0] * d[1] + d[2] * d[2] + d[3] * d[3]) % 3, out n);
            Report("VO^-_4(3)", g, n, null, "affine-polar minus, VT");
        }
        // VO^+_4(3): Q = x0*x1 + x2*x3 (hyperbolic)
        {
            int n; var g = AffinePolar(3, 4, d => (d[0] * d[1] + d[2] * d[3]) % 3, out n);
            Report("VO^+_4(3)", g, n, null, "affine-polar plus, VT");
        }
        // VO^-_4(2): Q = x0*x1 + x2^2 + x2*x3 + x3^2
        {
            int n; var g = AffinePolar(2, 4, d => (d[0] * d[1] + d[2] * d[2] + d[2] * d[3] + d[3] * d[3]) % 2, out n);
            Report("VO^-_4(2)", g, n, null, "affine-polar minus q=2, VT");
        }
        // VO^-_6(2)
        {
            int n; var g = AffinePolar(2, 6, d => (d[0] * d[1] + d[2] * d[3] + d[4] * d[4] + d[4] * d[5] + d[5] * d[5]) % 2, out n);
            Report("VO^-_6(2)", g, n, null, "affine-polar minus q=2 d=6, VT");
        }
    }

    // ── RRU falsifier: does Phase 1 actually harvest ALL of Aut(G)? ──────────
    // Compares the RecoveryOnly (Phase-1, defer-all-reals) harvest order against a
    // brute-force |Aut(G)|. Phase-1 harvest < true |Aut| ⟹ a genuine symmetry the
    // cascade oracle could not certify ⟹ "Phase 1 consumes every symmetry" FAILS
    // on that graph. Restricted to n small enough for the brute force not to cap.
    [Fact]
    public void RRU_Phase1HarvestsAllOfAut()
    {
        void Check(string name, int[] adj, int n, int[]? types)
        {
            var d1 = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
            { EnableLinearOracle = true, EnableDeferral = true, RecoveryOnly = true };
            d1.Canonize(SeedFromTypes(n, types), new WarmPartition(n));
            var (o1, _) = OrbitProfile(d1.Automorphisms, n);

            var (trueOrder, capped, _) = FusionBatteryExperiment.BruteForceAutInfo(adj, n, types);
            var harvested = d1.Automorphisms.Order;
            bool complete = !capped && harvested == trueOrder;

            // THE RRU TEST: at the pairwise-consumption fixpoint (no cell has a mergeable
            // pair), is the residue rigid?  Aut_D by brute force with D individualized.
            var d2 = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
            { EnableLinearOracle = true, EnableDeferral = true, RigidCoreProbe = true };
            d2.Canonize(SeedFromTypes(n, types), new WarmPartition(n));

            string rru = "no rigid-core node reached";
            if (d2.RigidCoreFound)
            {
                var t2 = new int[n];
                if (types != null) for (int i = 0; i < n; i++) t2[i] = types[i] * (n + 2);
                int c2 = 1;
                foreach (int v in d2.RigidCorePath) t2[v] += c2++;
                var (stabOrder, stabCapped, _) = FusionBatteryExperiment.BruteForceAutInfo(adj, n, t2);
                rru = stabCapped ? "|Aut_D|=CAPPED"
                    : stabOrder == 1 ? $"RRU HOLDS: |Aut_D|=1 at |D|={d2.RigidCorePath.Count}"
                                     : $"*** RRU FALSIFIED: |Aut_D|={stabOrder} at |D|={d2.RigidCorePath.Count} ***";
            }

            _out.WriteLine($"{name,-22} n={n,3} | phase1 |H|={harvested,-10} orb={o1,-3} stuck={(d1.StuckResidual ? "Y" : "n")}" +
                           $" | true |Aut|={(capped ? "CAPPED" : trueOrder.ToString()),-10}" +
                           $" | harvest={(capped ? "?" : complete ? "COMPLETE" : "LEAK"),-8} | {rru}");
        }

        _out.WriteLine("Phase-1 (RecoveryOnly) harvest vs brute-force |Aut| — a LEAK falsifies 'Phase 1 consumes every symmetry'");
        _out.WriteLine(new string('-', 130));

        var mp = MultipedeGenerator.BuildCirculant(5);
        Check("Multipede(circ 5)", FlatAdj(mp.Graph), mp.Graph.VertexCount, mp.VertexTypes);

        int n1; var t8 = Johnson(8, 2, out n1);
        Check("T(8) = J(8,2)", t8, n1, null);
        Check("Chang-A (matching)", SeidelSwitch(t8, n1, ChangMask(n1, ChangA)), n1, null);
        Check("Chang-B (8-cycle)", SeidelSwitch(t8, n1, ChangMask(n1, ChangB)), n1, null);

        int n2; Check("Johnson J(7,2)", Johnson(7, 2, out n2), n2, null);
        int n3; Check("Hamming H(3,3)", Hamming(3, 3, out n3), n3, null);
        int n4; Check("Hamming H(2,5)", Hamming(2, 5, out n4), n4, null);
        int n5; Check("VO^-_4(2) Clebsch", AffinePolar(2, 4, dd => (dd[0]*dd[1] + dd[2]*dd[2] + dd[2]*dd[3] + dd[3]*dd[3]) % 2, out n5), n5, null);

        var cfi = CfiGraphGenerator.Generate("K4");
        Check("CFI(K4) even", FlatAdj(cfi.Even), cfi.Even.VertexCount, null);
    }
}
