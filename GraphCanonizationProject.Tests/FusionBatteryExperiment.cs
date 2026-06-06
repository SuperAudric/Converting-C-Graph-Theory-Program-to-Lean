using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ── The no-fusion battery (docs/chain-descent-fusion-battery-plan.md) ──────────
//
// Measures, per graph G (optionally vertex-coloured by `types`): the ground-truth
// colour-preserving Aut(G); the RECOVERY-ONLY (defer-all-reals) harvest — what the
// symmetry-only descent finds before any real decision (ChainDescent.RecoveryOnly);
// and the verdict on the stuck-state residual.
//
//   harvest == Aut, nontrivial     → Clean  (symmetry fully consumed)
//   harvest == Aut, trivial        → TrivialResidual (IR-core, the rigid pole)
//   harvest ⊊ Aut, |Aut| SMALL     → LEAK   (a small symmetry the harvest could not
//                                              reach without a real decision = fusion)
//   harvest ⊊ Aut, |Aut| LARGE     → LargeExpected (largeness, not a leak — §3)
//
// The decisive signal is LEAK. Increment 1: measurement + ground truth + Tier-1
// controls (validate the instrument — a failure here falsifies the measurement, not
// the property). Tier-2 (products) and Tier-3 (adversarial grafts) follow.
//
// COLOURING. The multipede is the IR-core only as a *vertex-coloured* graph (its raw
// adjacency keeps the circulant base's rotational symmetry). So the battery is
// colour-aware: `types` seeds both the descent (a P-matrix ordering different types,
// like CanonGraphOrdererChainDescent.SeedFromTypes — already transitively closed since
// type-< is transitive) and the brute-force ground truth (initial 1-WL colour).
//
// GROUND TRUTH is the graph's OWN brute-force Aut — BFS-ordered, colour-filtered,
// node-capped (naive backtracking is exponential on rigid multipedes by construction).
// Faithfulness rule (Shrikhande / A2-i, plan §7): never the construction's intended group.
public class FusionBatteryExperiment(ITestOutputHelper output)
{
    public enum FusionVerdict { Clean, TrivialResidual, Leak, LargeExpected }

    private const long SmallAutCutoff = 10_000;     // "small" |Aut| for the leak signal at battery sizes

    private static FusionVerdict Classify(BigInteger harvestOrder, BigInteger autOrder)
    {
        if (harvestOrder == autOrder)
            return autOrder.IsOne ? FusionVerdict.TrivialResidual : FusionVerdict.Clean;
        return autOrder <= SmallAutCutoff ? FusionVerdict.Leak : FusionVerdict.LargeExpected;
    }

    // ── Vertex-type → P-matrix seed (replicates SeedFromTypes; TC-free, type-< is
    // transitive so the total preorder is already closed). ──────────────────────
    public static sbyte[] SeedFromTypes(int n, int[]? types)
    {
        var p = new sbyte[n * n];
        if (types == null) return p;
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                if (i != j && types[i] < types[j]) { p[i * n + j] = -1; p[j * n + i] = 1; }
        return p;
    }

    // ── 1-WL stable colouring (refinement filter for the brute force) ────────────
    private static int[] OneWLColours(int[] adj, int n, int[]? types)
    {
        var col = new int[n];
        for (int i = 0; i < n; i++)
        {
            int d = 0; for (int j = 0; j < n; j++) d += adj[i * n + j];
            col[i] = (types?[i] ?? 0) * (n + 1) + d;       // seed by (type, degree)
        }
        int distinct = col.Distinct().Count();
        for (int iter = 0; iter < n; iter++)
        {
            var sig = new (int, string)[n];
            for (int i = 0; i < n; i++)
            {
                var nbr = new List<int>();
                for (int j = 0; j < n; j++) if (adj[i * n + j] == 1) nbr.Add(col[j]);
                nbr.Sort();
                sig[i] = (col[i], string.Join(",", nbr));
            }
            var map = new Dictionary<(int, string), int>();
            var nc = new int[n]; int next = 0;
            for (int i = 0; i < n; i++)
            {
                if (!map.TryGetValue(sig[i], out int id)) { id = next++; map[sig[i]] = id; }
                nc[i] = id;
            }
            col = nc;
            if (next == distinct) break;
            distinct = next;
        }
        return col;
    }

    // ── Ground truth: brute-force Aut(G) — BFS-ordered, colour-filtered, capped ──
    // Returns |Aut|, whether the cap was hit, and the Aut-orbit partition on vertices
    // (union-find over images during enumeration — for the leak triage).
    public static (BigInteger order, bool capped, int[] orbitId) BruteForceAutInfo(
        int[] adj, int n, int[]? types = null, long cap = 3_000_000)
    {
        int[] col = OneWLColours(adj, n, types);

        var order = new int[n];
        var placed = new bool[n];
        int idx = 0;
        var q = new Queue<int>();
        for (int s = 0; s < n; s++)
        {
            if (placed[s]) continue;
            placed[s] = true; q.Enqueue(s);
            while (q.Count > 0)
            {
                int x = q.Dequeue(); order[idx++] = x;
                for (int y = 0; y < n; y++) if (adj[x * n + y] == 1 && !placed[y]) { placed[y] = true; q.Enqueue(y); }
            }
        }

        var parent = Enumerable.Range(0, n).ToArray();
        int Find(int x) { while (parent[x] != x) { parent[x] = parent[parent[x]]; x = parent[x]; } return x; }
        void Union(int a2, int b2) { int ra = Find(a2), rb = Find(b2); if (ra != rb) parent[ra] = rb; }

        long nodes = 0; BigInteger count = 0; bool capped = false;
        var img = new int[n]; var used = new bool[n]; Array.Fill(img, -1);

        void Rec(int oi)
        {
            if (capped) return;
            if (oi == n) { count++; for (int w = 0; w < n; w++) Union(w, img[w]); return; }
            int v = order[oi];
            for (int c = 0; c < n; c++)
            {
                if (used[c] || col[c] != col[v]) continue;
                if (++nodes > cap) { capped = true; return; }
                bool ok = true;
                for (int k = 0; k < oi && ok; k++) { int u = order[k]; if (adj[v * n + u] != adj[c * n + img[u]]) ok = false; }
                if (!ok) continue;
                img[v] = c; used[c] = true;
                Rec(oi + 1);
                used[c] = false; img[v] = -1;
            }
        }
        Rec(0);

        var orbitId = new int[n];
        var rep = new Dictionary<int, int>(); int next = 0;
        for (int v = 0; v < n; v++) { int r = Find(v); if (!rep.TryGetValue(r, out int id)) { id = next++; rep[r] = id; } orbitId[v] = id; }
        return (count, capped, orbitId);
    }

    public static (BigInteger order, bool capped) BruteForceAutOrder(
        int[] adj, int n, int[]? types = null, long cap = 3_000_000)
    {
        var (o, c, _) = BruteForceAutInfo(adj, n, types, cap);
        return (o, c);
    }

    // ── The recovery-only (defer-all-reals) harvest ──────────────────────────────
    public static (PermutationGroup harvest, bool stuck) RecoveryOnlyHarvest(int[] adj, int n, int[]? types = null)
    {
        var d = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        {
            EnableLinearOracle = true,
            EnableDeferral = true,
            RecoveryOnly = true,
        };
        d.Canonize(SeedFromTypes(n, types), new WarmPartition(n));
        return (d.Automorphisms, d.StuckResidual);
    }

    // Full canonizer harvest (Phase-2 on) — the byproduct Aut(G), for leak triage.
    public static PermutationGroup FullHarvest(int[] adj, int n, int[]? types = null)
    {
        var d = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        {
            EnableLinearOracle = true,
            EnableDeferral = true,
        };
        d.Canonize(SeedFromTypes(n, types), new WarmPartition(n));
        return d.Automorphisms;
    }

    // ── Graph utilities ──────────────────────────────────────────────────────────
    public static int[] Flatten(AdjMatrix g)
    {
        int n = g.VertexCount;
        var a = new int[n * n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) a[i * n + j] = g[i, j] != 0 ? 1 : 0;
        return a;
    }

    public static int[] Cycle(int n)
    {
        var a = new int[n * n];
        for (int i = 0; i < n; i++) { int j = (i + 1) % n; a[i * n + j] = 1; a[j * n + i] = 1; }
        return a;
    }

    // Disjoint union (block-diagonal) with concatenated, disjointly-renumbered types.
    public static (int[] adj, int n, int[] types) Disjoint(
        int[] a, int na, int[]? ta, int[] b, int nb, int[]? tb)
    {
        int n = na + nb;
        var c = new int[n * n];
        for (int i = 0; i < na; i++) for (int j = 0; j < na; j++) c[i * n + j] = a[i * na + j];
        for (int i = 0; i < nb; i++) for (int j = 0; j < nb; j++) c[(na + i) * n + (na + j)] = b[i * nb + j];

        var types = new int[n];
        int maxA = 0;
        for (int i = 0; i < na; i++) { types[i] = ta?[i] ?? 0; if (types[i] > maxA) maxA = types[i]; }
        for (int i = 0; i < nb; i++) types[na + i] = (tb?[i] ?? 0) + maxA + 1;   // disjoint type ranges
        return (c, n, types);
    }

    // Tensor (categorical) product G × H: (i,h)~(i',h') iff i~i' in G AND h~h' in H.
    // Aut ⊇ Aut(G) × Aut(H). Keep factors non-bipartite (else disconnected).
    public static (int[] adj, int n) Tensor(int[] a, int na, int[] b, int nb)
    {
        int n = na * nb;
        var c = new int[n * n];
        for (int i = 0; i < na; i++) for (int ip = 0; ip < na; ip++)
        {
            if (a[i * na + ip] != 1) continue;
            for (int h = 0; h < nb; h++) for (int hp = 0; hp < nb; hp++)
                if (b[h * nb + hp] == 1) c[(i * nb + h) * n + (ip * nb + hp)] = 1;
        }
        return (c, n);
    }

    // Lexicographic product G[H]: (i,h)~(i',h') iff i~i' in G, or (i==i' and h~h' in H).
    // The classic structure-fuser (Aut is a wreath-like product, Sabidussi).
    public static (int[] adj, int n) Lex(int[] a, int na, int[] b, int nb)
    {
        int n = na * nb;
        var c = new int[n * n];
        for (int i = 0; i < na; i++) for (int ip = 0; ip < na; ip++)
            for (int h = 0; h < nb; h++) for (int hp = 0; hp < nb; hp++)
            {
                if (i == ip && h == hp) continue;
                bool edge = a[i * na + ip] == 1 || (i == ip && b[h * nb + hp] == 1);
                if (edge) c[(i * nb + h) * n + (ip * nb + hp)] = 1;
            }
        return (c, n);
    }

    public static int[] Complete(int n)
    {
        var a = new int[n * n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i != j) a[i * n + j] = 1;
        return a;
    }

    // Orbit partition (vertex → orbit id) under a permutation group.
    public static int[] OrbitsOf(PermutationGroup g, int n)
    {
        var id = new int[n]; Array.Fill(id, -1);
        int next = 0;
        for (int v = 0; v < n; v++)
        {
            if (id[v] != -1) continue;
            foreach (int u in g.Orbit(v)) id[u] = next;
            next++;
        }
        return id;
    }

    // Two labellings induce the same partition iff (a[i]==a[j] ⟺ b[i]==b[j]) for all i,j.
    public static bool SamePartition(int[] a, int[] b, int n)
    {
        for (int i = 0; i < n; i++)
            for (int j = i + 1; j < n; j++)
                if ((a[i] == a[j]) != (b[i] == b[j])) return false;
        return true;
    }

    // ── Leak triage (plan §2/§6): mechanism-gap-B vs abstract-fusion-A ───────────
    //
    // A leak is harvest ⊊ Aut. Distinguish:
    //   • MechanismGapB — harvest recovered the full ORBIT partition (saw all the
    //     symmetry structure) but a proper subgroup (missed transversal generators):
    //     a representation/depth gap of the built oracle, not a missed symmetry.
    //   • AbstractFusionA — harvest's orbits are strictly FINER than Aut's: a genuine
    //     symmetry the recovery-only harvest could not see without a real decision —
    //     the fusion the theory predicts is hard to build (a place to work from).
    // The full-canonizer harvest (Phase-2 on) is logged as a cross-check that the
    // canonizer itself reaches Aut (else the canonizer, not fusion, is incomplete).
    public enum LeakKind { None, MechanismGapB, AbstractFusionA }

    private LeakKind Triage(int[] adj, int n, int[]? types, PermutationGroup harvest,
                            BigInteger autOrder, int[] autOrbits)
    {
        if (harvest.Order == autOrder) return LeakKind.None;
        var harvestOrbits = OrbitsOf(harvest, n);
        var kind = SamePartition(harvestOrbits, autOrbits, n) ? LeakKind.MechanismGapB : LeakKind.AbstractFusionA;
        var full = FullHarvest(adj, n, types).Order;
        int ho = harvestOrbits.Distinct().Count(), ao = autOrbits.Distinct().Count();
        output.WriteLine($"    triage: {kind}  harvestOrbits={ho} autOrbits={ao}  fullCanonizer={full} (Aut={autOrder})");
        return kind;
    }

    // k interchangeable copies of a unit (IDENTICAL types per copy ⇒ Aut ⊇ S_k
    // permuting copies). Disjoint (no inter-copy edges).
    public static (int[] adj, int n, int[] types) KCopies(int[] u, int nu, int[] ut, int k)
    {
        int n = nu * k;
        var adj = new int[n * n];
        var types = new int[n];
        for (int c = 0; c < k; c++)
            for (int i = 0; i < nu; i++)
            {
                types[c * nu + i] = ut[i];                         // identical across copies
                for (int j = 0; j < nu; j++) adj[(c * nu + i) * n + (c * nu + j)] = u[i * nu + j];
            }
        return (adj, n, types);
    }

    // Add a single hub vertex adjacent to vertex `anchor` of every copy — connects the
    // copies symmetrically (S_k still permutes copies, fixing the hub). The hub is an
    // articulation vertex: removing it restores the disjoint copies (layered/decomposable).
    public static (int[] adj, int n, int[] types) AddHub(
        (int[] adj, int n, int[] types) g, int nu, int k, int anchor)
    {
        int n2 = g.n + 1, hub = g.n;
        var adj = new int[n2 * n2];
        for (int i = 0; i < g.n; i++) for (int j = 0; j < g.n; j++) adj[i * n2 + j] = g.adj[i * g.n + j];
        for (int c = 0; c < k; c++) { int a = c * nu + anchor; adj[hub * n2 + a] = 1; adj[a * n2 + hub] = 1; }
        var types = new int[n2];
        int maxT = g.types.Max();
        for (int i = 0; i < g.n; i++) types[i] = g.types[i];
        types[hub] = maxT + 1;
        return (adj, n2, types);
    }

    // ── Decomposability probe (separable-layered vs genuine fusion) ──────────────
    // Number of connected components, optionally after deleting a vertex set.
    public static int ComponentCount(int[] adj, int n, HashSet<int>? deleted = null)
    {
        var seen = new bool[n]; int comps = 0;
        var st = new Stack<int>();
        for (int s = 0; s < n; s++)
        {
            if (seen[s] || (deleted?.Contains(s) ?? false)) continue;
            comps++; seen[s] = true; st.Push(s);
            while (st.Count > 0)
            {
                int x = st.Pop();
                for (int y = 0; y < n; y++)
                    if (adj[x * n + y] == 1 && !seen[y] && !(deleted?.Contains(y) ?? false)) { seen[y] = true; st.Push(y); }
            }
        }
        return comps;
    }

    // A leak is "decomposable" (separable / layered — the calculator §7 case that is NOT
    // the hard fusion) if the graph is disconnected, or a small vertex cut (here: a few
    // highest-degree vertices, e.g. a hub) disconnects it into ≥ 2 pieces.
    public static bool LeakIsDecomposable(int[] adj, int n, int cutBudget = 1)
    {
        if (ComponentCount(adj, n) >= 2) return true;
        var deg = new int[n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) deg[i] += adj[i * n + j];
        var top = Enumerable.Range(0, n).OrderByDescending(v => deg[v]).Take(cutBudget).ToHashSet();
        return ComponentCount(adj, n, top) >= 2;
    }

    public static int[] Scramble(int[] adj, int n, int[] perm)
    {
        var b = new int[n * n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) b[perm[i] * n + perm[j]] = adj[i * n + j];
        return b;
    }

    private static int[] RandomPerm(int n, int seed)
    {
        var p = Enumerable.Range(0, n).ToArray();
        var rng = new Random(seed);
        for (int i = n - 1; i > 0; i--) { int j = rng.Next(i + 1); (p[i], p[j]) = (p[j], p[i]); }
        return p;
    }

    private void Log(string name, int n, BigInteger autOrder, BigInteger harvestOrder, bool stuck, FusionVerdict v)
        => output.WriteLine($"{name,-26} n={n,3}  |Aut|={autOrder,-7} harvest={harvestOrder,-7} " +
                            $"stuck={(stuck ? "Y" : "N")}  ⇒ {v}");

    // ── Tier 1 — controls (validate the instrument + PP2's separable case) ───────

    [Theory]
    [InlineData("Johnson", 5, 2)]   // n=10, |Aut|=120
    [InlineData("Hamming", 3, 2)]   // n=8,  |Aut|=48
    [InlineData("Hamming", 2, 3)]   // n=9,  |Aut|=72
    [InlineData("Kneser", 5, 2)]    // n=10, |Aut|=120 (Petersen)
    public void Tier1_Cameron_PureSymmetric_HarvestsFullAut(string family, int a, int b)
    {
        var cg = family switch
        {
            "Johnson" => CameronGraphGenerator.Johnson(a, b),
            "Hamming" => CameronGraphGenerator.Hamming(a, b),
            "Kneser" => CameronGraphGenerator.Kneser(a, b),
            _ => throw new ArgumentException(family),
        };
        int n = cg.VertexCount;
        var adj = Flatten(cg.Graph);

        var (bf, capped) = BruteForceAutOrder(adj, n);
        Assert.False(capped, "brute force hit the cap on a small Cameron graph");
        Assert.Equal(cg.KnownAutOrder, bf);                    // independent ground truth

        var (harvest, stuck) = RecoveryOnlyHarvest(adj, n);
        var verdict = Classify(harvest.Order, cg.KnownAutOrder);
        Log(cg.Name, n, cg.KnownAutOrder, harvest.Order, stuck, verdict);

        // Pure scheme graph cascades ⇒ symmetry-only harvest reaches the full Aut.
        Assert.Equal(FusionVerdict.Clean, verdict);
    }

    [Theory]
    [InlineData(5)]   // 30 vertices, odd base ⇒ coloured multipede rigid
    [InlineData(6)]   // 36 vertices
    public void Tier1_Multipede_ColouredIrCore_TrivialResidual(int m)
    {
        var mp = MultipedeGenerator.BuildCirculant(m);
        Assert.True(mp.BaseIsOdd, $"circulant base m={m} must be odd (rigid)");
        int n = mp.Graph.VertexCount;
        var adj = Flatten(mp.Graph);
        var types = mp.VertexTypes;

        // Colour-preserving ground truth: the coloured multipede is rigid.
        var (bf, capped) = BruteForceAutOrder(adj, n, types);
        Assert.False(capped, "brute force hit the cap on a rigid multipede");
        Assert.Equal(BigInteger.One, bf);

        var (harvest, stuck) = RecoveryOnlyHarvest(adj, n, types);
        var verdict = Classify(harvest.Order, bf);
        Log($"Multipede(circ {m})", n, bf, harvest.Order, stuck, verdict);

        // Rigid IR-core: no symmetry to consume.
        Assert.Equal(FusionVerdict.TrivialResidual, verdict);
    }

    [Fact]
    public void Tier1_Disjoint_SeparableControl_HarvestsSymmetricFactor()
    {
        var mp = MultipedeGenerator.BuildCirculant(5);          // coloured-rigid, 30 vertices
        int nm = mp.Graph.VertexCount;
        var (adj, n, types) = Disjoint(Flatten(mp.Graph), nm, mp.VertexTypes, Cycle(7), 7, null);

        var (bf, capped) = BruteForceAutOrder(adj, n, types);
        Assert.False(capped, "brute force hit the cap on the disjoint control");
        // Separable: Aut = Aut(coloured multipede) × Aut(C₇) = 1 × 14.
        Assert.Equal(new BigInteger(14), bf);

        var (harvest, stuck) = RecoveryOnlyHarvest(adj, n, types);
        var verdict = Classify(harvest.Order, bf);
        Log("Multipede(5) ⊔ C7", n, bf, harvest.Order, stuck, verdict);

        // Symmetry-only harvest consumes the C₇ factor (D₇, order 14) and STOPS on the
        // rigid multipede part — PP2's separable case, empirically.
        Assert.Equal(FusionVerdict.Clean, verdict);
        Assert.True(stuck, "the rigid multipede component should leave a stuck residue");
    }

    // ── Tier 2 — operation closure: products preserve NoFusion (the structure-fusers) ─

    private static (int[] adj, int n) Factor(string s) => s switch
    {
        "C3" => (Cycle(3), 3),
        "C4" => (Cycle(4), 4),
        "C5" => (Cycle(5), 5),
        "K2" => (Complete(2), 2),
        _ => throw new ArgumentException(s),
    };

    [Theory]
    [InlineData("tensor", "C5", "C3")]   // 15v — circulant, |Aut|=60
    [InlineData("tensor", "C5", "C5")]   // 25v — |Aut|=200 (with factor swap)
    [InlineData("lex", "C5", "K2")]      // 10v — wreath D5 ≀ S2, |Aut|=320
    [InlineData("lex", "C4", "K2")]      // 8v  — |Aut|=128
    public void Tier2_Products_PreserveNoFusion(string op, string f1, string f2)
    {
        var (a, na) = Factor(f1);
        var (b, nb) = Factor(f2);
        var (adj, n) = op == "tensor" ? Tensor(a, na, b, nb) : Lex(a, na, b, nb);

        var (autOrd, capped, autOrbits) = BruteForceAutInfo(adj, n);
        Assert.False(capped, $"{f1} {op} {f2} brute force hit the cap");

        var (harvest, stuck) = RecoveryOnlyHarvest(adj, n);
        var verdict = Classify(harvest.Order, autOrd);
        Log($"{f1} {op} {f2}", n, autOrd, harvest.Order, stuck, verdict);
        var leak = Triage(adj, n, null, harvest, autOrd, autOrbits);

        // A product of cascade-class graphs must not FUSE: the symmetry-only harvest
        // sees the full orbit structure (no abstract-fusion leak). A MechanismGapB
        // (orbits found, proper subgroup) is logged but is not a fusion.
        Assert.NotEqual(LeakKind.AbstractFusionA, leak);
    }

    // Deterministic validation of the triage's two branches (no leak occurs naturally
    // on Tier-1/2, so exercise the logic directly with synthetic harvest groups on C₅,
    // whose Aut = D₅ (order 10, single orbit)).
    [Fact]
    public void Triage_DistinguishesMechanismFromFusion()
    {
        var adj = Cycle(5);
        var (autOrd, _, autOrbits) = BruteForceAutInfo(adj, 5);
        Assert.Equal(new BigInteger(10), autOrd);            // D₅

        // Trivial harvest: orbits are 5 singletons ⊊ Aut's single orbit ⇒ a missed
        // symmetry ⇒ AbstractFusionA.
        var trivial = new PermutationGroup(5);
        Assert.Equal(LeakKind.AbstractFusionA, Triage(adj, 5, null, trivial, autOrd, autOrbits));

        // Z₅ harvest (rotations only): same single orbit as D₅ but proper subgroup
        // (missed the reflections) ⇒ MechanismGapB, not a fusion.
        var z5 = new PermutationGroup(5);
        z5.AddGenerator(Perm.FromCycles(5, new[] { 0, 1, 2, 3, 4 }));
        Assert.Equal(LeakKind.MechanismGapB, Triage(adj, 5, null, z5, autOrd, autOrbits));
    }

    // ── Tier 3 — adversarial grafts (the decisive non-abelian fusion attempt) ────
    //
    // Tries to BUILD a hidden non-abelian symmetry. A genuine fusion = a CONNECTED,
    // NON-decomposable graph whose recovery-only harvest misses a small non-abelian
    // symmetry (AbstractFusionA ∧ ¬decomposable). The copy-based constructions are
    // predicted to register as SEPARABLE/LAYERED (the S₃ is an outer action over
    // identifiable IR-core blocks — calculator §7 "layered products decompose"), NOT
    // genuine fusion. Watch the failure mode: it is the proof insight.

    // Combined Tier-3 measurement + classification. Returns (leak, decomposable).
    private (LeakKind leak, bool decomposable) Tier3Measure(string name, int[] adj, int n, int[]? types)
    {
        var (autOrd, capped, autOrbits) = BruteForceAutInfo(adj, n, types);
        Assert.False(capped, $"{name}: brute force hit the cap");
        var (harvest, stuck) = RecoveryOnlyHarvest(adj, n, types);
        var verdict = Classify(harvest.Order, autOrd);
        var leak = Triage(adj, n, types, harvest, autOrd, autOrbits);
        bool decomp = LeakIsDecomposable(adj, n);
        int comps = ComponentCount(adj, n);
        string interp = leak switch
        {
            LeakKind.AbstractFusionA when decomp => "SEPARABLE/layered (Tier-0/IR-core — NOT fusion)",
            LeakKind.AbstractFusionA => "*** GENUINE CONNECTED FUSION ***",
            LeakKind.MechanismGapB => "mechanism gap (orbits found, proper subgroup)",
            _ => verdict.ToString(),
        };
        output.WriteLine($"{name,-26} n={n,3}  |Aut|={autOrd,-6} harvest={harvest.Order,-6} " +
                         $"stuck={(stuck ? "Y" : "N")} comps={comps} decomp={(decomp ? "Y" : "N")} " +
                         $"⇒ {verdict} / {leak} — {interp}");
        return (leak, decomp);
    }

    [Fact]
    public void Tier3_DisjointCopies_S3_IsSeparable()
    {
        var mp = MultipedeGenerator.BuildCirculant(5);
        var (adj, n, types) = KCopies(Flatten(mp.Graph), mp.Graph.VertexCount, mp.VertexTypes, 3);
        var (leak, decomp) = Tier3Measure("3× Multipede(5) disjoint", adj, n, types);

        // Aut ⊇ S₃ (interchangeable IR-core copies, order 6 — non-abelian). If recovery-only
        // misses it (raw ChainDescent has no Tier-0), it MUST be the separable/Tier-0 case
        // (disconnected), never a genuine connected fusion.
        if (leak == LeakKind.AbstractFusionA)
            Assert.True(decomp, "a disjoint-copy leak must be decomposable (separable, PP2 / Tier-0)");
    }

    [Fact]
    public void Tier3_HubBridgedCopies_S3_IsLayeredSeparable()
    {
        var mp = MultipedeGenerator.BuildCirculant(5);
        int nu = mp.Graph.VertexCount;
        var copies = KCopies(Flatten(mp.Graph), nu, mp.VertexTypes, 3);
        var (adj, n, types) = AddHub(copies, nu, 3, anchor: 0);   // connect copies via one hub vertex
        var (leak, decomp) = Tier3Measure("3× Multipede(5) + hub", adj, n, types);

        // Connected now, but the hub is an articulation vertex — removing it restores the
        // disjoint copies, so the S₃ is an outer action over identifiable blocks (layered,
        // calculator §7 "decomposes"). Any leak must be flagged decomposable — NOT a
        // genuine connected non-decomposable fusion. If this fails, a fusion was built.
        if (leak == LeakKind.AbstractFusionA)
            Assert.True(decomp, "a hub-bridged leak must be decomposable (layered, calculator §7)");
    }

    // k copies, each independently RELABELLED (structurally identical, label-misaligned).
    // Tests that the harvest certifies the copy-swap STRUCTURALLY (construct-and-check),
    // not by label-alignment — the adversarial sharpening of the disjoint case.
    public static (int[] adj, int n, int[] types) KCopiesScrambled(int[] u, int nu, int[] ut, int k)
    {
        int n = nu * k;
        var adj = new int[n * n]; var types = new int[n];
        for (int c = 0; c < k; c++)
        {
            var pi = RandomPerm(nu, 7000 + c);
            for (int i = 0; i < nu; i++)
            {
                types[c * nu + pi[i]] = ut[i];
                for (int j = 0; j < nu; j++) adj[(c * nu + pi[i]) * n + (c * nu + pi[j])] = u[i * nu + j];
            }
        }
        return (adj, n, types);
    }

    [Fact]
    public void Tier3_ScrambledCopies_S3_StillConsumed()
    {
        var mp = MultipedeGenerator.BuildCirculant(5);
        var (adj, n, types) = KCopiesScrambled(Flatten(mp.Graph), mp.Graph.VertexCount, mp.VertexTypes, 3);
        var (leak, decomp) = Tier3Measure("3× Multipede(5) scrambled", adj, n, types);

        // The S₃ now maps structurally-corresponding (not label-aligned) vertices. The
        // construct-and-check harvest must still certify it — and any miss must be the
        // separable/Tier-0 case (disconnected), never a genuine connected fusion.
        if (leak == LeakKind.AbstractFusionA)
            Assert.True(decomp, "a scrambled-copy leak must be decomposable (separable, Tier-0)");
    }

    [Fact]
    public void Tier3_Cfi_Abelian_IsNotFusion()
    {
        var cfi = CfiGraphGenerator.Generate("K4").Even;
        int n = cfi.VertexCount;
        var adj = Flatten(cfi);
        var (leak, _) = Tier3Measure("CFI(K4) [abelian gauge]", adj, n, null);

        // CFI's hidden symmetry is the abelian Z₂^β gauge. By the bottom-up route (L3,
        // §0.7.4) abelian is unique-candidate ⟹ consumable — never a fusion species. At
        // low treewidth it cascades (consumed); regardless it must not be AbstractFusionA.
        Assert.NotEqual(LeakKind.AbstractFusionA, leak);
    }

    // ── Measurement scramble-invariance (verdict must be relabel-independent) ─────
    [Fact]
    public void Measurement_ScrambleInvariant()
    {
        var cg = CameronGraphGenerator.Johnson(5, 2);
        int n = cg.VertexCount;
        var adj = Flatten(cg.Graph);

        var (baseHarvest, _) = RecoveryOnlyHarvest(adj, n);
        for (int s = 0; s < 4; s++)
        {
            var scr = Scramble(adj, n, RandomPerm(n, 1000 + s));
            var (h, _) = RecoveryOnlyHarvest(scr, n);
            Assert.Equal(baseHarvest.Order, h.Order);
        }
    }
}
