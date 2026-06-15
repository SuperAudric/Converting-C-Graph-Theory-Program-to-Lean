using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Xunit;
using Xunit.Abstractions;

// ─────────────────────────────────────────────────────────────────────────────
// A2 MONOVARIANT probe — does a potential drop GEOMETRICALLY per seed?
// Route doc: docs/chain-descent-a2-potential-route.md (this probe is its evidence).
// Probe plan/findings (archived): docs/Archive/ChainDescent/chain-descent-a2-monovariant-probe.md.
// Added 2026-06-15.
//
// CONTEXT.  A1 reduced the seal's open input to "bound (k(X_T)−1)·c(X_T) at a small
// base".  Reframed dynamically (cxt-scoping §5): individualize a few SEED vertices,
// 1-WL PROPAGATES for free; the cost is the seed count = the number of times
// propagation STALLS.  The ONLY route to an unconditional, Lean-portable A2 is a
// POTENTIAL-DROP argument:
//
//   ∃ Φ (a structural quantity of the 1-WL-refined, partially-individualized config)
//   that drops by a constant FACTOR ρ<1 per seed on the non-carved residue
//   ⟹ O(log n) seeds discretize, uniformly.
//
// The group side has this free (|Aut| halves per seed → b(G) ≤ log₂|Aut|).  A2 is
// the same for a SCHEME-LEVEL potential, where the geometric drop is NOT known.
// This probe asks empirically whether such a Φ exists, and what it is a function of.
//
// PRIMARY POTENTIAL  Φ_cell = max 1-WL cell size (=1 ⟺ discrete).  Headline measure:
// the per-step drop factor Φ_cell(t+1)/Φ_cell(t).  Geometric ⟺ every factor ≤ ρ<1.
//
// SWEEP  residue {Shrikhande, Clebsch, Clebsch-complement} vs carved-contrast
// {rook L(m)=lattice/Hamming, triangular T(m)=Johnson, Paley(q)=conference}.
// HEADLINE  Shrikhande vs rook L(4): both (16,6,2,2) AND cospectral, so base/drop
// difference ⟹ base is SUB-SPECTRAL (structural); p-rank (2-rank differs) is the
// candidate finer invariant.
//
// CORRELATES (per graph, once): (n,k,λ,μ); spectrum + min eigenvalue multiplicity
// (closed form; conference ⟹ min-mult (n−1)/2); p-rank mod 2 and mod 3.
//
// All outcomes REPORTED, not asserted (every answer is a finding); only SRG-validity
// + the cospectral params are asserted.  Self-contained by probe convention; touches
// no production code.  1-WL (= warmRefine) is the cost-model object; the greedy base
// is an upper bound on b(X) = a witness that a fast-drop sequence EXISTS.
// ─────────────────────────────────────────────────────────────────────────────
public class A2MonovariantProbe(ITestOutputHelper output)
{
    sealed class Graph
    {
        public required string Name;
        public required string Category;   // RESIDUE | CARVED:lattice | CARVED:Johnson | CARVED:conference
        public required int N;
        public required bool[,] Adj;
    }

    // ── graph builders ──────────────────────────────────────────────────────────
    static bool[,] Empty(int n) => new bool[n, n];
    static void Edge(bool[,] a, int u, int v) { a[u, v] = true; a[v, u] = true; }

    // Cayley graph on Z_4 × Z_4 (vertex = 4*x + y), connection set as (dx,dy) pairs.
    static bool[,] CayleyZ4Sq((int, int)[] conn)
    {
        var set = new HashSet<(int, int)>();
        foreach (var (dx, dy) in conn) { set.Add((((dx % 4) + 4) % 4, ((dy % 4) + 4) % 4)); }
        var a = Empty(16);
        for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++)
            for (int x2 = 0; x2 < 4; x2++) for (int y2 = 0; y2 < 4; y2++)
            {
                if (x == x2 && y == y2) continue;
                var d = (((x - x2) % 4 + 4) % 4, ((y - y2) % 4 + 4) % 4);
                if (set.Contains(d)) a[4 * x + y, 4 * x2 + y2] = true;
            }
        return a;
    }

    // Cayley graph on Z_2^4 (vertex = 4-bit int), connection set as bit-masks; XOR-diff.
    static bool[,] CayleyZ2Pow4(int[] conn)
    {
        var set = new HashSet<int>(conn);
        var a = Empty(16);
        for (int u = 0; u < 16; u++) for (int v = u + 1; v < 16; v++)
            if (set.Contains(u ^ v)) Edge(a, u, v);
        return a;
    }

    static bool[,] Complement(bool[,] a, int n)
    {
        var c = Empty(n);
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (!a[u, v]) Edge(c, u, v);
        return c;
    }

    // Rook's / lattice graph L(m) = K_m □ K_m: vertex i*m+j, adjacent iff same row XOR same col.
    static bool[,] Rook(int m)
    {
        var a = Empty(m * m);
        for (int i = 0; i < m; i++) for (int j = 0; j < m; j++)
            for (int i2 = 0; i2 < m; i2++) for (int j2 = 0; j2 < m; j2++)
            {
                if (i == i2 && j == j2) continue;
                if ((i == i2) ^ (j == j2)) a[i * m + j, i2 * m + j2] = true;
            }
        return a;
    }

    // Triangular / Johnson J(m,2): vertices = 2-subsets of [m], adjacent iff they meet.
    static bool[,] Triangular(int m)
    {
        var pairs = new List<(int, int)>();
        for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) pairs.Add((i, j));
        int n = pairs.Count;
        var a = Empty(n);
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++)
        {
            var (a1, a2) = pairs[u]; var (b1, b2) = pairs[v];
            int common = (a1 == b1 || a1 == b2 ? 1 : 0) + (a2 == b1 || a2 == b2 ? 1 : 0);
            if (common == 1) Edge(a, u, v);
        }
        return a;
    }

    // Paley graph on F_q (q prime, q ≡ 1 mod 4): adjacent iff (i−j) is a nonzero QR.
    static bool[,] Paley(int q)
    {
        var qr = new HashSet<int>();
        for (int x = 1; x < q; x++) qr.Add((x * x) % q);
        var a = Empty(q);
        for (int u = 0; u < q; u++) for (int v = u + 1; v < q; v++)
            if (qr.Contains(((u - v) % q + q) % q)) Edge(a, u, v);
        return a;
    }

    // ── SRG validation + parameters ──────────────────────────────────────────────
    static (bool ok, int k, int lam, int mu) SrgParams(int n, bool[,] adj)
    {
        int Common(int u, int v) { int c = 0; for (int w = 0; w < n; w++) if (adj[u, w] && adj[v, w]) c++; return c; }
        int Deg(int u) { int d = 0; for (int w = 0; w < n; w++) if (adj[u, w]) d++; return d; }

        int k = Deg(0);
        for (int u = 1; u < n; u++) if (Deg(u) != k) return (false, k, -1, -1);

        int lam = -1, mu = -1;
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++)
        {
            int c = Common(u, v);
            if (adj[u, v]) { if (lam < 0) lam = c; else if (c != lam) return (false, k, lam, mu); }
            else { if (mu < 0) mu = c; else if (c != mu) return (false, k, lam, mu); }
        }
        return (true, k, lam, mu);
    }

    // SRG spectrum (closed form) + min eigenvalue multiplicity; conference flagged.
    static (string desc, int minMult, int twoMultLow) Spectrum(int n, int k, int lam, int mu)
    {
        int disc = (lam - mu) * (lam - mu) + 4 * (k - mu);
        int s = (int)Math.Round(Math.Sqrt(disc));
        if (disc > 0 && s * s == disc)
        {
            int r = (lam - mu + s) / 2, ss = (lam - mu - s) / 2;
            double f = 0.5 * ((n - 1) - (2.0 * k + (n - 1) * (lam - mu)) / s);
            int fi = (int)Math.Round(f), gi = n - 1 - fi;   // f ↔ eigenvalue r, g ↔ s
            int minM = Math.Min(fi, gi);
            return ($"r={r}(m{fi}), s={ss}(m{gi})", minM, minM);
        }
        // conference (disc not a perfect square): f = g = (n−1)/2
        return ($"conference ±√{n}", (n - 1) / 2, (n - 1) / 2);
    }

    // p-rank of the 0/1 adjacency matrix over F_p (Gaussian elimination).
    static int PRank(int n, bool[,] adj, int p)
    {
        var M = new int[n, n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) M[i, j] = adj[i, j] ? 1 : 0;
        int rank = 0;
        for (int col = 0; col < n && rank < n; col++)
        {
            int piv = -1;
            for (int r = rank; r < n; r++) if (M[r, col] % p != 0) { piv = r; break; }
            if (piv < 0) continue;
            for (int j = 0; j < n; j++) { (M[rank, j], M[piv, j]) = (M[piv, j], M[rank, j]); }
            int inv = ModInv(((M[rank, col] % p) + p) % p, p);
            for (int j = 0; j < n; j++) M[rank, j] = (M[rank, j] * inv % p + p) % p;
            for (int r = 0; r < n; r++)
            {
                if (r == rank) continue;
                int f = M[r, col] % p;
                if (f == 0) continue;
                for (int j = 0; j < n; j++) M[r, j] = ((M[r, j] - f * M[rank, j]) % p + p) % p;
            }
            rank++;
        }
        return rank;
    }
    static int ModInv(int a, int p) { for (int x = 1; x < p; x++) if (a * x % p == 1) return x; return 1; }

    // ── 1-WL (warmRefine) colour refinement with an individualized set ───────────
    // Returns the stable colouring (canonical small ints 0..#cells−1).
    static int[] Refine(int n, bool[,] adj, IReadOnlyList<int> indiv)
    {
        var color = new int[n];
        var isInd = new bool[n];
        foreach (var v in indiv) isInd[v] = true;
        // initial: each individualized vertex a unique colour; the rest share colour 0.
        int next = 1;
        for (int v = 0; v < n; v++) color[v] = isInd[v] ? next++ : 0;

        int numColors = color.Distinct().Count();
        while (true)
        {
            var keyOf = new string[n];
            for (int v = 0; v < n; v++)
            {
                var nbr = new List<int>();
                for (int u = 0; u < n; u++) if (adj[v, u]) nbr.Add(color[u]);
                nbr.Sort();
                keyOf[v] = color[v] + "|" + string.Join(",", nbr);
            }
            var map = new Dictionary<string, int>();
            foreach (var key in keyOf.Distinct().OrderBy(s => s, StringComparer.Ordinal)) map[key] = map.Count;
            for (int v = 0; v < n; v++) color[v] = map[keyOf[v]];
            if (map.Count == numColors) break;  // refinement only splits; fixpoint when count stops growing
            numColors = map.Count;
        }
        return color;
    }

    static int MaxCell(int[] color, int n)
    {
        var cnt = new Dictionary<int, int>();
        foreach (var c in color) cnt[c] = cnt.GetValueOrDefault(c) + 1;
        return cnt.Values.Max();
    }

    // Greedy-best 1-WL individualization: at each step pick the vertex (from a
    // non-singleton cell) whose refinement minimizes the resulting max cell.
    // Returns the Φ_cell curve [Φ(0), Φ(1), …, 1].
    static List<int> GreedyBaseCurve(int n, bool[,] adj)
    {
        var indiv = new List<int>();
        var curve = new List<int>();
        var color = Refine(n, adj, indiv);
        curve.Add(MaxCell(color, n));

        int guard = 0;
        while (MaxCell(color, n) > 1 && guard++ < n)
        {
            // candidates: one is enough but we scan all non-singleton-cell vertices.
            var cellSize = new Dictionary<int, int>();
            foreach (var c in color) cellSize[c] = cellSize.GetValueOrDefault(c) + 1;

            int best = -1, bestMax = int.MaxValue;
            for (int v = 0; v < n; v++)
            {
                if (indiv.Contains(v) || cellSize[color[v]] == 1) continue;
                var trial = new List<int>(indiv) { v };
                int m = MaxCell(Refine(n, adj, trial), n);
                if (m < bestMax) { bestMax = m; best = v; }
            }
            if (best < 0) break;   // safety: nothing left to split
            indiv.Add(best);
            color = Refine(n, adj, indiv);
            curve.Add(MaxCell(color, n));
        }
        return curve;
    }

    static string CurveStr(List<int> curve) => string.Join("→", curve);
    static double WorstDropFactor(List<int> curve)
    {
        double worst = 0;   // closest to 1 = worst stall
        for (int t = 0; t + 1 < curve.Count; t++)
            if (curve[t] > 0) worst = Math.Max(worst, (double)curve[t + 1] / curve[t]);
        return worst;
    }

    // Seidel switching: flip adjacency across the (S, V∖S) cut. Preserves SRG-ness
    // only for special "regular" sets S — the probe validates the result.
    static bool[,] SeidelSwitch(int n, bool[,] adj, HashSet<int> S)
    {
        var b = (bool[,])adj.Clone();
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++)
            if (S.Contains(u) != S.Contains(v)) { b[u, v] = !adj[u, v]; b[v, u] = !adj[u, v]; }
        return b;
    }

    // Index map for T(m) vertices (2-subsets of [m]) — to build switching sets from
    // edge sets of subgraphs of K_m (the Chang-graph construction at m=8).
    static (List<(int, int)> pairs, Dictionary<(int, int), int> idx) TriIndex(int m)
    {
        var pairs = new List<(int, int)>();
        var idx = new Dictionary<(int, int), int>();
        for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) { idx[(i, j)] = pairs.Count; pairs.Add((i, j)); }
        return (pairs, idx);
    }
    static HashSet<int> EdgeSetToVertices((int, int)[] edges, Dictionary<(int, int), int> idx)
    {
        var s = new HashSet<int>();
        foreach (var (a, b) in edges) s.Add(idx[(Math.Min(a, b), Math.Max(a, b))]);
        return s;
    }

    // One measurement row.
    (bool ok, int k, int lam, int mu, string spec, int minMult, int r2, int r3, int baseSize, double drop, string curve)
        Measure(Graph g)
    {
        var (ok, k, lam, mu) = SrgParams(g.N, g.Adj);
        if (!ok) return (false, k, lam, mu, "", 0, 0, 0, 0, 0, "");
        var (spec, minMult, _) = Spectrum(g.N, k, lam, mu);
        int r2 = PRank(g.N, g.Adj, 2), r3 = PRank(g.N, g.Adj, 3);
        var curve = GreedyBaseCurve(g.N, g.Adj);
        return (true, k, lam, mu, spec, minMult, r2, r3, curve.Count - 1, WorstDropFactor(curve), CurveStr(curve));
    }

    // ── Run 2: scaling — does the residue drop factor stay bounded < 1 while the
    //    carved (geometric) families' factor climbs toward 1 as n grows? ──────────
    [Fact]
    public void Probe_ScalingResidueVsCarved()
    {
        var (_, idx8) = TriIndex(8);
        // Chang switching sets (edge sets of subgraphs of K_8): perfect matching,
        // C_8, and C_3 ∪ C_5 — the classical three (28,12,6,4) Chang graphs.
        var changSets = new (string tag, (int, int)[] edges)[]
        {
            ("Chang-4K2", new[]{(0,1),(2,3),(4,5),(6,7)}),
            ("Chang-C8",  new[]{(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,7)}),
            ("Chang-C3C5",new[]{(0,1),(1,2),(0,2),(3,4),(4,5),(5,6),(6,7),(3,7)}),
        };

        var graphs = new List<Graph>
        {
            // RESIDUE, n=16
            new() { Name = "Shrikhande",  Category = "RESIDUE", N = 16, Adj = CayleyZ4Sq(new[]{(1,0),(3,0),(0,1),(0,3),(1,1),(3,3)}) },
            new() { Name = "Clebsch",     Category = "RESIDUE", N = 16, Adj = CayleyZ2Pow4(new[]{1,2,4,8,15}) },
            // CARVED twin / scaling
            new() { Name = "Rook L(4)",   Category = "CARVED:lattice", N = 16, Adj = Rook(4) },
            new() { Name = "Rook L(5)",   Category = "CARVED:lattice", N = 25, Adj = Rook(5) },
            new() { Name = "Rook L(6)",   Category = "CARVED:lattice", N = 36, Adj = Rook(6) },
            new() { Name = "Rook L(7)",   Category = "CARVED:lattice", N = 49, Adj = Rook(7) },
            new() { Name = "Rook L(8)",   Category = "CARVED:lattice", N = 64, Adj = Rook(8) },
            new() { Name = "Triangular T(6)", Category = "CARVED:Johnson", N = 15, Adj = Triangular(6) },
            new() { Name = "Triangular T(7)", Category = "CARVED:Johnson", N = 21, Adj = Triangular(7) },
            new() { Name = "Triangular T(8)", Category = "CARVED:Johnson", N = 28, Adj = Triangular(8) },
            new() { Name = "Paley(13)",   Category = "CARVED:conference", N = 13, Adj = Paley(13) },
            new() { Name = "Paley(29)",   Category = "CARVED:conference", N = 29, Adj = Paley(29) },
            new() { Name = "Paley(37)",   Category = "CARVED:conference", N = 37, Adj = Paley(37) },
        };
        // RESIDUE at n=28: Chang graphs by switching T(8); validated below.
        var t8 = Triangular(8);
        foreach (var (tag, edges) in changSets)
            graphs.Add(new() { Name = tag, Category = "RESIDUE", N = 28, Adj = SeidelSwitch(28, t8, EdgeSetToVertices(edges, idx8)) });

        // RESIDUE attempt at n=36: switch T(9) by edge sets of K_9 subgraphs (only
        // the ones that validate as (36,14,7,4) SRGs are genuine residue, reported).
        var (_, idx9) = TriIndex(9);
        var t9 = Triangular(9);
        var t9Sets = new (string, (int, int)[])[]
        {
            ("T9sw-C9",   new[]{(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,8)}),
            ("T9sw-4K2",  new[]{(0,1),(2,3),(4,5),(6,7)}),
            ("T9sw-C4C5", new[]{(0,1),(1,2),(2,3),(0,3),(4,5),(5,6),(6,7),(7,8),(4,8)}),
        };
        foreach (var (tag, edges) in t9Sets)
            graphs.Add(new() { Name = tag, Category = "RESIDUE", N = 36, Adj = SeidelSwitch(36, t9, EdgeSetToVertices(edges, idx9)) });

        output.WriteLine("A2 MONOVARIANT — SCALING: does residue drop-factor stay bounded <1 while carved → 1?");
        output.WriteLine("");
        output.WriteLine($"{"graph",-18} {"category",-18} {"n",-4} {"(k,λ,μ)",-12} {"2rk",-4} {"3rk",-4} {"base",-5} {"drop",-7} curve");
        output.WriteLine(new string('─', 120));

        var t8row = Measure(graphs.First(x => x.Name == "Triangular T(8)"));
        foreach (var g in graphs)
        {
            var m = Measure(g);
            if (!m.ok) { output.WriteLine($"{g.Name,-18} {g.Category,-18} {g.N,-4} NOT AN SRG (k={m.k},λ={m.lam},μ={m.mu}) — skipped"); continue; }
            string nonIso = g.Category == "RESIDUE" && g.N == 28
                ? (m.r2 != t8row.r2 ? $"  [2rk≠T8={t8row.r2} ⇒ ≇ T(8): genuine residue]" : "  [2rk=T8 ⇒ possibly ≅ T(8)]")
                : "";
            output.WriteLine($"{g.Name,-18} {g.Category,-18} {g.N,-4} {$"({m.k},{m.lam},{m.mu})",-12} {m.r2,-4} {m.r3,-4} {m.baseSize,-5} {m.drop,-7:F3} {m.curve}{nonIso}");
        }

        output.WriteLine("");
        output.WriteLine("SCALING TREND — worst drop factor vs n (climb toward 1 = √n/large-base signature):");
        foreach (var grp in graphs.GroupBy(g => g.Category))
        {
            var pts = grp.Select(g => (g.N, m: Measure(g))).Where(x => x.m.ok)
                         .OrderBy(x => x.N)
                         .Select(x => $"n{x.N}:{x.m.drop:F3}(b{x.m.baseSize})");
            output.WriteLine($"  {grp.Key,-18} {string.Join("  ", pts)}");
        }
        output.WriteLine("");
        output.WriteLine("READ: RESIDUE drop should stay flat/bounded across n; CARVED:lattice & Johnson should climb toward 1.");
        output.WriteLine("Paired twins: Shrikhande vs Rook L(4) @16; Chang vs Triangular T(8) @28.");
    }

    [Fact]
    public void Probe_CellSizeDropAcrossSRGs()
    {
        var graphs = new List<Graph>
        {
            // ── RESIDUE (the A2 target — expect geometric Φ_cell drop) ──
            new() { Name = "Shrikhande",        Category = "RESIDUE",
                    N = 16, Adj = CayleyZ4Sq(new[] { (1,0),(3,0),(0,1),(0,3),(1,1),(3,3) }) },
            new() { Name = "Clebsch",           Category = "RESIDUE",
                    N = 16, Adj = CayleyZ2Pow4(new[] { 1, 2, 4, 8, 15 }) },
            new() { Name = "Clebsch-complement", Category = "RESIDUE",
                    N = 16, Adj = Complement(CayleyZ2Pow4(new[] { 1, 2, 4, 8, 15 }), 16) },

            // ── CARVED: lattice / Hamming (Cameron, geometric) — expect base ≈ √n ──
            new() { Name = "Rook L(4)",  Category = "CARVED:lattice", N = 16, Adj = Rook(4) },
            new() { Name = "Rook L(5)",  Category = "CARVED:lattice", N = 25, Adj = Rook(5) },
            new() { Name = "Rook L(6)",  Category = "CARVED:lattice", N = 36, Adj = Rook(6) },

            // ── CARVED: Johnson (Cameron) — expect large base ──
            new() { Name = "Triangular T(6)", Category = "CARVED:Johnson", N = 15, Adj = Triangular(6) },
            new() { Name = "Triangular T(7)", Category = "CARVED:Johnson", N = 21, Adj = Triangular(7) },
            new() { Name = "Triangular T(8)", Category = "CARVED:Johnson", N = 28, Adj = Triangular(8) },

            // ── CARVED: conference (cyclotomic → abelian leg B) — reported ──
            new() { Name = "Paley(13)", Category = "CARVED:conference", N = 13, Adj = Paley(13) },
            new() { Name = "Paley(17)", Category = "CARVED:conference", N = 17, Adj = Paley(17) },
            new() { Name = "Paley(29)", Category = "CARVED:conference", N = 29, Adj = Paley(29) },
            new() { Name = "Paley(37)", Category = "CARVED:conference", N = 37, Adj = Paley(37) },
        };

        output.WriteLine("A2 MONOVARIANT PROBE — does Φ_cell (max 1-WL cell size) drop geometrically per seed?");
        output.WriteLine("greedy-best 1-WL individualization; base = seeds to discrete; drop = max_t Φ(t+1)/Φ(t)");
        output.WriteLine("");
        output.WriteLine($"{"graph",-20} {"category",-18} {"(n,k,λ,μ)",-16} {"spectrum",-22} {"2rk",-4} {"3rk",-4} {"base",-5} {"worstDrop",-10} Φ-curve");
        output.WriteLine(new string('─', 140));

        var rows = new List<(Graph g, int baseSize, double drop, int twoRank, int minMult)>();

        foreach (var g in graphs)
        {
            var (ok, k, lam, mu) = SrgParams(g.N, g.Adj);
            Assert.True(ok, $"{g.Name} is not a valid SRG (regular + constant λ,μ)");

            var (spec, minMult, _) = Spectrum(g.N, k, lam, mu);
            int r2 = PRank(g.N, g.Adj, 2);
            int r3 = PRank(g.N, g.Adj, 3);

            var curve = GreedyBaseCurve(g.N, g.Adj);
            int baseSize = curve.Count - 1;        // seeds individualized to reach discrete
            double drop = WorstDropFactor(curve);

            output.WriteLine($"{g.Name,-20} {g.Category,-18} {$"({g.N},{k},{lam},{mu})",-16} {spec,-22} {r2,-4} {r3,-4} {baseSize,-5} {drop,-10:F3} {CurveStr(curve)}");
            rows.Add((g, baseSize, drop, r2, minMult));
        }

        // ── Headline: the cospectral (16,6,2,2) pair — Shrikhande vs rook L(4) ──
        var shrik = rows.First(x => x.g.Name == "Shrikhande");
        var rook4 = rows.First(x => x.g.Name == "Rook L(4)");
        output.WriteLine("");
        output.WriteLine("HEADLINE — cospectral (16,6,2,2) pair (identical params AND spectrum):");
        output.WriteLine($"  Shrikhande : base={shrik.baseSize}, worstDrop={shrik.drop:F3}, 2-rank={shrik.twoRank}");
        output.WriteLine($"  Rook L(4)  : base={rook4.baseSize}, worstDrop={rook4.drop:F3}, 2-rank={rook4.twoRank}");
        output.WriteLine(shrik.baseSize != rook4.baseSize || Math.Abs(shrik.drop - rook4.drop) > 1e-9
            ? $"  ⇒ base/drop DIFFER on identical spectrum ⇒ base is SUB-SPECTRAL (structural). "
              + $"2-rank {(shrik.twoRank != rook4.twoRank ? "DIFFERS (candidate carving invariant)" : "matches")}."
            : "  ⇒ base/drop identical on this pair (no sub-spectral signal here).");

        // ── Monovariant verdict (reported) ──
        double residueWorst = rows.Where(x => x.g.Category == "RESIDUE").Max(x => x.drop);
        double latticeWorst = rows.Where(x => x.g.Category == "CARVED:lattice").Max(x => x.drop);
        double johnsonWorst = rows.Where(x => x.g.Category == "CARVED:Johnson").Max(x => x.drop);
        output.WriteLine("");
        output.WriteLine("MONOVARIANT signal (worst per-step drop factor; <1 = geometric, ≈1 = plateau/stall):");
        output.WriteLine($"  RESIDUE          worst drop = {residueWorst:F3}");
        output.WriteLine($"  CARVED:lattice   worst drop = {latticeWorst:F3}");
        output.WriteLine($"  CARVED:Johnson   worst drop = {johnsonWorst:F3}");
        output.WriteLine(residueWorst < 0.99 && (latticeWorst >= 0.99 || johnsonWorst >= 0.99)
            ? "  ⇒ CANDIDATE FOUND: Φ_cell drops geometrically on the residue but plateaus on a carved family. "
              + "Φ_cell (max 1-WL cell size) is a monovariant candidate for the A1/A3 potential argument."
            : residueWorst < 0.99
                ? "  ⇒ Φ_cell drops geometrically on the residue, but carved families did not visibly plateau at this n. "
                  + "Re-run at larger n / inspect curves before trusting a uniform ρ."
                : "  ⇒ No geometric drop on the residue at this n — Φ_cell is not the monovariant; try a 2-WL / p-rank potential.");

        output.WriteLine("");
        output.WriteLine("base vs correlates (does base track min-eigenvalue-multiplicity or p-rank?):");
        foreach (var x in rows.OrderBy(x => x.baseSize))
            output.WriteLine($"  {x.g.Name,-20} base={x.baseSize,-3} minMult={x.minMult,-4} 2-rank={x.twoRank,-3} drop={x.drop:F3}");
    }
}
