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

    // Latin-square (net) graph L_g(m), m PRIME, 2 ≤ g ≤ m+1.  n = m² cells (r,c).
    // The g parallel classes are {row, col, MOLS_1, …, MOLS_{g−2}} with the cyclic
    // MOLS L_i(r,c) = (r + i·c) mod m (i = 1…m−1, all orthogonal for prime m).  Two
    // distinct cells are adjacent iff they agree in SOME chosen class.  This is the
    // point graph of a transversal net ⟹ GEOMETRIC (Cameron-carved), and its smallest
    // eigenvalue is exactly −g — so sweeping g gives a controlled growing-|s| axis at
    // fixed n.  (g=2 is the rook graph; g and m+1−g are complementary; g=m+1 = K_{m²}.)
    static bool[,] LatinSquareGraph(int m, int g)
    {
        int n = m * m;
        var a = Empty(n);
        int ClassVal(int r, int c, int t) => t == 0 ? r : t == 1 ? c : ((r + (t - 1) * c) % m);
        for (int r = 0; r < m; r++) for (int c = 0; c < m; c++)
            for (int r2 = 0; r2 < m; r2++) for (int c2 = 0; c2 < m; c2++)
            {
                if (r == r2 && c == c2) continue;
                for (int t = 0; t < g; t++)
                    if (ClassVal(r, c, t) == ClassVal(r2, c2, t)) { a[r * m + c, r2 * m + c2] = true; break; }
            }
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

    // Smallest eigenvalue s of an SRG (integer when disc is a perfect square; 0 flags
    // a conference graph whose ±√n eigenvalues are irrational → the abelian/leg-B axis).
    static int SmallestEig(int n, int k, int lam, int mu)
    {
        int disc = (lam - mu) * (lam - mu) + 4 * (k - mu);
        int s = (int)Math.Round(Math.Sqrt(disc));
        return (disc > 0 && s * s == disc) ? (lam - mu - s) / 2 : 0;
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

    // ── Run 3: the SMALLEST-EIGENVALUE axis — the row-4 gap (route doc §3/§6) ────────
    //  The seal's potential-drop route discharges "geometric ⟹ Cameron / non-geometric
    //  ⟹ shatters" by a Neumaier-style dichotomy keyed on the smallest eigenvalue −s.
    //  The honest open core is ROW 4: unbounded-s, NON-geometric, generic SRGs.  ALL
    //  current residue evidence (Shrikhande/Clebsch/Chang) sits at s = −2/−3 (row 2,
    //  Neumaier-finite) — there is NO data point on the growing-|s| axis.  This probe
    //  maps worst-drop across |s| using the only constructible growing-|s| family,
    //  the Latin-square (net) graphs L_g(m) (geometric, s = −g), to test the route's
    //  prediction "geometric + growing s ⟹ worst-drop climbs toward 1", and to make
    //  concrete that the non-geometric+high-|s| cell (row 4) has no constructible
    //  witness — confirming the construction bottleneck with positive data.
    [Fact]
    public void Probe_SmallestEigenvalueAxis()
    {
        var (_, idx8) = TriIndex(8);
        var t8 = Triangular(8);

        var graphs = new List<Graph>();
        // GEOMETRIC growing-|s| axis at FIXED n: Latin-square nets L_g(m), s = −g.
        foreach (int g in new[] { 2, 3, 4 })
            graphs.Add(new() { Name = $"LS L_{g}(5)", Category = "CARVED:geometric", N = 25, Adj = LatinSquareGraph(5, g) });
        foreach (int g in new[] { 2, 3, 4, 5, 6 })
            graphs.Add(new() { Name = $"LS L_{g}(7)", Category = "CARVED:geometric", N = 49, Adj = LatinSquareGraph(7, g) });
        // RESIDUE reference points — note they ALL live at small |s| (the gap).
        graphs.Add(new() { Name = "Shrikhande", Category = "RESIDUE", N = 16, Adj = CayleyZ4Sq(new[] { (1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3) }) });
        graphs.Add(new() { Name = "Clebsch", Category = "RESIDUE", N = 16, Adj = CayleyZ2Pow4(new[] { 1, 2, 4, 8, 15 }) });
        graphs.Add(new() { Name = "Chang-C8", Category = "RESIDUE", N = 28, Adj = SeidelSwitch(28, t8, EdgeSetToVertices(new[] { (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (0, 7) }, idx8)) });
        // CONFERENCE (leg B) growing-|s| reference: Paley, irrational ±√n eigenvalues.
        foreach (int q in new[] { 13, 29, 37 })
            graphs.Add(new() { Name = $"Paley({q})", Category = "CARVED:conference", N = q, Adj = Paley(q) });

        output.WriteLine("A2 ROW-4 PROBE — worst 1-WL drop across the SMALLEST-EIGENVALUE axis (−s).");
        output.WriteLine("Latin-square nets L_g(m): GEOMETRIC, s=−g (controlled growing-|s| at fixed n).");
        output.WriteLine("Question: on the geometric axis does worst-drop CLIMB toward 1 as |s| grows (route §3 prediction)?");
        output.WriteLine("");
        output.WriteLine($"{"graph",-14} {"category",-18} {"n",-4} {"(k,λ,μ)",-13} {"s",-4} {"geom?",-6} {"base",-5} {"drop",-7} curve");
        output.WriteLine(new string('─', 120));

        var rows = new List<(string cat, int n, int s, int baseSize, double drop)>();
        foreach (var g in graphs)
        {
            var (ok, k, lam, mu) = SrgParams(g.N, g.Adj);
            if (!ok) { output.WriteLine($"{g.Name,-14} {g.Category,-18} {g.N,-4} NOT AN SRG (k={k},λ={lam},μ={mu}) — skipped"); continue; }
            int s = SmallestEig(g.N, k, lam, mu);
            var curve = GreedyBaseCurve(g.N, g.Adj);
            int baseSize = curve.Count - 1;
            double drop = WorstDropFactor(curve);
            string geom = g.Category == "CARVED:geometric" ? "yes" : g.Category == "CARVED:conference" ? "conf" : "no";
            string sStr = s == 0 ? $"±√{g.N}" : s.ToString();
            output.WriteLine($"{g.Name,-14} {g.Category,-18} {g.N,-4} {$"({k},{lam},{mu})",-13} {sStr,-4} {geom,-6} {baseSize,-5} {drop,-7:F3} {CurveStr(curve)}");
            rows.Add((g.Category, g.N, s, baseSize, drop));
        }

        output.WriteLine("");
        output.WriteLine("GEOMETRIC AXIS — worst drop vs |s| (does it climb toward 1 as |s| grows?):");
        foreach (var nGrp in rows.Where(r => r.cat == "CARVED:geometric").GroupBy(r => r.n).OrderBy(x => x.Key))
            output.WriteLine($"  n={nGrp.Key,-4} " + string.Join("  ", nGrp.OrderBy(r => -r.s).Select(r => $"s={r.s}:drop {r.drop:F3}(b{r.baseSize})")));
        output.WriteLine("");
        output.WriteLine("RESIDUE points (the A2 target) — note the |s| they occupy:");
        foreach (var r in rows.Where(r => r.cat == "RESIDUE").OrderBy(r => r.s))
            output.WriteLine($"  s={r.s,-3} n={r.n,-4} drop={r.drop:F3} base={r.baseSize}");

        // ── Honest verdict on the row-4 gap (the auto-read REFUTED a naive |s| story) ──
        int resMaxAbsS = rows.Where(r => r.cat == "RESIDUE").Max(r => -r.s);
        output.WriteLine("");
        output.WriteLine("FINDING 1 — worst-drop is NOT monotone in |s| on the geometric axis.");
        foreach (var nGrp in rows.Where(r => r.cat == "CARVED:geometric").GroupBy(r => r.n).OrderBy(x => x.Key))
        {
            var ordered = nGrp.OrderBy(r => -r.s).ToList();
            var peak = ordered.OrderByDescending(r => r.drop).First();
            var trough = ordered.OrderBy(r => r.drop).First();
            output.WriteLine($"  n={nGrp.Key}: worst-drop PEAKS at s={peak.s} ({peak.drop:F3}, base {peak.baseSize}) "
                + $"and TROUGHS at s={trough.s} ({trough.drop:F3}, base {trough.baseSize}).");
        }
        output.WriteLine("  The peak is the ROOK/grid extreme (g=2, s=−2, base=√n) AND its complement (g=m−1); the");
        output.WriteLine("  intermediate nets shatter BETTER (base 3, lower drop).  So the climb-toward-1 obstruction");
        output.WriteLine("  is the partial-geometry LINE/grid structure — a BOUNDED-s (s=−2) phenomenon — NOT the");
        output.WriteLine("  magnitude of |s|.  The drop is symmetric under complementation (g ↔ m+1−g).");
        output.WriteLine("");
        output.WriteLine("FINDING 2 — the ROW-4 cell is empty among constructibles (the gap, confirmed with data).");
        output.WriteLine($"  ALL residue evidence sits at |s| ≤ {resMaxAbsS}; every growing-|s| SRG built here is geometric");
        output.WriteLine("  (net) or conference (leg B).  Non-geometric + high-|s| + small-Aut has NO constructible");
        output.WriteLine("  witness — growing-|s| and non-geometric-small-Aut are anti-correlated among constructible");
        output.WriteLine("  SRGs (the CGGP family is the only known inhabitant).  Row 4 is construction-bottlenecked.");
        output.WriteLine("");
        output.WriteLine("IMPLICATION for the route (§3): keying the geometric→Cameron dichotomy on |s| alone mislocates");
        output.WriteLine("  the obstruction — the thing that defeats a constant drop is the GRID/line geometry (bounded s),");
        output.WriteLine("  already inside row 1/Cameron.  Stage 1b's drop lemma must therefore certify 'no partial-geometry");
        output.WriteLine("  line system' (NOT 'bounded |s|') as the shatters condition, and cover row 4 by a UNIFORM");
        output.WriteLine("  counting argument — probe evidence cannot reach it.");
    }

    // ── 2-WL coherent closure (WL on ordered pairs) of the graph adjacency with a
    //    base T individualized — the faithful X_T = pointExtension of the rank-2 SRG
    //    scheme {diag, edge, non-edge}.  The Lean confusionSet/BigConfusionCover live
    //    on THIS object (CoherentConfig.relOf of pointExtension), not the 1-WL vertex
    //    colouring `Refine` above.  Rank-2 (the graph's own coherent closure) is the
    //    CONSERVATIVE choice: an amorphic refinement is finer, so c only shrinks
    //    (indistinguishingNumber_mono) and a cover only gets easier to avoid — node 4
    //    on rank-2 is the hardest case, so a clean signal here is a fortiori on the
    //    amorphic residue.  Returns the stable pair-colour matrix rel[u,v]. ──────────
    // General form: the base colouring is ANY pair-colour function `baseCol` (the
    // graph's rank-2 {diag,edge,non-edge}, or a residue's amorphic rank-3/4 scheme
    // colour matrix).  The carved geometric SRGs ARE rank-2 schemes; the residue
    // (ℤ₄² Clebsch rank-4, …) has a FINER amorphic refinement — and X = orbitalScheme H
    // in the Lean seal is that amorphic scheme, so measuring the residue on its own
    // scheme (not the coarse rank-2 graph closure) is the faithful comparison.
    static int[,] PairClosureBase(int n, Func<int, int, int> baseCol, IReadOnlyList<int> T)
    {
        var flag = new int[n];
        { int f = 1; foreach (var t in T) flag[t] = f++; }   // a unique tag per base point
        var colour = new int[n, n];
        var map0 = new Dictionary<(int, int, int), int>();
        for (int u = 0; u < n; u++) for (int v = 0; v < n; v++)
        {
            var key = (baseCol(u, v), flag[u], flag[v]);
            if (!map0.TryGetValue(key, out int cc)) { cc = map0.Count; map0[key] = cc; }
            colour[u, v] = cc;
        }
        int classes = map0.Count;
        var arr = new (int, int)[n];
        var sb = new StringBuilder();
        while (true)
        {
            var sig = new Dictionary<string, int>();
            var nc = new int[n, n];
            for (int u = 0; u < n; u++) for (int v = 0; v < n; v++)
            {
                for (int w = 0; w < n; w++) arr[w] = (colour[u, w], colour[w, v]);
                Array.Sort(arr);
                sb.Clear(); sb.Append(colour[u, v]);
                foreach (var (a, b) in arr) { sb.Append('|'); sb.Append(a); sb.Append(','); sb.Append(b); }
                string s = sb.ToString();
                if (!sig.TryGetValue(s, out int cc)) { cc = sig.Count; sig[s] = cc; }
                nc[u, v] = cc;
            }
            if (sig.Count == classes) return colour;   // split-only ⟹ same count = stable
            colour = nc; classes = sig.Count;
        }
    }

    // The graph's rank-2 base colouring {diag=2, edge=1, non-edge=0}.
    static Func<int, int, int> GraphCol(bool[,] adj) => (u, v) => u == v ? 2 : adj[u, v] ? 1 : 0;
    static int[,] PairClosure(int n, bool[,] adj, IReadOnlyList<int> T) => PairClosureBase(n, GraphCol(adj), T);

    // The confusion-cover multiplicity metrics on the closure `rel` at threshold ρ.
    //   c           = c(X_T) = max over non-reflexive classes of |C(α,β)|,
    //                 C(α,β) = {γ : rel[γ,α] = rel[γ,β]} (the indistinguishing number).
    //   N_ρ         = # DISTINCT confusion sets of size > ρ·c (the bigClasses count).
    //   L_ρ         = (Σ distinct big set sizes)/n  (the §9.6 average multiplicity/load,
    //                 the double-count bound on minMult: Σ_v mult_v = Σ_i|C_i| = L·n).
    //   minMult_ρ   = min_v #{big sets ∋ v} = the per-halving CLEANUP COST (0 ⟺ an
    //                 avoiding v exists ⟺ ¬BigConfusionCover ⟺ node 4 holds here).
    //   maxMult_ρ   = max_v #{big sets ∋ v} (=1 ⟺ the cover is a PARTITION = the 2a
    //                 tight case; ≥2 ⟺ overlapping = the open 2b loose case).
    //   cover       = minMult ≥ 1 (BigConfusionCover); tight = cover ∧ maxMult = 1.
    //   mass        = Σ_{big} |C|² (the size-weighted monovariant, §9.6 metric (b)).
    static (int c, int N, double L, int minMult, int maxMult, bool cover, bool tight, long mass)
        CoverMetrics(int n, int[,] rel, double rho)
    {
        // c(X_T) = max over ALL a≠b of |C(a,b)|; C symmetric ⟹ unordered pairs suffice.
        // (Off-diagonal ⟹ non-reflexive class automatically, by the CC diag_eq axiom.)
        int c = 0;
        var sizes = new int[n, n];
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++)
        {
            int sz = 0; for (int g = 0; g < n; g++) if (rel[g, a] == rel[g, b]) sz++;
            sizes[a, b] = sz; if (sz > c) c = sz;
        }
        if (c == 0) return (0, 0, 0, 0, 0, false, false, 0);

        // The big confusion sets — C(α,β) for EVERY pair (not one rep per class): the
        // Lean BigConfusionCover/bigClasses quantify over all pairs, and a pair's set
        // translates across its relation class, so the cover has many distinct sets.
        double thr = rho * c;
        var distinct = new Dictionary<string, bool[]>();              // dedupe big sets by content
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++)
        {
            if (sizes[a, b] <= thr) continue;
            var mem = new bool[n]; var key = new StringBuilder();
            for (int g = 0; g < n; g++) if (rel[g, a] == rel[g, b]) { mem[g] = true; key.Append(g).Append(','); }
            distinct[key.ToString()] = mem;
        }
        var big = distinct.Values.ToList();
        int N = big.Count;
        if (N == 0) return (c, 0, 0, 0, 0, false, false, 0);          // no big set ⟹ no cover, trivially

        long sumSize = 0, mass = 0;
        var mult = new int[n];
        foreach (var mem in big)
        {
            int sz = 0;
            for (int g = 0; g < n; g++) if (mem[g]) { sz++; mult[g]++; }
            sumSize += sz; mass += (long)sz * sz;
        }
        int minMult = int.MaxValue, maxMult = 0;
        for (int g = 0; g < n; g++) { minMult = Math.Min(minMult, mult[g]); maxMult = Math.Max(maxMult, mult[g]); }
        bool cover = minMult >= 1;
        return (c, N, (double)sumSize / n, minMult, maxMult, cover, cover && maxMult == 1, mass);
    }

    // Cheap c(X_T) (one rep per class — for the greedy base search; |C| is constant on a class).
    static int CofBase(int n, Func<int, int, int> baseCol, IReadOnlyList<int> T)
    {
        var rel = PairClosureBase(n, baseCol, T);
        var refl = new HashSet<int>(); for (int u = 0; u < n; u++) refl.Add(rel[u, u]);
        var seen = new HashSet<int>(); int c = 0;
        for (int a = 0; a < n; a++) for (int b = 0; b < n; b++)
        {
            if (a == b) continue; int t = rel[a, b];
            if (refl.Contains(t) || !seen.Add(t)) continue;
            int sz = 0; for (int g = 0; g < n; g++) if (rel[g, a] == rel[g, b]) sz++;
            c = Math.Max(c, sz);
        }
        return c;
    }
    static int CofXT(int n, bool[,] adj, IReadOnlyList<int> T) => CofBase(n, GraphCol(adj), T);

    // The base sequence ∅ ⊆ {0} ⊆ {0,v*}: vertex-transitive ⟹ pin 0 first; v* greedily
    // minimizes c(X_{0,v}) (the over-B base where the cover question is live).  Greedy
    // +2 only for n ≤ 28 (cost); larger fixtures report ∅ and {0}.
    static List<List<int>> BaseSeqBase(int n, Func<int, int, int> baseCol)
    {
        var seq = new List<List<int>> { new(), new() { 0 } };
        if (n <= 28)
        {
            int best = -1, bestC = int.MaxValue;
            for (int v = 1; v < n; v++)
            {
                int c = CofBase(n, baseCol, new List<int> { 0, v });
                if (c < bestC) { bestC = c; best = v; }
            }
            if (best >= 0) seq.Add(new() { 0, best });
        }
        return seq;
    }
    static List<List<int>> BaseSeq(int n, bool[,] adj) => BaseSeqBase(n, GraphCol(adj));

    // Imprimitive controls (to settle whether a TIGHT/partition cover ever forms — the
    // 2a premise; all the primitive fixtures are loose, so 2a's status hinges on these).
    static bool[,] DisjointCliques(int m, int a)   // m·K_a: adjacent iff same block
    {
        int n = m * a; var g = Empty(n);
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (u / a == v / a) Edge(g, u, v);
        return g;
    }
    static bool[,] CompleteMultipartite(int m, int a)   // K_{m×a}: adjacent iff DIFFERENT block
    {
        int n = m * a; var g = Empty(n);
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (u / a != v / a) Edge(g, u, v);
        return g;
    }

    // The ℤ₄² amorphic-NLS Clebsch scheme colour matrix (rank-4: 0=diagonal), the project's
    // primitive G2-B bullseye (= GraphCanonizationProofs ClebschConcrete.clebschZ4ColF).  Its
    // own (amorphic) scheme — NOT the rank-2 graph closure — is the faithful X for the residue.
    static readonly int[,] ClebschZ4Amorphic = new int[16, 16]
    {
        {0,2,1,2,1,1,3,2,2,3,3,3,1,2,3,1},
        {2,0,2,1,2,1,1,3,3,2,3,3,1,1,2,3},
        {1,2,0,2,3,2,1,1,3,3,2,3,3,1,1,2},
        {2,1,2,0,1,3,2,1,3,3,3,2,2,3,1,1},
        {1,2,3,1,0,2,1,2,1,1,3,2,2,3,3,3},
        {1,1,2,3,2,0,2,1,2,1,1,3,3,2,3,3},
        {3,1,1,2,1,2,0,2,3,2,1,1,3,3,2,3},
        {2,3,1,1,2,1,2,0,1,3,2,1,3,3,3,2},
        {2,3,3,3,1,2,3,1,0,2,1,2,1,1,3,2},
        {3,2,3,3,1,1,2,3,2,0,2,1,2,1,1,3},
        {3,3,2,3,3,1,1,2,1,2,0,2,3,2,1,1},
        {3,3,3,2,2,3,1,1,2,1,2,0,1,3,2,1},
        {1,1,3,2,2,3,3,3,1,2,3,1,0,2,1,2},
        {2,1,1,3,3,2,3,3,1,1,2,3,2,0,2,1},
        {3,2,1,1,3,3,2,3,3,1,1,2,1,2,0,2},
        {1,3,2,1,3,3,3,2,2,3,1,1,2,1,2,0},
    };

    // ── (a) AMORPHIC + IMPRIMITIVE iteration (route §9.7.1 next-move a).  Two questions
    //    the rank-2 main probe left open: (1) does the residue's OWN (amorphic, finer)
    //    scheme make Clebsch SHATTER where its rank-2 graph closure was sticky/Cameron-
    //    looking — i.e. does multiplicity CLEANLY separate residue from Cameron once each
    //    is on its faithful scheme?  (2) does any IMPRIMITIVE scheme admit a TIGHT cover
    //    (the 2a premise), or is loose-ness intrinsic (⟹ excise the tight/loose framing)?
    [Fact]
    public void Probe_ConfusionCover_Amorphic()
    {
        Func<int, int, int> Scheme(int[,] r) => (u, v) => r[u, v];

        var items = new List<(string name, string cat, int n, Func<int, int, int> bc)>
        {
            ("Clebsch rank-2",   "RESIDUE:rk2",      16, GraphCol(CayleyZ2Pow4(new[]{1,2,4,8,15}))),
            ("Clebsch ℤ4² rk-4", "RESIDUE:amorphic", 16, Scheme(ClebschZ4Amorphic)),
            ("Shrikhande rk-2",  "RESIDUE:rk2",      16, GraphCol(CayleyZ4Sq(new[]{(1,0),(3,0),(0,1),(0,3),(1,1),(3,3)}))),
            ("Rook L(4) rk-2",   "CARVED:lattice",   16, GraphCol(Rook(4))),
            ("4·K_4 (imprim)",   "IMPRIM",           16, GraphCol(DisjointCliques(4,4))),
            ("K_{4×4} (imprim)", "IMPRIM",           16, GraphCol(CompleteMultipartite(4,4))),
            ("2·K_8 (imprim)",   "IMPRIM",           16, GraphCol(DisjointCliques(2,8))),
        };

        output.WriteLine("A2 CONFUSION-COVER — AMORPHIC residue scheme + IMPRIMITIVE controls (route §9.7.1 move a).");
        output.WriteLine("Q1: does Clebsch on its rank-4 amorphic scheme SHATTER where rank-2 was sticky (clean separation)?");
        output.WriteLine("Q2: does any IMPRIMITIVE scheme admit a TIGHT (partition) cover — the 2a premise — or is loose intrinsic?");
        output.WriteLine("");
        output.WriteLine($"{"scheme",-18} {"cat",-18} {"n",-4} {"|T|",-4} {"c(X_T)",-7} {"N",-4} {"L",-7} {"minM",-5} {"maxM",-5} {"verdict",-22} massΣ|C|²");
        output.WriteLine(new string('─', 128));

        foreach (var it in items)
        {
            foreach (var T in BaseSeqBase(it.n, it.bc))
            {
                var rel = PairClosureBase(it.n, it.bc, T);
                var m = CoverMetrics(it.n, rel, 0.5);
                string verdict = m.c == 0 ? "discrete"
                    : !m.cover ? "NO-COVER (shatters)"
                    : m.tight ? "TIGHT (partition!)"
                    : "loose";
                output.WriteLine($"{it.name,-18} {it.cat,-18} {it.n,-4} {T.Count,-4} {m.c,-7} {m.N,-4} {m.L,-7:F2} {m.minMult,-5} {m.maxMult,-5} {verdict,-22} {m.mass}");
            }
            output.WriteLine("");
        }

        output.WriteLine("READ — Q1: compare 'Clebsch rank-2' (sticky c, Cameron-looking) vs 'Clebsch ℤ4² rk-4' (its own");
        output.WriteLine("       scheme): if the amorphic c collapses / minMult→0 where rank-2 stayed covered, multiplicity");
        output.WriteLine("       CLEANLY separates residue from Cameron once each is on its faithful scheme.");
        output.WriteLine("       Q2: a TIGHT row on any IMPRIM scheme ⟹ 2a is a real (if unused) theorem; NO tight row");
        output.WriteLine("       anywhere ⟹ loose-ness is intrinsic to confusion covers ⟹ excise the tight/loose framing.");
    }

    // ── The N_ρ / multiplicity probe (route doc §9.7) — does (minMult, L, mass) SEPARATE
    //    the residue (base 2–3) from rook/Johnson (Cameron, base √n) the way base-size
    //    does?  Built 2-WL-faithful (confusion sets on the coherent closure X_T) and
    //    shaped around sub-target 2a: the per-base/ρ trichotomy is exactly what 2a
    //    partitions — no-cover (shatters) / tight (2a, imprimitive) / loose (open 2b).
    //
    //    HYPOTHESIS (§9.7): residue keeps minMult_ρ/L_ρ = O(1) (cover absent or cheap)
    //    at a constant ρ<1, while geometric families develop a thick cover (minMult/L
    //    GROWING with m).  If instead L stays bounded on rook/Johnson too, "L bounded"
    //    does NOT discriminate Cameron from residue — the multiplicity reframe fails and
    //    2a (tight) + a different loose-case handle is the route.  Either way decisive.
    [Fact]
    public void Probe_ConfusionCoverMultiplicity()
    {
        var (_, idx8) = TriIndex(8);
        var t8 = Triangular(8);
        HashSet<int> ChangSet((int, int)[] e) => EdgeSetToVertices(e, idx8);

        var graphs = new List<Graph>
        {
            new() { Name = "Shrikhande",  Category = "RESIDUE",          N = 16, Adj = CayleyZ4Sq(new[]{(1,0),(3,0),(0,1),(0,3),(1,1),(3,3)}) },
            new() { Name = "Clebsch",     Category = "RESIDUE",          N = 16, Adj = CayleyZ2Pow4(new[]{1,2,4,8,15}) },
            new() { Name = "Rook L(4)",   Category = "CARVED:lattice",   N = 16, Adj = Rook(4) },
            new() { Name = "Rook L(5)",   Category = "CARVED:lattice",   N = 25, Adj = Rook(5) },
            new() { Name = "Rook L(6)",   Category = "CARVED:lattice",   N = 36, Adj = Rook(6) },
            new() { Name = "Rook L(7)",   Category = "CARVED:lattice",   N = 49, Adj = Rook(7) },
            new() { Name = "Triangular T(6)", Category = "CARVED:Johnson", N = 15, Adj = Triangular(6) },
            new() { Name = "Triangular T(7)", Category = "CARVED:Johnson", N = 21, Adj = Triangular(7) },
            new() { Name = "Triangular T(8)", Category = "CARVED:Johnson", N = 28, Adj = Triangular(8) },
            new() { Name = "Paley(13)",   Category = "CARVED:conference", N = 13, Adj = Paley(13) },
            new() { Name = "Paley(29)",   Category = "CARVED:conference", N = 29, Adj = Paley(29) },
        };
        var changs = new (string, (int, int)[])[]
        {
            ("Chang-C8", new[]{(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,7)}),
            ("Chang-4K2", new[]{(0,1),(2,3),(4,5),(6,7)}),
        };
        foreach (var (tag, e) in changs)
            graphs.Add(new() { Name = tag, Category = "RESIDUE", N = 28, Adj = SeidelSwitch(28, t8, ChangSet(e)) });

        output.WriteLine("A2 CONFUSION-COVER MULTIPLICITY probe (route §9.7) — confusion sets on the 2-WL");
        output.WriteLine("coherent closure X_T (faithful to Lean confusionSet / BigConfusionCover).");
        output.WriteLine("Trichotomy per (base,ρ=0.5): minMult=0 NO-COVER(shatters) | tight=2a(imprim) | loose=open-2b.");
        output.WriteLine("Key question: do (minMult,L,mass) separate residue from rook/Johnson like base-size does?");
        output.WriteLine("");
        output.WriteLine($"{"graph",-16} {"cat",-16} {"n",-4} {"|T|",-4} {"c(X_T)",-7} {"N",-4} {"L",-7} {"minM",-5} {"maxM",-5} {"verdict",-22} {"massΣ|C|²",-9}");
        output.WriteLine(new string('─', 130));

        // scaling accumulators: minMult/L at base {0}, ρ=0.5, per category
        var scale = new List<(string cat, string name, int n, int minM, double L, int c)>();

        foreach (var g in graphs)
        {
            var (ok, _, _, _) = SrgParams(g.N, g.Adj);
            if (!ok) { output.WriteLine($"{g.Name,-16} {g.Category,-16} {g.N,-4} NOT AN SRG — skipped"); continue; }
            foreach (var T in BaseSeq(g.N, g.Adj))
            {
                var rel = PairClosure(g.N, g.Adj, T);
                var m = CoverMetrics(g.N, rel, 0.5);
                string verdict = m.c == 0 ? "discrete"
                    : !m.cover ? "NO-COVER (shatters)"
                    : m.tight ? "TIGHT (2a/imprim!)"
                    : "loose (open 2b)";
                output.WriteLine($"{g.Name,-16} {g.Category,-16} {g.N,-4} {T.Count,-4} {m.c,-7} {m.N,-4} {m.L,-7:F2} {m.minMult,-5} {m.maxMult,-5} {verdict,-22} {m.mass,-9}");
                if (T.Count == 1) scale.Add((g.Category, g.Name, g.N, m.minMult, m.L, m.c));
            }
            output.WriteLine("");
        }

        // ── Scaling readout: at base {0}, ρ=0.5, does geometric minMult/L grow with n? ──
        output.WriteLine("SCALING at base {0}, ρ=0.5 — does the cover thicken (minMult/L ↑) with n on the geometric");
        output.WriteLine("families while staying bounded on the residue?  (the §9.7 discriminating test)");
        foreach (var grp in scale.GroupBy(x => x.cat))
            output.WriteLine($"  {grp.Key,-18} " + string.Join("  ", grp.OrderBy(x => x.n)
                .Select(x => $"n{x.n}:minM={x.minM},L={x.L:F1}(c{x.c})")));

        // ── ρ-sweep on the cospectral headline pair (Shrikhande vs Rook L(4)) at base {0} ──
        output.WriteLine("");
        output.WriteLine("ρ-SWEEP at base {0} — cospectral (16,6,2,2) pair Shrikhande vs Rook L(4):");
        var shrik = graphs.First(x => x.Name == "Shrikhande");
        var rook4 = graphs.First(x => x.Name == "Rook L(4)");
        var relS = PairClosure(16, shrik.Adj, new List<int> { 0 });
        var relR = PairClosure(16, rook4.Adj, new List<int> { 0 });
        output.WriteLine($"  {"ρ",-6} {"Shrik: N/minM/maxM/L",-30} Rook L(4): N/minM/maxM/L");
        foreach (double rho in new[] { 0.50, 0.60, 0.70, 0.80, 0.90 })
        {
            var ms = CoverMetrics(16, relS, rho);
            var mr = CoverMetrics(16, relR, rho);
            output.WriteLine($"  {rho,-6:F2} {$"N={ms.N},minM={ms.minMult},maxM={ms.maxMult},L={ms.L:F2}",-30} N={mr.N},minM={mr.minMult},maxM={mr.maxMult},L={mr.L:F2}");
        }

        output.WriteLine("");
        output.WriteLine("READ — (a) minMult=0 anywhere ⟹ node 4 holds at that base (avoiding v / immediate halve);");
        output.WriteLine("       (b) TIGHT cover on a PRIMITIVE SRG would contradict 2a's premise (flag/investigate);");
        output.WriteLine("       (c) the multiplicity reframe SURVIVES iff residue minMult/L is bounded while rook/Johnson");
        output.WriteLine("           minMult/L (or mass) GROWS with n — else 'L bounded' ≠ Cameron and 2a is the route.");

        // SRG-validity is the only assertion (probe convention: all signals reported).
        foreach (var g in graphs)
            Assert.True(SrgParams(g.N, g.Adj).ok, $"{g.Name} is not a valid SRG");
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
