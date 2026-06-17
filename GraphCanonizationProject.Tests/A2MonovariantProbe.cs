using System;
using System.Collections.Generic;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
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

    // ─────────────────────────────────────────────────────────────────────────────
    //  ROW-4 SPORADICS probe (route doc §9.9.4 approach 4 / §9.9.5 action 4) — the
    //  confusion-cover multiplicity (the Lean BigConfusionCover / minMult objects) on
    //  the most RIGID constructible non-geometric SRGs: the PAULUS graphs srg(25,12,5,6)
    //  and srg(26,10,3,4), loaded from the VERIFIED Hanaki–Miyamoto catalogue
    //  (data/hanaki/as25.gz, as26.gz — the same source CatalogueSchemeProbe validates).
    //
    //  WHY.  §9.7's multiplicity evidence used Shrikhande/Clebsch/Chang, which have a
    //  BIGGISH automorphism group (ℤ₄²⋊…, etc.).  The seal's open predicate hSmallAutThin
    //  ("small-Aut primitive residue ⟹ bounded minMult") is sharpest exactly where Aut is
    //  GENUINELY small/trivial — the Paulus graphs (many trivial-Aut) are that data, and
    //  the sharpest available FALSIFIER hunt: a small-Aut SRG whose 2-WL cover stays thick
    //  (minMult ≥ 1, c not collapsing) to base+O(1) would be a seal counterexample.
    //
    //  HONEST SCOPE (state plainly, do not overclaim).  These have smallest eigenvalue
    //  s = −3 ⟹ BOUNDED eigenvalue ⟹ Neumaier-exceptional = NODE 3, not node 4.  Genuine
    //  NODE 4 (unbounded s, non-geometric, small-Aut) has NO constructible witness (§5 F2 /
    //  §9.9.3 G-construct) — no probe can reach it.  This probe EXTENDS the node-3 evidence
    //  to genuinely-trivial Aut and stress-tests hSmallAutThin there; it does not close node 4.
    //
    //  MEASUREMENT.  Reuses this file's CoverMetrics on PairClosureBase of the scheme's own
    //  rank-3 relation matrix (= the 2-WL coherent closure = the canonization-relevant object;
    //  for an SRG the rank-3 scheme IS its 2-WL closure, and the orbital scheme is only finer,
    //  so this is the conservative/hardest view, §9.7 note).  Bases ∅ / {0} / {0,v*}.
    //  Self-contained catalogue loader (probe convention); validates SRG-ness + |Aut| at runtime.
    // ─────────────────────────────────────────────────────────────────────────────

    static string Row4_DataPath(int n)
    {
        string fn = $"as{n:D2}.gz";
        foreach (var root in new[]
        {
            Path.Combine(AppContext.BaseDirectory, "data", "hanaki"),
            Path.Combine(AppContext.BaseDirectory, "..", "..", "..", "data", "hanaki"),
            Path.Combine(Directory.GetCurrentDirectory(), "data", "hanaki"),
        })
        {
            var p = Path.GetFullPath(Path.Combine(root, fn));
            if (File.Exists(p)) return p;
        }
        return "";
    }

    // GAP parser (mirror of CatalogueSchemeProbe.ParseCatalogue): last n*n ints per
    // "# No. k" block = the row-major relation matrix.
    static List<int[,]> Row4_Parse(string gzPath, int n)
    {
        string raw;
        using (var fs = File.OpenRead(gzPath))
        using (var gz = new GZipStream(fs, CompressionMode.Decompress))
        using (var sr = new StreamReader(gz))
            raw = sr.ReadToEnd();
        var schemes = new List<int[,]>();
        foreach (var b in Regex.Split(raw, @"#\s*No\.\s*\d+"))
        {
            var clean = string.Join("\n", b.Split('\n').Where(l => !l.TrimStart().StartsWith("#")));
            var ints = Regex.Matches(clean, @"-?\d+").Select(m => int.Parse(m.Value)).ToList();
            if (ints.Count < n * n) continue;
            var vals = ints.Skip(ints.Count - n * n).ToArray();
            var M = new int[n, n];
            for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) M[i, j] = vals[i * n + j];
            schemes.Add(M);
        }
        return schemes;
    }

    // Build (rel, rank, symmetric, valency) from a raw matrix; diagonal forced to 0,
    // valencies validated constant (the correctness gate). Returns null if invalid.
    static (int[,] rel, int rank, bool sym, int[] val)? Row4_Build(int[,] M, int n)
    {
        int diag = M[0, 0];
        var labels = new SortedSet<int>();
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) labels.Add(M[i, j]);
        var remap = new Dictionary<int, int> { [diag] = 0 };
        int next = 1;
        foreach (var v in labels) if (v != diag) remap[v] = next++;
        int rank = remap.Count;
        var rel = new int[n, n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) rel[i, j] = remap[M[i, j]];
        for (int i = 0; i < n; i++)
        {
            if (rel[i, i] != 0) return null;
            for (int j = 0; j < n; j++) if (i != j && rel[i, j] == 0) return null;
        }
        var val = new int[rank];
        for (int j = 0; j < n; j++) val[rel[0, j]]++;
        for (int i = 1; i < n; i++)
        {
            var v = new int[rank];
            for (int j = 0; j < n; j++) v[rel[i, j]]++;
            for (int k = 0; k < rank; k++) if (v[k] != val[k]) return null;
        }
        bool sym = true;
        for (int i = 0; i < n && sym; i++) for (int j = 0; j < n; j++) if (rel[i, j] != rel[j, i]) { sym = false; break; }
        return (rel, rank, sym, val);
    }

    // Primitive ⟺ every non-diagonal relation graph is connected.
    static bool Row4_Primitive(int[,] rel, int rank, int n)
    {
        for (int k = 1; k < rank; k++)
        {
            var seen = new bool[n]; var st = new Stack<int>(); st.Push(0); seen[0] = true; int c = 1;
            while (st.Count > 0) { int x = st.Pop(); for (int y = 0; y < n; y++) if (!seen[y] && rel[x, y] == k) { seen[y] = true; c++; st.Push(y); } }
            if (c != n) return false;
        }
        return true;
    }

    // |Aut| of the coloured scheme by backtracking with relation-consistency pruning;
    // returns the exact order, or −1 if it exceeds `cap` (= "large" / Cameron-side).
    static long Row4_AutOrder(int[,] rel, int n, long cap)
    {
        var img = new int[n]; var used = new bool[n]; long count = 0; bool over = false;
        bool Extend(int k)
        {
            if (over) return false;
            if (k == n) { count++; if (count > cap) { over = true; return false; } return true; }
            for (int w = 0; w < n; w++)
            {
                if (used[w]) continue;
                bool ok = rel[k, k] == rel[w, w];
                for (int a = 0; a < k && ok; a++)
                    if (rel[k, a] != rel[w, img[a]] || rel[a, k] != rel[img[a], w]) ok = false;
                if (!ok) continue;
                img[k] = w; used[w] = true;
                Extend(k + 1);
                img[k] = -1; used[w] = false;
                if (over) return false;
            }
            return true;
        }
        Extend(0);
        return over ? -1 : count;
    }

    // Extract the sparser non-diagonal relation as a 0/1 graph (for SRG params / spectrum).
    static bool[,] Row4_GraphOf(int[,] rel, int rank, int[] val, int n)
    {
        int e = 1; for (int k = 2; k < rank; k++) if (val[k] < val[e]) e = k;
        var a = Empty(n);
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (rel[u, v] == e) Edge(a, u, v);
        return a;
    }

    // The cover trajectory along the base sequence ∅ ⊆ {0} ⊆ {0,v*}, measured on the
    // scheme's own rank-3 relation matrix (the 2-WL closure).  Returns the per-base
    // (c, minMult, cover-verdict) and the final-base shatter flag.
    static (string traj, bool shattersFinal, int cFinal, int minMultFinal) Row4_CoverTrajectory(int n, int[,] rel)
    {
        Func<int, int, int> bc = (u, v) => rel[u, v];
        var sb = new StringBuilder();
        bool shatters = false; int cF = 0, mF = 0; bool first = true;
        foreach (var T in BaseSeqBase(n, bc))
        {
            var cl = PairClosureBase(n, bc, T);
            var m = CoverMetrics(n, cl, 0.5);
            string verdict = m.c == 0 ? "discrete" : !m.cover ? "shatter" : m.tight ? "tight" : "loose";
            if (!first) sb.Append("  →  ");
            sb.Append($"|T|{T.Count}: c={m.c} minM={m.minMult} maxM={m.maxMult} L={m.L:F1} [{verdict}]");
            first = false;
            shatters = m.c == 0 || !m.cover; cF = m.c; mF = m.minMult;
        }
        return (sb.ToString(), shatters, cF, mF);
    }

    [Fact]
    public void Probe_Row4Sporadics()
    {
        output.WriteLine("A2 ROW-4 SPORADICS — confusion-cover multiplicity on the most RIGID constructible");
        output.WriteLine("non-geometric SRGs (Paulus srg(25,12,5,6), srg(26,10,3,4)) from the verified Hanaki catalogue.");
        output.WriteLine("Tests hSmallAutThin (small-Aut ⟹ bounded minMult / shatters) where Aut is GENUINELY small.");
        output.WriteLine("HONEST SCOPE: these are s=−3 (bounded eigenvalue) = NODE 3, not node 4. Node 4 (unbounded s,");
        output.WriteLine("non-geometric, small-Aut) has NO constructible witness — no probe reaches it (§5 F2 / §9.9.3).");
        output.WriteLine("Measurement = Lean BigConfusionCover/minMult on the 2-WL closure (PairClosure of the scheme).");
        output.WriteLine("");

        const long autCap = 5000;                          // |Aut| > cap ⟹ "large" (geometric/Cameron-side)
        var orders = new[] { 25, 26, 28, 29 };

        // ── Carved geometric contrast at n=25 (large-Aut, the thick-cover reference) ──
        var contrasts = new (string name, bool[,] adj)[]
        {
            ("Rook L(5) [geom]", Rook(5)),
        };

        output.WriteLine($"{"graph",-22} {"src",-10} {"n",-4} {"(k,λ,μ)",-13} {"s",-4} {"2rk",-4} {"|Aut|",-9} {"base",-5} cover trajectory  ∅ → {{0}} → {{0,v*}}");
        output.WriteLine(new string('─', 150));

        var smallAut = new List<(string name, int n, int s, long aut, bool shatters, int cF, int mF)>();
        var largeAut = new List<(string name, int n, int s, int mF, int baseSize)>();
        int targetCount = 0;        // small-Aut non-geometric SRGs found (probe non-vacuity)
        int falsifiers = 0;         // small-Aut SRG whose cover stays thick to base {0,v*}

        // Algebraic carved contrasts first.
        foreach (var (name, adj) in contrasts)
        {
            int nn = (int)Math.Round(Math.Sqrt(adj.Length));
            var (ok, k, lam, mu) = SrgParams(nn, adj);
            if (!ok) { output.WriteLine($"{name,-22} {"algebraic",-10} {nn,-4} not-an-SRG"); continue; }
            int s = SmallestEig(nn, k, lam, mu); int r2 = PRank(nn, adj, 2);
            long aut = Row4_AutOrder(BuildRel(nn, adj), nn, autCap);
            int baseSize = GreedyBaseCurve(nn, adj).Count - 1;
            var (traj, _, cF, mF) = Row4_CoverTrajectory(nn, BuildRel(nn, adj));
            string autStr = aut < 0 ? $">{autCap}" : aut.ToString();
            output.WriteLine($"{name,-22} {"algebraic",-10} {nn,-4} {$"({k},{lam},{mu})",-13} {s,-4} {r2,-4} {autStr,-9} {baseSize,-5} {traj}");
            largeAut.Add((name, nn, s, mF, baseSize));
        }
        output.WriteLine("");

        // ── Catalogue SRGs (rank-3 symmetric primitive) at the target orders ──
        foreach (int n in orders)
        {
            var path = Row4_DataPath(n);
            if (path == "") { output.WriteLine($"order {n}: data file missing — skip"); continue; }
            var raw = Row4_Parse(path, n);
            int srgCount = 0;
            foreach (var (idx, M) in raw.Select((m, i) => (i, m)))
            {
                var built = Row4_Build(M, n);
                if (built is null) continue;
                var (rel, rank, sym, val) = built.Value;
                if (rank != 3 || !sym) continue;                       // SRG = rank-3 symmetric
                if (!Row4_Primitive(rel, rank, n)) continue;
                srgCount++;

                var adj = Row4_GraphOf(rel, rank, val, n);
                var (ok, k, lam, mu) = SrgParams(n, adj);
                if (!ok) continue;
                int s = SmallestEig(n, k, lam, mu); int r2 = PRank(n, adj, 2);
                long aut = Row4_AutOrder(rel, n, autCap);
                int baseSize = GreedyBaseCurve(n, adj).Count - 1;
                var (traj, _, cF, mF) = Row4_CoverTrajectory(n, rel);
                // "shatters" = a SMALL base (≪ √n); geometric/large-Aut needs base ≈ √n.
                bool sh = baseSize < (int)Math.Ceiling(Math.Sqrt(n));
                string autStr = aut < 0 ? $">{autCap}" : aut.ToString();
                bool large = aut < 0 || aut >= (long)n * n * n;         // |Aut| ≥ n³ ⟹ geometric/Cameron-side
                string name = $"#{idx + 1}";
                output.WriteLine($"{$"as{n} {name}",-22} {"catalogue",-10} {n,-4} {$"({k},{lam},{mu})",-13} {s,-4} {r2,-4} {autStr,-9} {baseSize,-5} {traj}");
                if (large) largeAut.Add(($"as{n} {name}", n, s, mF, baseSize));
                else
                {
                    targetCount++;
                    smallAut.Add(($"as{n} {name}", n, s, aut, sh, cF, mF));
                    if (!sh) falsifiers++;                              // small-Aut + non-shattering cover at base {0,v*}
                }
            }
            output.WriteLine($"  ── order {n}: {srgCount} rank-3 primitive SRG scheme(s) in catalogue ──");
            output.WriteLine("");
        }

        // ── Readouts ───────────────────────────────────────────────────────────────
        output.WriteLine("SMALL-Aut (Paulus-type, the genuine residue) SRGs — do they shatter (minMult→0 / c collapse)?");
        foreach (var x in smallAut.OrderBy(x => x.n).ThenBy(x => x.aut))
            output.WriteLine($"  {x.name,-12} n={x.n} s={x.s} |Aut|={x.aut,-5} ⟹ final base {{0,v*}}: c={x.cF} minMult={x.mF}  {(x.shatters ? "SHATTERS ✓" : "‼ THICK COVER (falsifier?)")}");
        output.WriteLine("");
        output.WriteLine("LARGE-Aut / geometric SRGs (the thick-cover Cameron reference):");
        foreach (var x in largeAut.OrderBy(x => x.n))
            output.WriteLine($"  {x.name,-12} n={x.n} s={x.s} base={x.baseSize} final minMult={x.mF} ⟹ {(x.mF >= 1 ? "THICK COVER (base ≈ √n, expected on geometric)" : "shatters")}");
        output.WriteLine("");

        int shatterCount = smallAut.Count(x => x.shatters);
        output.WriteLine($"VERDICT — small-Aut non-geometric SRGs found: {targetCount};  of those SHATTER (1-WL base < √n): {shatterCount};  falsifiers (base ≥ √n): {falsifiers}.");
        output.WriteLine(falsifiers == 0 && targetCount > 0
            ? "  ⇒ Every genuinely-small-Aut non-geometric SRG SHATTERS at base ≪ √n — hSmallAutThin holds on the most rigid"
            + " constructible data (no falsifier). Extends the §9.7 evidence from biggish-Aut to trivial-Aut residue."
            : targetCount == 0
                ? "  ⇒ No small-Aut non-geometric rank-3 SRG isolated at these orders — re-check catalogue/Aut classification."
                : "  ‼ A small-Aut SRG needs base ≥ √n (geometric-like) — a hSmallAutThin falsifier candidate; INVESTIGATE.");
        output.WriteLine("");
        output.WriteLine("CAVEAT (the honest scope): the data spans BOUNDED smallest eigenvalue only — n=25/26 are s=−3 (Paulus,");
        output.WriteLine("NODE 3 / Neumaier-exceptional), n=28 s=−2 (Chang, exceptional non-line-graph), n=29 s=0 (conference,");
        output.WriteLine("leg B). Node 4 = UNBOUNDED s, non-geometric, small-Aut remains construction-bottlenecked (CGGP is the");
        output.WriteLine("only known inhabitant, not codeable at scale) — no probe reaches it. This extends the node-3 evidence");
        output.WriteLine("to genuinely-trivial Aut (|Aut|=1) and finds NO falsifier; it does not close node 4.");

        // Assertions: probe non-vacuity (target SRGs found) + the falsifier headline.
        Assert.True(targetCount > 0, "no small-Aut non-geometric rank-3 SRG found at orders 25/26/28/29 — classification or data issue");
        Assert.Equal(0, falsifiers);   // no small-Aut SRG retains a thick cover to base+O(1) (seal stands on this data)
    }

    // ── D2 STABLE-COVER REGULARITY PROBE (route §9.9.2 / §9.9.4 — the one genuinely-novel
    //    node-4 lead, probe-tested before any Lean commitment) ─────────────────────────
    //
    //  THE BET (§9.9.2).  D2 must extract a partial geometry from a PERSISTENT big-confusion
    //  cover.  §9.7.1 found arbitrary covers INTRINSICALLY LOOSE (maxMult ≫ 1) and killed the
    //  tight/loose (2a) framing.  But REGULAR ≠ TIGHT: the rook grid's confusion cover is loose
    //  (every cell on 2 grid-lines, maxMult=2) yet a perfectly REGULAR partial geometry
    //  (constant point-degree, constant line-size, two lines meet in ≤ 1 point).  The bet: the
    //  STABLE (persistent-across-bases) cover is a REGULAR partial geometry on the geometric
    //  (Cameron) / imprimitive families, but IRREGULAR or EMPTY on the primitive non-Cameron
    //  residue — so "stable ⟹ regular line system ⟹ partial geometry ⟹ Cameron-or-block" is the
    //  D2/D3 mechanism, and the residue (no regular stable cover) is exactly why it shatters.
    //
    //  THE TRAP (why §9.7.1's minMult/maxMult did not already settle it).  At base ∅ a vertex-
    //  transitive scheme has CONSTANT point-degree by D1 (confusionMultiplicity_perm) — regular
    //  for free, vacuous.  The genuine discriminators: (a) at base ∅ — LINE-SIZE spread + the
    //  PAIRWISE-MEET (partial-geometry incidence) axiom, neither forced by transitivity; (b) at a
    //  NONTRIVIAL base {0},{0,v*} (transitivity broken) — POINT-DEGREE spread over non-base
    //  vertices.  The bet: the geometric cover stays regular as the base deepens while the
    //  residue's vanishes (shatters) or fragments (irregular).
    //
    //  MEASUREMENT on the FAITHFUL scheme (§9.7.2): residue on its amorphic/rank-3 scheme, rook/
    //  triangular on their rank-2 graph (they ARE rank-2 schemes that 2-WL-close to rank 3).
    //  Reuses PairClosureBase / BaseSeqBase / the Hanaki catalogue loader.  ρ = 0.5.

    // Richer confusion-cover metrics for the regularity test: distinct big sets, point-degree
    // spread (over NON-base vertices, to drop the individualized-base-point artifact), line-size
    // spread, and the pairwise-MEET (partial-geometry incidence) distribution.  min/maxMult stay
    // over ALL v (Lean BigConfusionCover-faithful; drives the cover/shatter verdict).
    readonly record struct RegM(
        int c, int N, int minMult, int maxMult, int degDistinct,
        int szMin, int szMax, int meetMax, int meetDistinct, bool meetOk);

    static RegM Regularity(int n, int[,] rel, double rho, HashSet<int> baseT)
    {
        int c = 0;
        var sizes = new int[n, n];
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++)
        {
            int sz = 0; for (int g = 0; g < n; g++) if (rel[g, a] == rel[g, b]) sz++;
            sizes[a, b] = sz; if (sz > c) c = sz;
        }
        if (c == 0) return new RegM(0, 0, 0, 0, 0, 0, 0, 0, 0, false);
        double thr = rho * c;
        var distinct = new Dictionary<string, bool[]>();
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++)
        {
            if (sizes[a, b] <= thr) continue;
            var mem = new bool[n]; var key = new StringBuilder();
            for (int g = 0; g < n; g++) if (rel[g, a] == rel[g, b]) { mem[g] = true; key.Append(g).Append(','); }
            distinct[key.ToString()] = mem;
        }
        var big = distinct.Values.ToList();
        int N = big.Count;
        if (N == 0) return new RegM(c, 0, 0, 0, 0, 0, 0, 0, 0, false);
        // point multiplicities: min/max over ALL v (cover test); distinct degrees over NON-base v.
        var mult = new int[n];
        foreach (var mem in big) for (int g = 0; g < n; g++) if (mem[g]) mult[g]++;
        int minMult = int.MaxValue, maxMult = 0;
        var degVals = new HashSet<int>();
        for (int g = 0; g < n; g++)
        {
            minMult = Math.Min(minMult, mult[g]); maxMult = Math.Max(maxMult, mult[g]);
            if (!baseT.Contains(g)) degVals.Add(mult[g]);
        }
        // line-size spread
        int szMin = int.MaxValue, szMax = 0;
        for (int i = 0; i < N; i++) { int s = big[i].Count(x => x); szMin = Math.Min(szMin, s); szMax = Math.Max(szMax, s); }
        // pairwise meets — the partial-geometry incidence axiom: all NONZERO meets equal ⟹ a
        // regular incidence (≤ 1 ⟹ a near-pencil / generalized quadrangle).  Capped for cost.
        int meetMax = 0; var meetVals = new HashSet<int>(); bool meetOk = N <= 300;
        if (meetOk)
            for (int i = 0; i < N; i++) for (int j = i + 1; j < N; j++)
            {
                int m = 0; var bi = big[i]; var bj = big[j];
                for (int g = 0; g < n; g++) if (bi[g] && bj[g]) m++;
                if (m > meetMax) meetMax = m;
                if (m > 0) meetVals.Add(m);
            }
        return new RegM(c, N, minMult, maxMult, degVals.Count, szMin, szMax, meetMax, meetVals.Count, meetOk);
    }

    static string RegVerdict(RegM m)
    {
        if (m.c == 0) return "discrete";
        if (m.N == 0 || m.minMult == 0) return "shatter";   // no big set / an avoiding v exists ⟹ ¬cover
        bool degReg = m.degDistinct <= 1;                   // constant point-degree (over non-base v)
        bool szReg = m.szMin == m.szMax;                    // constant line-size
        if (degReg && szReg) return m.meetOk && m.meetDistinct <= 1 ? "REG-PG" : "regular";
        if (degReg) return "reg-deg";
        return "IRREG";
    }

    static string RegRow(RegM m)
    {
        if (m.c == 0) return "discrete";
        if (m.N == 0) return $"c={m.c} no-big-set [shatter]";
        string meet = m.meetOk ? $"meet≤{m.meetMax}(#{m.meetDistinct})" : "meet=—";
        return $"c={m.c} N={m.N} deg[{m.minMult}..{m.maxMult}] sz[{m.szMin}..{m.szMax}] {meet} [{RegVerdict(m)}]";
    }

    // The regularity trajectory across ∅ ⊆ {0} ⊆ {0,v*} on a faithful pair-colour function.
    // coverPersists = a big cover survives to the deepest base (final ∉ {shatter,discrete});
    // finalRegular  = that surviving cover is REGULAR there (the D2 "stable ⟹ regular" predicate).
    static (string traj, string fin, bool coverPersists, bool finalRegular) Reg_Trajectory(int n, Func<int, int, int> bc)
    {
        var sb = new StringBuilder(); bool first = true; string fin = "";
        foreach (var T in BaseSeqBase(n, bc))
        {
            var rel = PairClosureBase(n, bc, T);
            var m = Regularity(n, rel, 0.5, new HashSet<int>(T));
            if (!first) sb.Append("  →  ");
            sb.Append($"|T|{T.Count}: {RegRow(m)}");
            first = false; fin = RegVerdict(m);
        }
        return (sb.ToString(), fin, fin is not ("shatter" or "discrete"), fin is "REG-PG" or "regular");
    }

    [Fact]
    public void Probe_StableCoverRegularity()
    {
        output.WriteLine("D2 STABLE-COVER REGULARITY (route §9.9.2/§9.9.4) — is a PERSISTENT big-confusion cover a REGULAR");
        output.WriteLine("partial geometry on the geometric/Cameron + imprimitive families, but IRREGULAR or EMPTY on the");
        output.WriteLine("primitive non-Cameron residue?  (REGULAR ≠ TIGHT: the rook grid cover is loose maxMult=2 yet a");
        output.WriteLine("regular partial geometry.)  Discriminators: line-SIZE + pairwise-MEET (PG incidence) at base ∅");
        output.WriteLine("[point-degree vacuously regular there by D1/transitivity]; point-DEGREE spread (non-base v) at {0},{0,v*}.");
        output.WriteLine("Faithful scheme (§9.7.2); ρ=0.5.  Verdicts: REG-PG=const deg+size+single line-meet · regular=const deg+size ·");
        output.WriteLine("reg-deg=const deg only · IRREG=degree spreads · shatter=no/avoidable cover · discrete.");
        output.WriteLine("");
        output.WriteLine($"{"scheme",-22} {"cat",-12} {"n",-4} regularity trajectory  ∅ → {{0}} → {{0,v*}}");
        output.WriteLine(new string('─', 150));

        // Per-scheme classification, accumulated for the two-sided verdict.
        // carved = geometric ∪ imprimitive (the Cameron / hImprim legs that SHOULD persist);
        // residue = primitive small-Aut non-Cameron (SHOULD shatter).
        var carved = new List<(string fin, bool persists, bool reg)>();
        var residue = new List<(string fin, bool persists, bool reg)>();
        bool rookHasCover = false;

        void Row(string name, string cat, int n, Func<int, int, int> bc)
        {
            var (traj, fin, persists, reg) = Reg_Trajectory(n, bc);
            string pad = name.Length > 0 ? $"{name,-22} {cat,-12} {n,-4} " : "";
            output.WriteLine($"{pad}{traj}");
            if (cat is "geometric" or "imprimitive" or "geom/large") carved.Add((fin, persists, reg));
            else residue.Add((fin, persists, reg));
        }

        // ── (1) Carved GEOMETRIC references (rank-2 schemes; the candidate regular partial geometries) ──
        foreach (var (name, adj) in new (string, bool[,])[]
        {
            ("Rook L(4)", Rook(4)), ("Rook L(5)", Rook(5)),
            ("Triangular T(6)", Triangular(6)), ("Triangular T(8)", Triangular(8)),
        })
        {
            int nn = (int)Math.Round(Math.Sqrt(adj.Length));
            Row(name, "geometric", nn, GraphCol(adj));
            if (name == "Rook L(4)")
                rookHasCover = Regularity(nn, PairClosure(nn, adj, new List<int>()), 0.5, new HashSet<int>()).minMult >= 1;
        }
        output.WriteLine("");

        // ── (2) n=16 RESIDUE on its FAITHFUL (amorphic) scheme — the cospectral contrast ──
        Row("Clebsch (amorphic)", "residue", 16, (u, v) => ClebschZ4Amorphic[u, v]);
        var shrik = CayleyZ4Sq(new[] { (1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3) });   // Shrikhande SRG(16,6,2,2)
        Row("Shrikhande", "residue", 16, GraphCol(shrik));
        output.WriteLine("");

        // ── (3) IMPRIMITIVE controls (the hImprim leg — a thick cover is EXPECTED to persist here) ──
        Row("4·K4", "imprimitive", 16, GraphCol(DisjointCliques(4, 4)));
        Row("K_{4x4}", "imprimitive", 16, GraphCol(CompleteMultipartite(4, 4)));
        output.WriteLine("");

        // ── (4) Genuinely-small-Aut catalogue RESIDUE (Paulus/Chang) on their rank-3 scheme ──
        output.WriteLine("Catalogue small-Aut residue (Paulus/Chang/conference) vs a large-Aut geometric reference, rank-3 scheme:");
        const long autCap = 5000;
        foreach (int n in new[] { 25, 26, 28, 29 })
        {
            var path = Row4_DataPath(n);
            if (path == "") { output.WriteLine($"  order {n}: data missing — skip"); continue; }
            int smallShown = 0, largeShown = 0;
            foreach (var (idx, M) in Row4_Parse(path, n).Select((m, i) => (i, m)))
            {
                if (smallShown >= 2 && largeShown >= 1) break;
                var built = Row4_Build(M, n);
                if (built is null) continue;
                var (rel, rank, sym, val) = built.Value;
                if (rank != 3 || !sym || !Row4_Primitive(rel, rank, n)) continue;
                long aut = Row4_AutOrder(rel, n, autCap);
                bool large = aut < 0 || aut >= (long)n * n * n;
                if (large ? largeShown >= 1 : smallShown >= 2) continue;
                var adj = Row4_GraphOf(rel, rank, val, n);
                var (ok, k, lam, mu) = SrgParams(n, adj); if (!ok) continue;
                int s = SmallestEig(n, k, lam, mu);
                string tag = large ? "geom/large" : "residue";
                string autStr = aut < 0 ? $">{autCap}" : aut.ToString();
                output.WriteLine($"  {$"as{n} #{idx + 1}",-16} {tag,-11} {$"|Aut|={autStr}",-13} s={s,-3} (below)");
                Row("", tag, n, (u, v) => rel[u, v]);
                if (large) largeShown++; else smallShown++;
            }
        }
        output.WriteLine("");

        // ── TWO-SIDED VERDICT (the bet needs BOTH halves) ──
        int carvedPersist = carved.Count(x => x.persists), carvedPersistReg = carved.Count(x => x.persists && x.reg);
        int residuePersistReg = residue.Count(x => x.persists && x.reg);
        int residueShatter = residue.Count(x => !x.persists);
        output.WriteLine("THE BET (§9.9.2): a PERSISTENT (stable) cover is a REGULAR partial geometry — so 'persistent ⟹ regular ⟹");
        output.WriteLine("Cameron/block' would route a stable cover to a carved leg, and the residue (no stable cover) shatters.");
        output.WriteLine("It needs BOTH: (A) carved covers PERSIST and are REGULAR there;  (B) residue covers do NOT persist-regular.");
        output.WriteLine($"  (A) carved (geom+imprim): {carvedPersist}/{carved.Count} persist;  of those REGULAR at the deepest base: {carvedPersistReg}.");
        output.WriteLine($"  (B) residue (prim small-Aut): {residueShatter}/{residue.Count} shatter;  persist-AND-regular: {residuePersistReg}.");
        output.WriteLine("");
        if (residuePersistReg == 0 && carvedPersistReg >= carvedPersist && carvedPersist > 0)
            output.WriteLine("  ⇒ BET SUPPORTED: carved covers persist regularly; no residue does.");
        else if (residuePersistReg == 0 && carvedPersist > 0)
            output.WriteLine("  ⇒ BET REFUTED as a PROOF ROUTE (half A fails): residue covers shatter (B ✓), but the PERSISTENT carved");
        else
            output.WriteLine("  ‼ BET STRESSED on the residue side (B): a residue carries a persistent regular cover — inspect.");
        if (residuePersistReg == 0 && carvedPersistReg < carvedPersist)
        {
            output.WriteLine("    covers go IRREGULAR under individualization (point-degree spreads) — NOT regular partial geometries in");
            output.WriteLine("    the confusion-cover incidence sense. So 'stable ⟹ regular' is FALSE; D2 cannot extract a partial");
            output.WriteLine("    geometry from a stable cover.  The robust separator is PERSISTENCE itself (thick vs shatter = bounded");
            output.WriteLine("    minMult), which is exactly `hSmallAutThin` — the existing wall.  The regularity refinement gives NO new");
            output.WriteLine("    handle; the D2 regular-PG extraction is unfounded — do NOT invest Lean effort there.");
        }
        output.WriteLine("");
        output.WriteLine("HONEST SCOPE: same construction bottleneck as §9.9.8 — all residue data is bounded s (node 3 / leg B);");
        output.WriteLine("node 4 (unbounded s) has no constructible witness.  This probes the D2 'stable⟹regular' bet on the");
        output.WriteLine("reachable residue before any Lean investment in the extraction; it does NOT close node 4.");

        Assert.True(rookHasCover, "rook reference has no base-∅ cover — metric/fixture issue");
        Assert.True(residue.Count > 0, "no small-Aut residue scheme measured — catalogue/Aut classification issue");
    }

    // The {diag=2, edge=1, non-edge=0} rank-2 relation matrix of a graph (for Row4 cover
    // measurement when the source is an algebraic adjacency rather than a catalogue scheme).
    static int[,] BuildRel(int n, bool[,] adj)
    {
        var rel = new int[n, n];
        for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) rel[u, v] = u == v ? 0 : adj[u, v] ? 1 : 2;
        return rel;
    }
}
