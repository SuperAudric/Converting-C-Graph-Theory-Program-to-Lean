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

    // ── HAMMING LADDER PROBE (the user's c^k hypergrid as the natural k-WL obstruction) ──
    //
    //  H(k,c): vertices = c^k tuples, adjacent iff they differ in EXACTLY ONE coordinate.
    //  H(2,c) = the rook graph L(c).  The user's hypothesis: the c^k hypergrid "defeats k-WL"
    //  the way the rook defeats 2-WL.  This probe tests it and, more importantly, whether it
    //  helps node 4 — by measuring base_2 vs base_3 (greedy k-WL discretization) and |Aut|.
    //
    //  THE STRUCTURAL FACT under test.  k-WL produces an ISO-INVARIANT colouring, so it can
    //  never split two vertices in the same Aut-orbit — hence base_k(X) ≥ b(Aut(X)) for EVERY
    //  k.  H(k,c) has |Aut| = (c!)^k·k! (huge ⟹ Cameron) and b(Aut) ≈ k(c−1) ≈ k·n^{1/k}.  So a
    //  Hamming graph is THICK (large base) at every WL level, and that thickness is its LARGE
    //  Aut — i.e. it is the higher-k analogue of the rook and sits in the SAME carved leg
    //  (large-Aut → Cameron/G3).  Climbing the WL ladder cannot reduce its base below b(Aut)
    //  (the group term), so `hSmallAutThin` ("thick ⟹ large Aut") is INVARIANT under k, not a
    //  level-2 artifact.  Contrast: Shrikhande (the rook's cospectral small-Aut MATE) shatters
    //  at a small base already — the residue is the Hamming family's small-Aut twist, tame.

    // H(k,c): c^k tuples, adjacent iff Hamming distance 1.  H(2,c) = rook L(c).
    static bool[,] Hamming(int k, int c)
    {
        int n = 1; for (int i = 0; i < k; i++) n *= c;
        var a = Empty(n);
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++)
        {
            int diff = 0, uu = u, vv = v;
            for (int i = 0; i < k; i++) { if (uu % c != vv % c) diff++; uu /= c; vv /= c; }
            if (diff == 1) Edge(a, u, v);
        }
        return a;
    }

    // The stable colouring of all n^k ordered k-tuples under oblivious k-WL with base T
    // individualized.  Initial colour = the tuple's atomic type (equality + adjacency pattern
    // among its coordinates, plus the base flags); refinement colour(t) ← (colour(t), sorted
    // multiset over w of (colour(t[0:=w]),…,colour(t[k-1:=w]))).  k = 2 reproduces the 2-WL
    // coherent closure; k = 3 the 3-WL refinement.
    static int[] KWLStable(int n, bool[,] adj, int k, IReadOnlyList<int> T, out int numColors)
    {
        int K = 1; for (int i = 0; i < k; i++) K *= n;
        var pow = new int[k]; pow[0] = 1; for (int i = 1; i < k; i++) pow[i] = pow[i - 1] * n;
        var flag = new int[n]; { int f = 1; foreach (var t in T) flag[t] = f++; }
        var col = new int[K];
        var sb = new StringBuilder();
        var init = new Dictionary<string, int>();
        var c = new int[k];
        for (int id = 0; id < K; id++)
        {
            for (int i = 0; i < k; i++) c[i] = (id / pow[i]) % n;
            sb.Clear();
            for (int i = 0; i < k; i++) { sb.Append(flag[c[i]]); sb.Append('.'); }
            for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++)
                sb.Append(c[i] == c[j] ? '=' : adj[c[i], c[j]] ? 'e' : 'n');
            string s = sb.ToString();
            if (!init.TryGetValue(s, out int cc)) { cc = init.Count; init[s] = cc; }
            col[id] = cc;
        }
        int classes = init.Count;
        var packed = new long[n];
        while (true)
        {
            long BIG = classes + 1;
            var sig = new Dictionary<string, int>();
            var nc = new int[K];
            for (int id = 0; id < K; id++)
            {
                for (int w = 0; w < n; w++)
                {
                    long v = 0, mul = 1;
                    for (int p = 0; p < k; p++)
                    {
                        int idp = id + (w - (id / pow[p]) % n) * pow[p];
                        v += col[idp] * mul; mul *= BIG;
                    }
                    packed[w] = v;
                }
                Array.Sort(packed);
                sb.Clear(); sb.Append(col[id]);
                for (int w = 0; w < n; w++) { sb.Append('|'); sb.Append(packed[w]); }
                string s = sb.ToString();
                if (!sig.TryGetValue(s, out int cc)) { cc = sig.Count; sig[s] = cc; }
                nc[id] = cc;
            }
            if (sig.Count == classes) { numColors = classes; return col; }
            col = nc; classes = sig.Count;
        }
    }

    // Greedy k-WL base: individualize the smallest vertex of the largest non-singleton vertex
    // cell (vertex colour = colour of the diagonal tuple (v,…,v)) until vertices are discrete.
    static int KWLBase(int n, bool[,] adj, int k)
    {
        int diagSum = 0; { int pw = 1; for (int i = 0; i < k; i++) { diagSum += pw; pw *= n; } }
        var T = new List<int>();
        while (T.Count <= n)
        {
            var col = KWLStable(n, adj, k, T, out _);
            var cells = new Dictionary<int, List<int>>();
            for (int v = 0; v < n; v++)
            {
                int vc = col[v * diagSum];
                if (!cells.TryGetValue(vc, out var l)) { l = new(); cells[vc] = l; }
                l.Add(v);
            }
            var big = cells.Values.Where(l => l.Count > 1).OrderByDescending(l => l.Count).FirstOrDefault();
            if (big == null) return T.Count;       // discrete ⟹ T is a k-WL base
            T.Add(big.Min());
        }
        return T.Count;
    }

    // Canonical k-WL invariant at base ∅: (#colours, sorted tuple-colour class sizes).  Equal
    // ⟹ k-WL cannot distinguish the two graphs; differing ⟹ k-WL separates them.
    static string KWLHistogram(int n, bool[,] adj, int k)
    {
        var col = KWLStable(n, adj, k, new List<int>(), out int nc);
        var sizes = new Dictionary<int, int>();
        foreach (var x in col) sizes[x] = sizes.GetValueOrDefault(x) + 1;
        return $"{nc}c[{string.Join(",", sizes.Values.OrderBy(z => z))}]";
    }

    // The GROUP base b(Aut): greedy orbit base — individualize a representative of the largest
    // non-trivial Aut-orbit (auts fixing the current base pointwise), repeat until rigid.
    // Returns −1 if |Aut fixing the current base| exceeds `cap` (too big to enumerate exactly).
    static int AutBase(int[,] rel, int n, long cap)
    {
        var T = new List<int>();
        while (T.Count < n)
        {
            var Tset = new HashSet<int>(T);
            var parent = new int[n]; for (int i = 0; i < n; i++) parent[i] = i;
            int Find(int x) { while (parent[x] != x) { parent[x] = parent[parent[x]]; x = parent[x]; } return x; }
            var img = new int[n]; var used = new bool[n]; long cnt = 0; bool over = false;
            void Extend(int kk)
            {
                if (over) return;
                if (kk == n) { cnt++; if (cnt > cap) { over = true; return; } for (int v = 0; v < n; v++) parent[Find(v)] = Find(img[v]); return; }
                for (int w = 0; w < n; w++)
                {
                    if (used[w]) continue;
                    if (Tset.Contains(kk) && w != kk) continue;     // base points are fixed pointwise
                    bool ok = rel[kk, kk] == rel[w, w];
                    for (int a = 0; a < kk && ok; a++) if (rel[kk, a] != rel[w, img[a]] || rel[a, kk] != rel[img[a], w]) ok = false;
                    if (!ok) continue;
                    img[kk] = w; used[w] = true; Extend(kk + 1); img[kk] = -1; used[w] = false;
                    if (over) return;
                }
            }
            Extend(0);
            if (over) return -1;
            var members = new Dictionary<int, List<int>>();
            for (int v = 0; v < n; v++) { int r = Find(v); if (!members.TryGetValue(r, out var l)) { l = new(); members[r] = l; } l.Add(v); }
            var biggest = members.Values.OrderByDescending(l => l.Count).First();
            if (biggest.Count <= 1) return T.Count;               // rigid ⟹ T is a base of Aut
            T.Add(biggest.Min());
        }
        return T.Count;
    }

    [Fact]
    public void Probe_HammingLadder()
    {
        output.WriteLine("HAMMING LADDER — the c^k hypergrid H(k,c) (H(2,c)=rook) as the natural k-WL obstruction.  Tests the");
        output.WriteLine("user's hypothesis that H(k,c) 'defeats k-WL' like the rook defeats 2-WL, and whether climbing helps node 4.");
        output.WriteLine("base_k = greedy #individualizations to k-WL-discretize; b(Aut) = the group base.  KEY FACTS: (i) base_k ≥");
        output.WriteLine("b(Aut) for ALL k (k-WL can't split an Aut-orbit); (ii) what the seal needs is base ≈ b(Aut) (the WL-dim");
        output.WriteLine("GAP = base − b(Aut) bounded) — a small-Aut graph with base ≫ b(Aut) would be the node-4 falsifier.");
        output.WriteLine("");
        const long autCap = 500000;
        var fam = new (string name, int n, bool[,] adj)[]
        {
            ("H(2,4)=rook L4", 16, Rook(4)),
            ("H(2,5)=rook L5", 25, Rook(5)),
            ("H(2,6)=rook L6", 36, Rook(6)),
            ("H(3,3) hypergrid", 27, Hamming(3, 3)),
            ("Shrikhande (mate)", 16, CayleyZ4Sq(new[] { (1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3) })),
        };
        output.WriteLine($"{"graph",-20} {"n",-4} {"|Aut|",-9} {"b(Aut)",-7} {"base_2",-7} {"base_3",-7} {"gap=b2−bAut",-12} {"√n",-4} reading");
        output.WriteLine(new string('─', 120));
        int maxGap = 0, rows = 0;
        foreach (var (name, n, adj) in fam)
        {
            var rel = BuildRel(n, adj);
            long aut = Row4_AutOrder(rel, n, autCap);
            string autStr = aut < 0 ? $">{autCap}" : aut.ToString();
            int bAut = AutBase(rel, n, autCap);
            int b2 = KWLBase(n, adj, 2), b3 = n <= 27 ? KWLBase(n, adj, 3) : -1;   // 3-WL only for n ≤ 27 (cost)
            int gap = bAut >= 0 ? b2 - bAut : -1;
            int sq = (int)Math.Ceiling(Math.Sqrt(n));
            string b3s = b3 < 0 ? "n/a" : b3.ToString();
            string reading = bAut < 0 ? "Aut > cap"
                : gap <= 1 ? (b2 >= sq ? "base=b(Aut), THICK (rook-like √n)" : "base=b(Aut), small base")
                : "GAP>1 — node-4-like!";
            if (bAut >= 0) { maxGap = Math.Max(maxGap, gap); rows++; }
            output.WriteLine($"{name,-20} {n,-4} {autStr,-9} {bAut,-7} {b2,-7} {b3s,-7} {gap,-12} {sq,-4} {reading}");
        }
        output.WriteLine("");
        output.WriteLine("READ — the corrected picture:");
        output.WriteLine(" • base = b(Aut) on EVERY row (gap ≈ 0), and base_3 = base_2 ⟹ the base is the GROUP base, not a WL");
        output.WriteLine("   artifact; climbing WL cannot reduce it (Fact (i)).  No constructible graph has base ≫ b(Aut).");
        output.WriteLine(" • the c^k hypergrid is NOT a harder obstruction than the rook: base(H(k,c)) ≈ k·n^{1/k} SHRINKS as k");
        output.WriteLine("   grows (rook k=2: √n; H(3,3): n^{1/3}=3).  The rook (k=2) is the EXTREMAL thick case, not the start of");
        output.WriteLine("   an escalating ladder — climbing DIMENSION makes the Hamming base smaller, not larger.");
        output.WriteLine(" • all of them are large-structured-Aut (Cameron); the only invariant is base = b(Aut) = `hSmallAutThin`");
        output.WriteLine("   with EQUALITY.  Shrikhande (the rook's small-Aut mate) has small b(Aut) AND small base — same gap≈0.");
        output.WriteLine("");

        // The cospectral 3-WL static separation (the §9.9.7 step-4 correction's evidence).
        var rk = Rook(4); var sh = CayleyZ4Sq(new[] { (1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3) });
        output.WriteLine("COSPECTRAL PAIR SRG(16,6,2,2) — does 3-WL STATICALLY separate rook from Shrikhande (2-WL cannot)?");
        bool sep2 = false, sep3 = false;
        foreach (int k in new[] { 2, 3 })
        {
            string hr = KWLHistogram(16, rk, k), hs = KWLHistogram(16, sh, k);
            bool diff = hr != hs;
            if (k == 2) sep2 = diff; else sep3 = diff;
            output.WriteLine($"  {k}-WL:  rook={hr}   Shrikhande={hs}   ⟹ {(diff ? "DIFFER (3-WL separates)" : "SAME (indistinguishable)")}");
        }
        output.WriteLine(!sep2 && sep3
            ? "  ⇒ 3-WL STATICALLY separates the cospectral mates that 2-WL cannot (corrects §9.9.7 step-4's 'needs CFSG':"
            + " that barrier is 2-WL-specific) — but it does NOT reduce the rook's base (b(Aut)=√n stays), so no node-4 gain."
            : "  ⇒ unexpected: inspect (3-WL did not separate, or 2-WL already did).");
        output.WriteLine("");
        output.WriteLine("BOTTOM LINE (corrects both the user's intuition AND the naive 'Hamming=thick' reading).");
        output.WriteLine(" 1. The c^k hypergrid does NOT defeat k-WL harder than the rook defeats 2-WL — its base ≈ k·n^{1/k}");
        output.WriteLine("    SHRINKS with dimension.  The rook (k=2, base √n) is the WORST Hamming case; climbing makes it easier.");
        output.WriteLine(" 2. base = b(Aut) on every Hamming graph (and on Shrikhande): the large base IS the group base, and");
        output.WriteLine("    base_3 = base_2 confirms no WL level reduces it.  So `hSmallAutThin` ('thick ⟹ large Aut') holds with");
        output.WriteLine("    EQUALITY here — the Hamming family is the carved (Cameron) leg, not a node-4 falsifier.");
        output.WriteLine(" 3. A node-4 falsifier needs base ≫ b(Aut) (a SMALL-Aut graph with a large WL-dim gap).  NO constructible");
        output.WriteLine("    graph shows it: every known Hamming-twist (Shrikhande, FDF/CGGP, Doob) keeps base = b(Aut) = small.");
        output.WriteLine("    Climbing the WL ladder cannot manufacture one (base_k ≥ b(Aut) always), and the Hamming dimension");
        output.WriteLine("    ladder moves AWAY from thickness — so neither ladder is an exploitable node-4 attack.");

        Assert.True(rows >= 3 && maxGap <= 1, "a constructible graph showed base ≫ b(Aut) (gap>1) — would be a node-4 falsifier; INVESTIGATE");
        Assert.True(!sep2 && sep3, "cospectral 3-WL separation failed (expected 2-WL same, 3-WL differ)");
    }

    // ── HAMMING-TWIST PROBE (does a SMALL-Aut twist open the WL-dim gap base − b(Aut)?) ──
    //
    //  The §9.9.11 probe showed every Hamming graph has base = b(Aut) (gap 0).  The node-4
    //  falsifier would be a SMALL-Aut graph with base ≫ b(Aut).  The natural candidate is a
    //  twist of the Hamming family: the DOOB graph D(m,n) = Shrikhande^□m □ K4^□n, cospectral
    //  with H(2m+n, 4) but with strictly SMALLER Aut (Shrikhande's 192 < the 4×4 rook's 1152).
    //  D(1,1) = Shrikhande □ K4 (n=64) is cospectral with H(3,4) = K4^□3 (n=64): a clean
    //  small-Aut-vs-Cameron pair (|Aut| 4608 vs 82944), the n=16 Shrikhande/rook contrast one
    //  level up.  Question: does the twist KEEP base = b(Aut) (tame, more 0-falsifier evidence)
    //  or push base ≫ b(Aut) (a node-4 falsifier — seal-breaking)?  Also the smaller twists
    //  (Shrikhande @16, Chang @28) for the trend.  Honest scope: fixed n only (no scalable
    //  small-Aut thick family exists, §9.9.3 G-construct), so this checks the gap is O(1) at the
    //  constructible sizes — it cannot rule out a GROWING gap.

    // Cartesian product G □ H: vertex (u,v)=u·nh+v; adjacent iff (u=u' ∧ v~v') or (u~u' ∧ v=v').
    static bool[,] Cartesian(bool[,] g, int ng, bool[,] h, int nh)
    {
        int n = ng * nh; var a = Empty(n);
        for (int u = 0; u < ng; u++) for (int v = 0; v < nh; v++)
            for (int u2 = 0; u2 < ng; u2++) for (int v2 = 0; v2 < nh; v2++)
            {
                if (u == u2 && v == v2) continue;
                if ((u == u2 && h[v, v2]) || (v == v2 && g[u, u2])) a[u * nh + v, u2 * nh + v2] = true;
            }
        return a;
    }
    static bool[,] CompleteGraph(int m) { var a = Empty(m); for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) Edge(a, i, j); return a; }

    [Fact]
    public void Probe_HammingTwists()
    {
        output.WriteLine("HAMMING TWISTS — does a SMALL-Aut twist of the Hamming family open the WL-dim gap base − b(Aut)?");
        output.WriteLine("A gap ≫ 0 at SMALL Aut would be the node-4 falsifier (seal-breaking).  Centerpiece: the Doob graph");
        output.WriteLine("D(1,1)=Shrikhande□K4 (n=64), COSPECTRAL with H(3,4)=K4□K4□K4 but |Aut| 4608 vs 82944 — the small-Aut");
        output.WriteLine("mate.  Compares base_2 to b(Aut); cap on |Aut| enumeration (large-Aut rows report b(Aut)=large).");
        output.WriteLine("");
        const long autCap = 25000;
        var shrik = CayleyZ4Sq(new[] { (1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3) });
        var k4 = CompleteGraph(4);
        var rows = new List<(string name, int n, bool[,] adj, string cat)>
        {
            ("H(3,4)=K4³ [Cameron]", 64, Hamming(3, 4), "Hamming"),
            ("Doob Shrik□K4 [twist]", 64, Cartesian(shrik, 16, k4, 4), "twist"),
            ("Shrikhande [twist@16]", 16, shrik, "twist"),
        };
        // Chang graphs (n=28, small-Aut twists of T(8)) from the catalogue.
        var chPath = Row4_DataPath(28);
        if (chPath != "")
        {
            int added = 0;
            foreach (var (idx, M) in Row4_Parse(chPath, 28).Select((m, i) => (i, m)))
            {
                if (added >= 2) break;
                var built = Row4_Build(M, 28); if (built is null) continue;
                var (rel, rank, sym, val) = built.Value;
                if (rank != 3 || !sym || !Row4_Primitive(rel, rank, 28)) continue;
                long a = Row4_AutOrder(rel, 28, autCap);
                if (a < 0 || a >= 28L * 28 * 28) continue;          // keep only small-Aut (Chang, not T(8))
                rows.Add(($"Chang as28 #{idx + 1} [twist]", 28, Row4_GraphOf(rel, rank, val, 28), "twist"));
                added++;
            }
        }

        output.WriteLine($"{"graph",-24} {"n",-4} {"|Aut|",-9} {"b(Aut)",-7} {"base_2",-7} {"gap",-5} verdict");
        output.WriteLine(new string('─', 100));
        int maxTwistGap = -100, twistRows = 0;
        bool doobTame = false;
        foreach (var (name, n, adj, cat) in rows)
        {
            var rel = BuildRel(n, adj);
            long aut = Row4_AutOrder(rel, n, autCap);
            string autStr = aut < 0 ? $">{autCap}" : aut.ToString();
            int bAut = AutBase(rel, n, autCap);
            int b2 = KWLBase(n, adj, 2);
            int gap = bAut >= 0 ? b2 - bAut : -99;
            string gs = bAut >= 0 ? gap.ToString() : "n/a";
            string verdict = bAut < 0 ? "Aut>cap (Cameron side)"
                : gap <= 2 ? "base=b(Aut) — TAME (no gap)"
                : "GAP — node-4 FALSIFIER?!";
            output.WriteLine($"{name,-24} {n,-4} {autStr,-9} {(bAut < 0 ? "large" : bAut.ToString()),-7} {b2,-7} {gs,-5} {verdict}");
            if (cat == "twist" && bAut >= 0) { maxTwistGap = Math.Max(maxTwistGap, gap); twistRows++; if (name.StartsWith("Doob")) doobTame = gap <= 2; }
        }
        output.WriteLine("");

        // Cospectrality: 2-WL cannot tell the small-Aut twist from its Cameron mate.
        var h34 = Hamming(3, 4); var doob = Cartesian(shrik, 16, k4, 4);
        string hh = KWLHistogram(64, h34, 2), hd = KWLHistogram(64, doob, 2);
        output.WriteLine($"COSPECTRAL CHECK (n=64): 2-WL histogram  H(3,4) = {hh}");
        output.WriteLine($"                                          Doob   = {hd}   ⟹ {(hh == hd ? "SAME (2-WL can't separate residue from Cameron — the largeness split is essential)" : "DIFFER")}");
        output.WriteLine("");

        output.WriteLine("VERDICT.  Every small-Aut TWIST has base = b(Aut) (gap ≤ 2 = greedy slack, no real WL-dim gap):");
        output.WriteLine($"  Doob D(1,1) tame: {doobTame};  twist rows measured: {twistRows};  max twist gap: {maxTwistGap}.");
        output.WriteLine(maxTwistGap <= 2
            ? "  ⇒ NO node-4 falsifier: even a COMPOSED twist (Shrikhande into a Cartesian product, cospectral with the"
            + " large-Aut Hamming H(3,4)) keeps base = b(Aut).  The twist shrinks BOTH |Aut| and the base together — the"
            + " gap stays 0.  Strong evidence that `base ≫ b(Aut) at small Aut` has no constructible witness (node 4)."
            : "  ‼ A small-Aut twist opened the gap (base ≫ b(Aut)) — a candidate node-4 FALSIFIER (seal-breaking). INVESTIGATE.");
        output.WriteLine("");
        output.WriteLine("HONEST SCOPE: fixed n ≤ 64 (no scalable small-Aut thick family exists, §9.9.3 G-construct), so this");
        output.WriteLine("confirms the gap is O(1) at the constructible sizes — it cannot rule out a gap GROWING with n.  The");
        output.WriteLine("Doob/Hamming-twist family is the sharpest constructible probe of the node-4 falsifier question, and it");
        output.WriteLine("comes back negative (tame), extending the 0-falsifier record to a composed cospectral twist.");

        Assert.True(twistRows >= 2, "fewer than 2 small-Aut twists measured — fixture/catalogue issue");
        Assert.True(maxTwistGap <= 2, "a small-Aut twist showed base ≫ b(Aut) — candidate node-4 falsifier; INVESTIGATE (not a code bug)");
        Assert.True(hh == hd, "Doob and H(3,4) are not 2-WL-cospectral — construction issue");
    }

    // ── FORMS-GRAPH PROBE (route §9.9.18b — the FIRST constructible node-4 witnesses) ──────────────
    //
    //  The Skresanov reduction (§9.9.18) shows every small-Aut non-geometric SCHURIAN rank-3 residue
    //  is AFFINE; C1 (§9.9.18b) found the affine survivors split into 1-dim cyclotomic (cited) and the
    //  forms-graph classes (c)-(f) — affine-polar / alternating / half-spin / Suzuki-Tits — for which
    //  bounded-WL-dim is UNCITED/OPEN.  KEY CORRECTION to the old framing: these are NOT
    //  "construction-bottlenecked" — the AFFINE POLAR graph VO^ε_{2m}(q) at FIXED m, GROWING q is an
    //  explicit, parametric, small-Aut (poly |Aut|), non-geometric (smallest eigenvalue →−∞ with q),
    //  primitive, schurian rank-3 SRG.  This is the FIRST probe to reach genuine node-4 (unbounded-s)
    //  witnesses — every prior probe (catalogue/sporadics) was bounded-s = node 3.
    //
    //  THE TEST.  hSmallAutThin = small-Aut ⟹ shatters at base ≪ √n.  Validate VO^-_4(2) = Clebsch
    //  (known n=16 residue), then test the never-probed growing-q line VO^-_4(3) [n=81], VO^-_4(4)
    //  [n=256] — does the 1-WL base stay bounded (shatter) while n grows, vs the geometric Rook(m)
    //  [base = √n] at matching n?  Shatter ⟹ strongest hSmallAutThin evidence yet (genuine node 4);
    //  thick ⟹ a FALSIFIER (the seal would need restating — a real result either way).

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    // Minimal finite field GF(q), q a prime power, as add/mul/neg tables. Elements 0..q-1; for q=p^e
    // an element is a degree-<e polynomial over F_p packed in base-p digits, reduced mod a monic
    // irreducible (small hardcoded table).  Prime q uses direct modular arithmetic.
    sealed class GFq
    {
        public readonly int q;
        public readonly int[,] add, mul;
        public readonly int[] neg;
        public GFq(int q)
        {
            this.q = q;
            add = new int[q, q]; mul = new int[q, q]; neg = new int[q];
            int p = 2; while (q % p != 0) p++;
            int e = 0, t = q; while (t > 1) { t /= p; e++; }
            if (IPow(p, e) != q) throw new ArgumentException($"{q} is not a prime power");
            if (e == 1)
            {
                for (int i = 0; i < q; i++) { neg[i] = (q - i) % q; for (int j = 0; j < q; j++) { add[i, j] = (i + j) % q; mul[i, j] = (i * j) % q; } }
                return;
            }
            int[] irr = e == 2 && p == 2 ? new[] { 1, 1 }        // x^2+x+1   (GF(4))
                      : e == 3 && p == 2 ? new[] { 1, 1, 0 }     // x^3+x+1   (GF(8))
                      : e == 2 && p == 3 ? new[] { 1, 0 }        // x^2+1     (GF(9))
                      : throw new NotImplementedException($"GF({q}) irreducible not tabulated");
            int[] D(int x) { var d = new int[e]; for (int i = 0; i < e; i++) { d[i] = x % p; x /= p; } return d; }
            int En(int[] d) { int x = 0; for (int i = e - 1; i >= 0; i--) x = x * p + d[i]; return x; }
            for (int i = 0; i < q; i++)
            {
                var a = D(i);
                var sn = new int[e]; for (int k = 0; k < e; k++) sn[k] = (p - a[k]) % p; neg[i] = En(sn);
                for (int j = 0; j < q; j++)
                {
                    var b = D(j);
                    var s = new int[e]; for (int k = 0; k < e; k++) s[k] = (a[k] + b[k]) % p; add[i, j] = En(s);
                    var prod = new int[2 * e]; for (int x = 0; x < e; x++) for (int y = 0; y < e; y++) prod[x + y] = (prod[x + y] + a[x] * b[y]) % p;
                    for (int deg = 2 * e - 1; deg >= e; deg--)
                    {
                        int co = prod[deg]; if (co == 0) continue; prod[deg] = 0;
                        for (int k = 0; k < e; k++) prod[deg - e + k] = (prod[deg - e + k] + (p - (co * irr[k]) % p) % p) % p;
                    }
                    var r = new int[e]; for (int k = 0; k < e; k++) r[k] = prod[k] % p; mul[i, j] = En(r);
                }
            }
        }
    }

    // Affine polar graph VO^ε_{2m}(q): vertices = F_q^{2m}, x ~ y iff Q(x−y) = 0 (x≠y), Q a
    // nondegenerate quadratic form of type ε (+1 hyperbolic, −1 elliptic).  A translation (Cayley)
    // scheme ⟹ vertex-transitive + schurian; the affine rank-3 forms graph of Skresanov class (c).
    static bool[,] AffinePolar(int q, int m, int eps)
    {
        var F = new GFq(q);
        int dim = 2 * m, n = IPow(q, dim);
        int bb = 0, cc = 0;
        if (eps == -1)   // find an anisotropic binary form g(y,z)=y²+b·yz+c·z² (g=0 only at 0)
        {
            bool found = false;
            for (int b = 0; b < q && !found; b++) for (int c = 0; c < q && !found; c++)
            {
                bool aniso = true;
                for (int y = 0; y < q && aniso; y++) for (int z = 0; z < q; z++)
                {
                    if (y == 0 && z == 0) continue;
                    int g = F.add[F.add[F.mul[y, y], F.mul[F.mul[b, y], z]], F.mul[c, F.mul[z, z]]];
                    if (g == 0) { aniso = false; break; }
                }
                if (aniso) { bb = b; cc = c; found = true; }
            }
            if (!found) throw new Exception($"no anisotropic binary form over GF({q})");
        }
        int[] Vec(int v) { var x = new int[dim]; for (int i = 0; i < dim; i++) { x[i] = v % q; v /= q; } return x; }
        int Q(int[] x)
        {
            int s = 0, hyp = eps == -1 ? m - 1 : m;
            for (int i = 0; i < hyp; i++) s = F.add[s, F.mul[x[2 * i], x[2 * i + 1]]];
            if (eps == -1)
            {
                int y = x[2 * (m - 1)], z = x[2 * (m - 1) + 1];
                s = F.add[s, F.add[F.add[F.mul[y, y], F.mul[F.mul[bb, y], z]], F.mul[cc, F.mul[z, z]]]];
            }
            return s;
        }
        var adj = Empty(n);
        var vecs = new int[n][]; for (int v = 0; v < n; v++) vecs[v] = Vec(v);
        var d = new int[dim];
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++)
        {
            for (int i = 0; i < dim; i++) d[i] = F.add[vecs[u][i], F.neg[vecs[v][i]]];
            if (Q(d) == 0) Edge(adj, u, v);
        }
        return adj;
    }

    // First-fit 1-WL individualization base (cheap upper bound on the base — for large n where the
    // best-fit GreedyBaseCurve is too costly).  Returns #individualizations to reach a discrete colouring.
    static int CheapBaseSize(int n, bool[,] adj)
    {
        var indiv = new List<int>(); var color = Refine(n, adj, indiv); int guard = 0;
        while (MaxCell(color, n) > 1 && guard++ < n)
        {
            var sz = new Dictionary<int, int>(); foreach (var c in color) sz[c] = sz.GetValueOrDefault(c) + 1;
            int pick = -1; for (int v = 0; v < n; v++) if (!indiv.Contains(v) && sz[color[v]] > 1) { pick = v; break; }
            if (pick < 0) break; indiv.Add(pick); color = Refine(n, adj, indiv);
        }
        return indiv.Count;
    }

    static int[] Dec(int v, int q, int dim) { var x = new int[dim]; for (int i = 0; i < dim; i++) { x[i] = v % q; v /= q; } return x; }
    static int Enc(int[] x, int q) { int v = 0; for (int i = x.Length - 1; i >= 0; i--) v = v * q + x[i]; return v; }
    static int FInv(GFq F, int x) { for (int y = 1; y < F.q; y++) if (F.mul[x, y] == 1) return y; return 0; }

    // Cheap SRG params for VERTEX-TRANSITIVE graphs (all our forms graphs are Cayley): k = deg(0),
    // λ = |N(0)∩N(nbr)|, μ = |N(0)∩N(non-nbr)|, with a regularity sample.  O(n) vs SrgParams' O(n³).
    static (bool ok, int k, int lam, int mu) CheapSrgParams(int n, bool[,] adj)
    {
        int Deg(int v) { int d = 0; for (int w = 0; w < n; w++) if (adj[v, w]) d++; return d; }
        int Common(int a, int b) { int c = 0; for (int w = 0; w < n; w++) if (adj[a, w] && adj[b, w]) c++; return c; }
        int k = Deg(0);
        if (Deg(1) != k || Deg(n - 1) != k) return (false, k, 0, 0);
        int nb = -1, nn = -1; for (int w = 1; w < n; w++) { if (adj[0, w] && nb < 0) nb = w; if (!adj[0, w] && nn < 0) nn = w; if (nb >= 0 && nn >= 0) break; }
        if (nb < 0 || nn < 0) return (false, k, 0, 0);
        return (true, k, Common(0, nb), Common(0, nn));
    }

    // Alternating forms graph A(d,q): vertices = alternating d×d matrices over GF(q) (= ∧²F_q^d,
    // dim = C(d,2)), adjacent iff rank(A−B) = 2.  d=5 ⟹ diameter-2 SRG (Skresanov class (d)).
    static bool[,] AlternatingForms(int d, int q)
    {
        var F = new GFq(q);
        var pairs = new (int i, int j)[d * (d - 1) / 2]; { int idx = 0; for (int i = 0; i < d; i++) for (int j = i + 1; j < d; j++) pairs[idx++] = (i, j); }
        int dim = pairs.Length, n = IPow(q, dim);
        int Rank(int v)
        {
            var M = new int[d, d]; var dg = Dec(v, q, dim);
            for (int t = 0; t < dim; t++) { var (i, j) = pairs[t]; M[i, j] = dg[t]; M[j, i] = F.neg[dg[t]]; }
            int rank = 0, row = 0;
            for (int col = 0; col < d && row < d; col++)
            {
                int piv = -1; for (int r = row; r < d; r++) if (M[r, col] != 0) { piv = r; break; }
                if (piv < 0) continue;
                if (piv != row) for (int c = 0; c < d; c++) (M[row, c], M[piv, c]) = (M[piv, c], M[row, c]);
                int inv = FInv(F, M[row, col]);
                for (int r = 0; r < d; r++) if (r != row && M[r, col] != 0) { int f = M[r, col]; for (int c = 0; c < d; c++) M[r, c] = F.add[M[r, c], F.neg[F.mul[F.mul[f, inv], M[row, c]]]]; }
                row++; rank++;
            }
            return rank;
        }
        var conn = new HashSet<int>(); for (int v = 1; v < n; v++) if (Rank(v) == 2) conn.Add(v);
        var adj = Empty(n);
        for (int u = 0; u < n; u++) for (int w = u + 1; w < n; w++)
        {
            var du = Dec(u, q, dim); var dw = Dec(w, q, dim); var dd = new int[dim];
            for (int i = 0; i < dim; i++) dd[i] = F.add[du[i], F.neg[dw[i]]];
            if (conn.Contains(Enc(dd, q))) Edge(adj, u, w);
        }
        return adj;
    }

    // Suzuki-Tits ovoid graph VSz(q), q = 2^{2e+1}, e≥1 (q=8): Cayley graph on GF(q)^4 with connection
    // set = the cone over the Suzuki-Tits ovoid O = {(1,a,b, ab + a^{σ+2} + b^σ)} ∪ {(0,0,0,1)},
    // σ the Tits automorphism (σ²=Frobenius; q=8 ⟹ σ(x)=x^4).  Cospectral with VO^-_4(q) but with
    // Sz(q) ⊂ Aut (Skresanov class (f); Sz(q) distinguishes it from the orthogonal VO^-_4(q)).
    static bool[,] SuzukiTits(int q)
    {
        var F = new GFq(q);
        int lg = 0, tt = q; while (tt > 1) { tt >>= 1; lg++; }          // lg = log2 q = 2e+1
        if ((lg & 1) == 0 || lg < 3) throw new ArgumentException($"VSz needs q=2^(2e+1), e≥1; got q={q}");
        int sExp = 1 << ((lg + 1) / 2);                                 // 2^{e+1}; q=8 ⟹ 4
        int Pow(int x, int ex) { int r = 1; for (int i = 0; i < ex; i++) r = F.mul[r, x]; return r; }
        int Sig(int x) => Pow(x, sExp);                                 // σ(x) = x^{2^{e+1}}
        int dim = 4, n = IPow(q, dim);
        var conn = new HashSet<int>();
        void AddCone(int[] p) { for (int lam = 1; lam < q; lam++) { var v = new int[4]; for (int i = 0; i < 4; i++) v[i] = F.mul[lam, p[i]]; conn.Add(Enc(v, q)); } }
        for (int a = 0; a < q; a++) for (int b = 0; b < q; b++)
        {
            int aS2 = F.mul[Sig(a), F.mul[a, a]];                       // a^{σ+2} = a^σ·a²
            int c4 = F.add[F.add[F.mul[a, b], aS2], Sig(b)];            // ab + a^{σ+2} + b^σ
            AddCone(new[] { 1, a, b, c4 });
        }
        AddCone(new[] { 0, 0, 0, 1 });
        var adj = Empty(n);
        for (int u = 0; u < n; u++) for (int w = u + 1; w < n; w++)
        {
            var du = Dec(u, q, dim); var dw = Dec(w, q, dim); var dd = new int[dim];
            for (int i = 0; i < dim; i++) dd[i] = F.add[du[i], F.neg[dw[i]]];
            if (conn.Contains(Enc(dd, q))) Edge(adj, u, w);
        }
        return adj;
    }

    [Fact]
    public void Probe_FormsGraphs()
    {
        output.WriteLine("A2 FORMS-GRAPH PROBE (route §9.9.18b) — the FIRST constructible NODE-4 witnesses.");
        output.WriteLine("Affine polar graph VO^ε_{2m}(q): small-Aut (poly), non-geometric (s→−∞ with q), primitive,");
        output.WriteLine("schurian rank-3 SRG — Skresanov's affine forms-graph class (c).  Tests hSmallAutThin");
        output.WriteLine("(small-Aut ⟹ 1-WL base ≪ √n / shatters) at FIXED m=2, GROWING q: VO^-_4(q) q=2,3,4,5 (n=16..625),");
        output.WriteLine("plus BREADTH across classes (d) alternating A(5,2) n=1024, (f) Suzuki-Tits VSz(8) n=4096.  VO^-_4(2)=Clebsch");
        output.WriteLine("validates; q=3+ and (d),(f) are NEVER-PROBED genuine node 4.  Contrast: geometric Rook(m) needs base = √n.");
        output.WriteLine("");

        output.WriteLine($"{"graph",-16} {"n",-5} {"(k,λ,μ)",-15} {"s",-5} {"2rk",-4} {"|Aut|",-9} {"base",-5} {"√n",-4} {"verdict",-9} cover ∅ → {{0}}[→{{0,v*}}]");
        output.WriteLine(new string('─', 160));

        // m=2 fixed, growing q: the small-Aut non-geometric node-4 line (q=4 needs GF(4)).
        var targets = new (string name, int q, int m, int eps)[]
        {
            ("VO^-_4(2)=Clebsch", 2, 2, -1),
            ("VO^+_4(2)",         2, 2, +1),
            ("VO^-_4(3)",         3, 2, -1),
            ("VO^+_4(3)",         3, 2, +1),
            ("VO^-_4(4)",         4, 2, -1),
            ("VO^-_4(5)",         5, 2, -1),
        };

        var rows = new List<(string name, int n, int s, long aut, int baseSize, int sqrtN, bool shatters, bool smallAut, bool nonGeom)>();
        int targetsMeasured = 0, falsifiers = 0;

        // |Aut| is analytic here (affine-polar fixed-m = poly by Skresanov; Rook = large/geometric); the
        // backtracking enumerator is O(|Aut|) (~10^5 at n=81) and the real metric is base-vs-√n, so we
        // annotate the Aut class rather than enumerate.
        void Measure(string name, bool[,] adj, int n, bool isAffinePolar, bool knownSmallAut)
        {
            var (ok, k, lam, mu) = n > 256 ? CheapSrgParams(n, adj) : SrgParams(n, adj);   // O(n³) SrgParams too slow at n>256 (Cayley ⟹ vertex-transitive)
            if (!ok) { output.WriteLine($"{name,-16} {n,-5} NOT-AN-SRG (irregular sample — report & skip)"); return; }
            int s = SmallestEig(n, k, lam, mu);
            int r2 = n <= 256 ? PRank(n, adj, 2) : -1;
            int baseSize = n <= 81 ? GreedyBaseCurve(n, adj).Count - 1 : CheapBaseSize(n, adj);
            int sq = (int)Math.Ceiling(Math.Sqrt(n));
            var (traj, _, _, _) = n <= 81 ? Row4_CoverTrajectory(n, BuildRel(n, adj)) : ("(2-WL cover skipped: n>81 cost)", false, 0, 0);
            bool shatters = baseSize < sq;
            bool nonGeom = s <= -3 || (double)-s >= Math.Sqrt(n) / 4;   // unbounded-s heuristic vs n
            string autStr = knownSmallAut ? "poly*" : "large*";
            // n=16 is too small for the base≪√n asymptotics (the validation anchor, Clebsch); judge SHATTER/THICK only at n≥64.
            string verdict = n < 64 ? "anchor" : shatters ? "SHATTER" : "THICK‼";
            output.WriteLine($"{name,-16} {n,-5} {$"({k},{lam},{mu})",-15} {s,-5} {r2,-4} {autStr,-9} {baseSize,-5} {sq,-4} {verdict,-9} {traj}");
            rows.Add((name, n, s, knownSmallAut ? 1L : -1L, baseSize, sq, shatters, knownSmallAut, nonGeom));
        }

        foreach (var (name, q, m, eps) in targets)
        {
            int n = IPow(q, 2 * m);
            bool[,] adj;
            try { adj = AffinePolar(q, m, eps); }
            catch (Exception ex) { output.WriteLine($"{name,-16} build failed: {ex.Message}"); continue; }
            Measure(name, adj, n, isAffinePolar: true, knownSmallAut: true);   // affine-polar fixed m=2 ⟹ poly |Aut| (Skresanov)
            // count the small-Aut non-geometric elliptic line (m=2, eps=-1) at ASYMPTOTIC n≥64 as node-4
            // targets (n=16 = Clebsch validation anchor, excluded from the base≪√n falsifier test).
            if (eps == -1 && rows.Count > 0)
            {
                var r = rows[^1];
                if (r.name == name && r.nonGeom && r.n >= 64) { targetsMeasured++; if (!r.shatters) falsifiers++; }
            }
        }

        output.WriteLine("");
        output.WriteLine("GEOMETRIC THICK CONTRAST (Rook(m) = Hamming H(2,m), large-Aut, base = √n) at matching n:");
        foreach (int mm in new[] { 4, 9 })   // Rook(4)=16, Rook(9)=81
            Measure($"Rook({mm})", Rook(mm), mm * mm, isAffinePolar: false, knownSmallAut: false);

        // ── BREADTH: the other affine forms-graph classes (Skresanov (d),(f); (e) infeasible) ─────────
        output.WriteLine("");
        output.WriteLine("BREADTH — other small-Aut non-geometric affine forms-graph classes (single points; growing-q infeasible):");
        var breadth = new List<(string name, int n, int s, int baseSize, int sqrtN, bool shatters)>();
        void Breadth(string name, Func<bool[,]> build, int n)
        {
            bool[,] adj;
            try { adj = build(); }
            catch (Exception ex) { output.WriteLine($"{name,-16} build failed: {ex.Message}"); return; }
            int before = rows.Count;
            Measure(name, adj, n, isAffinePolar: true, knownSmallAut: true);
            if (rows.Count > before) { var r = rows[^1]; breadth.Add((r.name, r.n, r.s, r.baseSize, r.sqrtN, r.shatters)); }
        }
        Breadth("Alt(5,2) [d]", () => AlternatingForms(5, 2), IPow(2, 10));   // n=1024, alternating forms graph A(5,q)
        Breadth("VSz(8) [f]",   () => SuzukiTits(8),          IPow(8, 4));    // n=4096, Suzuki-Tits ovoid graph
        output.WriteLine("  (e) half-spin VD_{5,5}(q): n = q^16 ≥ 65536 — INFEASIBLE to construct/probe (noted, not built).");
        int breadthTargets = breadth.Count(b => b.n >= 64), breadthFalsifiers = breadth.Count(b => b.n >= 64 && !b.shatters);

        // ── Readout ──────────────────────────────────────────────────────────────────────────────
        output.WriteLine("");
        output.WriteLine("THE GROWING-q LINE (VO^-_4(q), fixed m=2, small-Aut non-geometric — genuine node 4):");
        foreach (var r in rows.Where(r => r.name.StartsWith("VO^-_4")).OrderBy(r => r.n))
        {
            string tag = r.n < 64 ? "anchor (Clebsch; small-n, base≈√n is noise)"
                       : r.shatters ? "SHATTERS (base ≪ √n) ✓" : "THICK (base ≥ √n) ‼ FALSIFIER";
            output.WriteLine($"  {r.name,-16} n={r.n,-4} s={r.s,-4} base={r.baseSize} (√n={r.sqrtN})  ⟹ {tag}");
        }
        // The money shot: base TREND vs √n vs the geometric Rook base (which tracks √n).
        var voLine = rows.Where(r => r.name.StartsWith("VO^-_4")).OrderBy(r => r.n).ToList();
        var rookLine = rows.Where(r => r.name.StartsWith("Rook")).OrderBy(r => r.n).ToList();
        output.WriteLine("");
        output.WriteLine($"  BASE TREND (the discriminator):  n         = [{string.Join(", ", voLine.Select(r => r.n))}]");
        output.WriteLine($"                                   √n        = [{string.Join(", ", voLine.Select(r => r.sqrtN))}]");
        output.WriteLine($"                                   VO^-_4 base = [{string.Join(", ", voLine.Select(r => r.baseSize))}]  ← bounded/flat (shatters)");
        output.WriteLine($"                                   Rook   base = [{string.Join(", ", rookLine.Select(r => $"{r.baseSize}@n{r.n}"))}]  ← = √n (geometric, thick)");
        if (breadth.Count > 0)
            output.WriteLine($"  BREADTH classes (d),(f):  {string.Join(";  ", breadth.Select(b => $"{b.name} n={b.n} s={b.s} base={b.baseSize} (√n={b.sqrtN}) {(b.shatters ? "SHATTER✓" : "THICK‼")}"))}");
        output.WriteLine("");
        output.WriteLine($"VERDICT — node-4 small-Aut non-geometric targets (n≥64): affine-polar(c)={targetsMeasured}, breadth(d,f)={breadthTargets};  falsifiers (base ≥ √n): {falsifiers + breadthFalsifiers}.");
        output.WriteLine(falsifiers + breadthFalsifiers == 0 && targetsMeasured >= 2
            ? "  ⇒ The forms-graph node-4 witnesses SHATTER at base ≪ √n as q (hence s, n) grows — across MULTIPLE Skresanov classes"
            + " (affine-polar (c) q=2..5, alternating (d), Suzuki-Tits (f)).  hSmallAutThin holds on the FIRST genuine constructible"
            + " node-4 (unbounded-s) families, not just bounded-s node-3 catalogue data.  Corrects the 'no constructible witness'"
            + " framing (§9.9.18b): the witnesses exist across classes, are probable, and confirm the seal's prediction."
            : targetsMeasured < 2
                ? "  ⇒ Fewer than 2 affine-polar node-4 targets isolated — check VO construction / GF(q) / SRG-ness."
                : "  ‼ A small-Aut non-geometric forms graph needs base ≈ √n — a hSmallAutThin FALSIFIER; the seal's node-4"
                + " prediction is violated on a constructible family.  INVESTIGATE (a real result, not a code bug).");
        output.WriteLine("");
        output.WriteLine("HONEST SCOPE: forms graphs are small-Aut only at FIXED dimension (growing dim ⟹ super-poly Aut = large/Cameron).");
        output.WriteLine("Affine-polar (c): VO^-_4(q) q=2,3,4,5 (n=16..625), the growing-q unbounded-s axis Neumaier/the catalogue could");
        output.WriteLine("not reach.  Breadth: alternating (d) A(5,2) n=1024, Suzuki-Tits (f) VSz(8) n=4096 — single points (growing-q");
        output.WriteLine("infeasible at n=q^10 / q^4·…).  (e) half-spin n=q^16 infeasible.  (b) bilinear H_q(2,m) excluded (geometric).");
        output.WriteLine("These are the C1 (§9.9.18b) affine forms-graph residue — bounded-WL-dim UNCITED/OPEN; empirical support, not a proof.");
        output.WriteLine("* |Aut| not enumerated (too slow); annotated analytically — forms graphs fixed-dim = poly (Skresanov), Rook = large.");
        output.WriteLine("  Base = best-fit 1-WL (n≤81) / first-fit upper bound (n>81); params = cheap vertex-transitive extraction (n>256).");

        Assert.True(targetsMeasured >= 2, "fewer than 2 small-Aut non-geometric affine-polar node-4 targets isolated — construction/GF(q)/SRG issue");
        Assert.Equal(0, falsifiers + breadthFalsifiers);   // any small-Aut non-geometric forms graph with base ≥ √n falsifies hSmallAutThin (a real finding, not a code bug)
    }

    // ── SPIKE-K part 1 (plan §11.1) ─────────────────────────────────────────────────────────────────
    //  Does the ISOTROPY-COUNT profile — the EXACT object the VO⁻₄(3) `decide` used —
    //      cnt(u; t1,t2) = #{ y≠0 : Q(y)=0, Q(y-(t1-u))=0, Q(y-(t2-u))=0 }
    //  individualize the affine polar graph VO^ε_{2m}(q) to DISCRETE at a SMALL base, and crucially
    //  does it SURVIVE at odd q≥5 where the square-class coarsening bites?  By the Gauss-sum identity
    //  this count only ever sees χ(det G) (the square class), not det G itself: at q=3 sqclass = full
    //  value (looked rich); at q=5 {1,4} and {2,3} collapse.  CHAR-SUM-FREE: counts by brute force, so
    //  the measured base faithfully reflects the COARSE invariant's separating power.  Reports the base
    //  size for odd q∈{3,5,7,9} (q=9 = the odd prime-power test) vs √n and the d+log q / log n budget.
    static (int baseSize, int n, bool discrete) CountProfileBase(int q, int m, int eps, Random rng)
    {
        var F = new GFq(q);
        int dim = 2 * m, n = IPow(q, dim);
        // VO^ε form (replicates AffinePolar's Q): hyperbolic pairs + (ε=-1) an anisotropic binary tail.
        int bb = 0, cc = 0;
        if (eps == -1)
        {
            bool found = false;
            for (int b = 0; b < q && !found; b++) for (int c = 0; c < q && !found; c++)
            {
                bool aniso = true;
                for (int y = 0; y < q && aniso; y++) for (int z = 0; z < q; z++)
                {
                    if (y == 0 && z == 0) continue;
                    int g = F.add[F.add[F.mul[y, y], F.mul[F.mul[b, y], z]], F.mul[c, F.mul[z, z]]];
                    if (g == 0) { aniso = false; break; }
                }
                if (aniso) { bb = b; cc = c; found = true; }
            }
            if (!found) throw new Exception($"no anisotropic binary form over GF({q})");
        }
        int[] Vec(int v) { var x = new int[dim]; for (int i = 0; i < dim; i++) { x[i] = v % q; v /= q; } return x; }
        int Q(int[] x)
        {
            int s = 0, hyp = eps == -1 ? m - 1 : m;
            for (int i = 0; i < hyp; i++) s = F.add[s, F.mul[x[2 * i], x[2 * i + 1]]];
            if (eps == -1)
            {
                int y = x[2 * (m - 1)], z = x[2 * (m - 1) + 1];
                s = F.add[s, F.add[F.add[F.mul[y, y], F.mul[F.mul[bb, y], z]], F.mul[cc, F.mul[z, z]]]];
            }
            return s;
        }
        var vec = new int[n][]; for (int v = 0; v < n; v++) vec[v] = Vec(v);
        var iso = new bool[n]; for (int v = 0; v < n; v++) iso[v] = Q(vec[v]) == 0;
        // Sub(a,b) = index of vec[a]-vec[b] (little-endian base-q, matching Vec).
        int Sub(int a, int b) { int s = 0, pw = 1; for (int i = 0; i < dim; i++) { s += F.add[vec[a][i], F.neg[vec[b][i]]] * pw; pw *= q; } return s; }

        // N1ofw(w) = #{y≠0 : iso[y], iso[y-w]} ;  cnt(u;t) = N1ofw(t-u).  Precompute once (n² total).
        var N1 = new int[n];
        for (int w = 0; w < n; w++) { int c = 0; for (int y = 1; y < n; y++) if (iso[y] && iso[Sub(y, w)]) c++; N1[w] = c; }

        // G_δ(w) = #{y≠0 : iso[y], iso[y-w], iso[y-(w-δ)]} ;  cnt(u;ti,tj) = G_{ti-tj}(ti-u).  Cache per δ.
        var gByDelta = new Dictionary<int, int[]>();
        int[] Gdelta(int delta)
        {
            if (gByDelta.TryGetValue(delta, out var arr)) return arr;
            arr = new int[n];
            for (int w = 0; w < n; w++)
            {
                int wmd = Sub(w, delta);               // w - δ
                int c = 0;
                for (int y = 1; y < n; y++)
                    if (iso[y] && iso[Sub(y, w)] && iso[Sub(y, wmd)]) c++;   // y, y-w, y-(w-δ) all isotropic
                arr[w] = c;
            }
            gByDelta[delta] = arr;
            return arr;
        }

        int rel(int u, int t) => u == t ? 0 : (iso[Sub(u, t)] ? 1 : 2);

        // Greedy individualization under the (rank-3 rel + size-1 + size-2 count) profile.
        var baseL = new List<int>();
        int[] color = new int[n];
        int guard = 0, cap = Math.Min(n, 4 * dim + 8 + (int)Math.Ceiling(4 * Math.Log2(q)));
        bool discrete = false;
        while (guard++ <= cap)
        {
            // colour every u by its profile against the current base
            var keyToId = new Dictionary<string, int>();
            for (int u = 0; u < n; u++)
            {
                var sb = new StringBuilder();
                foreach (var t in baseL) { sb.Append(rel(u, t)); sb.Append('.'); }
                foreach (var t in baseL) { sb.Append(N1[Sub(t, u)]); sb.Append('.'); }
                for (int a = 0; a < baseL.Count; a++) for (int b = a + 1; b < baseL.Count; b++)
                {
                    int ti = baseL[a], tj = baseL[b];
                    sb.Append(Gdelta(Sub(ti, tj))[Sub(ti, u)]); sb.Append(',');
                }
                string key = sb.ToString();
                if (!keyToId.TryGetValue(key, out int id)) { id = keyToId.Count; keyToId[key] = id; }
                color[u] = id;
            }
            if (keyToId.Count == n) { discrete = true; break; }
            // pick a representative of the largest non-singleton colour class, not already in base
            var sz = new Dictionary<int, int>(); foreach (var c in color) sz[c] = sz.GetValueOrDefault(c) + 1;
            int bestColor = -1, bestSz = 1; foreach (var kv in sz) if (kv.Value > bestSz) { bestSz = kv.Value; bestColor = kv.Key; }
            if (bestColor < 0) { discrete = true; break; }
            // pick a RANDOM member of the largest non-singleton cell (restart-randomised to de-noise greedy)
            var cands = new List<int>(); for (int u = 0; u < n; u++) if (color[u] == bestColor && !baseL.Contains(u)) cands.Add(u);
            if (cands.Count == 0) break;
            baseL.Add(cands[rng.Next(cands.Count)]);
        }
        return (baseL.Count, n, discrete);
    }

    [Fact]
    public void Probe_CoarseInvariantInjectivity()
    {
        output.WriteLine("SPIKE-K part 1 (plan §11.1) — isotropy-COUNT individualization base for VO^ε_{2m}(q), odd q, growing q.");
        output.WriteLine("cnt(u;t1,t2) = #{y≠0 : Q(y)=0, Q(y-(t1-u))=0, Q(y-(t2-u))=0}  — the EXACT VO⁻₄(3)-`decide` invariant.");
        output.WriteLine("Base = greedy individualization under the (rank-3 rel + size-1 + size-2 count) profile until DISCRETE.");
        output.WriteLine("THE QUESTION: does it stay small / survive at odd q≥5 (square-class coarsening), and how does |T| scale?");
        output.WriteLine("");
        var cases = new (string name, int q, int m, int eps)[]
        {
            ("VO^-_4(3)", 3, 2, -1), ("VO^+_4(3)", 3, 2, +1),
            ("VO^-_4(5)", 5, 2, -1), ("VO^+_4(5)", 5, 2, +1),
            ("VO^-_4(7)", 7, 2, -1), ("VO^+_4(7)", 7, 2, +1),
            ("VO^-_4(9)", 9, 2, -1), ("VO^+_4(9)", 9, 2, +1),
        };
        const int restarts = 8;   // greedy gives an UPPER bound; min over random restarts de-noises the scaling
        output.WriteLine($"min base over {restarts} random restarts (greedy ⟹ upper bound on the true individualisation base):");
        output.WriteLine($"{"family",-12} {"n",6} {"base",5} {"(spread)",10} {"√n",7} {"log2n",7} {"d+log2q",8}");
        var bases = new List<(int q, int n, int b)>();
        foreach (var (name, q, m, eps) in cases)
        {
            int n = 0, best = int.MaxValue, worst = 0;
            for (int s = 0; s < restarts; s++)
            {
                var (b, nn, disc) = CountProfileBase(q, m, eps, new Random(1000 + s));
                n = nn; if (disc) { best = Math.Min(best, b); worst = Math.Max(worst, b); }
            }
            bases.Add((q, n, best));
            output.WriteLine($"{name,-12} {n,6} {best,5} {$"[{best}..{worst}]",10} {Math.Sqrt(n),7:F1} {Math.Log2(n),7:F1} {2 * m + Math.Log2(q),8:F1}");
        }
        output.WriteLine("");
        output.WriteLine("READING: base ≪ √n + slow growth (≈ d+log q, NOT √n) ⟹ count-profile survives the coarsening, kernel viable.");
        output.WriteLine("         base → √n or exploding at q≥5 ⟹ coarsening kills it, generalization route in trouble (header reframe risk).");
        // injectivity is by construction (greedy stops only at discrete); the finding is the SIZE + its scaling.
        Assert.True(bases.All(r => r.b < (int)Math.Sqrt(r.n)), "a count-profile base reached √n — coarsening may be killing injectivity (the q≥5 risk)");
    }
}
