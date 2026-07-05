using System.Collections.Generic;
using System.Linq;

namespace Canonizer
{
    // Route C — C4 (Aut-free coordinatization, the piece that unblocks C3's d-scaling). See
    // docs/chain-descent-route-c-plan.md §9.2.2 (C4) / §7a R1. F1 as built coordinatizes from
    // T = O_p(Aut) — it CONSUMES a harvested Aut (the open T0 problem). C4 recovers the geometry
    // from ADJACENCY ALONE, so recognition no longer needs the descent's harvest (the value-prop
    // §9.2.0 "d-scalability" leg).
    //
    // LANDED (this file): the enabling step validated by route_c_bootstrap_probe.py — recover the
    // isotropic LINES through a vertex o from adjacency alone, via the local invariant
    // |N(o) ∩ N(x) ∩ N(y)| that separates collinear from non-collinear isotropic triangles. The
    // recovered line-directions span V (checked in the probe + the C4 test).
    //
    // REMAINING (scoped, not built): the full coordinate assignment — labelling the p points on each
    // line as scalar multiples (Von Staudt cross-ratio / the fundamental theorem of projective
    // geometry) and reading a vertex's coordinates off the parallel-line grid (Buekenhout–Shult, poly
    // + citable for rank ≥ 3 i.e. d ≥ 6; d = 4 is the special GQ case). This is what turns the line
    // geometry into an AffineStructure; until it lands, C3's wire uses F1's harvest at small d.
    internal static class GeometricCoordinatizer
    {
        // ── Harvest-free canonical INVARIANT recovery ────────────────────────────
        //
        // KEY (2026-07-04): the affine-polar iso-type (q, m, eps) — hence C3's whole answer (the
        // standard canonical graph + closed-form |Aut|) — needs NO coordinatization: it is fixed by
        // (n, valency, strong-regularity) alone. n = q^{2m} pins q,m; the valency
        // k = (q^m - eps)(q^{m-1} + eps) pins eps. So the d-scaling concern for the ANSWER is
        // resolved WITHOUT the Aut harvest / full geometric coordinatization. (Coordinatization is
        // still needed only for the safety CONFIRMATION — distinguishing a genuine VO graph from a
        // hypothetical parameter-mate SRG; that is the remaining C4 work.)
        //
        // Returns false if `adj` is not strongly regular, or n is not q^{2m} with a valency matching
        // some VO^eps. Uses adjacency ALONE (no PermutationGroup, no AffineStructure).
        public static bool RecoverAffinePolarInvariant(int[] adj, int n, out int q, out int m, out int eps)
        {
            q = m = 0; eps = 0;
            if (!FormsGraphClassifier.StronglyRegular(adj, n, out int k, out _, out _)) return false;
            if (!PrimePower(n, out int p, out int d) || d % 2 != 0 || d < 4) return false;
            int mm = d / 2, qq = p;
            foreach (int e in new[] { +1, -1 })
            {
                long val = (long)(IntPow(qq, mm) - e) * (IntPow(qq, mm - 1) + e);
                if (val == k) { q = qq; m = mm; eps = e; return true; }
            }
            return false;
        }

        // ── FULL Aut-free coordinatization (odd p) via line-sum constraints ──────────────────────────
        //
        // KEY: an isotropic line of a Cayley forms-graph over F_p is an arithmetic progression
        // {x, x+d, …, x+(p-1)d}; the sum of its p points is p·x + d·p(p-1)/2 ≡ 0 (odd p). So each
        // recovered line gives the LINEAR constraint Σ_{v∈line} coord(v) = 0 — with NO ordering or
        // orientation (the wall that stalled the parallelism approach). The valid coordinate functions
        // are exactly the linear functionals ξ↦⟨ξ,·⟩ (each kills the line-sum since Σ points = 0), so the
        // solution space of {f(o)=0, Σ_line f = 0} is (for a rich enough line system) exactly d-dimensional,
        // and ANY basis f_1..f_d gives a valid coordinatization coord(w) = (f_1(w),…,f_d(w)) — HARVEST-FREE.
        //
        // The line-sum solution space is {linear functionals} ⊕ {cone-blind functions}: the quadratic
        // form Q itself satisfies every isotropic-line-sum (Σ Q over a line = 2Q(d) = 0 since Q(d)=0), and
        // for larger p so do more functions (nullDim = d + A, A the cone-blind ambiguity; measured A=1 for
        // p=3, A=45 for p=5 at d=4). So the linear part is not immediately isolated — the CONE-BLINDNESS
        // obstruction (the graph is blind to Q's off-cone values). We isolate the linear part by a SHEAR
        // SEARCH over the ambiguity: the true coordinatization is the unique complement (mod the cone-blind
        // subspace) that RECONSTRUCTS the form (only linear coords make adjacency a clean Cayley quadric).
        // Feasible only when the search p^{d·A} is small (A=1 ⟹ p^d, e.g. 81 for p=3) — so this delivers
        // harvest-free coordinatization for the small-ambiguity regime (VO±₄(3)) and DECLINES otherwise.
        //
        // Returns an AffineStructure (coords) from adjacency ALONE, or null if p even / under-determined /
        // the ambiguity search is infeasible / no shear reconstructs.
        public static AffineStructureRecovery.AffineStructure? CoordinatizeByLineSums(int[] adj, int n)
        {
            if (!PrimePower(n, out int p, out int dim) || p == 2) return null;

            var lines = RecoverAllIsotropicLines(adj, n, p);
            if (lines.Count == 0) return null;

            // S = solution space of {f(0)=0, Σ_{v∈line} f = 0}.
            var rows = new List<int[]>();
            var origin = new int[n]; origin[0] = 1; rows.Add(origin);
            foreach (var line in lines) { var r = new int[n]; foreach (int v in line) r[v] = 1; rows.Add(r); }
            var S = NullSpaceModP(rows, n, p);
            if (S.Count < dim) return null;

            int amb = S.Count - dim;                       // cone-blind ambiguity dimension
            long search = 1;
            for (int i = 0; i < dim * amb && search <= 200000; i++) search *= p;
            if (search > 200000) return null;              // infeasible (large-p cone-blind ambiguity)

            // A = the cone-blind subspace = solutions vanishing on the whole cone N(o) (contains Q).
            var coneRows = new List<int[]>(rows);
            for (int w = 0; w < n; w++) if (adj[0 * n + w] == 1) { var r = new int[n]; r[w] = 1; coneRows.Add(r); }
            var A = NullSpaceModP(coneRows, n, p);
            if (A.Count != amb) return null;

            // C = a complement of A in S (dim = dim). Greedily take S-vectors independent of A ∪ chosen.
            var C = new List<int[]>();
            var span = new List<int[]>(A);
            foreach (var s in S) { if (C.Count == dim) break; if (Independent(span, s, p)) { C.Add(s); span.Add(s); } }
            if (C.Count != dim) return null;

            // shear search: coords_φ(w) = C_i(w) + Σ_j φ[i,j]·A_j(w); the reconstructing φ is the linear part.
            var phi = new int[dim * amb];
            while (true)
            {
                var coords = new int[n][];
                var seen = new HashSet<string>();
                bool injective = true;
                for (int w = 0; w < n; w++)
                {
                    var c = new int[dim];
                    for (int i = 0; i < dim; i++)
                    {
                        long v = C[i][w];
                        for (int j = 0; j < amb; j++) v += (long)phi[i * amb + j] * A[j][w];
                        c[i] = (int)(((v % p) + p) % p);
                    }
                    coords[w] = c;
                    if (!seen.Add(string.Join(",", c))) { injective = false; break; }
                }
                if (injective)
                {
                    var aff = new AffineStructureRecovery.AffineStructure
                    { Translations = new PermutationGroup(n), Origin = 0, P = p, Dim = dim, Coords = coords };
                    if (Reconstructs(adj, n, aff)) return aff;
                }
                // increment φ (base-p odometer)
                int k = 0;
                for (; k < phi.Length; k++) { if (++phi[k] < p) break; phi[k] = 0; }
                if (k == phi.Length) break;
            }
            return null;
        }

        // The recovered coords make the graph a quadric Cayley graph: RecoverForm + full reconstruction.
        static bool Reconstructs(int[] adj, int n, AffineStructureRecovery.AffineStructure aff)
        {
            var Q = QuadraticFormRecovery.RecoverForm(adj, n, aff);
            if (Q is null) return false;
            int p = aff.P, dim = aff.Dim; var d = new int[dim];
            for (int x = 0; x < n; x++)
                for (int y = x + 1; y < n; y++)
                {
                    for (int i = 0; i < dim; i++) d[i] = ((aff.Coords[x][i] - aff.Coords[y][i]) % p + p) % p;
                    if ((Q.Evaluate(d) == 0) != (adj[x * n + y] == 1)) return false;
                }
            return true;
        }

        // whether `v` is linearly independent of `basis` over F_p (append-and-rank).
        static bool Independent(List<int[]> basis, int[] v, int p)
        {
            var test = new List<int[]>(basis) { v };
            return Rank(test, p) == basis.Count + 1;
        }

        static int Rank(List<int[]> vs, int p)
        {
            if (vs.Count == 0) return 0;
            int ncols = vs[0].Length;
            var A = vs.Select(r => (int[])r.Clone()).ToList();
            int rank = 0;
            for (int c = 0; c < ncols && rank < A.Count; c++)
            {
                int piv = -1;
                for (int i = rank; i < A.Count; i++) if (A[i][c] % p != 0) { piv = i; break; }
                if (piv < 0) continue;
                (A[rank], A[piv]) = (A[piv], A[rank]);
                int inv = ModInv(((A[rank][c] % p) + p) % p, p);
                for (int cc = 0; cc < ncols; cc++) A[rank][cc] = ((A[rank][cc] * inv) % p + p) % p;
                for (int i = 0; i < A.Count; i++)
                    if (i != rank && A[i][c] % p != 0)
                    {
                        int f = A[i][c];
                        for (int cc = 0; cc < ncols; cc++)
                            A[i][cc] = (int)((((long)A[i][cc] - (long)f * A[rank][cc]) % p + (long)p * p) % p);
                    }
                rank++;
            }
            return rank;
        }

        // The full line-sum solution space basis (coordinate-function candidates), for analysis.
        public static List<int[]> LineSumSolutionSpace(int[] adj, int n)
        {
            if (!PrimePower(n, out int p, out _)) return new List<int[]>();
            var lines = RecoverAllIsotropicLines(adj, n, p);
            var rows = new List<int[]>();
            var origin = new int[n]; origin[0] = 1; rows.Add(origin);
            foreach (var line in lines) { var r = new int[n]; foreach (int v in line) r[v] = 1; rows.Add(r); }
            return NullSpaceModP(rows, n, p);
        }

        // Diagnostic: (number of recovered lines, null-space dimension of the line-sum system).
        public static (int lines, int nullDim) LineSumDiagnostic(int[] adj, int n)
        {
            if (!PrimePower(n, out int p, out _)) return (0, -1);
            var lines = RecoverAllIsotropicLines(adj, n, p);
            var rows = new List<int[]>();
            var origin = new int[n]; origin[0] = 1; rows.Add(origin);
            foreach (var line in lines) { var r = new int[n]; foreach (int v in line) r[v] = 1; rows.Add(r); }
            return (lines.Count, NullSpaceModP(rows, n, p).Count);
        }

        // All isotropic lines of the graph (each a full p-point line, vertex-index list), recovered from
        // adjacency alone by grouping every vertex's cone into lines and deduping.
        public static List<List<int>> RecoverAllIsotropicLines(int[] adj, int n, int p)
        {
            var seen = new HashSet<string>();
            var all = new List<List<int>>();
            for (int o = 0; o < n; o++)
                foreach (var grp in RecoverIsotropicLines(adj, n, o))
                {
                    var line = new List<int>(grp) { o };
                    line.Sort();
                    var key = string.Join(",", line);
                    if (seen.Add(key)) all.Add(line);
                }
            return all;
        }

        // Null space basis of the F_p system with rows `rows` over `ncols` variables.
        static List<int[]> NullSpaceModP(List<int[]> rows, int ncols, int p)
        {
            var A = rows.Select(r => (int[])r.Clone()).ToList();
            int nrows = A.Count;
            var pivotCol = new List<int>();
            var isPivot = new bool[ncols];
            int rr = 0;
            for (int c = 0; c < ncols && rr < nrows; c++)
            {
                int piv = -1;
                for (int i = rr; i < nrows; i++) if (A[i][c] % p != 0) { piv = i; break; }
                if (piv < 0) continue;
                (A[rr], A[piv]) = (A[piv], A[rr]);
                int inv = ModInv(((A[rr][c] % p) + p) % p, p);
                for (int cc = 0; cc < ncols; cc++) A[rr][cc] = ((A[rr][cc] * inv) % p + p) % p;
                for (int i = 0; i < nrows; i++)
                    if (i != rr && A[i][c] % p != 0)
                    {
                        int f = A[i][c];
                        for (int cc = 0; cc < ncols; cc++)
                            A[i][cc] = (int)((((long)A[i][cc] - (long)f * A[rr][cc]) % p + (long)p * p) % p);
                    }
                isPivot[c] = true; pivotCol.Add(c); rr++;
            }
            var basis = new List<int[]>();
            for (int c = 0; c < ncols; c++)
            {
                if (isPivot[c]) continue;
                var vec = new int[ncols];
                vec[c] = 1;
                for (int i = 0; i < pivotCol.Count; i++) vec[pivotCol[i]] = ((-A[i][c]) % p + p) % p;
                basis.Add(vec);
            }
            return basis;
        }

        static int ModInv(int a, int p) { a = ((a % p) + p) % p; int r = 1; for (int i = 0; i < p - 2; i++) r = r * a % p; return r; }

        // The isotropic lines through vertex `o`, recovered from `adj` alone (no Aut). Each returned
        // line is the list of the OTHER p-1 vertices on it (all in N(o)); o itself is excluded. A line
        // through o is a maximal set of cone points that are pairwise "collinear per the invariant".
        public static List<List<int>> RecoverIsotropicLines(int[] adj, int n, int o)
        {
            var No = new List<int>();
            for (int w = 0; w < n; w++) if (adj[o * n + w] == 1) No.Add(w);
            var noSet = new HashSet<int>(No);

            // neighbour sets (within the graph) for the cone points, for the ∩ invariant
            var nbr = new Dictionary<int, HashSet<int>>();
            foreach (int x in No)
            {
                var s = new HashSet<int>();
                for (int w = 0; w < n; w++) if (adj[x * n + w] == 1) s.Add(w);
                nbr[x] = s;
            }

            // invariant over isotropic triangles (o,x,y): inv = |N(o) ∩ N(x) ∩ N(y)|
            int Inv(int x, int y)
            {
                int c = 0;
                var (small, big) = nbr[x].Count < nbr[y].Count ? (nbr[x], nbr[y]) : (nbr[y], nbr[x]);
                foreach (int w in small) if (noSet.Contains(w) && big.Contains(w)) c++;
                return c;
            }

            // collect the invariant of every triangle, then split at the largest gap: collinear =
            // the top value-cluster (the probe shows a clean separation).
            var pairs = new List<(int x, int y, int inv)>();
            for (int i = 0; i < No.Count; i++)
                for (int j = i + 1; j < No.Count; j++)
                {
                    int x = No[i], y = No[j];
                    if (nbr[x].Contains(y)) pairs.Add((x, y, Inv(x, y)));
                }
            if (pairs.Count == 0) return new List<List<int>>();
            int threshold = CollinearThreshold(pairs.Select(t => t.inv));

            // union-find cone points joined by a collinear-per-invariant adjacent pair
            var parent = new Dictionary<int, int>();
            foreach (int v in No) parent[v] = v;
            int Find(int a) { while (parent[a] != a) { parent[a] = parent[parent[a]]; a = parent[a]; } return a; }
            void Union(int a, int b) { parent[Find(a)] = Find(b); }
            foreach (var (x, y, inv) in pairs) if (inv >= threshold) Union(x, y);

            var lines = new Dictionary<int, List<int>>();
            foreach (int v in No) { int r = Find(v); if (!lines.ContainsKey(r)) lines[r] = new List<int>(); lines[r].Add(v); }
            return lines.Values.Select(l => { l.Sort(); return l; }).ToList();
        }

        // The collinearity threshold: the smallest value of the top cluster, found by the largest gap
        // in the sorted distinct invariant values. (Collinear triangles cluster at high invariant.)
        static int CollinearThreshold(IEnumerable<int> invs)
        {
            var distinct = invs.Distinct().OrderBy(x => x).ToList();
            if (distinct.Count <= 1) return distinct.Count == 1 ? distinct[0] : 0;
            int bestGap = -1, splitAt = distinct[0];
            for (int i = 1; i < distinct.Count; i++)
            {
                int gap = distinct[i] - distinct[i - 1];
                if (gap > bestGap) { bestGap = gap; splitAt = distinct[i]; }
            }
            return splitAt;   // collinear ⟺ inv ≥ splitAt (top cluster)
        }

        static bool PrimePower(int n, out int p, out int d)
        {
            p = 0; d = 0;
            if (n < 2) return false;
            int cand = 2;
            while (n % cand != 0) cand++;
            int m = n, e = 0;
            while (m % cand == 0) { m /= cand; e++; }
            if (m != 1) return false;
            p = cand; d = e; return true;
        }

        static int IntPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }
    }
}
