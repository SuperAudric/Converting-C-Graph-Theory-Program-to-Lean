using System.Collections.Generic;
using System.Linq;

namespace Canonizer
{
    // Route C — A1: recover the quadratic form Q (up to scalar) from the abstract graph.
    // See docs/chain-descent-route-c-plan.md §2b / §6.
    //
    // After F1 (AffineStructureRecovery) coordinatizes the vertices as (F_p)^Dim, the
    // graph's connection set from the origin is the punctured isotropic cone
    // C = { coords[x] : x ~ origin } = { v != 0 : Q(v) = 0 }. The homogeneous degree-2
    // forms vanishing on C form a vector space; for a nondegenerate quadric (Dim >= 3,
    // odd q) that space is 1-dimensional = <Q>, so Q is recovered up to scalar by ONE
    // linear solve — no WL, no orbits (this is exactly what sidesteps the node-4 wall).
    // Probe route_c_reconstruct_probe.py confirmed vanishDim = 1 across all eps/d/q.
    //
    // Odd q only: over F_{2^k} squaring collapses degree, so the degree-2 vanishing space
    // differs (the char-2 track uses Arf, not this solve). RecoverForm returns null when
    // the cone does NOT pin Q up to scalar (kernel dimension != 1).
    internal static class QuadraticFormRecovery
    {
        internal sealed class RecoveredForm
        {
            public required int P { get; init; }
            public required int Dim { get; init; }
            public required (int i, int j)[] Monomials { get; init; }   // x_i x_j, i <= j
            public required int[] Coeffs { get; init; }                 // a_{(i,j)}, up to a global scalar

            // Q(v) = sum_{i<=j} a_{ij} v_i v_j  (mod p).
            public int Evaluate(int[] v)
            {
                long s = 0;
                for (int k = 0; k < Monomials.Length; k++)
                    s += (long)Coeffs[k] * v[Monomials[k].i] * v[Monomials[k].j];
                return (int)(((s % P) + P) % P);
            }
        }

        // The monomials x_i x_j (i <= j) in a fixed order.
        static (int i, int j)[] MonomialsOf(int dim)
        {
            var m = new List<(int, int)>();
            for (int i = 0; i < dim; i++) for (int j = i; j < dim; j++) m.Add((i, j));
            return m.ToArray();
        }

        // Recover Q (up to scalar) from the graph `adj` (flat n*n) using F1's coordinates
        // `aff`. Returns null if q is even (use the char-2 track) or the cone's degree-2
        // vanishing space is not 1-dimensional (Q not uniquely pinned).
        public static RecoveredForm? RecoverForm(int[] adj, int n, AffineStructureRecovery.AffineStructure aff)
        {
            int p = aff.P, dim = aff.Dim, origin = aff.Origin;
            if (p == 2) return null;   // char-2 is a separate (Arf) track

            var monos = MonomialsOf(dim);
            int M = monos.Length;

            // one linear constraint per cone vector: sum a_ij v_i v_j = 0
            var rows = new List<int[]>();
            for (int x = 0; x < n; x++)
                if (x != origin && adj[origin * n + x] == 1)
                {
                    var v = aff.Coords[x];
                    var row = new int[M];
                    for (int k = 0; k < M; k++) row[k] = v[monos[k].i] * v[monos[k].j] % p;
                    rows.Add(row);
                }

            var kernel = NullSpaceModP(rows, M, p);
            if (kernel.Count != 1) return null;                       // cone under-determines Q
            if (kernel[0].All(a => a % p == 0)) return null;          // degenerate (all-zero) — shouldn't happen

            return new RecoveredForm { P = p, Dim = dim, Monomials = monos, Coeffs = kernel[0] };
        }

        // A basis of { c in F_p^ncols : A c = 0 }, where A's rows are `rows`. Row-reduces A
        // to RREF; free columns give the kernel basis by back-substitution.
        static List<int[]> NullSpaceModP(List<int[]> rows, int ncols, int p)
        {
            var A = rows.Select(r => (int[])r.Clone()).ToList();
            int nrows = A.Count;
            var pivotCol = new List<int>();
            var isPivot = new bool[ncols];
            int r = 0;
            for (int c = 0; c < ncols && r < nrows; c++)
            {
                int piv = -1;
                for (int i = r; i < nrows; i++) if (A[i][c] % p != 0) { piv = i; break; }
                if (piv < 0) continue;
                (A[r], A[piv]) = (A[piv], A[r]);
                int inv = ModInv(((A[r][c] % p) + p) % p, p);
                for (int cc = 0; cc < ncols; cc++) A[r][cc] = ((A[r][cc] * inv) % p + p) % p;
                for (int i = 0; i < nrows; i++)
                    if (i != r && A[i][c] % p != 0)
                    {
                        int f = A[i][c];
                        for (int cc = 0; cc < ncols; cc++) A[i][cc] = (((A[i][cc] - f * A[r][cc]) % p) + p * p) % p;
                    }
                isPivot[c] = true; pivotCol.Add(c); r++;
            }
            var basis = new List<int[]>();
            for (int c = 0; c < ncols; c++)
            {
                if (isPivot[c]) continue;                     // free columns only
                var vec = new int[ncols];
                vec[c] = 1;
                for (int i = 0; i < pivotCol.Count; i++) vec[pivotCol[i]] = ((-A[i][c]) % p + p) % p;
                basis.Add(vec);
            }
            return basis;
        }

        static int ModInv(int a, int p) { int r = 1; for (int i = 0; i < p - 2; i++) r = r * a % p; return r; }  // p prime
    }
}
