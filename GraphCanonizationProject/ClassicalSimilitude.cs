using System;
using System.Collections.Generic;

namespace Canonizer
{
    // Route C — C1b support: construct a NON-SQUARE-factor similitude of the recovered
    // quadratic form Q, the index-2 generator missing from {reflections (O(Q)) + scalar
    // scalings (square factors)}. Without it the built group is the wrong (index-2) subgroup
    // (the order-check ratio is exactly 2 = [F_p^* : squares]). See docs/chain-descent-route-c-plan.md §9.2.2.
    //
    // Method (uniform over O^+ / O^- and all odd p): congruence-diagonalize Q's polar form,
    // rescale each diagonal coefficient to its square-class rep {1, ν} (ν a fixed non-square),
    // then build a factor-ν block map in the diagonal coordinates and conjugate back.
    //   - a same-class pair <c,c>: rotation [[a,b],[-b,a]] with a²+b²=ν scales it by ν.
    //   - a mixed pair <1,ν>: the swap [[0,ν],[1,0]] scales it by ν.
    // Even dim ⟹ disc(μQ)=μ^{even}disc(Q) ⟹ μQ ≅ Q for every μ, so a factor-ν similitude
    // always exists; the block construction realizes one.
    internal static class ClassicalSimilitude
    {
        // A non-square-factor similitude of Q, as a vertex permutation (linear map on coords).
        // Returns null only if Q's polar form is degenerate (should not happen for a recovered
        // nondegenerate form) or p = 2.
        public static int[]? NonSquareSimilitudePerm(QuadraticFormRecovery.RecoveredForm Q,
                                                     AffineStructureRecovery.AffineStructure aff)
        {
            int p = aff.P, dim = aff.Dim;
            if (p == 2) return null;
            var g = NonSquareSimilitudeMatrix(Q, aff);
            if (g is null) return null;
            return ToVertexPerm(g, aff);
        }

        // The dim×dim linear map g over F_p with Q(g·x) = ν·Q(x), ν a non-square.
        public static int[][]? NonSquareSimilitudeMatrix(QuadraticFormRecovery.RecoveredForm Q,
                                                         AffineStructureRecovery.AffineStructure aff)
        {
            int p = aff.P, dim = aff.Dim;

            // polar Gram matrix M[i][j] = B(e_i, e_j)
            var M = new int[dim][];
            for (int i = 0; i < dim; i++) { M[i] = new int[dim]; }
            for (int i = 0; i < dim; i++)
                for (int j = 0; j < dim; j++)
                    M[i][j] = Bilin(Q, Unit(dim, i, p), Unit(dim, j, p), p);

            // congruence-diagonalize: Tᵀ M T = D (diagonal), T invertible
            if (!CongruenceDiagonalize(M, p, out int[][] T, out int[] D)) return null;

            int nu = NonSquare(p);
            // rescale each coord so D[i] becomes 1 (square class) or nu (non-square class):
            // scale coord i by s_i with D[i]·s_i² == class-rep. Track class in cls[i] (0=sq,1=nonsq)
            //   D[i] square:      s_i = 1/sqrt(D[i]),  new coeff 1
            //   D[i] non-square:  s_i = sqrt(nu/D[i]), new coeff nu
            var s = new int[dim];
            var cls = new int[dim];
            for (int i = 0; i < dim; i++)
            {
                int di = ((D[i] % p) + p) % p;
                if (di == 0) return null;                 // degenerate
                if (IsSquare(di, p)) { s[i] = ModInv(Sqrt(di, p), p); cls[i] = 0; }
                else { s[i] = Sqrt(Mul(nu, ModInv(di, p), p), p); cls[i] = 1; }
            }

            // R = factor-nu block map in the rescaled diagonal coords (z). Pair coords by class.
            var R = Identity(dim, p);
            var A = new List<int>(); var Bc = new List<int>();
            for (int i = 0; i < dim; i++) (cls[i] == 0 ? A : Bc).Add(i);
            (int a2, int b2) = TwoSquares(nu, p);         // a²+b²=nu

            int ai = 0, bi = 0;
            // if both class-lists are odd, consume one mixed pair <1,nu> first
            if ((A.Count % 2 == 1) && (Bc.Count % 2 == 1))
            {
                int u = A[A.Count - 1], v = Bc[Bc.Count - 1];   // coeff 1 and nu
                // swap map on (u,v): z_u ↦ nu·z_v, z_v ↦ z_u   (scales <1,nu> by nu)
                R[u][u] = 0; R[u][v] = nu;
                R[v][v] = 0; R[v][u] = 1;
                A.RemoveAt(A.Count - 1); Bc.RemoveAt(Bc.Count - 1);
            }
            // pair within each class using the rotation [[a,b],[-b,a]] (factor a²+b²=nu)
            foreach (var list in new[] { A, Bc })
                for (int k = 0; k + 1 < list.Count; k += 2)
                {
                    int u = list[k], v = list[k + 1];
                    R[u][u] = a2; R[u][v] = b2;
                    R[v][u] = ((-b2 % p) + p) % p; R[v][v] = a2;
                }

            // g = (T·Sdiag) · R · (T·Sdiag)⁻¹, Sdiag = diag(s)
            var TS = MatMul(T, Diag(s), p);
            var TSinv = MatInv(TS, p);
            if (TSinv is null) return null;
            var g = MatMul(MatMul(TS, R, p), TSinv, p);
            return g;
        }

        // ── linear algebra mod p ──────────────────────────────────────────────

        static int Bilin(QuadraticFormRecovery.RecoveredForm Q, int[] x, int[] y, int p)
        {
            int dim = x.Length; var s = new int[dim];
            for (int k = 0; k < dim; k++) s[k] = (x[k] + y[k]) % p;
            int b = Q.Evaluate(s) - Q.Evaluate(x) - Q.Evaluate(y);
            return (((b % p) + p) % p);
        }

        // Tᵀ M T = D (diagonal). M is modified in place; T and D are outputs.
        static bool CongruenceDiagonalize(int[][] M, int p, out int[][] T, out int[] D)
        {
            int dim = M.Length;
            T = Identity(dim, p);
            for (int k = 0; k < dim; k++)
            {
                if (M[k][k] % p == 0)
                {
                    int r = -1;
                    for (int i = k + 1; i < dim; i++) if (M[i][i] % p != 0) { r = i; break; }
                    if (r >= 0) { SwapCong(M, T, k, r, p); }
                    else
                    {
                        int c = -1;
                        for (int j = k + 1; j < dim; j++) if (M[k][j] % p != 0) { c = j; break; }
                        if (c < 0) { D = Array.Empty<int>(); return false; }   // degenerate
                        AddColCong(M, T, c, k, 1, p);      // col_k += col_c ⟹ M[k][k] = 2 M[k][c] ≠ 0
                    }
                }
                int piv = ((M[k][k] % p) + p) % p;
                int pinv = ModInv(piv, p);
                for (int j = k + 1; j < dim; j++)
                {
                    int mkj = ((M[k][j] % p) + p) % p;
                    if (mkj != 0) AddColCong(M, T, k, j, ((-mkj * pinv) % p + p) % p, p);  // col_j += f·col_k
                }
            }
            D = new int[dim];
            for (int i = 0; i < dim; i++) D[i] = ((M[i][i] % p) + p) % p;
            return true;
        }

        // congruence swap of indices i,j: swap rows i,j and cols i,j of M; swap cols i,j of T.
        static void SwapCong(int[][] M, int[][] T, int i, int j, int p)
        {
            int dim = M.Length;
            (M[i], M[j]) = (M[j], M[i]);
            for (int r = 0; r < dim; r++) (M[r][i], M[r][j]) = (M[r][j], M[r][i]);
            for (int r = 0; r < dim; r++) (T[r][i], T[r][j]) = (T[r][j], T[r][i]);
        }

        // congruence col op: col_dst += f·col_src (and the symmetric row op) on M; col_dst += f·col_src on T.
        static void AddColCong(int[][] M, int[][] T, int src, int dst, int f, int p)
        {
            int dim = M.Length;
            for (int r = 0; r < dim; r++) M[r][dst] = ((M[r][dst] + f * M[r][src]) % p + p) % p;
            for (int r = 0; r < dim; r++) M[dst][r] = ((M[dst][r] + f * M[src][r]) % p + p) % p;
            for (int r = 0; r < dim; r++) T[r][dst] = ((T[r][dst] + f * T[r][src]) % p + p) % p;
        }

        static int[] Unit(int dim, int i, int p) { var e = new int[dim]; e[i] = 1; return e; }

        static int[][] Identity(int dim, int p)
        {
            var I = new int[dim][];
            for (int i = 0; i < dim; i++) { I[i] = new int[dim]; I[i][i] = 1; }
            return I;
        }

        static int[][] Diag(int[] s)
        {
            int dim = s.Length; var D = new int[dim][];
            for (int i = 0; i < dim; i++) { D[i] = new int[dim]; D[i][i] = s[i]; }
            return D;
        }

        static int[][] MatMul(int[][] A, int[][] B, int p)
        {
            int n = A.Length, m = B[0].Length, k = B.Length;
            var C = new int[n][];
            for (int i = 0; i < n; i++)
            {
                C[i] = new int[m];
                for (int j = 0; j < m; j++)
                {
                    long s = 0;
                    for (int t = 0; t < k; t++) s += (long)A[i][t] * B[t][j];
                    C[i][j] = (int)(((s % p) + p) % p);
                }
            }
            return C;
        }

        static int[][]? MatInv(int[][] A, int p)
        {
            int n = A.Length;
            var M = new int[n][];
            for (int i = 0; i < n; i++)
            {
                M[i] = new int[2 * n];
                for (int j = 0; j < n; j++) M[i][j] = ((A[i][j] % p) + p) % p;
                M[i][n + i] = 1;
            }
            for (int c = 0; c < n; c++)
            {
                int piv = -1;
                for (int r = c; r < n; r++) if (M[r][c] % p != 0) { piv = r; break; }
                if (piv < 0) return null;
                (M[c], M[piv]) = (M[piv], M[c]);
                int inv = ModInv(M[c][c], p);
                for (int j = 0; j < 2 * n; j++) M[c][j] = M[c][j] * inv % p;
                for (int r = 0; r < n; r++)
                    if (r != c && M[r][c] % p != 0)
                    {
                        int f = M[r][c];
                        for (int j = 0; j < 2 * n; j++) M[r][j] = (((M[r][j] - f * M[c][j]) % p) + p * p) % p % p;
                    }
            }
            var Inv = new int[n][];
            for (int i = 0; i < n; i++) { Inv[i] = new int[n]; for (int j = 0; j < n; j++) Inv[i][j] = M[i][n + j]; }
            return Inv;
        }

        static int[] ToVertexPerm(int[][] g, AffineStructureRecovery.AffineStructure aff)
        {
            int p = aff.P, dim = aff.Dim, n = aff.Coords.Length;
            var vertexOf = new int[n];
            for (int v = 0; v < n; v++) vertexOf[Encode(aff.Coords[v], p)] = v;
            var perm = new int[n];
            for (int v = 0; v < n; v++)
            {
                var c = aff.Coords[v]; var c2 = new int[dim];
                for (int i = 0; i < dim; i++)
                {
                    long s = 0; for (int j = 0; j < dim; j++) s += (long)g[i][j] * c[j];
                    c2[i] = (int)(((s % p) + p) % p);
                }
                perm[v] = vertexOf[Encode(c2, p)];
            }
            return perm;
        }

        static int Encode(int[] c, int p) { int v = 0, pw = 1; for (int i = 0; i < c.Length; i++) { v += (((c[i] % p) + p) % p) * pw; pw *= p; } return v; }

        // ── field arithmetic mod p ────────────────────────────────────────────

        static int Mul(int a, int b, int p) => (int)(((long)a * b % p + p) % p);
        static int ModInv(int a, int p) { a = ((a % p) + p) % p; int r = 1; for (int i = 0; i < p - 2; i++) r = r * a % p; return r; }

        static bool IsSquare(int a, int p) { a = ((a % p) + p) % p; if (a == 0) return true; for (int x = 1; x < p; x++) if (x * x % p == a) return true; return false; }
        static int Sqrt(int a, int p) { a = ((a % p) + p) % p; for (int x = 0; x < p; x++) if (x * x % p == a) return x; return -1; }
        static int NonSquare(int p) { for (int a = 2; a < p; a++) if (!IsSquare(a, p)) return a; return -1; }

        // a,b with a²+b² = nu (mod p). Exists for all p (every element is a sum of two squares).
        static (int, int) TwoSquares(int nu, int p)
        {
            for (int a = 0; a < p; a++)
                for (int b = 0; b < p; b++)
                    if ((a * a + b * b) % p == ((nu % p) + p) % p) return (a, b);
            return (0, 0);
        }
    }
}
