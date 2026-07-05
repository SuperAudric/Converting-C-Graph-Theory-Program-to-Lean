using System;
using System.Collections.Generic;
using System.Linq;

namespace Canonizer
{
    // Route C — the SUZUKI–TITS ovoid construction (char-2, q = 2^{2e+1}). Ports the validated probe
    // route_c_suzuki_probe.py: GF(q), the Tits endomorphism σ (σ²=Frob), the Tits ovoid O, the cone
    // (connection set), the standard VSz(q) Cayley graph on GF(q)^4 = F₂^{4k}, and TWO form validations —
    //   (a) the σ-twisted GF(q) type-(1,2) forms whose joint zero = cone (the Lean suzukiAdapter's SF_k), and
    //   (b) the FIELD-AGNOSTIC F₂ degree signature (cone is cut by cubics but NOT by quadrics) — the sound
    //       discriminator vs the cospectral affine-polar mate VO⁻₄(q) (whose cone IS quadric-cut).
    //
    // FEASIBILITY: only q=8 (n=4096) is instantiable in the dense n×n infrastructure (q=32 ⟹ n=2^20).
    // q=2 is degenerate (Sz(2) solvable). So q=8 is the sole genuine, buildable Suzuki instance; the code
    // is written general in k for clarity but only k=3 is runnable and primitive-poly-registered.
    internal static class SuzukiOvoid
    {
        // ── GF(2^k), primitive polynomial per k (low-bit = constant term) ──────────────────────────────
        // k=3 (q=8): x³+x+1 = 0b1011.  (Others can be added when/if a larger case ever becomes feasible.)
        internal sealed class Gf
        {
            public readonly int K, Q, Poly;
            readonly int[] _exp, _log;
            public Gf(int k)
            {
                K = k; Q = 1 << k;
                Poly = k switch { 3 => 0b1011, _ => throw new NotSupportedException($"GF(2^{k}) primitive poly not registered (only k=3 is feasible for VSz).") };
                _exp = new int[Q]; _log = new int[Q];
                int x = 1;
                for (int i = 0; i < Q - 1; i++) { _exp[i] = x; _log[x] = i; x = MulRaw(x, 2); }
            }
            int MulRaw(int a, int b)
            {
                int r = 0;
                while (b != 0) { if ((b & 1) != 0) r ^= a; b >>= 1; a <<= 1; if ((a & Q) != 0) a ^= Poly; }
                return r;
            }
            public int Mul(int a, int b) => (a == 0 || b == 0) ? 0 : _exp[(_log[a] + _log[b]) % (Q - 1)];
            public int Pow(int a, int e) { if (a == 0) return 0; e %= (Q - 1); if (e < 0) e += Q - 1; return _exp[(_log[a] * e) % (Q - 1)]; }
            public int Inv(int a) => _exp[(Q - 1 - _log[a]) % (Q - 1)];
            // Tits endomorphism σ(x) = x^{2^{e+1}} where k = 2e+1, so σ² = Frobenius (x↦x²). k=3 ⟹ σ(x)=x⁴.
            public int Sigma(int a) { int e = (K - 1) / 2; return Pow(a, 1 << (e + 1)); }
            public int Frob(int a) => Mul(a, a);
        }

        // ── the Tits ovoid, its cone, and the packed F₂^{4k} index encoding ────────────────────────────
        // pack(v0..v3) = v0 | v1<<k | v2<<2k | v3<<3k ; GF(q)^4 additive = 4k-bit XOR, so the vector
        // difference of two vertices is the XOR of their packed indices ⟹ VSz(q) = Cayley on (Z/2)^{4k}.
        static int Pack(Gf g, int[] v) => v[0] | (v[1] << g.K) | (v[2] << (2 * g.K)) | (v[3] << (3 * g.K));
        static int[] Unpack(Gf g, int idx) { int m = g.Q - 1; return new[] { idx & m, (idx >> g.K) & m, (idx >> (2 * g.K)) & m, (idx >> (3 * g.K)) & m }; }

        // O = {(1,a,b, ab + σ(a)a² + σ(b)) : a,b ∈ GF(q)} ∪ {(0,0,0,1)} ; |O| = q²+1.
        static List<int[]> Ovoid(Gf g)
        {
            var pts = new List<int[]>();
            for (int a = 0; a < g.Q; a++)
                for (int b = 0; b < g.Q; b++)
                {
                    int c = g.Mul(a, b) ^ g.Mul(g.Sigma(a), g.Mul(a, a)) ^ g.Sigma(b);
                    pts.Add(new[] { 1, a, b, c });
                }
            pts.Add(new[] { 0, 0, 0, 1 });
            return pts;
        }

        // The cone = GF(q)^* · O (nonzero scalar multiples of ovoid points), packed. |cone| = (q²+1)(q−1).
        public static HashSet<int> Cone(Gf g)
        {
            var cone = new HashSet<int>();
            foreach (var o in Ovoid(g))
                for (int lam = 1; lam < g.Q; lam++)
                    cone.Add(Pack(g, new[] { g.Mul(lam, o[0]), g.Mul(lam, o[1]), g.Mul(lam, o[2]), g.Mul(lam, o[3]) }));
            cone.Remove(0);
            return cone;
        }

        // The standard VSz(q) graph: Cayley on F₂^{4k} with u~v iff (u⊕v) ∈ cone. Dense; feasible q=8 only.
        public static int[] StandardGraph(int q)
        {
            var g = new Gf(Log2(q));
            var cone = Cone(g);
            int dim = 4 * g.K, n = 1 << dim;
            // predicate over an F₂^dim difference vector: pack to a dim-bit index, test cone membership.
            return FormsGraphBuilder.StandardCayleyGraph(2, dim, d =>
            {
                int idx = 0; for (int i = 0; i < dim; i++) idx |= (d[i] & 1) << i;
                return cone.Contains(idx);
            });
        }

        // ── (a) the σ-twisted GF(q) type-(1,2) forms σ(x_a)·x_b·x_c whose JOINT zero = cone (Lean model) ─
        // Returns the nullspace basis (over GF(q)) of forms vanishing on the whole cone, and whether their
        // joint zero over GF(q)^4 equals cone∪{0}. This validates the Lean adapter's SF_k form family.
        public static (int basisDim, bool jointZeroIsCone) SigmaFormModel(int q)
        {
            var g = new Gf(Log2(q));
            var cone = Cone(g);
            var mono = Mono12();                                        // 40 type-(1,2) monomials (a; b≤c)
            var rows = cone.Select(idx => { var v = Unpack(g, idx); return mono.Select(m => MonoVal(g, m, v)).ToArray(); }).ToList();
            var basis = GfNullspace(g, rows, mono.Count);
            int n = 1 << (4 * g.K);
            var joint = new HashSet<int>();
            for (int idx = 0; idx < n; idx++) { var v = Unpack(g, idx); if (basis.All(c => FormVal(g, mono, c, v) == 0)) joint.Add(idx); }
            var want = new HashSet<int>(cone) { 0 };
            return (basis.Count, joint.SetEquals(want));
        }

        static List<(int a, int b, int c)> Mono12()
        {
            var m = new List<(int, int, int)>();
            for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) for (int c = b; c < 4; c++) m.Add((a, b, c));
            return m;
        }
        static int MonoVal(Gf g, (int a, int b, int c) m, int[] v) => g.Mul(g.Sigma(v[m.a]), g.Mul(v[m.b], v[m.c]));
        static int FormVal(Gf g, List<(int a, int b, int c)> mono, int[] coef, int[] v)
        { int s = 0; for (int j = 0; j < mono.Count; j++) if (coef[j] != 0) s ^= g.Mul(coef[j], MonoVal(g, mono[j], v)); return s; }

        // GF(q) nullspace (forms coef with rows·coef = 0): RREF then free-variable basis.
        static List<int[]> GfNullspace(Gf g, List<int[]> rows, int cols)
        {
            var M = rows.Select(r => (int[])r.Clone()).ToList();
            int R = M.Count, rank = 0; var piv = new List<int>();
            for (int col = 0; col < cols && rank < R; col++)
            {
                int p = -1; for (int i = rank; i < R; i++) if (M[i][col] != 0) { p = i; break; }
                if (p < 0) continue;
                (M[rank], M[p]) = (M[p], M[rank]);
                int inv = g.Inv(M[rank][col]);
                for (int j = 0; j < cols; j++) M[rank][j] = g.Mul(M[rank][j], inv);
                for (int i = 0; i < R; i++) if (i != rank && M[i][col] != 0) { int f = M[i][col]; for (int j = 0; j < cols; j++) M[i][j] ^= g.Mul(f, M[rank][j]); }
                piv.Add(col); rank++;
            }
            var pivSet = new HashSet<int>(piv); var basis = new List<int[]>();
            for (int free = 0; free < cols; free++)
            {
                if (pivSet.Contains(free)) continue;
                var vec = new int[cols]; vec[free] = 1;
                for (int r = 0; r < piv.Count; r++) vec[piv[r]] = M[r][free];   // −x = x in char 2
                basis.Add(vec);
            }
            return basis;
        }

        // ── (b) FIELD-AGNOSTIC F₂ degree signature (the sound Confirm discriminator) ────────────────────
        // Does the multilinear-F₂-form space of degree ≤ maxDeg vanishing on `cone` have joint zero exactly
        // cone∪{0} over F₂^dim? VO⁻₄(q) cone is quadric-cut (maxDeg 2 already true); the Tits-ovoid cone is
        // genuinely cubic (maxDeg 2 FALSE, maxDeg 3 TRUE). So Suzuki ⟺ !CutByForms(2) && CutByForms(3).
        // `cone` = the neighbours-of-origin difference vectors (each an F₂^dim vector). Basis-invariant
        // (a linear change of the F₂ coords preserves monomial degree), so it needs no field alignment.
        public static bool CutByForms(IReadOnlyList<int[]> cone, int dim, int maxDeg)
        {
            var mono = Monomials(dim, maxDeg);                          // multilinear index-sets, degree 1..maxDeg
            // rows = cone vectors evaluated on each monomial (AND of the selected bits), over F₂.
            var rows = cone.Select(v => mono.Select(mask => EvalMono(mask, v) ? 1 : 0).ToArray()).ToList();
            var basis = F2Nullspace(rows, mono.Count);                  // forms vanishing on the whole cone
            if (basis.Count == 0) return false;
            int n = 1 << dim;
            // joint zero over F₂^dim must equal cone∪{0} (all these homogeneous forms already vanish at 0).
            var coneSet = new HashSet<int>(cone.Select(PackBits)) { 0 };
            for (int idx = 0; idx < n; idx++)
            {
                var v = BitsOf(idx, dim);
                bool allZero = basis.All(c => FormValF2(mono, c, v) == 0);
                if (allZero != coneSet.Contains(idx)) return false;     // joint zero ≠ cone∪{0}
            }
            return true;
        }

        static List<int[]> Monomials(int dim, int maxDeg)
        {
            var res = new List<int[]>();
            void Rec(int start, List<int> cur)
            {
                if (cur.Count >= 1) res.Add(cur.ToArray());
                if (cur.Count == maxDeg) return;
                for (int i = start; i < dim; i++) { cur.Add(i); Rec(i + 1, cur); cur.RemoveAt(cur.Count - 1); }
            }
            Rec(0, new List<int>());
            return res;
        }
        static bool EvalMono(int[] vars, int[] v) { foreach (int i in vars) if ((v[i] & 1) == 0) return false; return true; }
        static int FormValF2(List<int[]> mono, int[] coef, int[] v)
        { int s = 0; for (int j = 0; j < mono.Count; j++) if (coef[j] != 0 && EvalMono(mono[j], v)) s ^= 1; return s; }

        static List<int[]> F2Nullspace(List<int[]> rows, int cols)
        {
            var M = rows.Select(r => (int[])r.Clone()).ToList();
            int R = M.Count, rank = 0; var piv = new List<int>();
            for (int col = 0; col < cols && rank < R; col++)
            {
                int p = -1; for (int i = rank; i < R; i++) if (M[i][col] != 0) { p = i; break; }
                if (p < 0) continue;
                (M[rank], M[p]) = (M[p], M[rank]);
                for (int i = 0; i < R; i++) if (i != rank && M[i][col] != 0) for (int j = 0; j < cols; j++) M[i][j] ^= M[rank][j];
                piv.Add(col); rank++;
            }
            var pivSet = new HashSet<int>(piv); var basis = new List<int[]>();
            for (int free = 0; free < cols; free++)
            {
                if (pivSet.Contains(free)) continue;
                var vec = new int[cols]; vec[free] = 1;
                for (int r = 0; r < piv.Count; r++) vec[piv[r]] = M[r][free];
                basis.Add(vec);
            }
            return basis;
        }

        // The neighbours-of-origin difference vectors in F₂ coordinates (the cone, in the recovered basis).
        public static List<int[]> ConeFromGraph(int[] adj, int n, AffineStructureRecovery.AffineStructure aff)
        {
            int origin = aff.Origin;
            var cone = new List<int[]>();
            for (int v = 0; v < n; v++) if (v != origin && adj[origin * n + v] == 1) cone.Add(aff.Coords[v]);
            return cone;
        }

        // The Suzuki discriminator: the cone is genuinely CUBIC over F₂ (not quadric-cut) — separates VSz(q)
        // from its cospectral affine-polar mate VO⁻₄(q) (quadric-cut). Basis-invariant, field-agnostic.
        public static bool IsOvoidConeBySignature(IReadOnlyList<int[]> cone, int dim) =>
            !CutByForms(cone, dim, 2) && CutByForms(cone, dim, 3);

        static int PackBits(int[] v) { int idx = 0; for (int i = 0; i < v.Length; i++) idx |= (v[i] & 1) << i; return idx; }
        static int[] BitsOf(int idx, int dim) { var v = new int[dim]; for (int i = 0; i < dim; i++) v[i] = (idx >> i) & 1; return v; }

        static int Log2(int q) { int k = 0; while ((1 << k) < q) k++; if ((1 << k) != q) throw new ArgumentException($"q={q} is not a power of two."); return k; }
    }
}
