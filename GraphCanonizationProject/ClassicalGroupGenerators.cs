using System.Collections.Generic;
using System.Linq;

namespace Canonizer
{
    // Route C — C1b (the load-bearing runtime piece): build a generating set for the
    // ANSWER GROUP affineG(similitudeGroup Q) = translations ⋊ AΓO(Q) as int[] permutations
    // of the p^d vertices, from the recovered form Q + F1's coordinates. See
    // docs/chain-descent-route-c-plan.md §9.2.2 (C1b) / §9.2.6.
    //
    // Lean contract (schemeAutGroup_coarse_eq_affineG): the group these generators produce
    // must equal affineG(similitudeGroup Q). The acceptance gate is the ORDER-CHECK: at small d
    // the harness's own harvest (CanonResult.ResidualGroup) delivers the TRUE |Aut|, so
    // Build(...).Order is compared against that harvested order (bootstrap), not a hand-derived
    // closed form. A proper subgroup (missing a similitude) or supergroup (spurious generator)
    // both fail the order-check — the executable form of the group-pinning theorem.
    //
    // Odd q (q = p prime here), single quadratic. Char-2 / multi-form families are separate tracks.
    internal static class ClassicalGroupGenerators
    {
        // Build the answer group for a single quadratic Q over (F_p)^Dim, coordinatized by `aff`.
        // Generators: translations (affine), orthogonal reflections (generate O(Q) by
        // Cartan–Dieudonné), and scalar scalings x↦c·x (the square-factor similitudes).
        public static PermutationGroup Build(QuadraticFormRecovery.RecoveredForm Q,
                                             AffineStructureRecovery.AffineStructure aff)
        {
            int p = aff.P, dim = aff.Dim, n = aff.Coords.Length;
            var G = new PermutationGroup(n);
            foreach (var g in Generators(Q, aff)) G.AddGenerator(g);
            return G;
        }

        // The generator list (before deduping into a PermutationGroup).
        public static List<int[]> Generators(QuadraticFormRecovery.RecoveredForm Q,
                                              AffineStructureRecovery.AffineStructure aff)
        {
            int p = aff.P, dim = aff.Dim, n = aff.Coords.Length;
            var vertexOf = ReverseCoordMap(aff);   // encoded coord -> vertex
            var gens = new List<int[]>();

            // Apply a coord-space map f: (F_p)^dim -> (F_p)^dim as a vertex permutation.
            int[] PermOf(System.Func<int[], int[]> f)
            {
                var perm = new int[n];
                for (int v = 0; v < n; v++) perm[v] = vertexOf[Encode(f(aff.Coords[v]), p)];
                return perm;
            }

            // ── translations x ↦ x + e_i ────────────────────────────────────────
            for (int i = 0; i < dim; i++)
            {
                int ii = i;
                gens.Add(PermOf(c => { var r = (int[])c.Clone(); r[ii] = (r[ii] + 1) % p; return r; }));
            }

            // ── orthogonal reflections r_a(x) = x − (B(x,a)/Q(a))·a, a anisotropic ──
            // r_{λa} = r_a, so dedup by taking a over anisotropic PROJECTIVE points
            // (first nonzero coord normalized to 1).
            foreach (var a in AnisotropicProjectivePoints(Q, aff, p))
            {
                int qa = Q.Evaluate(a);
                int qaInv = ModInv(((qa % p) + p) % p, p);
                var aa = a;
                gens.Add(PermOf(c =>
                {
                    int bxa = Bilin(Q, c, aa, p);
                    int t = bxa * qaInv % p;
                    var r = new int[dim];
                    for (int k = 0; k < dim; k++) r[k] = (((c[k] - t * aa[k]) % p) + p * p) % p % p;
                    return r;
                }));
            }

            // ── scalar scalings x ↦ g·x (g a primitive root) — square-factor similitudes ──
            int g0 = PrimitiveRoot(p);
            gens.Add(PermOf(c => c.Select(v => v * g0 % p).ToArray()));

            // ── the NON-SQUARE-factor similitude (the index-2 generator; AΓO ⊋ AO·squares) ──
            var nsq = ClassicalSimilitude.NonSquareSimilitudePerm(Q, aff);
            if (nsq is not null) gens.Add(nsq);

            return gens;
        }

        // B(x,y) = Q(x+y) − Q(x) − Q(y), the polar bilinear form, mod p.
        static int Bilin(QuadraticFormRecovery.RecoveredForm Q, int[] x, int[] y, int p)
        {
            int dim = x.Length;
            var s = new int[dim];
            for (int k = 0; k < dim; k++) s[k] = (x[k] + y[k]) % p;
            int b = Q.Evaluate(s) - Q.Evaluate(x) - Q.Evaluate(y);
            return (((b % p) + p) % p);
        }

        // Anisotropic projective points: one representative per {λa} class with Q(a) ≠ 0
        // (first nonzero coordinate = 1).
        static IEnumerable<int[]> AnisotropicProjectivePoints(
            QuadraticFormRecovery.RecoveredForm Q, AffineStructureRecovery.AffineStructure aff, int p)
        {
            int n = aff.Coords.Length;
            for (int v = 0; v < n; v++)
            {
                var a = aff.Coords[v];
                int lead = -1;
                for (int k = 0; k < a.Length; k++) if (a[k] % p != 0) { lead = k; break; }
                if (lead < 0) continue;                 // zero vector
                if (a[lead] % p != 1) continue;         // not the normalized projective rep
                if (Q.Evaluate(a) % p != 0) yield return a;
            }
        }

        // encoded coord -> vertex, inverse of aff.Coords.
        static int[] ReverseCoordMap(AffineStructureRecovery.AffineStructure aff)
        {
            int n = aff.Coords.Length, p = aff.P;
            var rev = new int[n];
            for (int v = 0; v < n; v++) rev[Encode(aff.Coords[v], p)] = v;
            return rev;
        }

        static int Encode(int[] c, int p)
        {
            int v = 0, pw = 1;
            for (int i = 0; i < c.Length; i++) { v += (((c[i] % p) + p) % p) * pw; pw *= p; }
            return v;
        }

        static int ModInv(int a, int p) { int r = 1; for (int i = 0; i < p - 2; i++) r = r * a % p; return r; }

        static int PrimitiveRoot(int p)
        {
            if (p == 2) return 1;
            for (int g = 2; g < p; g++)
            {
                var seen = new HashSet<int>();
                int x = 1;
                for (int i = 0; i < p - 1; i++) { x = x * g % p; seen.Add(x); }
                if (seen.Count == p - 1) return g;
            }
            return p - 1;
        }
    }
}
