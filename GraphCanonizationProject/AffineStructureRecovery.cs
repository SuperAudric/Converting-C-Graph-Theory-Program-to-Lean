using System.Collections.Generic;
using System.Linq;

namespace Canonizer
{
    // Route C — F1: recover the affine (F_p)^d structure from an abstract affine-polar
    // graph's automorphism group. See docs/chain-descent-route-c-plan.md §6.
    //
    // The vertex set of VO^eps_{2m}(q) is (F_p)^d (q = p prime here, d = 2m); the graph
    // is a translation (Cayley) scheme, so its automorphism group is affine-primitive
    // and its SOCLE is the regular translation group T = O_p(Aut) ≅ (F_p)^d. Recovering
    // T and a basis coordinatizes the vertices — the additive structure "z - t" and the
    // downstream form recovery A1 (recover Q from the cone) both need.
    //
    // Input = a harvested automorphism group (e.g. CanonResult.ResidualGroup, which
    // carries the full |Aut| for these huge-Aut graphs). Confirmed end-to-end against
    // the real harness by RouteCF1Probe (VO^eps_4(q), q=2,3,5, both types).
    internal static class AffineStructureRecovery
    {
        // The recovered additive structure: the translation group, an origin vertex, and
        // a vertex -> coordinate map (each vertex ↦ its (Z_p)^Dim vector, origin ↦ 0).
        internal sealed class AffineStructure
        {
            public required PermutationGroup Translations { get; init; }
            public required int Origin { get; init; }
            public required int P { get; init; }
            public required int Dim { get; init; }
            public required int[][] Coords { get; init; }   // Coords[vertex] = length-Dim vector over Z_p
        }

        // Recover the affine structure from an automorphism group `aut` over n = p^Dim
        // points, using `origin` as the coordinate zero. Returns null if `aut` has no
        // regular normal elementary-abelian p-subgroup (i.e. it is not affine-primitive
        // over F_p), or if n is not a power of p.
        public static AffineStructure? Recover(PermutationGroup aut, int p, int origin = 0)
        {
            int n = aut.N;
            int dim = 0; long pw = 1;
            while (pw < n) { pw *= p; dim++; }
            if (pw != n) return null;                       // n is not a power of p

            var t = aut.RegularNormalPSubgroup(p);          // T = the socle / translations
            if (t is null) return null;

            var coords = Coordinatize(t, p, n, dim, origin);
            if (coords is null) return null;

            return new AffineStructure { Translations = t, Origin = origin, P = p, Dim = dim, Coords = coords };
        }

        // Coordinatize the vertices via the regular action of T: pick an F_p-basis of T
        // (elements whose image at the origin lies outside the current span), then map
        // each coefficient tuple c ∈ (Z_p)^Dim to the vertex (prod basis[k]^c[k])[origin].
        static int[][]? Coordinatize(PermutationGroup t, int p, int n, int dim, int origin)
        {
            var basis = new List<int[]>();
            var spanVerts = new HashSet<int> { origin };    // vertices reachable by <basis> from origin
            foreach (var g in t.Elements())
            {
                if (Perm.IsIdentity(g) || spanVerts.Contains(g[origin])) continue;   // identity / dependent
                basis.Add(g);
                spanVerts = SpanVertices(basis, p, origin, n);
                if (basis.Count == dim) break;
            }
            if (basis.Count != dim || spanVerts.Count != n) return null;

            var coords = new int[n][];
            foreach (var c in Tuples(p, dim))
            {
                var e = Perm.Identity(n);
                for (int k = 0; k < dim; k++) e = Perm.Compose(e, Perm.Pow(basis[k], c[k]));
                coords[e[origin]] = c;
            }
            return coords;
        }

        // The set of vertices { (prod basis[k]^c[k])[origin] : c ∈ (Z_p)^|basis| }.
        static HashSet<int> SpanVertices(List<int[]> basis, int p, int origin, int n)
        {
            var set = new HashSet<int>();
            foreach (var c in Tuples(p, basis.Count))
            {
                var e = Perm.Identity(n);
                for (int k = 0; k < basis.Count; k++) e = Perm.Compose(e, Perm.Pow(basis[k], c[k]));
                set.Add(e[origin]);
            }
            return set;
        }

        // Odometer over (Z_p)^d.
        static IEnumerable<int[]> Tuples(int p, int d)
        {
            var c = new int[d];
            while (true)
            {
                yield return (int[])c.Clone();
                int i = 0;
                for (; i < d; i++) { if (++c[i] < p) break; c[i] = 0; }
                if (i == d) yield break;
            }
        }
    }
}
