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
    }
}
