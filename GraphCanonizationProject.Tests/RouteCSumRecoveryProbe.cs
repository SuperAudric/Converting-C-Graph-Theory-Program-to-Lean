using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — C4 hard core: can ADDITION (x+y) be recovered from the graph, to break cone-blindness?
// (2026-07-04). z = x+y (for cone points x,y with x≁y) is a common neighbour of x,y forming an
// INDUCED 4-cycle o-x-z-y. This probe measures, on VO±₄(5) with KNOWN coords, whether the true x+y
// is UNIQUELY pinned by that characterization (and refinements), which decides the recovery approach.
public class RouteCSumRecoveryProbe
{
    private readonly ITestOutputHelper _out;
    public RouteCSumRecoveryProbe(ITestOutputHelper o) => _out = o;

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    [Theory]
    [InlineData(5, -1)]
    [InlineData(5, +1)]
    [InlineData(3, -1)]
    public void Sum_UniquenessStructure(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim);
        var (adj, vec, enc) = RouteCVO4.Build(q, eps);
        int o = 0;   // zero vector

        // cone points = neighbours of o (isotropic vectors)
        var cone = new List<int>();
        for (int w = 0; w < n; w++) if (adj[o * n + w] == 1) cone.Add(w);

        // neighbour sets
        var N = new HashSet<int>[n];
        for (int v = 0; v < n; v++) { N[v] = new HashSet<int>(); for (int w = 0; w < n; w++) if (adj[v * n + w] == 1) N[v].Add(w); }

        int Sum(int a, int b) { var s = new int[dim]; for (int i = 0; i < dim; i++) s[i] = (vec(a)[i] + vec(b)[i]) % q; return enc(s); }

        var candCounts = new List<int>();
        var refinedCounts = new List<int>();
        int trials = 0, trueInCand = 0, trueUniqueRefined = 0;
        var rng = new Random(1);
        // sample pairs of cone points that are non-adjacent (x≁y ⟺ B(x,y)≠0 for isotropic x,y)
        for (int it = 0; it < 400; it++)
        {
            int x = cone[rng.Next(cone.Count)], y = cone[rng.Next(cone.Count)];
            if (x == y || adj[x * n + y] == 1) continue;          // need x≁y
            trials++;
            int z = Sum(x, y);

            // candidates: common neighbours of x,y that are NOT adjacent to o (induced 4-cycle o-x-w-y)
            var cand = N[x].Where(w => N[y].Contains(w) && w != o && adj[o * n + w] == 0).ToHashSet();
            candCounts.Add(cand.Count);
            if (cand.Contains(z)) trueInCand++;

            // refinement: also require the "opposite corner" symmetry — w such that x is a common
            // neighbour of o and w AND y is too, with the same 4-cycle; plus w-x isotropic-collinear
            // with o-y. Approximate refinement: candidates w where additionally N[o]∩N[w] contains both
            // x and y as an induced 4-cycle AND |N[x]∩N[w]∩cone|, |N[y]∩N[w]∩cone| match o's profile.
            var refined = cand.Where(w =>
                N[o].Contains(x) && N[o].Contains(y) &&
                (N[o].Intersect(N[w]).Count() == N[x].Intersect(N[y]).Count())).ToHashSet();
            refinedCounts.Add(refined.Count);
            if (refined.Count == 1 && refined.Contains(z)) trueUniqueRefined++;

            if (trials >= 60) break;
        }

        _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_4({q}): trials={trials} trueInCand={trueInCand}/{trials}");
        _out.WriteLine($"    candidate-count distribution: min={candCounts.Min()} max={candCounts.Max()} avg={candCounts.Average():0.0}");
        _out.WriteLine($"    refined-count: min={refinedCounts.Min()} max={refinedCounts.Max()} avg={refinedCounts.Average():0.0}; trueUniqueRefined={trueUniqueRefined}");
        Assert.Equal(trials, trueInCand);   // the true sum must always be a candidate
    }
}
