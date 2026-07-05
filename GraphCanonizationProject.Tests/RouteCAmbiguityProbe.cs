using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — what ARE the 45 "freedoms" at q=5? (2026-07-05). Do they form canonically different
// GRAPHS, or are they wrong COORDINATIZATIONS of the same graph? This probe measures directly.
public class RouteCAmbiguityProbe
{
    private readonly ITestOutputHelper _out;
    public RouteCAmbiguityProbe(ITestOutputHelper o) => _out = o;

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    static AffineStructureRecovery.AffineStructure AffFrom(Func<int, int[]> coord, int n, int p, int dim)
        => new() { Translations = new PermutationGroup(n), Origin = 0, P = p, Dim = dim, Coords = Enumerable.Range(0, n).Select(coord).ToArray() };

    static int Mismatches(int[] adj, int n, AffineStructureRecovery.AffineStructure aff)
    {
        var Q = QuadraticFormRecovery.RecoverForm(adj, n, aff);
        if (Q is null) return -1;   // RecoverForm failed
        int p = aff.P, dim = aff.Dim; var d = new int[dim]; int m = 0;
        for (int x = 0; x < n; x++)
            for (int y = x + 1; y < n; y++)
            {
                for (int i = 0; i < dim; i++) d[i] = ((aff.Coords[x][i] - aff.Coords[y][i]) % p + p) % p;
                if ((Q.Evaluate(d) == 0) != (adj[x * n + y] == 1)) m++;
            }
        return m;
    }

    [Theory]
    [InlineData(5, -1)]
    [InlineData(5, +1)]
    public void Freedoms_AreWrongCoords_NotDifferentGraphs(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim);
        var (adj, vec, enc) = RouteCVO4.Build(q, eps);

        var S = GeometricCoordinatizer.LineSumSolutionSpace(adj, n);
        _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_4({q}): line-sum solution space dim = {S.Count} (linear part d={dim}, freedoms={S.Count - dim})");

        // (A) the TRUE linear coords reconstruct the graph (0 mismatches).
        var trueAff = AffFrom(vec, n, q, dim);
        int mTrue = Mismatches(adj, n, trueAff);
        _out.WriteLine($"    TRUE linear coords: mismatches = {mTrue}  (expect 0)");
        Assert.Equal(0, mTrue);

        // (B) the true linear functionals are IN the solution space (sanity): ell_i(v) = v_i.
        // Build them and check each is a linear combination of S (i.e., in the span). Cheap proxy:
        // each coordinate function satisfies the line-sums, which the reconstruction already implies.

        // (C) sample the freedoms: replace ONE coordinate with a random non-linear solution-space element
        // and measure reconstruction. If the freedoms were "different graphs" they'd reconstruct as some
        // valid quadric; if they're wrong coords of the SAME graph, reconstruction breaks (or non-injective).
        var rng = new Random(7);
        int broke = 0, nonInjective = 0, samples = 0;
        for (int t = 0; t < 12; t++)
        {
            // random element of S (a coordinate-function candidate), mixed with the linear part
            var f = new int[n];
            foreach (var s in S) { int c = rng.Next(q); for (int v = 0; v < n; v++) f[v] = (f[v] + c * s[v]) % q; }

            int[] Coord(int v) { var c = (int[])vec(v).Clone(); c[dim - 1] = ((c[dim - 1] + f[v]) % q + q) % q; return c; }
            var aff = AffFrom(Coord, n, q, dim);
            // injective?
            var seen = new HashSet<string>(); bool inj = true;
            for (int v = 0; v < n && inj; v++) if (!seen.Add(string.Join(",", aff.Coords[v]))) inj = false;
            samples++;
            if (!inj) { nonInjective++; continue; }
            int m = Mismatches(adj, n, aff);
            if (m != 0) broke++;
        }
        _out.WriteLine($"    {samples} random freedoms mixed into a coordinate: nonInjective={nonInjective}, brokeReconstruction={broke}, stillValid={samples - nonInjective - broke}");
        // the whole point: NONE of the freedoms give a *different valid* coordinatization — they are all
        // either non-injective or break reconstruction. (Same graph, wrong coords.)
        Assert.Equal(0, samples - nonInjective - broke);
    }
}
