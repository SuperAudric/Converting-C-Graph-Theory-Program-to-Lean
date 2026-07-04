using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — C4 hard core, step: can 2-FLATS (affine planes) be recovered from the graph? A plane
// through o spanned by cone points x,y is {sx+ty} (p² points); x+y lives there, so recovering the plane
// (then pinning x+y within it) breaks cone-blindness. Affine subspaces are closed under line-completion,
// so we test: does ISOTROPIC-LINE CLOSURE of {o,x,y} recover exactly the 2-flat? (Ground truth via coords.)
public class RouteCPlaneRecoveryProbe
{
    private readonly ITestOutputHelper _out;
    public RouteCPlaneRecoveryProbe(ITestOutputHelper o) => _out = o;

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    [Theory]
    [InlineData(3, -1)]
    [InlineData(5, -1)]
    [InlineData(5, +1)]
    public void PlaneByLineClosure(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim);
        var (adj, vec, enc) = RouteCVO4.Build(q, eps);

        // isotropic lines through every vertex, indexed by vertex for closure
        var linesThrough = new List<int[]>[n];
        for (int v = 0; v < n; v++) linesThrough[v] = new List<int[]>();
        foreach (var line in GeometricCoordinatizer.RecoverAllIsotropicLines(adj, n, q))
            foreach (int v in line) linesThrough[v].Add(line.ToArray());

        int trials = 0, exactPlane = 0; var closureSizes = new List<int>(); var planeSize = q * q;
        var rng = new Random(2);
        for (int it = 0; it < 200 && trials < 20; it++)
        {
            // pick independent cone points x,y (o=0)
            int x = 1 + rng.Next(n - 1), y = 1 + rng.Next(n - 1);
            if (adj[0 * n + x] != 1 || adj[0 * n + y] != 1) continue;   // both isotropic (cone)
            if (Dependent(vec(x), vec(y), q, dim)) continue;            // independent directions
            trials++;

            // true 2-flat {s x + t y}
            var flat = new HashSet<int>();
            for (int s = 0; s < q; s++) for (int t = 0; t < q; t++)
                { var w = new int[dim]; for (int i = 0; i < dim; i++) w[i] = (s * vec(x)[i] + t * vec(y)[i]) % q; flat.Add(enc(w)); }

            // isotropic-line closure of {o,x,y}
            var closure = new HashSet<int> { 0, x, y };
            bool grew = true;
            while (grew)
            {
                grew = false;
                foreach (int a in closure.ToArray())
                    foreach (var line in linesThrough[a])
                        if (line.Count(pt => closure.Contains(pt)) >= 2)
                            foreach (int pt in line) if (closure.Add(pt)) grew = true;
            }
            closureSizes.Add(closure.Count);
            if (closure.Count == planeSize && closure.SetEquals(flat)) exactPlane++;
        }

        _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_4({q}): trials={trials} planeSize={planeSize} exactPlaneRecovered={exactPlane}");
        _out.WriteLine($"    closure sizes: {string.Join(",", closureSizes.Distinct().OrderBy(z => z))}");
    }

    static bool Dependent(int[] x, int[] y, int q, int d)
    {
        for (int c = 0; c < q; c++) if (Enumerable.Range(0, d).All(k => (c * x[k]) % q == ((y[k] % q) + q) % q)) return true;
        for (int c = 0; c < q; c++) if (Enumerable.Range(0, d).All(k => (c * y[k]) % q == ((x[k] % q) + q) % q)) return true;
        return false;
    }
}
