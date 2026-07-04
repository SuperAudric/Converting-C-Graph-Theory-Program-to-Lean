using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — C4: Aut-free isotropic-line recovery (2026-07-04).
// docs/chain-descent-route-c-plan.md §9.2.2 (C4). The enabling step for Aut-free coordinatization:
// recover the isotropic lines through o from ADJACENCY ALONE (no automorphism harvest), via the
// local invariant |N(o)∩N(x)∩N(y)|. Validates: (i) recovered lines match ground-truth collinearity;
// (ii) each line has p-1 points; (iii) line directions span (F_q)^d. (route_c_bootstrap_probe.py.)
public class RouteCGeometryProbe
{
    private readonly ITestOutputHelper _out;
    public RouteCGeometryProbe(ITestOutputHelper o) => _out = o;

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    [Theory]
    [InlineData(3, -1)]
    [InlineData(3, +1)]
    [InlineData(5, -1)]
    [InlineData(5, +1)]
    public void RecoverIsotropicLines_AutFree(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim);
        var (adj, vec, _) = RouteCVO4.Build(q, eps);
        int o = 0;   // origin = zero vector

        // recover lines from ADJACENCY ALONE (RecoverIsotropicLines never sees coordinates)
        var lines = GeometricCoordinatizer.RecoverIsotropicLines(adj, n, o);
        _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_4({q}) n={n}: recovered {lines.Count} lines, sizes {string.Join(",", lines.Select(l => l.Count).Distinct().OrderBy(x => x))}");

        // (i) every recovered line is a genuine isotropic line through o: all its points are scalar
        // multiples of a common direction (ground truth via coords, used only to CHECK).
        foreach (var line in lines)
        {
            var dir = vec(line[0]);
            foreach (int v in line)
                Assert.True(Dependent(vec(v), dir, q, dim), $"VO^{eps}_4({q}): recovered line is not collinear");
        }

        // (ii) each line has exactly p-1 = q-1 non-o points (a full affine line minus o)
        foreach (var line in lines)
            Assert.True(line.Count == q - 1, $"VO^{eps}_4({q}): line size {line.Count} != q-1={q - 1}");

        // (iii) the recovered directions span (F_q)^dim (the enabling property for coordinatization)
        var dirs = lines.Select(l => vec(l[0])).ToList();
        Assert.Equal(dim, SpanDim(dirs, q, dim));
        _out.WriteLine($"    directions span dim {dim} ✓ ({lines.Count} lines, all collinear, all size {q - 1})");
    }

    // Harvest-free invariant recovery: (q,m,eps) from adjacency ALONE (no AffineStructure, no Aut),
    // matching the coord-based classifier. This is C3's canonical answer without coordinatization.
    [Theory]
    [InlineData(3, -1)]
    [InlineData(3, +1)]
    [InlineData(5, -1)]
    [InlineData(5, +1)]
    public void RecoverInvariant_HarvestFree(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim);
        var (adj, _, _) = RouteCVO4.Build(q, eps);
        bool ok = GeometricCoordinatizer.RecoverAffinePolarInvariant(adj, n, out int rq, out int rm, out int reps);
        _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_4({q}): harvest-free ⇒ q={rq} m={rm} eps={reps}");
        Assert.True(ok);
        Assert.Equal(q, rq);
        Assert.Equal(2, rm);
        Assert.Equal(eps, reps);
    }

    // FULL Aut-free coordinatization via line-sum constraints (small cone-blind ambiguity, p=3):
    // recover coords from ADJACENCY ALONE (no harvest), then confirm they reconstruct the quadratic
    // form (0 mismatches) — i.e. the graph IS a quadric Cayley graph in the recovered coords. This is
    // the C4 payoff for VO±₄(3): harvest-free confirmation ⟹ the Route-C pipeline is harvest-free
    // (the provable-poly leg) for this case.
    [Theory]
    [InlineData(3, -1)]
    [InlineData(3, +1)]
    public void CoordinatizeByLineSums_ReconstructsForm_HarvestFree(int q, int eps)
    {
        const int dim = 4;
        int n = IPow(q, dim);
        var (adj, _, _) = RouteCVO4.Build(q, eps);

        var aff = GeometricCoordinatizer.CoordinatizeByLineSums(adj, n);
        Assert.True(aff is not null, $"VO^{eps}_4({q}): line-sum coordinatization returned null");
        Assert.Equal(dim, aff!.Dim);

        var Q = QuadraticFormRecovery.RecoverForm(adj, n, aff);
        Assert.True(Q is not null, $"VO^{eps}_4({q}): RecoverForm null on line-sum coords");
        int mism = 0;
        var d = new int[dim];
        for (int x = 0; x < n; x++)
            for (int y = x + 1; y < n; y++)
            {
                for (int i = 0; i < dim; i++) d[i] = ((aff.Coords[x][i] - aff.Coords[y][i]) % q + q) % q;
                if ((Q!.Evaluate(d) == 0) != (adj[x * n + y] == 1)) mism++;
            }
        _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_4({q}) n={n}: HARVEST-FREE coords reconstruct graph, mismatches={mism}/{n * (n - 1) / 2}");
        Assert.Equal(0, mism);
    }

    // The documented boundary: for p ≥ 5 the cone-blind ambiguity (nullDim − d) is large (45 at q=5,d=4),
    // so the shear search is infeasible and the coordinatizer HONESTLY DECLINES (returns null) — it does
    // NOT emit wrong coords. This bounds where the line-sum method delivers harvest-free coordinatization.
    [Theory]
    [InlineData(5, -1)]
    [InlineData(5, +1)]
    public void CoordinatizeByLineSums_DeclinesWhenAmbiguityLarge(int q, int eps)
    {
        int n = IPow(q, 4);
        var (adj, _, _) = RouteCVO4.Build(q, eps);
        var aff = GeometricCoordinatizer.CoordinatizeByLineSums(adj, n);
        _out.WriteLine($"VO^{(eps < 0 ? "-" : "+")}_4({q}): coordinatizer declined (null) as expected (large cone-blind ambiguity)");
        Assert.Null(aff);
    }

    static bool Dependent(int[] x, int[] y, int q, int d)
    {
        for (int c = 0; c < q; c++) if (Enumerable.Range(0, d).All(k => (c * x[k]) % q == ((y[k] % q) + q) % q)) return true;
        for (int c = 0; c < q; c++) if (Enumerable.Range(0, d).All(k => (c * y[k]) % q == ((x[k] % q) + q) % q)) return true;
        return false;
    }

    // dimension of the F_q-span of `vecs` (Gaussian elimination mod q, q prime)
    static int SpanDim(List<int[]> vecs, int q, int d)
    {
        var rows = vecs.Select(v => v.Select(x => ((x % q) + q) % q).ToArray()).ToList();
        int rank = 0;
        for (int col = 0; col < d && rank < rows.Count; col++)
        {
            int piv = -1;
            for (int r = rank; r < rows.Count; r++) if (rows[r][col] % q != 0) { piv = r; break; }
            if (piv < 0) continue;
            (rows[rank], rows[piv]) = (rows[piv], rows[rank]);
            int inv = ModInv(rows[rank][col], q);
            for (int c = 0; c < d; c++) rows[rank][c] = rows[rank][c] * inv % q;
            for (int r = 0; r < rows.Count; r++)
                if (r != rank && rows[r][col] % q != 0)
                {
                    int f = rows[r][col];
                    for (int c = 0; c < d; c++) rows[r][c] = (((rows[r][c] - f * rows[rank][c]) % q) + q * q) % q;
                }
            rank++;
        }
        return rank;
    }

    static int ModInv(int a, int p) { a = ((a % p) + p) % p; int r = 1; for (int i = 0; i < p - 2; i++) r = r * a % p; return r; }
}
