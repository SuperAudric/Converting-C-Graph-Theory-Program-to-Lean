using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — the SUZUKI–TITS runtime prototype (2026-07-05). Validates, in production C#, the pieces the
// SuzukiHandler is built on: the object (VSz(8)=SRG(4096,455,6,56)), the σ-twisted GF(8) form model (Lean
// suzukiAdapter), and — the sound Confirm discriminator — the FIELD-AGNOSTIC F₂ degree signature that
// separates VSz(8) from its cospectral affine-polar mate VO⁻₄(8) (quadric-cut, degree 2).
// q=8 (n=4096) is the ONLY feasible + genuine Suzuki instance.
public class RouteCSuzukiProbe
{
    private readonly ITestOutputHelper _out;
    public RouteCSuzukiProbe(ITestOutputHelper o) => _out = o;

    // Build VSz(8) once; assert it is exactly SRG(4096,455,6,56).
    [Fact]
    [Trait("Category", "LongRunning")]
    public void StandardGraph_IsVSz8_SRG()
    {
        var adj = SuzukiOvoid.StandardGraph(8);
        int n = 4096;
        Assert.Equal(n * n, adj.Length);
        Assert.True(FormsGraphClassifier.StronglyRegular(adj, n, out int k, out int lam, out int mu));
        _out.WriteLine($"VSz(8): SRG({n},{k},{lam},{mu})");
        Assert.Equal(455, k);
        Assert.Equal(6, lam);
        Assert.Equal(56, mu);
    }

    // The σ-twisted GF(8) type-(1,2) forms cut the cone EXACTLY (the Lean suzukiAdapter's SF_k model).
    [Fact]
    public void SigmaFormModel_JointZeroIsCone()
    {
        var (basisDim, jointZeroIsCone) = SuzukiOvoid.SigmaFormModel(8);
        _out.WriteLine($"σ-twisted GF(8) form family: dim={basisDim}, joint zero == cone∪{{0}}: {jointZeroIsCone}");
        Assert.True(jointZeroIsCone, "σ-twisted forms must cut the cone exactly");
        Assert.True(basisDim >= 5, $"expected the ≥5-dim σ-form family, got {basisDim}");
    }

    // THE Confirm discriminator: VSz(8)'s cone is genuinely CUBIC over F₂ (cut by degree-3 forms) but NOT
    // quadric-cut (degree 2) — the sound separator from the cospectral VO⁻₄(8), whose cone IS a quadric.
    [Fact]
    [Trait("Category", "LongRunning")]
    public void DegreeSignature_CubicNotQuadric()
    {
        var adj = SuzukiOvoid.StandardGraph(8);
        int n = 4096, dim = 12;
        var cone = new List<int[]>();
        for (int v = 1; v < n; v++)
            if (adj[0 * n + v] == 1) { var b = new int[dim]; for (int i = 0; i < dim; i++) b[i] = (v >> i) & 1; cone.Add(b); }
        Assert.Equal(455, cone.Count);

        bool quadCut = SuzukiOvoid.CutByForms(cone, dim, maxDeg: 2);
        bool cubicCut = SuzukiOvoid.CutByForms(cone, dim, maxDeg: 3);
        _out.WriteLine($"VSz(8) cone F₂ degree signature: quadric-cut={quadCut}, cubic-cut={cubicCut} (Suzuki ⟺ cubic∧¬quadric)");
        Assert.False(quadCut, "the Tits ovoid cone is NOT a quadric — else it would alias the VO⁻₄ mate");
        Assert.True(cubicCut, "the Tits ovoid cone IS cut by cubic F₂ forms");
        Assert.True(SuzukiOvoid.IsOvoidConeBySignature(cone, dim), "VSz(8) must read as the ovoid (cubic, not quadric)");
    }

    // NEGATIVE CONTROL: the cospectral char-2 QUADRIC graph Clebsch = VO⁻₄(2) must be REJECTED by the same
    // discriminator (its cone IS a quadric, degree 2). This proves the signature is specific, not "cubic is
    // always true". Clebsch (n=16) is the feasible char-2 quadric stand-in for VO⁻₄(8).
    [Fact]
    public void DegreeSignature_RejectsQuadricMate_Clebsch()
    {
        var (adj, _, _) = RouteCVO4.Build(2, -1);   // VO⁻₄(2) = Clebsch, F₂⁴
        int n = 16, dim = 4;
        var cone = new List<int[]>();
        for (int v = 1; v < n; v++)
            if (adj[0 * n + v] == 1) { var b = new int[dim]; for (int i = 0; i < dim; i++) b[i] = (v >> i) & 1; cone.Add(b); }

        bool quadCut = SuzukiOvoid.CutByForms(cone, dim, maxDeg: 2);
        _out.WriteLine($"Clebsch VO⁻₄(2) cone: quadric-cut={quadCut} (⟹ ovoid-signature={SuzukiOvoid.IsOvoidConeBySignature(cone, dim)})");
        Assert.True(quadCut, "the Clebsch cone IS a quadric");
        Assert.False(SuzukiOvoid.IsOvoidConeBySignature(cone, dim), "a quadric mate must NOT read as the Suzuki ovoid");
    }

    // Confirm's code path (ConeFromGraph → IsOvoidConeBySignature) on VSz(8), under a NON-NATURAL F₂ basis.
    // The whole reason Confirm needs no field recovery is BASIS-INVARIANCE: a linear F₂ change of the coords
    // preserves monomial degree, so the degree signature is unchanged. This applies a random invertible
    // (upper-unitriangular) change of basis and confirms the ovoid signature still reads true — exactly what
    // guarantees Confirm works on any F1-recovered basis, not just the natural bit-vector one.
    [Fact]
    [Trait("Category", "LongRunning")]
    public void Confirm_Path_IsBasisInvariant_VSz8()
    {
        var adj = SuzukiOvoid.StandardGraph(8);
        int n = 4096, dim = 12;

        // a random invertible F₂ change of basis M (upper-unitriangular ⟹ always invertible)
        var rng = new Random(7);
        var M = new int[dim][];
        for (int i = 0; i < dim; i++) { M[i] = new int[dim]; M[i][i] = 1; for (int j = i + 1; j < dim; j++) M[i][j] = rng.Next(2); }
        int[] Transform(int v) { var c = new int[dim]; for (int i = 0; i < dim; i++) { int s = 0; for (int j = 0; j < dim; j++) s ^= M[i][j] & ((v >> j) & 1); c[i] = s; } return c; }

        var aff = new AffineStructureRecovery.AffineStructure
        {
            Translations = new PermutationGroup(n),   // unused by ConeFromGraph / the signature
            Origin = 0, P = 2, Dim = dim,
            Coords = Enumerable.Range(0, n).Select(Transform).ToArray(),
        };
        Assert.Equal(0, aff.Coords[0].Sum());          // origin ↦ 0 (M·0 = 0)

        var cone = SuzukiOvoid.ConeFromGraph(adj, n, aff);
        Assert.Equal(455, cone.Count);
        Assert.True(SuzukiOvoid.IsOvoidConeBySignature(cone, aff.Dim),
            "the degree signature must be basis-invariant (holds under a non-natural F₂ basis)");
    }

    // The closed-form |Aut(VSz(q))| the handler reports (guards the arithmetic; the TRUE-|Aut| verification
    // is blocked by the PermutationGroup sifting wall at n=q^4).
    [Fact]
    public void AutOrder_ClosedForm_VSz8()
    {
        // q^4 · |Sz(8)| · 3 = 4096 · (64·65·7) · 3 = 4096 · 29120 · 3.
        Assert.Equal(new System.Numerics.BigInteger(4096L) * 29120 * 3, RouteCCanonicalizer.SuzukiAutOrder(8));
    }
}
