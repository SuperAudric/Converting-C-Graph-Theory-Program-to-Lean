using System.Numerics;

namespace Canonizer
{
    // Route C — the FORMS-GRAPH FAMILY DISPATCH (the C# mirror of the Lean `FormAdapter` engine;
    // docs/chain-descent-route-c-plan.md §9.2.2 / §9.2.7). Node 4 is FOUR families {affine-polar,
    // alternating, half-spin, Suzuki–Tits}; each is recognized and canonicalized by its own handler,
    // and `RouteCCanonicalizer` dispatches over the registry. Only affine-polar is fully built; the
    // other three are handlers with all INTERCONNECTION live and only their per-family MATH CORE stubbed
    // (see each handler's TODOs). A dormant handler's `RecognizeInvariant` returns null, so it never
    // fires and the graph falls back to the descent — SAFE.
    //
    // The runtime canonicalization of a family, in four hooks:
    //   RecognizeInvariant  — HARVEST-FREE family + iso-type recovery from (n, valency, SRG params).
    //                         The iso-type is a COMPLETE invariant, so it fixes the answer with no coords.
    //   Confirm             — SAFETY: the graph is GENUINELY this family (rules out a parameter-mate SRG).
    //                         Odd-q families reuse ConfirmByMultiQuadricReconstruction (C1a); Suzuki = char-2.
    //   StandardGraph       — the canonical standard graph of the iso-type (the emitted canonical form).
    //   AutOrder            — the closed-form |Aut| of the iso-type.
    internal interface IFormFamilyHandler
    {
        FormFamily Family { get; }
        // Recognize + canonicalize `adj` from an already-harvested descent `harvest`. null = not this family.
        RouteCCanonicalResult? TryCanonicalize(int[] adj, int n, CanonResult harvest);
    }

    // The canonicalization result — family-agnostic. `Classification` carries affine-polar detail
    // (default for other families; kept for the existing affine-polar tests).
    internal sealed class RouteCCanonicalResult
    {
        public required FormFamily Family { get; init; }
        public required BigInteger AutOrder { get; init; }
        public required int[] CanonicalAdjacency { get; init; }   // the standard graph of this iso-type
        public string Invariant { get; init; } = "";
        public FormsGraphClassification Classification { get; init; }
    }

    // The generic per-family skeleton. A family implements the four hooks; the base wires the flow,
    // the harvest-free-invariant-then-confirm ordering, and shared helpers.
    internal abstract class FormFamilyHandlerBase<TInv> : IFormFamilyHandler where TInv : class
    {
        public abstract FormFamily Family { get; }

        // HARVEST-FREE recognition of the iso-type invariant; null ⟹ the graph is not this family.
        protected abstract TInv? RecognizeInvariant(int[] adj, int n);
        // The canonical standard graph of the iso-type (natural vertex order).
        protected abstract int[] StandardGraph(TInv inv);
        // The closed-form |Aut| of the iso-type.
        protected abstract BigInteger AutOrder(TInv inv);
        // SAFETY confirmation: `adj` is genuinely this family (not a same-parameter mate).
        protected abstract bool Confirm(int[] adj, int n, CanonResult harvest, TInv inv);
        // Human-readable invariant (for diagnostics).
        protected abstract string Describe(TInv inv);
        // Optional affine-polar detail on the result (default for other families).
        protected virtual FormsGraphClassification MakeClassification(TInv inv) => default;

        public RouteCCanonicalResult? TryCanonicalize(int[] adj, int n, CanonResult harvest)
        {
            if (harvest.Flagged) return null;
            var inv = RecognizeInvariant(adj, n);          // harvest-free; null = not this family
            if (inv is null) return null;
            if (!Confirm(adj, n, harvest, inv)) return null;   // rules out a parameter-mate (safe)
            return new RouteCCanonicalResult
            {
                Family = Family,
                AutOrder = AutOrder(inv),
                CanonicalAdjacency = StandardGraph(inv),
                Invariant = Describe(inv),
                Classification = MakeClassification(inv),
            };
        }

        // ── shared helpers ────────────────────────────────────────────────────

        // F1 harvest-based coordinatization (odd-q prime-power families). C4 (Aut-free) would replace
        // this, making Confirm harvest-free (the d-scaling goal). Returns null if n is not a prime power
        // or the harvest has no regular normal p-subgroup.
        protected static AffineStructureRecovery.AffineStructure? Coordinatize(CanonResult harvest, int n)
        {
            if (!PrimeBase(n, out int p, out _)) return null;
            return AffineStructureRecovery.Recover(harvest.ResidualGroup, p, origin: 0);
        }

        // Shared multi-quadric confirmation (affine-polar / alternating / half-spin): the recovered
        // degree-2 vanishing space's JOINT CONE must reconstruct the whole adjacency. Odd q. This is the
        // C1a machinery (RecoverFormFamily), already validated on single- and multi-quadric Cayley graphs.
        //
        // Coordinatization tries HARVEST-FREE first (C4 line-sum, works where the cone-blind ambiguity is
        // small — VO±₄(3)); only falls back to the descent harvest when that declines. So for the
        // harvest-free regime the WHOLE confirmation (hence the Route-C pipeline) is harvest-free — the
        // provable-poly leg, no dependence on the descent / T0.
        protected static bool ConfirmByMultiQuadricReconstruction(int[] adj, int n, CanonResult harvest)
        {
            var aff = GeometricCoordinatizer.CoordinatizeByLineSums(adj, n) ?? Coordinatize(harvest, n);
            if (aff is null) return false;
            var fam = QuadraticFormRecovery.RecoverFormFamily(adj, n, aff);
            if (fam is null) return false;
            int p = aff.P, dim = aff.Dim;
            var d = new int[dim];
            for (int x = 0; x < n; x++)
                for (int y = x + 1; y < n; y++)
                {
                    for (int i = 0; i < dim; i++) d[i] = ((aff.Coords[x][i] - aff.Coords[y][i]) % p + p) % p;
                    if (fam.OnCone(d) != (adj[x * n + y] == 1)) return false;
                }
            return true;
        }

        protected static bool PrimeBase(int n, out int p, out int d)
        {
            p = 0; d = 0;
            if (n < 2) return false;
            int cand = 2;
            while (n % cand != 0) cand++;
            int m = n, e = 0;
            while (m % cand == 0) { m /= cand; e++; }
            if (m != 1) return false;
            p = cand; d = e; return true;
        }

        protected static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }
    }
}
