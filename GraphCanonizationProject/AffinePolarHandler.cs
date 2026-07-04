using System.Numerics;

namespace Canonizer
{
    // Route C — the AFFINE-POLAR family handler (VO^eps_{2m}(q), odd q). The fully-built reference
    // implementation; the other three handlers mirror this shape. docs/chain-descent-route-c-plan.md §9.2.
    //
    // Iso-type invariant = (q, m, eps): n = q^{2m} pins q,m; valency = (q^m-eps)(q^{m-1}+eps) pins eps —
    // all HARVEST-FREE. Confirmation = multi-quadric reconstruction (the cone is cut by ONE quadric).
    internal sealed class AffinePolarHandler : FormFamilyHandlerBase<AffinePolarHandler.Inv>
    {
        internal sealed class Inv { public int Q, M, Eps; }

        public override FormFamily Family => FormFamily.AffinePolar;

        protected override Inv? RecognizeInvariant(int[] adj, int n) =>
            GeometricCoordinatizer.RecoverAffinePolarInvariant(adj, n, out int q, out int m, out int eps)
                ? new Inv { Q = q, M = m, Eps = eps } : null;

        protected override bool Confirm(int[] adj, int n, CanonResult harvest, Inv inv) =>
            ConfirmByMultiQuadricReconstruction(adj, n, harvest);

        protected override int[] StandardGraph(Inv inv) => RouteCCanonicalizer.StandardVO(inv.Q, inv.M, inv.Eps);

        protected override BigInteger AutOrder(Inv inv) => RouteCCanonicalizer.AffinePolarAutOrder(inv.Q, inv.M, inv.Eps);

        protected override string Describe(Inv inv) => $"VO^{(inv.Eps < 0 ? "-" : "+")}_{2 * inv.M}({inv.Q})";

        protected override FormsGraphClassification MakeClassification(Inv inv) =>
            new() { Family = FormFamily.AffinePolar, P = inv.Q, M = inv.M, Eps = inv.Eps };
    }
}
