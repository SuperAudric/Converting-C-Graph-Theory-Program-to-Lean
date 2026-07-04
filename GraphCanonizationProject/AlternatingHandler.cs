using System;
using System.Numerics;

namespace Canonizer
{
    // Route C — the ALTERNATING forms-graph family handler (Lean: Plucker.reachesRigidOrCameron_alternating,
    // via the multi-quadric engine + the Plücker sub-Pfaffians `plucker_hjoint`). Odd q, MULTI-QUADRIC.
    //
    // ── STATUS: SCAFFOLD READY, math core STUBBED. ──────────────────────────────────────────────────
    // INTERCONNECTION DONE: registered in the dispatch; `Confirm` is fully wired (multi-quadric
    // reconstruction reuses C1a `RecoverFormFamily`, already validated on multi-quadric Cayley graphs);
    // result plumbing generic. The handler is DORMANT (RecognizeInvariant returns null) ⟹ never fires,
    // graphs fall back to the descent — SAFE.
    //
    // TO COMPLETE (well-defined, no interconnection needed):
    //   (1) RecognizeInvariant — the SRG parameter fingerprint (n,k,λ,μ) of the alternating forms graph
    //       and the map params → iso-type invariant (q + the underlying dimension). Source: the Lean
    //       adapter's family definition + the standard alternating-forms-graph parameters.
    //   (2) StandardGraph — build the canonical alternating forms graph on q^d vertices whose connection
    //       set is the joint zero of the standard Plücker quadrics (the `S`-forms of the Lean adapter).
    //   (3) AutOrder — the closed-form |Aut| = |affineG(alternating similitude group)| = |translations|
    //       · |ΓSp/AΓL-type factor|. Source: the classical-group order for the alternating similitudes.
    // Confirm (multi-quadric) is ALREADY correct — activating (1)–(3) completes the family.
    internal sealed class AlternatingHandler : FormFamilyHandlerBase<AlternatingHandler.Inv>
    {
        internal sealed class Inv { public int Q, D; }   // field + underlying dimension (d = 2m)

        public override FormFamily Family => FormFamily.Alternating;

        protected override Inv? RecognizeInvariant(int[] adj, int n)
        {
            // DORMANT until the alternating-forms-graph SRG fingerprint is filled in (TODO 1).
            // When implemented: StronglyRegular(adj,n,out k,out lam,out mu) + match the alternating
            // parameters + PrimeBase(n) ⟹ return new Inv{ Q=p, D=d }.
            return null;
        }

        // WIRED (multi-quadric): the recovered degree-2 vanishing space (Plücker quadrics) reconstructs
        // the graph. Already correct — reuses the shared C1a machinery.
        protected override bool Confirm(int[] adj, int n, CanonResult harvest, Inv inv) =>
            ConfirmByMultiQuadricReconstruction(adj, n, harvest);

        // TODO 2: with the standard Plücker quadrics Q_0..Q_r, this is a one-liner:
        //   FormsGraphBuilder.StandardCayleyGraph(inv.Q, inv.D, diff => Q_0(diff)==0 && ... && Q_r(diff)==0);
        protected override int[] StandardGraph(Inv inv) =>
            throw new NotImplementedException("AlternatingHandler.StandardGraph — via FormsGraphBuilder.StandardCayleyGraph with the standard Plücker quadrics (TODO 2).");

        protected override BigInteger AutOrder(Inv inv) =>
            throw new NotImplementedException("AlternatingHandler.AutOrder — closed-form |Aut| of the alternating similitude group (TODO 3).");

        protected override string Describe(Inv inv) => $"Alt_{inv.D}({inv.Q})";
    }
}
