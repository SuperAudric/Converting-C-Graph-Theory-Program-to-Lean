using System;
using System.Numerics;

namespace Canonizer
{
    // Route C — the HALF-SPIN forms-graph family handler (Lean: HalfSpin.reachesRigidOrCameron_halfSpin,
    // via the 10 validated D₅ spinor quadrics `S0..S9` + `spinor_hjoint` + the multi-quadric engine).
    // Odd q, MULTI-QUADRIC — same shape as AlternatingHandler.
    //
    // ── STATUS: SCAFFOLD READY, math core STUBBED. ──────────────────────────────────────────────────
    // INTERCONNECTION DONE: registered; `Confirm` wired (multi-quadric reconstruction via C1a); result
    // plumbing generic. DORMANT (RecognizeInvariant returns null) ⟹ SAFE fallback to the descent.
    //
    // TO COMPLETE (well-defined):
    //   (1) RecognizeInvariant — the SRG fingerprint of the half-spin geometry (D₅ spinor variety) and
    //       params → iso-type (q + rank). Source: route_c_halfspin_probe.py (the 10 spinor quadrics,
    //       vanishing dim 10) + the Lean adapter's `S0..S9`.
    //   (2) StandardGraph — the canonical half-spin graph on q^d vertices, connection set = joint zero
    //       of the standard spinor quadrics S0..S9.
    //   (3) AutOrder — closed-form |Aut| = |affineG(half-spin similitude group)| (the D₅/spin group order).
    // Confirm (multi-quadric) is ALREADY correct — activating (1)–(3) completes the family.
    internal sealed class HalfSpinHandler : FormFamilyHandlerBase<HalfSpinHandler.Inv>
    {
        internal sealed class Inv { public int Q, D; }

        public override FormFamily Family => FormFamily.HalfSpin;

        protected override Inv? RecognizeInvariant(int[] adj, int n)
        {
            // DORMANT until the half-spin SRG fingerprint is filled in (TODO 1).
            return null;
        }

        protected override bool Confirm(int[] adj, int n, CanonResult harvest, Inv inv) =>
            ConfirmByMultiQuadricReconstruction(adj, n, harvest);

        // TODO 2: with the 10 standard spinor quadrics S0..S9, a one-liner:
        //   FormsGraphBuilder.StandardCayleyGraph(inv.Q, inv.D, diff => S0(diff)==0 && ... && S9(diff)==0);
        protected override int[] StandardGraph(Inv inv) =>
            throw new NotImplementedException("HalfSpinHandler.StandardGraph — via FormsGraphBuilder.StandardCayleyGraph with the spinor quadrics S0..S9 (TODO 2).");

        protected override BigInteger AutOrder(Inv inv) =>
            throw new NotImplementedException("HalfSpinHandler.AutOrder — closed-form |Aut| of the half-spin similitude group (TODO 3).");

        protected override string Describe(Inv inv) => $"HalfSpin_{inv.D}({inv.Q})";
    }
}
