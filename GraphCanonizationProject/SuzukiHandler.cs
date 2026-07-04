using System;
using System.Numerics;

namespace Canonizer
{
    // Route C — the SUZUKI–TITS forms-graph family handler (Lean: Suzuki.reachesRigidOrCameron_suzuki,
    // CITATION-FREE, via the 5 σ-twisted ovoid forms + the GF(q)^4↔𝔽₂^d module bridge + second-derivative
    // recovery). CHAR-2 (Sz(q), q = 2^{2e+1}) — a SEPARATE track from the odd-q multi-quadric machinery.
    //
    // ── STATUS: SCAFFOLD READY; recognition LIVE for VSz(8); recovery (char-2) STUBBED. ─────────────
    // INTERCONNECTION DONE: registered; the SRG fingerprint recognition is LIVE (the known VSz(8)
    // instance); result plumbing generic. `Confirm` is the char-2 stub — it returns FALSE (declines),
    // so the handler recognizes the fingerprint but SAFELY falls back to the descent until the char-2
    // recovery lands. Once Confirm is real, StandardGraph/AutOrder must also be filled (they throw).
    //
    // TO COMPLETE (well-defined; char-2 track — does NOT reuse the odd-q RecoverFormFamily):
    //   (1) RecognizeInvariant — generalize the fingerprint from VSz(8)=SRG(4096,455,6,56) to Sz(q),
    //       q = 2^{2e+1} (params as a function of q). Currently the q=8 instance only.
    //   (2) Confirm — char-2 form recovery: recover the 5 σ-twisted ovoid forms via the GF(q)^4↔𝔽₂^d
    //       module bridge + second-derivative recovery (Arf, not the degree-2 kernel solve), then check
    //       the joint zero reconstructs the graph. Source: route_c_suzuki_probe.py / _determine_probe.py
    //       + the Lean `suzukiAdapter` (SF_k, suzukiForms_determine).
    //   (3) StandardGraph — the canonical Sz(q) ovoid graph on q^4 vertices.
    //   (4) AutOrder — closed-form |Aut| = |affineG(Sz(q))| = q^4 · |Sz(q)|·(field/similitude factors);
    //       |Sz(q)| = q^2 (q^2+1)(q-1).
    internal sealed class SuzukiHandler : FormFamilyHandlerBase<SuzukiHandler.Inv>
    {
        internal sealed class Inv { public int Q; }

        public override FormFamily Family => FormFamily.Suzuki;

        protected override Inv? RecognizeInvariant(int[] adj, int n)
        {
            // LIVE for the known VSz(8) instance; general Sz(q) fingerprint is TODO 1.
            if (!FormsGraphClassifier.StronglyRegular(adj, n, out int k, out int lam, out int mu)) return null;
            if (n == 4096 && k == 455 && lam == 6 && mu == 56) return new Inv { Q = 8 };
            return null;
        }

        // STUB (char-2 recovery not built): declines safely ⟹ falls back to the descent. TODO 2.
        protected override bool Confirm(int[] adj, int n, CanonResult harvest, Inv inv) => false;

        protected override int[] StandardGraph(Inv inv) =>
            throw new NotImplementedException("SuzukiHandler.StandardGraph — canonical Sz(q) ovoid graph (TODO 3).");

        protected override BigInteger AutOrder(Inv inv) =>
            throw new NotImplementedException("SuzukiHandler.AutOrder — closed-form |affineG(Sz(q))| (TODO 4).");

        protected override string Describe(Inv inv) => $"Sz({inv.Q})";
    }
}
