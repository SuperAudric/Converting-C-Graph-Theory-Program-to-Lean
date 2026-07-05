using System;
using System.Numerics;

namespace Canonizer
{
    // Route C — the SUZUKI–TITS forms-graph family handler (Lean: Suzuki.reachesRigidOrCameron_suzuki,
    // CITATION-FREE, via the 5 σ-twisted ovoid forms + the GF(q)^4↔𝔽₂^d module bridge + second-derivative
    // recovery). CHAR-2 (Sz(q), q = 2^{2e+1}) — a SEPARATE track from the odd-q multi-quadric machinery.
    //
    // ── STATUS: BUILT (runtime prototype, q=8). ─────────────────────────────────────────────────────
    // All four hooks are implemented against SuzukiOvoid (the validated construction, RouteCSuzukiProbe).
    // FEASIBILITY: q=8 (VSz(8), n=4096) is the ONLY genuine + dense-instantiable Suzuki case (q=2 is
    // degenerate; q=32 ⟹ n=2^20). So this handler runs/tests at q=8; larger q is formula-only (unreachable
    // in the dense n×n infra) — see docs/chain-descent-route-c-plan.md §9.2.7.
    //
    // The four hooks (char-2 track — does NOT reuse the odd-q RecoverFormFamily):
    //   RecognizeInvariant — n=q^4, q=2^{2e+1}, valency (q²+1)(q−1). LOOSE (aliases the cospectral VO⁻₄(q));
    //                        Confirm does the sound disambiguation.
    //   Confirm            — the FIELD-AGNOSTIC F₂ DEGREE SIGNATURE: the recovered cone is cut by cubic F₂
    //                        forms but NOT by quadrics. VO⁻₄(q)'s cone IS a quadric ⟹ rejected. This is the
    //                        runtime image of the Lean σ-twisted `suzukiAdapter`, without needing field
    //                        recovery (a linear F₂ basis change preserves monomial degree). Needs F1 coords.
    //   StandardGraph      — SuzukiOvoid.StandardGraph(q) (the Tits-ovoid Cayley graph).
    //   AutOrder           — q^4 · |Sz(q)| · (field autos); |Sz(q)| = q²(q²+1)(q−1). CITED closed form —
    //                        NOT empirically verified (the order-check hits the PermutationGroup sifting wall
    //                        at n≫81; the harness cannot compute |Aut| of a 4096-vertex SRG).
    internal sealed class SuzukiHandler : FormFamilyHandlerBase<SuzukiHandler.Inv>
    {
        internal sealed class Inv { public int Q; }

        public override FormFamily Family => FormFamily.Suzuki;

        protected override Inv? RecognizeInvariant(int[] adj, int n)
        {
            int q = IntRoot(n, 4);
            if (q < 8 || IPow(q, 4) != n) return null;   // n = q^4, q ≥ 8
            if (!IsPow2OddExp(q)) return null;            // q = 2^{2e+1} (genuine Suzuki)
            long k = (long)(q * q + 1) * (q - 1);         // valency (q²+1)(q−1)
            if (!RegularWithValency(adj, n, k)) return null;
            return new Inv { Q = q };
        }

        // Sound disambiguation vs the cospectral VO⁻₄(q): the Tits-ovoid cone is genuinely cubic over F₂.
        protected override bool Confirm(int[] adj, int n, CanonResult harvest, Inv inv)
        {
            var aff = Coordinatize(harvest, n);           // F1 socle recovery, p=2 (char-agnostic)
            if (aff is null || aff.P != 2) return false;  // no F₂ coords ⟹ decline (safe)
            var cone = SuzukiOvoid.ConeFromGraph(adj, n, aff);
            return SuzukiOvoid.IsOvoidConeBySignature(cone, aff.Dim);
        }

        protected override int[] StandardGraph(Inv inv) => SuzukiOvoid.StandardGraph(inv.Q);

        protected override BigInteger AutOrder(Inv inv) => RouteCCanonicalizer.SuzukiAutOrder(inv.Q);

        protected override string Describe(Inv inv) => $"Sz({inv.Q})";

        // ── local helpers ───────────────────────────────────────────────────────
        static int IntRoot(int n, int r) { int x = (int)Math.Round(Math.Pow(n, 1.0 / r)); foreach (int c in new[] { x - 1, x, x + 1 }) if (c > 0 && IPow(c, r) == n) return c; return -1; }
        static bool IsPow2OddExp(int q) { if (q < 2) return false; int e = 0, m = q; while (m % 2 == 0) { m /= 2; e++; } return m == 1 && (e % 2 == 1); }
        static bool RegularWithValency(int[] adj, int n, long k)
        {
            for (int v = 0; v < n; v++) { long deg = 0; int b = v * n; for (int w = 0; w < n; w++) deg += adj[b + w]; if (deg != k) return false; }
            return true;
        }
    }
}
