using System.Numerics;

namespace Canonizer
{
    // Route C — C3 (the family-dispatch entry): canonicalize a forms-graph residue via the RECOVERED
    // ALGEBRAIC INVARIANT, not via WL/harvest. See docs/chain-descent-route-c-plan.md §9.2.2 / §9.2.7.
    //
    // Mechanism: each node-4 family {affine-polar, alternating, half-spin, Suzuki} has an
    // IFormFamilyHandler that recognizes its iso-type (a COMPLETE invariant), confirms it (rules out a
    // parameter-mate), and emits the STANDARD canonical graph + closed-form |Aut|. This dispatch tries
    // the handlers in order; the first that recognizes wins. Only affine-polar is fully built; the other
    // handlers are dormant scaffolds (they return null ⟹ fall back to the descent — SAFE).
    //
    // Integration (option ii): the orderer wire (CanonGraphOrdererChainDescent) calls RecognizeFromResult
    // with its already-harvested CanonResult (no extra descent).
    internal static class RouteCCanonicalizer
    {
        // The family-handler registry (dispatch order). affine-polar first (the built family); the
        // others are scaffolds — see each handler's STATUS.
        static readonly IFormFamilyHandler[] Handlers =
        {
            new AffinePolarHandler(),
            new AlternatingHandler(),
            new HalfSpinHandler(),
            new SuzukiHandler(),
        };

        // Recognize + canonicalize `adj` as a forms graph, running its own descent harvest. Returns
        // null if the graph flags or no family recognizes it.
        public static RouteCCanonicalResult? Recognize(int[] adj, int n)
        {
            var cd = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
            { EnableLinearOracle = true, EnableDeferral = true };
            var res = cd.Canonize(new sbyte[n * n], new WarmPartition(n));
            return RecognizeFromResult(adj, n, res);
        }

        // The no-double-descent entry (option-ii harness wire): dispatch over the family handlers using
        // an ALREADY-harvested CanonResult. First recognizer wins; null if none.
        public static RouteCCanonicalResult? RecognizeFromResult(int[] adj, int n, CanonResult res)
        {
            if (res.Flagged) return null;
            foreach (var h in Handlers)
            {
                var r = h.TryCanonicalize(adj, n, res);
                if (r is not null) return r;
            }
            return null;
        }

        // |affineG^eps_{2m}(q)| = q^{2m} · [ 2 q^{m(m-1)} (q^m - eps) ∏_{i=1}^{m-1}(q^{2i}-1) ] · (q-1)
        //   = |translations| · |O^eps_{2m}(q)| · |similitude factor group (q-1)|   (q = p prime).
        public static BigInteger AffinePolarAutOrder(int q, int m, int eps)
        {
            BigInteger Q = q;
            BigInteger o = 2 * BigInteger.Pow(Q, m * (m - 1)) * (BigInteger.Pow(Q, m) - eps);
            for (int i = 1; i < m; i++) o *= BigInteger.Pow(Q, 2 * i) - 1;
            return BigInteger.Pow(Q, 2 * m) * o * (Q - 1);
        }

        // The standard affine-polar graph VO^eps_{2m}(q) on (F_q)^{2m}, natural vertex order, standard
        // form Q = sum_{i<m-?} x_{2i}x_{2i+1} (+ anisotropic binary tail y^2+by z+c z^2 for eps=-1).
        public static int[] StandardVO(int q, int m, int eps)
        {
            int dim = 2 * m;
            int bb = 0, cc = 0;
            if (eps == -1) AnisotropicBinary(q, out bb, out cc);

            int Qf(int[] x)
            {
                int s = 0, hyp = eps == -1 ? m - 1 : m;
                for (int i = 0; i < hyp; i++) s = (s + x[2 * i] * x[2 * i + 1]) % q;
                if (eps == -1)
                {
                    int y = x[2 * (m - 1)], z = x[2 * (m - 1) + 1];
                    s = (s + (y * y + bb * y % q * z) % q + cc * (z * z % q)) % q;
                }
                return ((s % q) + q) % q;
            }
            return FormsGraphBuilder.StandardCayleyGraph(q, dim, d => Qf(d) == 0);
        }

        static void AnisotropicBinary(int q, out int bb, out int cc)
        {
            bb = 0; cc = 0;
            for (int b = 0; b < q; b++)
                for (int c = 0; c < q; c++)
                {
                    bool aniso = true;
                    for (int y = 0; y < q && aniso; y++)
                        for (int z = 0; z < q; z++)
                        {
                            if (y == 0 && z == 0) continue;
                            int g = ((y * y + b * y % q * z) % q + c * (z * z % q)) % q;
                            if (g % q == 0) { aniso = false; break; }
                        }
                    if (aniso) { bb = b; cc = c; return; }
                }
        }

        static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }
    }
}
