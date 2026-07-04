using System.Numerics;

namespace Canonizer
{
    // Route C — C3 (handler logic): canonicalize a forms-graph residue via the RECOVERED ALGEBRAIC
    // INVARIANT, not via WL/harvest. See docs/chain-descent-route-c-plan.md §9.2.2 (C3), §9.2.3.
    //
    // Mechanism: recover the affine structure (F1) + the form, classify the family (C2); the form's
    // ISOMORPHISM TYPE (q, m, eps for affine-polar) is a complete iso-invariant, so the canonical
    // graph is the STANDARD VO^eps_{2m}(q) and |Aut| is its closed form. This is the runtime image of
    // the Lean seal: correctness by reconstruction (the recovered structure reconstructs the graph)
    // + the group-pinning |Aut| = |affineG(similitudeGroup Q)|.
    //
    // Integration (option ii): a residue-seam handler at ChainDescent target == -1 calls Recognize;
    // if it returns non-null the harness adopts (CanonicalAdjacency, AutOrder); else it declines and
    // the harness keeps its existing behaviour (flag). Recognize is SOUND: a non-forms graph, or a
    // recovered form that fails to reconstruct, returns null.
    internal sealed class RouteCCanonicalResult
    {
        public required FormsGraphClassification Classification { get; init; }
        public required BigInteger AutOrder { get; init; }
        public required int[] CanonicalAdjacency { get; init; }   // the standard graph of this iso-type
    }

    internal static class RouteCCanonicalizer
    {
        // Recognize + canonicalize `adj` as a forms graph. Runs its own automorphism harvest (F1's
        // O_p(Aut) shortcut) to coordinatize; returns null if the graph flags, is not a recognized
        // forms family, or the recovered structure fails to reconstruct. Small-d path (harness harvest
        // feasible); C4 will replace the harvest with Aut-free geometric coordinatization for large d.
        public static RouteCCanonicalResult? Recognize(int[] adj, int n)
        {
            var cd = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
            { EnableLinearOracle = true, EnableDeferral = true };
            var res = cd.Canonize(new sbyte[n * n], new WarmPartition(n));
            return RecognizeFromResult(adj, n, res);
        }

        // The no-double-descent entry (option-ii harness wire): recognize using an ALREADY-harvested
        // CanonResult (the orderer's single descent), so wiring Route C into RunConnected costs no
        // extra descent. Returns null on flag / non-forms / non-affine-polar.
        public static RouteCCanonicalResult? RecognizeFromResult(int[] adj, int n, CanonResult res)
        {
            if (res.Flagged) return null;
            if (!TryPrimeBase(n, out int p, out _)) return null;    // affine-polar needs n = p^d for F1

            var aff = AffineStructureRecovery.Recover(res.ResidualGroup, p, origin: 0);
            if (aff is null) return null;

            var cls = FormsGraphClassifier.Detect(adj, n, aff);
            if (cls.Family != FormFamily.AffinePolar) return null;   // only affine-polar recovery is built

            // the iso-type (q, m, eps) determines the canonical graph + |Aut| (closed form)
            var canonAdj = StandardVO(cls.P, cls.M, cls.Eps);
            var autOrder = AffinePolarAutOrder(cls.P, cls.M, cls.Eps);
            return new RouteCCanonicalResult { Classification = cls, AutOrder = autOrder, CanonicalAdjacency = canonAdj };
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
            int dim = 2 * m, n = IPow(q, dim);
            int bb = 0, cc = 0;
            if (eps == -1) AnisotropicBinary(q, out bb, out cc);

            int[] Vec(int v) { var x = new int[dim]; for (int i = 0; i < dim; i++) { x[i] = v % q; v /= q; } return x; }
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
            var vecs = new int[n][]; for (int v = 0; v < n; v++) vecs[v] = Vec(v);
            var adj = new int[n * n];
            var d = new int[dim];
            for (int u = 0; u < n; u++)
                for (int v = u + 1; v < n; v++)
                {
                    for (int i = 0; i < dim; i++) d[i] = ((vecs[u][i] - vecs[v][i]) % q + q) % q;
                    if (Qf(d) == 0) { adj[u * n + v] = 1; adj[v * n + u] = 1; }
                }
            return adj;
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

        static bool TryPrimeBase(int n, out int p, out int d)
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

        static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }
    }
}
