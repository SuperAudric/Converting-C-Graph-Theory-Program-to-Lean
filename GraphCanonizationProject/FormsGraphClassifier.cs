using System;

namespace Canonizer
{
    // Route C — C2: decide which forms-graph family a residue is (docs/chain-descent-route-c-plan.md
    // §9.2.2). The C# analog of the L3 classification citation. Detection is CONSTRUCTIVE and
    // self-validating where a recovery path exists: "it is affine-polar iff the recovered single
    // quadric reconstructs the graph" — so a misclassification is SAFE (a wrong tag ⟹ the recovered
    // structure fails to reconstruct/verify ⟹ the handler declines and the harness falls back to its
    // flag, never a wrong answer). For families whose recovery is future work (alternating / half-spin
    // / Suzuki) it returns a tentative tag from the SRG-parameter fingerprint.
    internal enum FormFamily { Unknown, AffinePolar, Alternating, HalfSpin, Suzuki }

    internal readonly struct FormsGraphClassification
    {
        public FormFamily Family { get; init; }
        public int P { get; init; }       // prime (affine-polar; 0 otherwise)
        public int M { get; init; }       // dim = 2m (affine-polar)
        public int Eps { get; init; }     // +1 / -1 (affine-polar); 0 otherwise
        public override string ToString() =>
            Family == FormFamily.AffinePolar ? $"AffinePolar VO^{(Eps < 0 ? "-" : "+")}_{2 * M}({P})" : Family.ToString();
        public static readonly FormsGraphClassification Unknown = new() { Family = FormFamily.Unknown };
    }

    internal static class FormsGraphClassifier
    {
        // Classify `adj` (flat n×n). `aff` = F1's coordinatization (needed for the constructive
        // affine-polar confirmation); pass null to get the parameter-only (non-confirmed) verdict.
        public static FormsGraphClassification Detect(int[] adj, int n, AffineStructureRecovery.AffineStructure? aff)
        {
            if (!StronglyRegular(adj, n, out int k, out int lam, out int mu))
                return FormsGraphClassification.Unknown;

            // Suzuki–Tits fingerprint: VSz(8) = SRG(4096, 455, 6, 56).
            if (n == 4096 && k == 455 && lam == 6 && mu == 56)
                return new FormsGraphClassification { Family = FormFamily.Suzuki };

            // affine-polar: n = p^d with d = 2m even; valency matches the VO^eps isotropic count.
            if (IsPrimePower(n, out int p, out int d) && d % 2 == 0 && d >= 4)
            {
                int m = d / 2, q = p;
                // #nonzero isotropic vectors of a type-eps form in dim 2m: (q^m - eps)(q^{m-1} + eps)
                foreach (int eps in new[] { +1, -1 })
                {
                    long isotropic = (long)(IPow(q, m) - eps) * (IPow(q, m - 1) + eps);
                    if (isotropic != k) continue;
                    // constructive confirmation: the recovered single quadric reconstructs the graph
                    if (aff is not null && ConfirmAffinePolar(adj, n, aff))
                        return new FormsGraphClassification { Family = FormFamily.AffinePolar, P = p, M = m, Eps = eps };
                    if (aff is null)
                        return new FormsGraphClassification { Family = FormFamily.AffinePolar, P = p, M = m, Eps = eps };
                }
            }

            // alternating / half-spin: recovery not built yet — leave Unknown (safe) unless a param
            // fingerprint is added. (Placeholder for the multi-form C1a/C1b track.)
            return FormsGraphClassification.Unknown;
        }

        // The recovered single quadratic + coords reproduce the whole adjacency (Q(c_x−c_y)=0 ⟺ x~y).
        static bool ConfirmAffinePolar(int[] adj, int n, AffineStructureRecovery.AffineStructure aff)
        {
            var Q = QuadraticFormRecovery.RecoverForm(adj, n, aff);
            if (Q is null) return false;
            int p = aff.P, dim = aff.Dim;
            var d = new int[dim];
            for (int x = 0; x < n; x++)
                for (int y = x + 1; y < n; y++)
                {
                    for (int i = 0; i < dim; i++) d[i] = ((aff.Coords[x][i] - aff.Coords[y][i]) % p + p) % p;
                    if ((Q.Evaluate(d) == 0) != (adj[x * n + y] == 1)) return false;
                }
            return true;
        }

        // Strong regularity: constant valency k, and constant common-neighbour counts λ (adjacent)
        // and μ (non-adjacent). Returns false (with k/λ/μ = -1) if any is non-constant.
        public static bool StronglyRegular(int[] adj, int n, out int k, out int lam, out int mu)
        {
            k = lam = mu = -1;
            if (n <= 1) return false;
            for (int v = 0; v < n; v++)
            {
                int deg = 0;
                for (int w = 0; w < n; w++) if (adj[v * n + w] == 1) deg++;
                if (k == -1) k = deg; else if (deg != k) return false;
            }
            for (int u = 0; u < n; u++)
                for (int v = u + 1; v < n; v++)
                {
                    int common = 0;
                    for (int w = 0; w < n; w++) if (adj[u * n + w] == 1 && adj[v * n + w] == 1) common++;
                    if (adj[u * n + v] == 1) { if (lam == -1) lam = common; else if (common != lam) return false; }
                    else { if (mu == -1) mu = common; else if (common != mu) return false; }
                }
            return true;
        }

        static bool IsPrimePower(int n, out int p, out int d)
        {
            p = 0; d = 0;
            if (n < 2) return false;
            int cand = 2;
            while (n % cand != 0) cand++;          // smallest prime factor
            int m = n, e = 0;
            while (m % cand == 0) { m /= cand; e++; }
            if (m != 1) return false;              // n has ≥ 2 distinct prime factors
            p = cand; d = e; return true;
        }

        static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }
    }
}
