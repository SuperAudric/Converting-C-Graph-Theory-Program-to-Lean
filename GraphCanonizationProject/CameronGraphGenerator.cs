using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

// Cameron-group graph generator — the EOL "Cameron battery" positive controls.
//
// Purpose (docs/chain-descent-exhaustive-obstruction.md §5 Approach 2, §4 R1)
// ---------------------------------------------------------------------------
// The Exhaustive-Obstruction Lemma's hypothesis is about residuals that are
// non-cascade AND non-abelian — the "Cameron section" case. But the near-theorem
// (docs/chain-descent-hidden-johnson.md, calculator §7) says a graph whose
// *visible* automorphism group is a Cameron group has its edge set equal to a
// union of association-scheme classes — so it IS a scheme graph, hence CASCADES
// (theorem_2_HOR_of_pPolynomial: the whole metric/DRG family recovers at depth 1)
// and the canonizer CANONIZES it. The genuinely hard residual (non-cascade,
// non-abelian) requires an ENCODED Cameron section (CFI-style) — the GI-hard
// (O*)-existence construction, the open EOL research frontier, not built here.
//
// So this battery is the POSITIVE-CONTROL / scheme-validation half of Approach 2:
//   * Johnson J(n,k) — the d=1 Cameron case (A_k on k-subsets, Aut = S_n).
//   * Hamming H(d,q) — the product-action Cameron case (Aut = S_q ≀ S_d), the
//     direct control for refutation angle R1 ("Johnson is too narrow — product
//     actions"); Hamming is exactly a product-action Cameron group.
//   * Kneser K(n,k) — a second S_n control (Petersen = K(5,2)).
// Each carries its KNOWN |Aut| in closed form so the probe can validate the
// canonizer's harvested group order against ground truth — the strongest
// checkable signal that the scheme/cascade leg and the a-posteriori harvest
// actually fire (the canonizer-level analogue of the D18 / D9≀Z2 group tests).
//
// The hypothesis predicts every instance CANONIZES (cascade, symmetry consumed),
// with NO Tier2Like flag; a Cameron-group graph that unexpectedly flags is a
// gap-B finding (built oracle vs. proven cascade) and is exactly what the battery
// is looking for.
//
// References
// ----------
//   - Brouwer, Cohen, Neumaier, "Distance-Regular Graphs" (1989) — Johnson,
//     Hamming, Kneser schemes and their automorphism groups.
//   - Cameron, "Permutation Groups" (1999) — product-action / Cameron groups.

namespace Canonizer
{
    using EdgeType = Int32;

    public static class CameronGraphGenerator
    {
        /// <summary>
        /// A Cameron-family graph and its known automorphism-group order. `Family`
        /// is "Johnson" / "Hamming" / "Kneser"; `KnownAutOrder` is the closed-form
        /// |Aut(G)| the probe validates the harvested order against.
        /// </summary>
        public record CameronGraph(
            AdjMatrix Graph,
            string Name,
            BigInteger KnownAutOrder,
            string Family,
            int VertexCount);

        // ── Johnson J(n,k): k-subsets of [n], adjacent iff |A ∩ B| = k − 1 ───────

        public static CameronGraph Johnson(int n, int k)
        {
            if (k < 1 || k >= n) throw new ArgumentException("Johnson requires 1 ≤ k < n.");
            var sets = Subsets(n, k);
            int v = sets.Count;
            var adj = new EdgeType[v, v];
            for (int i = 0; i < v; i++)
                for (int j = i + 1; j < v; j++)
                    if (IntersectionSize(sets[i], sets[j]) == k - 1)
                        adj[i, j] = adj[j, i] = 1;

            // Aut(J(n,k)) = S_n  (n ≠ 2k);  S_n × Z_2  (n = 2k, complementation).
            var autOrder = Factorial(n);
            if (n == 2 * k) autOrder *= 2;
            return new CameronGraph(new AdjMatrix(adj), $"J({n},{k})", autOrder, "Johnson", v);
        }

        // ── Hamming H(d,q): [q]^d, adjacent iff they differ in exactly one coord ─

        public static CameronGraph Hamming(int d, int q)
        {
            if (d < 1 || q < 2) throw new ArgumentException("Hamming requires d ≥ 1, q ≥ 2.");
            var words = Words(d, q);
            int v = words.Count;
            var adj = new EdgeType[v, v];
            for (int i = 0; i < v; i++)
                for (int j = i + 1; j < v; j++)
                    if (HammingDistance(words[i], words[j]) == 1)
                        adj[i, j] = adj[j, i] = 1;

            // Aut(H(d,q)) = S_q ≀ S_d, order (q!)^d · d!.
            var autOrder = BigInteger.Pow(Factorial(q), d) * Factorial(d);
            return new CameronGraph(new AdjMatrix(adj), $"H({d},{q})", autOrder, "Hamming", v);
        }

        // ── Kneser K(n,k): k-subsets of [n], adjacent iff disjoint ───────────────

        public static CameronGraph Kneser(int n, int k)
        {
            if (k < 1 || n < 2 * k + 1)
                throw new ArgumentException("Kneser requires n ≥ 2k + 1 (avoid the n = 2k perfect matching).");
            var sets = Subsets(n, k);
            int v = sets.Count;
            var adj = new EdgeType[v, v];
            for (int i = 0; i < v; i++)
                for (int j = i + 1; j < v; j++)
                    if (IntersectionSize(sets[i], sets[j]) == 0)
                        adj[i, j] = adj[j, i] = 1;

            // Aut(K(n,k)) = S_n for n ≥ 2k + 1.
            return new CameronGraph(new AdjMatrix(adj), $"K({n},{k})", Factorial(n), "Kneser", v);
        }

        // ── Diagnostics ──────────────────────────────────────────────────────────

        /// <summary>
        /// Sanity-check structural invariants: square symmetric loopless graph,
        /// the expected vertex count, and regularity (every Cameron-family graph
        /// above is vertex-transitive, hence regular). Throws on failure so a probe
        /// failure can be trusted as a canonizer finding, not a generator artifact.
        /// </summary>
        public static void AssertWellFormed(CameronGraph cg)
        {
            int n = cg.Graph.VertexCount;
            if (n != cg.VertexCount)
                throw new InvalidOperationException($"{cg.Name}: vertex count mismatch.");
            int deg0 = -1;
            for (int i = 0; i < n; i++)
            {
                if (cg.Graph[i, i] != 0)
                    throw new InvalidOperationException($"{cg.Name} is not loopless at {i}.");
                int deg = 0;
                for (int j = 0; j < n; j++)
                {
                    if (cg.Graph[i, j] != cg.Graph[j, i])
                        throw new InvalidOperationException($"{cg.Name} adjacency is not symmetric at ({i},{j}).");
                    if (i != j && cg.Graph[i, j] != 0) deg++;
                }
                if (deg0 < 0) deg0 = deg;
                else if (deg != deg0)
                    throw new InvalidOperationException($"{cg.Name} is not regular ({deg} ≠ {deg0} at {i}).");
            }
        }

        // ── internals ──────────────────────────────────────────────────────────

        // All k-subsets of {0,..,n-1}, each as a sorted int[], in lexicographic order.
        private static List<int[]> Subsets(int n, int k)
        {
            var result = new List<int[]>();
            var cur = new int[k];
            void Rec(int start, int depth)
            {
                if (depth == k) { result.Add((int[])cur.Clone()); return; }
                for (int x = start; x <= n - (k - depth); x++)
                {
                    cur[depth] = x;
                    Rec(x + 1, depth + 1);
                }
            }
            Rec(0, 0);
            return result;
        }

        // All length-d words over {0,..,q-1}, in mixed-radix (lexicographic) order.
        private static List<int[]> Words(int d, int q)
        {
            int total = (int)BigInteger.Pow(q, d);
            var result = new List<int[]>(total);
            for (int code = 0; code < total; code++)
            {
                var w = new int[d];
                int c = code;
                for (int p = d - 1; p >= 0; p--) { w[p] = c % q; c /= q; }
                result.Add(w);
            }
            return result;
        }

        // |A ∩ B| for two sorted int[] (merge walk).
        private static int IntersectionSize(int[] a, int[] b)
        {
            int i = 0, j = 0, c = 0;
            while (i < a.Length && j < b.Length)
            {
                if (a[i] == b[j]) { c++; i++; j++; }
                else if (a[i] < b[j]) i++;
                else j++;
            }
            return c;
        }

        private static int HammingDistance(int[] a, int[] b)
        {
            int c = 0;
            for (int i = 0; i < a.Length; i++) if (a[i] != b[i]) c++;
            return c;
        }

        private static BigInteger Factorial(int x)
        {
            BigInteger f = 1;
            for (int i = 2; i <= x; i++) f *= i;
            return f;
        }
    }
}
