using System;
using System.Collections.Generic;
using System.Linq;

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    // Single-constraint variant of CanonGraphOrdererPartialOrderIR.
    //
    // Every guess writes exactly ONE cell of P: pick one Unknown (incomparable)
    // pair (a, b) and commit a < b. The recursion explores both a < b and b < a
    // for every guessed pair, so the two branches of a pair genuinely partition
    // the order-completions through that pair — no total order is ever implicitly
    // dropped by the guess. (The block guesses of …PartialOrderIR, by ordering a
    // whole vertex below its cell or a whole cell below another, silently discard
    // every interleaving of those vertices; this variant does not.)
    //
    // Why single-pair guesses are safe here but were NOT in
    // CanonGraphOrdererOneWLPartialOrder: there, refinement itself WROTE order
    // into the matrix (a signature comparison concluding a < b), so a single-pair
    // tiebreak perturbed signatures and refinement cascaded that perturbation into
    // a — often wrongly directed — total order. That coupling is what forced that
    // orderer onto whole-class block tiebreaks. Here refinement is split-only: it
    // reads P to subdivide cells and NEVER writes P. Order enters P exclusively
    // through guesses and transitive closure. Given that property, full-strength
    // 1-WL and single-pair guesses coexist cleanly — the refinement does not need
    // to be weakened.
    //
    // Both branches of a guess are always consistent: P[a,b] == Unknown means a, b
    // are incomparable, and adding one relation between two incomparable elements
    // of a partial order can never close a cycle.
    //
    // Cost: a guess is no longer a clean "individualise a cell" unit, so the guess
    // count is not uniform across root-to-leaf paths (different pairs imply
    // different amounts through transitive closure). GuessDepthRange reports the
    // spread instead of a single number.
    //
    // Exponential recursion; clarity over performance.
    public sealed class CanonGraphOrdererPartialOrderSinglePair : ICanonGraphOrderer
    {
        private const sbyte LESS = -1, UNKNOWN = 0, GREATER = 1;

        public AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            int n = G.VertexCount;
            int[] adj = ExtractAdj(G);
            sbyte[] p = SeedFromTypes(n, vertexTypes);

            int[]? best = null;
            var leafDepths = new List<int>();
            Search(n, adj, p, 0, leafDepths, ref best);
            if (best == null)
                throw new InvalidOperationException("PartialOrderSinglePair: no total order reached");

            var result = new EdgeType[n, n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    result[i, j] = best[i * n + j];
            return new AdjMatrix(result);
        }

        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // Diagnostic: (fewest, most) guesses over all root-to-leaf paths, and the
        // number of leaves. Single-pair guessing makes the tree ragged, so a
        // single "guesses per path" number does not exist.
        public (int min, int max, int leaves) GuessDepthRange(VertexType[] vertexTypes, AdjMatrix G)
        {
            int n = G.VertexCount;
            int[] adj = ExtractAdj(G);
            sbyte[] p = SeedFromTypes(n, vertexTypes);

            int[]? best = null;
            var leafDepths = new List<int>();
            Search(n, adj, p, 0, leafDepths, ref best);
            if (leafDepths.Count == 0)
                throw new InvalidOperationException("PartialOrderSinglePair: no total order reached");
            return (leafDepths.Min(), leafDepths.Max(), leafDepths.Count);
        }

        // ── The recursion ─────────────────────────────────────────────────────
        private static void Search(int n, int[] adj, sbyte[] p, int depth,
                                   List<int> leafDepths, ref int[]? best)
        {
            // (1) Derive cells from (adj, P) only. Used purely to GROUP candidate
            //     pairs into an isomorphism-invariant target set — never to order.
            int[] cellOf = Refine(n, adj, p);

            // (2) Leaf? P total ⇔ no Unknown off the diagonal.
            if (IsTotal(n, p))
            {
                leafDepths.Add(depth);
                int[] perm = ReadPermutation(n, p);
                int[] m = new int[n * n];
                for (int i = 0; i < n; i++)
                    for (int j = 0; j < n; j++)
                        m[perm[i] * n + perm[j]] = adj[i * n + j];
                if (best == null || LexLess(m, best)) best = m;
                return;
            }

            // (3) Target = the lex-min cell-pair-type {t1 ≤ t2} (canonical cell
            //     ids) that still has an Unknown ordered pair. t1 == t2 is a
            //     within-cell type; t1 < t2 is a cross-cell type.
            int t1 = -1, t2 = -1;
            for (int u = 0; u < n; u++)
                for (int v = 0; v < n; v++)
                {
                    if (u == v || p[u * n + v] != UNKNOWN) continue;
                    int c1 = Math.Min(cellOf[u], cellOf[v]);
                    int c2 = Math.Max(cellOf[u], cellOf[v]);
                    if (t1 < 0 || c1 < t1 || (c1 == t1 && c2 < t2)) { t1 = c1; t2 = c2; }
                }

            // (4) Branch over every ordered Unknown pair (a, b) of that type,
            //     committing the single constraint a < b. Both directions of each
            //     unordered pair appear (as (a,b) and (b,a)), so nothing is lost.
            for (int a = 0; a < n; a++)
                for (int b = 0; b < n; b++)
                {
                    if (a == b || p[a * n + b] != UNKNOWN) continue;
                    int c1 = Math.Min(cellOf[a], cellOf[b]);
                    int c2 = Math.Max(cellOf[a], cellOf[b]);
                    if (c1 != t1 || c2 != t2) continue;

                    sbyte[] p2 = (sbyte[])p.Clone();
                    p2[a * n + b] = LESS;
                    p2[b * n + a] = GREATER;
                    if (TransitiveClose(p2, n)) // always true for an Unknown pair
                        Search(n, adj, p2, depth + 1, leafDepths, ref best);
                }
        }

        // ── Transitive closure ────────────────────────────────────────────────
        private static bool TransitiveClose(sbyte[] p, int n)
        {
            for (int k = 0; k < n; k++)
                for (int i = 0; i < n; i++)
                {
                    if (p[i * n + k] != LESS) continue;
                    for (int j = 0; j < n; j++)
                    {
                        if (p[k * n + j] != LESS) continue;
                        if (i == j) return false;
                        sbyte cur = p[i * n + j];
                        if (cur == GREATER) return false;
                        if (cur == UNKNOWN) { p[i * n + j] = LESS; p[j * n + i] = GREATER; }
                    }
                }
            return true;
        }

        // ── Refinement (split-only; reads P, never writes it) ─────────────────
        //
        // Identical to CanonGraphOrdererPartialOrderIR.Refine: 1-WL to a fixed
        // point, cells numbered in canonical signature order.
        private static int[] Refine(int n, int[] adj, sbyte[] p)
        {
            int[] color = new int[n];
            while (true)
            {
                int[] next = RefineRound(n, adj, p, color);
                bool same = SamePartition(n, color, next);
                color = next;
                if (same) break;
            }
            return color;
        }

        private static int[] RefineRound(int n, int[] adj, sbyte[] p, int[] color)
        {
            var sigs = new string[n];
            for (int v = 0; v < n; v++)
            {
                var parts = new List<string>(n);
                for (int u = 0; u < n; u++)
                {
                    if (u == v) continue;
                    parts.Add(color[u] + "." + adj[v * n + u] + "." + ((int)p[v * n + u]));
                }
                parts.Sort(StringComparer.Ordinal);
                sigs[v] = color[v] + "/" + string.Join(",", parts);
            }

            var distinct = new List<string>(new HashSet<string>(sigs));
            distinct.Sort(StringComparer.Ordinal);
            var rank = new Dictionary<string, int>(distinct.Count);
            for (int i = 0; i < distinct.Count; i++) rank[distinct[i]] = i;

            var nextColor = new int[n];
            for (int v = 0; v < n; v++) nextColor[v] = rank[sigs[v]];
            return nextColor;
        }

        private static bool SamePartition(int n, int[] a, int[] b)
        {
            for (int i = 0; i < n; i++)
                for (int j = i + 1; j < n; j++)
                    if ((a[i] == a[j]) != (b[i] == b[j])) return false;
            return true;
        }

        // ── Plain helpers ─────────────────────────────────────────────────────

        private static int[] ExtractAdj(AdjMatrix G)
        {
            int n = G.VertexCount;
            var adj = new int[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    adj[i * n + j] = G[i, j];
            return adj;
        }

        private static sbyte[] SeedFromTypes(int n, int[] types)
        {
            var p = new sbyte[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (i != j && types[i] < types[j]) { p[i * n + j] = LESS; p[j * n + i] = GREATER; }
            TransitiveClose(p, n);
            return p;
        }

        private static bool IsTotal(int n, sbyte[] p)
        {
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (i != j && p[i * n + j] == UNKNOWN) return false;
            return true;
        }

        private static int[] ReadPermutation(int n, sbyte[] p)
        {
            var perm = new int[n];
            for (int v = 0; v < n; v++)
            {
                int r = 0;
                for (int u = 0; u < n; u++)
                    if (p[u * n + v] == LESS) r++;
                perm[v] = r;
            }
            return perm;
        }

        private static bool LexLess(int[] a, int[] b)
        {
            for (int i = 0; i < a.Length; i++)
                if (a[i] != b[i]) return a[i] < b[i];
            return false;
        }
    }
}
