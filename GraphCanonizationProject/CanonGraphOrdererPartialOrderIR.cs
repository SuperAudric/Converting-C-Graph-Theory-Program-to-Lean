using System;
using System.Collections.Generic;
using System.Linq;

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    // Individualization–refinement canonizer whose ONLY persistent state is the
    // partial-ordering matrix P.
    //
    //   P[u, v] ∈ { Less, Unknown, Greater }, antisymmetric, transitively closed.
    //   P begins "empty" (all Unknown) apart from the order vertex types force.
    //
    // Nothing else is carried between recursion levels. The vertex partition
    // ("cells") and the order between cells are RE-DERIVED from (adj, P) at every
    // node — they are pure functions of the state, never stored.
    //
    // ── Two operations ────────────────────────────────────────────────────────
    //
    //   Refine (free, no guess): 1-WL colour refinement that READS P. Each
    //     vertex's colour is its sorted multiset of (neighbour colour, edge,
    //     P-relation) tuples, iterated to a fixed point. Refinement only ever
    //     SPLITS cells. It never writes to P — in particular it never invents an
    //     order between two cells. A split leaves the new sub-cells incomparable
    //     unless P already related them.
    //
    //   Guess (writes P, one recursion level): the only thing that ever adds to
    //     P. Two kinds, and a guess adds the *minimal* relation for one decision:
    //       • within-cell — individualise one vertex v of a cell C as the cell
    //         minimum: add v < (C \ {v}). The rest of C stays mutually Unknown.
    //       • between-cell — order two P-incomparable cells X, Y as whole blocks:
    //         add x < y for every x∈X, y∈Y (or the reverse).
    //     between-cell is preferred over within-cell, so a cell is split into a
    //     total order before its interior is touched.
    //
    // The recursion branches over every choice in an isomorphism-invariant set
    // (every vertex of the target cell; both directions of the target cell pair),
    // recurses, and keeps the lexicographically minimal permuted matrix over all
    // leaves. Because every leaf is a genuine relabelling of the input, the
    // lex-min leaf is automatically a complete canonical form: lex-min(G) ≅ G, so
    // lex-min(G) = lex-min(H) ⟹ G ≅ H. Refinement strength only affects how much
    // the tree is pruned, never correctness.
    //
    // Why "partial": a within-cell guess records v < (C\{v}) and NOTHING about
    // how C\{v} orders internally. On a triangle, individualising one vertex
    // leaves the other two a genuine 2-cell — a second guess is unavoidable. An
    // implementation that finished the triangle in one guess would be writing a
    // *total* order per guess, not using P as a partial order.
    //
    // Exponential recursion; clarity over performance.
    public sealed class CanonGraphOrdererPartialOrderIR : ICanonGraphOrderer
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
            var leafDepths = new HashSet<int>();
            Search(n, adj, p, 0, leafDepths, ref best);
            if (best == null)
                throw new InvalidOperationException("PartialOrderIR: no total order reached");

            var result = new EdgeType[n, n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    result[i, j] = best[i * n + j];
            return new AdjMatrix(result);
        }

        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // Diagnostic. Runs the full search and returns the guess count on every
        // root-to-leaf path. Throws if the tree is ragged (paths disagree) — that
        // would mean the guess discipline is not well defined.
        public int GuessesPerPath(VertexType[] vertexTypes, AdjMatrix G)
        {
            int n = G.VertexCount;
            int[] adj = ExtractAdj(G);
            sbyte[] p = SeedFromTypes(n, vertexTypes);

            int[]? best = null;
            var leafDepths = new HashSet<int>();
            Search(n, adj, p, 0, leafDepths, ref best);

            if (leafDepths.Count == 0)
                throw new InvalidOperationException("PartialOrderIR: no total order reached");
            if (leafDepths.Count != 1)
                throw new InvalidOperationException(
                    "PartialOrderIR: guess depth not uniform across paths: " +
                    string.Join(", ", leafDepths.OrderBy(d => d)));
            return leafDepths.First();
        }

        // ── The recursion ─────────────────────────────────────────────────────
        //
        // depth == number of guesses made on the path from the root to here.
        private static void Search(int n, int[] adj, sbyte[] p, int depth,
                                   HashSet<int> leafDepths, ref int[]? best)
        {
            // (1) Derive the cells from (adj, P) alone. cellOf[v] is a canonical
            //     cell id: cells are numbered in canonical signature order, so any
            //     "lex-min cell / cell pair" rule below is isomorphism-invariant.
            int[] cellOf = Refine(n, adj, p);

            // (2) Leaf? P is a total order ⇔ no Unknown off the diagonal.
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

            int numCells = cellOf.Max() + 1;
            var cells = new List<List<int>>(numCells);
            for (int c = 0; c < numCells; c++) cells.Add(new List<int>());
            for (int v = 0; v < n; v++) cells[cellOf[v]].Add(v);

            // (3a) between-cell guess — preferred. Target = lex-min (a<b) cell pair
            //      that still has an Unknown cross entry. Branch both directions.
            int ba = -1, bb = -1;
            for (int u = 0; u < n; u++)
                for (int v = 0; v < n; v++)
                {
                    if (cellOf[u] == cellOf[v] || p[u * n + v] != UNKNOWN) continue;
                    int ca = Math.Min(cellOf[u], cellOf[v]);
                    int cb = Math.Max(cellOf[u], cellOf[v]);
                    if (ba < 0 || ca < ba || (ca == ba && cb < bb)) { ba = ca; bb = cb; }
                }

            if (ba >= 0)
            {
                foreach (sbyte dir in new[] { LESS, GREATER })
                {
                    sbyte[] p2 = (sbyte[])p.Clone();
                    if (ApplyBetween(p2, n, cells[ba], cells[bb], dir))
                        Search(n, adj, p2, depth + 1, leafDepths, ref best);
                }
                return;
            }

            // (3b) within-cell guess. Target = lex-min cell id that is a
            //      non-singleton with an Unknown interior pair. Branch over
            //      individualising each member as the cell minimum.
            int target = -1;
            for (int c = 0; c < numCells && target < 0; c++)
            {
                var mem = cells[c];
                if (mem.Count < 2) continue;
                for (int i = 0; i < mem.Count && target < 0; i++)
                    for (int j = i + 1; j < mem.Count; j++)
                        if (p[mem[i] * n + mem[j]] == UNKNOWN) { target = c; break; }
            }
            if (target < 0)
                throw new InvalidOperationException("PartialOrderIR: non-total P with no guessable pair");

            foreach (int v in cells[target])
            {
                sbyte[] p2 = (sbyte[])p.Clone();
                if (ApplyIndividualize(p2, n, v, cells[target]))
                    Search(n, adj, p2, depth + 1, leafDepths, ref best);
            }
        }

        // ── Guesses (the only writers of P) ───────────────────────────────────

        // Order cell A entirely below (dir == LESS) or above (dir == GREATER)
        // cell B. Returns false if that contradicts an existing relation.
        private static bool ApplyBetween(sbyte[] p, int n, List<int> a, List<int> b, sbyte dir)
        {
            foreach (int u in a)
                foreach (int v in b)
                {
                    sbyte cur = p[u * n + v];
                    if (cur == UNKNOWN) { p[u * n + v] = dir; p[v * n + u] = (sbyte)(-dir); }
                    else if (cur != dir) return false;
                }
            return TransitiveClose(p, n);
        }

        // Individualise v as the minimum of its cell: v < every other member.
        private static bool ApplyIndividualize(sbyte[] p, int n, int v, List<int> cell)
        {
            foreach (int u in cell)
            {
                if (u == v) continue;
                sbyte cur = p[v * n + u];
                if (cur == UNKNOWN) { p[v * n + u] = LESS; p[u * n + v] = GREATER; }
                else if (cur != LESS) return false;
            }
            return TransitiveClose(p, n);
        }

        // Floyd–Warshall transitive closure of the Less relation. Returns false on
        // a contradiction (a cycle, i.e. x < x becomes derivable).
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

        // ── Refinement (free; reads P, never writes it) ───────────────────────
        //
        // 1-WL to a fixed point. Returns cellOf[v] = canonical cell id, cells
        // numbered in ascending signature order.
        private static int[] Refine(int n, int[] adj, sbyte[] p)
        {
            int[] color = new int[n]; // one cell to start
            while (true)
            {
                int[] next = RefineRound(n, adj, p, color);
                bool same = SamePartition(n, color, next);
                color = next;            // `next` always carries canonical labels
                if (same) break;         // grouping stabilised
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

        // True when two colourings induce the same grouping (labels may differ).
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

        // P starts "empty" except for the order vertex types force: a lower type
        // is below a higher type. (For unlabelled graphs this is all Unknown.)
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

        // Total P ⇒ rank(v) = number of vertices below v ⇒ a permutation.
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
