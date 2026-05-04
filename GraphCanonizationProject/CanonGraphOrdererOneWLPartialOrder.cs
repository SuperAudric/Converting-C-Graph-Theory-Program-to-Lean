using System;

// 1-WL canonizer whose persistent rank state is a partial-ordering matrix
// rather than a vertex-type / integer-rank array.
//
// Where CanonGraphOrdererOneWL keeps an int[] ranks and refines it via
// dense-ranked signatures, this orderer keeps an N×N matrix M with each
// off-diagonal cell M[a, b] ∈ {Less, Greater, Unknown} — meaning a<b, a>b,
// or "we don't know yet (tie or incomparable)". Refinement turns Unknown
// cells into Less/Greater whenever a 1-WL signature comparison provides
// evidence; the outer loop forces an arbitrary tiebreak on the lex-smallest
// remaining Unknown pair and propagates by transitive closure, until the
// matrix is total.
//
// Differences from CanonGraphOrdererOneWL:
//   * State is a small dedicated class (PartialOrder), not a flat int[].
//   * Refinement is pairwise: each Unknown (a, b) is examined and either
//     resolved or left Unknown for a later iteration. The original orderer
//     dense-ranks all vertices in one shot.
//   * Tiebreak is a structural operation on the partial order ("force the
//     lex-smallest Unknown pair to Less, then close transitively") rather
//     than an in-place rank shift.
//
// Code clarity is prioritized over performance. The algorithm is roughly
// O(N^7); vertex counts beyond a couple of dozen will be slow.

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    public sealed class CanonGraphOrdererOneWLPartialOrder : ICanonGraphOrderer
    {
        public AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            int[] adj = ExtractAdj(G);
            var po = PartialOrder.FromVertexTypes(vertexTypes);
            po.TransitiveClose();

            while (!po.IsTotal())
            {
                RefineToFixedPoint(po, adj);
                if (po.IsTotal()) break;
                BreakLowestTiedClass(po);
                po.TransitiveClose();
            }

            return PermuteByPartialOrder(G, po);
        }

        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // ── PartialOrder ───────────────────────────────────────────────────────
        //
        // Wraps an N×N matrix of {Less, Unknown, Greater} that maintains the
        // antisymmetry invariant on every Set (M[a,b]=Less ⇔ M[b,a]=Greater)
        // and offers explicit transitive closure. Diagonal cells are always
        // Unknown.
        public enum Ordering : sbyte { Less = -1, Unknown = 0, Greater = 1 }

        public sealed class PartialOrder
        {
            public readonly int N;
            private readonly Ordering[] M;

            private PartialOrder(int n)
            {
                N = n;
                M = new Ordering[n * n];
            }

            public static PartialOrder FromVertexTypes(int[] vertexTypes)
            {
                int n = vertexTypes.Length;
                var po = new PartialOrder(n);
                for (int a = 0; a < n; a++)
                {
                    for (int b = 0; b < n; b++)
                    {
                        if (a == b) continue;
                        if (vertexTypes[a] < vertexTypes[b])      po.M[a * n + b] = Ordering.Less;
                        else if (vertexTypes[a] > vertexTypes[b]) po.M[a * n + b] = Ordering.Greater;
                    }
                }
                return po;
            }

            public Ordering Compare(int a, int b) => M[a * N + b];

            public void Set(int a, int b, Ordering ord)
            {
                if (a == b) throw new InvalidOperationException("A vertex has no ordering with itself");
                if (ord == Ordering.Unknown) throw new InvalidOperationException("Cannot regress a cell to Unknown");
                Ordering existing = M[a * N + b];
                if (existing != Ordering.Unknown && existing != ord)
                    throw new InvalidOperationException(
                        $"Inconsistent ordering at ({a},{b}): existing {existing}, new {ord}");
                M[a * N + b] = ord;
                M[b * N + a] = (Ordering)(-(int)ord);
            }

            // Vertices definitely below v (M[u, v] == Less).
            public int BelowCount(int v)
            {
                int count = 0;
                for (int u = 0; u < N; u++)
                    if (u != v && M[u * N + v] == Ordering.Less) count++;
                return count;
            }

            // Vertices definitely above v (M[u, v] == Greater).
            public int AboveCount(int v)
            {
                int count = 0;
                for (int u = 0; u < N; u++)
                    if (u != v && M[u * N + v] == Ordering.Greater) count++;
                return count;
            }

            public bool IsTotal()
            {
                for (int i = 0; i < N; i++)
                    for (int j = i + 1; j < N; j++)
                        if (M[i * N + j] == Ordering.Unknown) return false;
                return true;
            }

            // Lex-smallest (a, b) with a < b and M[a, b] Unknown, or null.
            public (int A, int B)? LexSmallestUnknownPair()
            {
                for (int i = 0; i < N; i++)
                    for (int j = i + 1; j < N; j++)
                        if (M[i * N + j] == Ordering.Unknown) return (i, j);
                return null;
            }

            // Floyd-Warshall over Less. After this call, for every chain
            // a < x_1 < … < x_k < b implied by M, the cell M[a, b] is Less.
            // Throws on cycle (which would mean callers violated antisymmetry).
            public void TransitiveClose()
            {
                for (int k = 0; k < N; k++)
                {
                    for (int i = 0; i < N; i++)
                    {
                        if (i == k || M[i * N + k] != Ordering.Less) continue;
                        for (int j = 0; j < N; j++)
                        {
                            if (j == i || j == k) continue;
                            if (M[k * N + j] != Ordering.Less) continue;
                            Ordering ij = M[i * N + j];
                            if (ij == Ordering.Greater)
                                throw new InvalidOperationException(
                                    $"Cycle: {i} < {k} < {j} contradicts existing {i} > {j}");
                            if (ij == Ordering.Unknown)
                            {
                                M[i * N + j] = Ordering.Less;
                                M[j * N + i] = Ordering.Greater;
                            }
                        }
                    }
                }
            }
        }

        // ── Signatures ─────────────────────────────────────────────────────────
        //
        // A vertex v's signature is its own colour Lead followed by the sorted
        // multiset of NeighborEntry tuples — one per u ∈ V. Each entry records
        //
        //   * Color    — u's own (BelowCount, AboveCount) packed into an int.
        //                Two vertices with the same (Below, Above) are treated
        //                as the same colour. This is coarser than 1-WL would
        //                be and will need refining once the partial order is
        //                allowed to have a < b, b ≈ c, a ≁ c, but it is sound
        //                today: a transitive partial order with all "ties"
        //                being mutually unknown means same-(Below, Above) is
        //                still an equivalence.
        //
        //   * IsSelf   — whether u == v. Without this bit, a self-loop edge
        //                of type t at v collides with a same-colour neighbour
        //                connected by a t-edge.
        //
        //   * Relation — M[v, u]. *This is the key fix versus a vanilla 1-WL
        //                signature.* Without it, a vertex with two edges, both
        //                to colour-X neighbours that lie *above* it, looks
        //                identical to a vertex with two edges, both to
        //                colour-X neighbours that lie *below* it.
        //
        //   * Edge     — adj[v, u].
        //
        // Lead = colour(v) is preserved as an early-out tiebreak (a < b in M
        // ⇒ Lead(a) < Lead(b)) and ensures that whenever M already orders the
        // pair, refinement can never contradict it.
        //
        // Comparison order within a NeighborEntry: Color → IsSelf → Relation →
        // Edge. Comparison across two VertexSigs: Lead → Tail element-by-
        // element on the sorted multiset.

        private readonly struct NeighborEntry(int color, bool isSelf, Ordering relation, int edge)
            : IComparable<NeighborEntry>
        {
            public readonly int Color = color;
            public readonly bool IsSelf = isSelf;
            public readonly Ordering Relation = relation;
            public readonly int Edge = edge;

            public int CompareTo(NeighborEntry o)
            {
                int c = Color.CompareTo(o.Color);
                if (c != 0) return c;
                c = IsSelf.CompareTo(o.IsSelf);
                if (c != 0) return c;
                c = ((sbyte)Relation).CompareTo((sbyte)o.Relation);
                if (c != 0) return c;
                return Edge.CompareTo(o.Edge);
            }
        }

        private readonly struct VertexSig(int lead, NeighborEntry[] tail)
            : IComparable<VertexSig>
        {
            public readonly int Lead = lead;
            public readonly NeighborEntry[] Tail = tail;

            public int CompareTo(VertexSig o)
            {
                int c = Lead.CompareTo(o.Lead);
                if (c != 0) return c;
                for (int i = 0; i < Tail.Length; i++)
                {
                    c = Tail[i].CompareTo(o.Tail[i]);
                    if (c != 0) return c;
                }
                return 0;
            }
        }

        // ── Refinement ─────────────────────────────────────────────────────────
        //
        // Until a step makes no change, build VertexSigs over the current
        // partial order and resolve every Unknown pair (a, b) whose signatures
        // differ. Lex order on signatures is transitive, so refinement never
        // produces an entry that contradicts the existing matrix.

        private static void RefineToFixedPoint(PartialOrder po, int[] adj)
        {
            int maxIters = po.N * po.N + 1;
            for (int iter = 0; iter < maxIters; iter++)
                if (!RefineOneStep(po, adj)) return;
        }

        private static bool RefineOneStep(PartialOrder po, int[] adj)
        {
            int n = po.N;
            VertexSig[] sigs = BuildSignatures(po, adj);

            bool anyChange = false;
            for (int a = 0; a < n; a++)
            {
                for (int b = a + 1; b < n; b++)
                {
                    if (po.Compare(a, b) != Ordering.Unknown) continue;
                    int cmp = sigs[a].CompareTo(sigs[b]);
                    if (cmp == 0) continue;
                    po.Set(a, b, cmp < 0 ? Ordering.Less : Ordering.Greater);
                    anyChange = true;
                }
            }
            return anyChange;
        }

        private static VertexSig[] BuildSignatures(PartialOrder po, int[] adj)
        {
            int n = po.N;

            int[] color = new int[n];
            for (int v = 0; v < n; v++)
                color[v] = (po.BelowCount(v) << 16) | (po.AboveCount(v) & 0xFFFF);

            var sigs = new VertexSig[n];
            for (int v = 0; v < n; v++)
            {
                var tail = new NeighborEntry[n];
                int rowBase = v * n;
                for (int u = 0; u < n; u++)
                    tail[u] = new NeighborEntry(
                        color: color[u],
                        isSelf: u == v,
                        relation: po.Compare(v, u),
                        edge: adj[rowBase + u]);
                Array.Sort(tail);
                sigs[v] = new VertexSig(color[v], tail);
            }
            return sigs;
        }

        // ── Tiebreak ───────────────────────────────────────────────────────────
        //
        // Mirrors CanonGraphOrdererOneWL.BreakTieInPlace, which keeps the
        // lowest-index member of the lowest-rank tied class at its current
        // rank and shifts EVERY OTHER member of the class up by one. Setting
        // a single pair's relation here was a real bug: it left the rest of
        // the tied class with their original (Below, Above) levels, so the
        // un-touched members ended up at lower levels than the "chosen"
        // vertex (whose AboveCount went up by one) and refinement resolved
        // them BELOW chosen — the opposite of what BreakTieInPlace does.
        //
        // At a fixed point of refinement, sig(a) = sig(b) ⇔ M[a,b] = Unknown,
        // so "every vertex Unknown relative to chosen" is exactly chosen's
        // tied class. Promoting the whole set above chosen in one pass is
        // the partial-order analogue of OneWL's whole-class shift.
        //
        // No cycle is possible: the prior TransitiveClose has already pushed
        // any implied inequalities into M, so any (chosen, u) still Unknown
        // is genuinely comparable in the integer-rank world.
        private static void BreakLowestTiedClass(PartialOrder po)
        {
            int n = po.N;

            // Find the lowest-leveled vertex that still has any Unknown
            // relation. Lowest-leveled, not lowest-INDEX, mirrors OneWL's
            // outer loop (target = 0, 1, 2, …): the lowest-rank tied class
            // always breaks first. At fixed point, classes are uniquely
            // identified by (BelowCount, AboveCount) — different sigs give
            // a known relation, so two classes never share a level — so
            // "lowest-leveled" picks an iso-invariant class.
            int chosen = -1;
            long chosenLevel = 0;
            for (int v = 0; v < n; v++)
            {
                if (!HasUnknownNeighbor(po, v)) continue;
                long level = ((long)po.BelowCount(v) << 32) | (uint)po.AboveCount(v);
                if (chosen < 0 || level < chosenLevel || (level == chosenLevel && v < chosen))
                {
                    chosen = v;
                    chosenLevel = level;
                }
            }
            if (chosen < 0)
                throw new InvalidOperationException("BreakLowestTiedClass called on a total order");

            for (int u = 0; u < n; u++)
                if (u != chosen && po.Compare(chosen, u) == Ordering.Unknown)
                    po.Set(chosen, u, Ordering.Less);
        }

        private static bool HasUnknownNeighbor(PartialOrder po, int v)
        {
            int n = po.N;
            for (int u = 0; u < n; u++)
                if (u != v && po.Compare(v, u) == Ordering.Unknown) return true;
            return false;
        }

        // ── Output ─────────────────────────────────────────────────────────────
        //
        // When the partial order is total, BelowCount(v) is unique for each
        // v (precisely v's position in the total order), so it is the
        // canonical permutation index.
        private static AdjMatrix PermuteByPartialOrder(AdjMatrix G, PartialOrder po)
        {
            int n = G.VertexCount;
            var perm = new int[n];
            for (int v = 0; v < n; v++) perm[v] = po.BelowCount(v);

            var result = new EdgeType[n, n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    result[perm[i], perm[j]] = G[i, j];
            return new AdjMatrix(result);
        }

        private static int[] ExtractAdj(AdjMatrix G)
        {
            int n = G.VertexCount;
            var adj = new int[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    adj[i * n + j] = G[i, j];
            return adj;
        }
    }
}
