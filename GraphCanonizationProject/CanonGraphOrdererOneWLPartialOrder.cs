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
                BreakLexSmallestTie(po);
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

        // ── Refinement ─────────────────────────────────────────────────────────
        //
        // Until a step makes no change, build per-vertex 1-WL signatures over
        // the current partial order and resolve every Unknown pair (a, b)
        // whose signatures differ.
        //
        // Each vertex's level is the pair (BelowCount(v), AboveCount(v)),
        // packed into a single sortable int. This is a total preorder
        // consistent with M: a < b in M ⇒ BelowCount(a) < BelowCount(b), so
        // the lead component of the signature already orders vertices that
        // M orders. The signature's tail is the sorted multiset of
        // (level(u)·2 + selfBit, edge[v, u]) pairs over u ∈ V — exactly the
        // shape used by CanonGraphOrdererOneWL, with the level swapped in
        // for the integer rank.
        //
        // Because lex order on signatures is itself transitive, refinement
        // never produces an entry that contradicts the existing matrix.

        private static void RefineToFixedPoint(PartialOrder po, int[] adj)
        {
            int maxIters = po.N * po.N + 1;
            for (int iter = 0; iter < maxIters; iter++)
                if (!RefineOneStep(po, adj)) return;
        }

        private static bool RefineOneStep(PartialOrder po, int[] adj)
        {
            int n = po.N;
            long[][] sigs = BuildSignatures(po, adj);

            bool anyChange = false;
            for (int a = 0; a < n; a++)
            {
                for (int b = a + 1; b < n; b++)
                {
                    if (po.Compare(a, b) != Ordering.Unknown) continue;
                    int cmp = LexCompare(sigs[a], sigs[b]);
                    if (cmp == 0) continue;
                    po.Set(a, b, cmp < 0 ? Ordering.Less : Ordering.Greater);
                    anyChange = true;
                }
            }
            return anyChange;
        }

        private static long[][] BuildSignatures(PartialOrder po, int[] adj)
        {
            int n = po.N;

            int[] levelKey = new int[n];
            for (int v = 0; v < n; v++)
                levelKey[v] = (po.BelowCount(v) << 16) | (po.AboveCount(v) & 0xFFFF);

            var sigs = new long[n][];
            for (int v = 0; v < n; v++)
            {
                var sig = new long[n + 1];
                sig[0] = levelKey[v];
                int rowBase = v * n;
                for (int u = 0; u < n; u++)
                {
                    long ru = (long)levelKey[u] * 2 + (u == v ? 1 : 0);
                    sig[1 + u] = (ru << 32) | (uint)adj[rowBase + u];
                }
                Array.Sort(sig, 1, n);
                sigs[v] = sig;
            }
            return sigs;
        }

        private static int LexCompare(long[] a, long[] b)
        {
            int len = a.Length;
            for (int i = 0; i < len; i++)
                if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
            return 0;
        }

        // ── Tiebreak ───────────────────────────────────────────────────────────
        //
        // When refinement reaches a fixed point but Unknowns remain, force
        // the lex-smallest Unknown pair to Less. This matches the spirit of
        // CanonGraphOrdererOneWL.BreakTieInPlace, which keeps the
        // lowest-index member of a tied class at its current rank and shifts
        // the rest up — both rules are iso-variant by index, but consistent
        // with the original orderer's behaviour.
        //
        // No cycle is possible: if there were a chain b → … → a in Less,
        // the prior TransitiveClose would have set M[a, b] = Greater, and
        // LexSmallestUnknownPair would not have returned (a, b).
        private static void BreakLexSmallestTie(PartialOrder po)
        {
            var pair = po.LexSmallestUnknownPair()
                ?? throw new InvalidOperationException("BreakLexSmallestTie called on a total order");
            po.Set(pair.A, pair.B, Ordering.Less);
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
