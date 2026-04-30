using System;
using System.Collections.Generic;

// 2-WL (Weisfeiler–Leman, dimension 2) graph canonizer. Same outer skeleton as
// CanonGraphOrdererV4Fast — Discriminate → BreakTie → Discriminate → BreakTie
// until every vertex is in a singleton class — but the discrimination engine is
// classical 2-WL on pair colors instead of the path-multiset/history scheme.
//
// Pair colors c[u, v] are refined by:
//   c'[u, v] = denseRank( c[u, v],  multiset_w (c[u, w], c[w, v]) )
// to a fixed point, then vertex ranks are read off the diagonal:
//   newRanks[v] = denseRank( oldRanks[v],  c[v, v] )  over all v.
//
// Departure from textbook 2-WL: where the standard formulation hashes the
// (prev color, multiset) tuple to a fresh integer with no relation to past
// values, we sort the tuples and assign dense ranks. Combined with placing the
// previous rank as the lead component of every signature, this guarantees a
// strict-refinement invariant: if at any step rank(x) < rank(y), then at every
// subsequent step rank(x) < rank(y). The outer pipeline relies on this so a
// later TieBreak/VertexRank extension can attribute rank movements to specific
// tie-break events rather than reconstructing them from structural diffs.
//
// Equivalence-class behaviour:
//   * Iso → same canonical: holds (every operation is automorphism-equivariant).
//   * Non-iso → different canonical: holds up to 2-WL's strength bound; CFI
//     pairs whose base graph has treewidth ≥ 2 are not separated by any 2-WL
//     variant. The same caveat applies to V4Fast.
// Canonical bytes are NOT the same as V4Fast's — tests must check
// canonicality, not bit parity.

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    public sealed class CanonGraphOrdererTwoWL : ICanonGraphOrderer
    {
        public AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            int n = G.VertexCount;
            var adj = new int[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    adj[i * n + j] = G[i, j];

            var ws = new Workspace(n);
            var ranks = new int[n];
            DenseRankInto(vertexTypes, ranks, ws);

            for (int target = 0; target < n; target++)
            {
                Discriminate(n, adj, ranks, ws);
                BreakTieInPlace(ranks, target);
            }

            return PermuteByDenseRanks(G, ranks);
        }

        public static int[] RunConvergeLoopForTesting(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            int n = G.VertexCount;
            var adj = new int[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    adj[i * n + j] = G[i, j];

            var ws = new Workspace(n);
            var ranks = new int[n];
            DenseRankInto(vertexTypes, ranks, ws);
            Discriminate(n, adj, ranks, ws);
            return ranks;
        }

        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // ── Workspace ───────────────────────────────────────────────────────────
        private sealed class Workspace
        {
            public readonly int N;
            public readonly int[] PairRanks;       // [u * n + v] — previous iteration
            public readonly int[] PairRanksNew;    // [u * n + v] — current iteration
            public readonly long[] SigBuf;         // [(u*n + v) * SigStride + i]
            public readonly int SigStride;
            public readonly int[] SigLen;
            public readonly int[] CellIdx;
            public readonly long[] VertexSigBuf;   // [v * 2 + i]
            public readonly int[] VertexIdx;
            public readonly long[] RankPairs;
            public readonly Comparer<int> CellComparer;
            public readonly Comparer<int> VertexSigComparer;

            public Workspace(int n)
            {
                N = n;
                PairRanks = new int[n * n];
                PairRanksNew = new int[n * n];
                // SigStride must hold both the initial 5-slot signature and
                // the refined (n + 1)-slot signature. The initial form dominates
                // for n < 4 (e.g. AllPermutations(size=1) below).
                SigStride = Math.Max(n + 1, 5);
                SigBuf = new long[n * n * SigStride];
                SigLen = new int[n * n];
                CellIdx = new int[n * n];
                VertexSigBuf = new long[n * 2];
                VertexIdx = new int[n];
                RankPairs = new long[n];

                var sigBuf = SigBuf;
                var sigLen = SigLen;
                var sigStride = SigStride;
                CellComparer = Comparer<int>.Create((a, b) =>
                {
                    int ba = a * sigStride;
                    int bb = b * sigStride;
                    int la = sigLen[a];
                    int lb = sigLen[b];
                    int lim = la < lb ? la : lb;
                    for (int i = 0; i < lim; i++)
                    {
                        long va = sigBuf[ba + i];
                        long vb = sigBuf[bb + i];
                        if (va != vb) return va < vb ? -1 : 1;
                    }
                    return la == lb ? 0 : (la < lb ? -1 : 1);
                });

                var vertexSigBuf = VertexSigBuf;
                VertexSigComparer = Comparer<int>.Create((a, b) =>
                {
                    long va0 = vertexSigBuf[a * 2];
                    long vb0 = vertexSigBuf[b * 2];
                    if (va0 != vb0) return va0 < vb0 ? -1 : 1;
                    long va1 = vertexSigBuf[a * 2 + 1];
                    long vb1 = vertexSigBuf[b * 2 + 1];
                    if (va1 != vb1) return va1 < vb1 ? -1 : 1;
                    return 0;
                });
            }
        }

        // ── Dense rank ─────────────────────────────────────────────────────────
        // [5,0,5,3] → [2,0,2,1]. Ties broken by original index.
        private static void DenseRankInto(int[] arr, int[] dest, Workspace ws)
        {
            int n = arr.Length;
            if (n == 0) return;
            if (n == 1) { dest[0] = 0; return; }
            for (int i = 0; i < n; i++) ws.RankPairs[i] = ((long)arr[i] << 32) | (uint)i;
            Array.Sort(ws.RankPairs, 0, n);
            int rank = 0;
            int prev = (int)(ws.RankPairs[0] >> 32);
            dest[(int)(uint)ws.RankPairs[0]] = 0;
            for (int i = 1; i < n; i++)
            {
                int v = (int)(ws.RankPairs[i] >> 32);
                int origIdx = (int)(uint)ws.RankPairs[i];
                if (v != prev) { rank++; prev = v; }
                dest[origIdx] = rank;
            }
        }

        // ── Discriminate: 2-WL refinement → vertex-rank update ────────────────
        // Refines pair colors to a fixed point, then promotes the diagonal to
        // a refined vertex ranking. Mutates `ranks` in place.
        private static void Discriminate(int n, int[] adj, int[] ranks, Workspace ws)
        {
            BuildInitialPairSignatures(n, adj, ranks, ws);
            AssignPairRanks(n, ws);
            Array.Copy(ws.PairRanksNew, ws.PairRanks, n * n);

            // 2-WL converges in at most n² − 1 refinement iterations: each iteration
            // that does not stabilize splits at least one pair-color class, and there
            // are at most n² classes total. In practice it converges much faster.
            int maxIters = n * n;
            for (int iter = 0; iter < maxIters; iter++)
            {
                BuildRefinedPairSignatures(n, ws);
                AssignPairRanks(n, ws);
                if (!PairRanksDiffer(n, ws)) break;
                Array.Copy(ws.PairRanksNew, ws.PairRanks, n * n);
            }

            UpdateVertexRanks(n, ranks, ws);
        }

        // Initial pair signature for (u, v): five longs encoding
        //   (ranks[u], ranks[v], u == v, adj[u,v], adj[v,u]).
        // Length = 5 (independent of n).
        private static void BuildInitialPairSignatures(int n, int[] adj, int[] ranks, Workspace ws)
        {
            long[] sigBuf = ws.SigBuf;
            int stride = ws.SigStride;
            int[] sigLen = ws.SigLen;
            for (int u = 0; u < n; u++)
            {
                long ru = ranks[u];
                int uBase = u * n;
                for (int v = 0; v < n; v++)
                {
                    int cell = uBase + v;
                    int baseIdx = cell * stride;
                    sigBuf[baseIdx + 0] = ru;
                    sigBuf[baseIdx + 1] = ranks[v];
                    sigBuf[baseIdx + 2] = u == v ? 1 : 0;
                    sigBuf[baseIdx + 3] = adj[uBase + v];
                    sigBuf[baseIdx + 4] = adj[v * n + u];
                    sigLen[cell] = 5;
                }
            }
        }

        // Refined pair signature for (u, v): slot 0 = previous pairRanks[u, v];
        // slots 1..n = sorted (ascending) packed longs ((pairRanks[u,w] << 32) |
        // pairRanks[w,v]) for each w. Length = n + 1.
        // Putting the previous rank in slot 0 enforces the strict-refinement
        // invariant: if pairRanks[a] < pairRanks[b] at this step, then
        // pairRanksNew[a] < pairRanksNew[b] after this step (their sigs differ
        // in slot 0 already, so they cannot collapse to the same dense rank).
        private static void BuildRefinedPairSignatures(int n, Workspace ws)
        {
            long[] sigBuf = ws.SigBuf;
            int stride = ws.SigStride;
            int[] sigLen = ws.SigLen;
            int[] pr = ws.PairRanks;
            for (int u = 0; u < n; u++)
            {
                int uBase = u * n;
                for (int v = 0; v < n; v++)
                {
                    int cell = uBase + v;
                    int baseIdx = cell * stride;
                    sigBuf[baseIdx] = pr[cell];
                    for (int w = 0; w < n; w++)
                    {
                        int leftRank = pr[uBase + w];
                        int rightRank = pr[w * n + v];
                        sigBuf[baseIdx + 1 + w] = ((long)leftRank << 32) | (uint)rightRank;
                    }
                    Array.Sort(sigBuf, baseIdx + 1, n);
                    sigLen[cell] = n + 1;
                }
            }
        }

        // Sort all n² cells by their current signature and write dense ranks
        // into PairRanksNew.
        private static void AssignPairRanks(int n, Workspace ws)
        {
            int total = n * n;
            int[] idx = ws.CellIdx;
            for (int i = 0; i < total; i++) idx[i] = i;
            Array.Sort(idx, 0, total, ws.CellComparer);

            int[] target = ws.PairRanksNew;
            int rank = 0;
            target[idx[0]] = 0;
            for (int i = 1; i < total; i++)
            {
                if (ws.CellComparer.Compare(idx[i - 1], idx[i]) != 0) rank++;
                target[idx[i]] = rank;
            }
        }

        private static bool PairRanksDiffer(int n, Workspace ws)
        {
            int total = n * n;
            int[] cur = ws.PairRanks;
            int[] nu = ws.PairRanksNew;
            for (int i = 0; i < total; i++)
                if (cur[i] != nu[i]) return true;
            return false;
        }

        // ranks[v] ← denseRank((oldRanks[v], pairRanks[v, v])) over all v.
        // The lead component is the prior vertex rank, so the strict-refinement
        // invariant carries from pair ranks to vertex ranks: an existing strict
        // ordering between two vertices' ranks survives this update.
        private static void UpdateVertexRanks(int n, int[] ranks, Workspace ws)
        {
            long[] sig = ws.VertexSigBuf;
            int[] pr = ws.PairRanksNew;
            for (int v = 0; v < n; v++)
            {
                sig[v * 2] = ranks[v];
                sig[v * 2 + 1] = pr[v * n + v];
            }

            int[] idx = ws.VertexIdx;
            for (int i = 0; i < n; i++) idx[i] = i;
            Array.Sort(idx, 0, n, ws.VertexSigComparer);

            int rank = 0;
            long prev0 = sig[idx[0] * 2];
            long prev1 = sig[idx[0] * 2 + 1];
            ranks[idx[0]] = 0;
            for (int i = 1; i < n; i++)
            {
                int v = idx[i];
                long cur0 = sig[v * 2];
                long cur1 = sig[v * 2 + 1];
                if (cur0 != prev0 || cur1 != prev1)
                {
                    rank++;
                    prev0 = cur0;
                    prev1 = cur1;
                }
                ranks[v] = rank;
            }
        }

        // ── BreakTie ───────────────────────────────────────────────────────────
        // Identical to V4Fast: shift ranks above `target` up by one to open a
        // slot, then promote every-but-the-first occurrence of `target` to
        // `target + 1`. No-op when fewer than two vertices share `target`.
        private static void BreakTieInPlace(int[] ranks, int target)
        {
            int count = 0;
            for (int i = 0; i < ranks.Length; i++)
                if (ranks[i] == target) count++;
            if (count < 2) return;

            for (int i = 0; i < ranks.Length; i++)
                if (ranks[i] > target) ranks[i]++;

            bool first = true;
            for (int i = 0; i < ranks.Length; i++)
            {
                if (ranks[i] != target) continue;
                if (first) { first = false; continue; }
                ranks[i] = target + 1;
            }
        }

        // ── Permute by dense ranks ─────────────────────────────────────────────
        // Identical to V4Fast: build a position permutation from ranks (ties
        // broken by original index) and apply it to the adjacency matrix.
        private static AdjMatrix PermuteByDenseRanks(AdjMatrix G, int[] ranks)
        {
            int n = G.VertexCount;
            var pairs = new long[n];
            for (int i = 0; i < n; i++) pairs[i] = ((long)ranks[i] << 32) | (uint)i;
            Array.Sort(pairs, 0, n);

            var perm = new int[n];
            for (int r = 0; r < n; r++)
                perm[(int)(uint)pairs[r]] = r;

            var result = new EdgeType[n, n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    result[perm[i], perm[j]] = G[i, j];
            return new AdjMatrix(result);
        }
    }
}
