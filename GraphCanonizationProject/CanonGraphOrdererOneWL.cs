using System;
using System.Collections.Generic;

// 1-WL (Weisfeiler–Leman, dimension 1 / color refinement) graph canonizer.
// Same outer skeleton as CanonGraphOrdererTwoWL — Discriminate → BreakTie until
// every vertex is in a singleton class — but the discrimination engine is
// classical color refinement on single vertices instead of pair refinement.
//
// Vertex colors c[v] are refined by:
//   c'[v] = denseRank( c[v],  multiset_u (c[u], adj[v, u], u == v) )
// to a fixed point. No pair-color table.
//
// Sorting-not-hashing departure (same as TwoWL): the previous rank is the lead
// component of every signature, and dense-rank is computed over sorted sigs.
// Together this enforces the strict-refinement invariant — any rank ordering
// rank(x) < rank(y) at one step survives every subsequent step.
//
// The "u == v" bit in the per-neighbor entry distinguishes the self-entry from
// any other vertex's entry that happens to share the same (rank, edge). Without
// it, "v has a self-loop" can collide with "v has a same-rank neighbor with a
// matching incident edge". Encoded by doubling the rank and using the low bit:
//   effectiveRank = ranks[u] * 2 + (u == v ? 1 : 0)
//
// Equivalence-class behaviour:
//   * Iso → same canonical: holds.
//   * Non-iso → different canonical: 1-WL is strictly weaker than 2-WL. Any
//     pair distinguishable only by length-≥2 path information collapses (e.g.
//     two non-isomorphic k-regular graphs of the same size). The CFI pairs
//     and other 2-WL counterexamples a fortiori defeat 1-WL.

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    public sealed class CanonGraphOrdererOneWL : ICanonGraphOrderer
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

        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // ── Workspace ───────────────────────────────────────────────────────────
        private sealed class Workspace
        {
            public readonly int N;
            public readonly int[] RanksNew;
            public readonly long[] SigBuf;          // [v * SigStride + i]
            public readonly int SigStride;          // = n + 1
            public readonly int[] VertexIdx;
            public readonly long[] RankPairs;
            public readonly Comparer<int> SigComparer;

            public Workspace(int n)
            {
                N = n;
                RanksNew = new int[n];
                SigStride = n + 1;
                SigBuf = new long[n * SigStride];
                VertexIdx = new int[n];
                RankPairs = new long[n];

                var sigBuf = SigBuf;
                var sigStride = SigStride;
                int sigCmpLen = sigStride;
                SigComparer = Comparer<int>.Create((a, b) =>
                {
                    int ba = a * sigStride;
                    int bb = b * sigStride;
                    for (int i = 0; i < sigCmpLen; i++)
                    {
                        long va = sigBuf[ba + i];
                        long vb = sigBuf[bb + i];
                        if (va != vb) return va < vb ? -1 : 1;
                    }
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

        // ── Discriminate: 1-WL refinement to fixed point ─────────────────────
        // Mutates `ranks` in place. 1-WL converges in at most n iterations:
        // each iteration that does not stabilize splits at least one rank
        // class, and there are at most n classes total.
        private static void Discriminate(int n, int[] adj, int[] ranks, Workspace ws)
        {
            for (int iter = 0; iter < n; iter++)
            {
                BuildVertexSignatures(n, adj, ranks, ws);
                AssignVertexRanks(n, ws);
                if (!RanksDiffer(n, ranks, ws.RanksNew)) return;
                Array.Copy(ws.RanksNew, ranks, n);
            }
        }

        // sig[v]: slot 0 = ranks[v]; slots 1..n = sorted longs encoding
        // ((ranks[u] * 2 + (u == v ? 1 : 0)) << 32) | adj[v, u] for each u.
        // The self bit puts the (u == v) entry into a sort lane disjoint
        // from any other vertex's entry of the same rank.
        // Slot 0 (lead) preserves ordering: if ranks[a] < ranks[b], the
        // signatures differ in slot 0 and so do the dense-rank outputs.
        private static void BuildVertexSignatures(int n, int[] adj, int[] ranks, Workspace ws)
        {
            long[] sigBuf = ws.SigBuf;
            int stride = ws.SigStride;
            for (int v = 0; v < n; v++)
            {
                int baseIdx = v * stride;
                sigBuf[baseIdx] = ranks[v];
                int vRowBase = v * n;
                for (int u = 0; u < n; u++)
                {
                    long ru = (long)ranks[u] * 2 + (u == v ? 1 : 0);
                    sigBuf[baseIdx + 1 + u] = (ru << 32) | (uint)adj[vRowBase + u];
                }
                Array.Sort(sigBuf, baseIdx + 1, n);
            }
        }

        // Sort all n vertices by signature and dense-rank into RanksNew.
        private static void AssignVertexRanks(int n, Workspace ws)
        {
            int[] idx = ws.VertexIdx;
            for (int i = 0; i < n; i++) idx[i] = i;
            Array.Sort(idx, 0, n, ws.SigComparer);

            int[] target = ws.RanksNew;
            int rank = 0;
            target[idx[0]] = 0;
            for (int i = 1; i < n; i++)
            {
                if (ws.SigComparer.Compare(idx[i - 1], idx[i]) != 0) rank++;
                target[idx[i]] = rank;
            }
        }

        private static bool RanksDiffer(int n, int[] cur, int[] nu)
        {
            for (int i = 0; i < n; i++)
                if (cur[i] != nu[i]) return true;
            return false;
        }

        // ── BreakTie ───────────────────────────────────────────────────────────
        // Identical to TwoWL/V4Fast: shift ranks above `target` up by one,
        // then promote all-but-the-first occurrence of `target` to `target + 1`.
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
        // Identical to TwoWL/V4Fast.
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
