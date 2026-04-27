using System;
using System.Collections.Generic;

// Performance-focused reimplementation of CanonGraphOrdererV4. Same path-multiset
// refinement, same BreakTie/ShiftAbove discipline, same observable behaviour at
// the equivalence-class level (isomorphic input ↔ equal canonical output, with
// CFI pairs distinguished where the reference distinguishes them).
//
// The canonical bit pattern is NOT guaranteed to match CanonGraphOrdererV4 byte
// for byte: ordering conventions inside path-segment compare were naturalized for
// packed-long sorting. Tests on this class must verify canonicality (iso → same
// canon, non-iso → different canon), not bit-parity with the reference.
//
// Internal differences from the reference, all purely representational:
//   * PathState/AllPathsFrom/AllPathsBetween/PathSegment object graph replaced
//     by flat int/long buffers indexed by depth*n*n + from*n + to.
//   * All hot-path buffers preallocated in a Workspace and reused across every
//     ConvergeOnce, every depth, and every OrderVertices iteration.
//   * Per-comparison double-sort in OrderInsensitiveListComparison replaced by
//     a one-shot signature compute: each cell's segments are sorted once into
//     its signature slot, then cells are ranked by lex compare on those slots.
//   * Path segments encoded as packed longs ((subRank << 32) | edgeType).
//   * LabelEdgesAccordingToRankings's n × SwapVertexLabels (O(n³)) replaced by
//     a single permutation pass (O(n²)).
//   * BreakTie + ShiftAbove + BreakTiePromote fused into one in-place pass.
//   * Defensive clones removed from internal helpers; mutation is contained to
//     buffers the caller owns.

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    public sealed class CanonGraphOrdererV4Fast
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
                ConvergeLoop(n, adj, ranks, ws);
                BreakTieInPlace(ranks, target);
            }

            return PermuteByDenseRanks(G, ranks);
        }

        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // ── Workspace ───────────────────────────────────────────────────────────
        // Every buffer the convergence pipeline needs, allocated once per Run.
        private sealed class Workspace
        {
            public readonly int N;
            public readonly int[] BetweenRanks;       // [d * n * n + from * n + to]
            public readonly int[] FromRanks;          // [d * n + from]
            public readonly long[] SigBuf;            // [(from*n + to) * SigStride + i], i ∈ [0..SigLen[cell])
            public readonly int SigStride;
            public readonly int[] SigLen;
            public readonly int[] CellIdx;
            public readonly long[] FromSigBuf;        // [from * FromSigStride + i], i ∈ [0..n]
            public readonly int FromSigStride;
            public readonly int[] FromIdx;
            public readonly long[] RankPairs;
            public readonly Comparer<int> CellComparer;
            public readonly Comparer<int> FromComparer;

            public Workspace(int n)
            {
                N = n;
                BetweenRanks = new int[n * n * n];
                FromRanks = new int[n * n];
                SigStride = n + 1;
                SigBuf = new long[n * n * SigStride];
                SigLen = new int[n * n];
                CellIdx = new int[n * n];
                FromSigStride = n + 1;
                FromSigBuf = new long[n * FromSigStride];
                FromIdx = new int[n];
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

                var fromSigBuf = FromSigBuf;
                var fromSigStride = FromSigStride;
                int fromCmpLen = n + 1;
                FromComparer = Comparer<int>.Create((a, b) =>
                {
                    int ba = a * fromSigStride;
                    int bb = b * fromSigStride;
                    for (int i = 0; i < fromCmpLen; i++)
                    {
                        long va = fromSigBuf[ba + i];
                        long vb = fromSigBuf[bb + i];
                        if (va != vb) return va < vb ? -1 : 1;
                    }
                    return 0;
                });
            }
        }

        // ── Dense rank (replaces GetArrayRank) ─────────────────────────────────
        // [5,0,5,3] → [2,0,2,1]. Ties broken by original index, but only the
        // value-class is preserved in the output (not the position permutation).
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

        // ── ConvergeLoop / ConvergeOnce ────────────────────────────────────────
        private static void ConvergeLoop(int n, int[] adj, int[] ranks, Workspace ws)
        {
            for (int iter = 0; iter < n; iter++)
                if (!ConvergeOnce(n, adj, ranks, ws)) break;
        }

        private static bool ConvergeOnce(int n, int[] adj, int[] ranks, Workspace ws)
        {
            for (int d = 0; d < n; d++)
            {
                BuildBetweenSignatures(n, d, adj, ranks, ws);
                AssignBetweenRanks(n, d, ws);
                BuildFromSignatures(n, d, ranks, ws);
                AssignFromRanks(n, d, ws);
            }

            bool changed = false;
            int baseIdx = (n - 1) * n;
            for (int v = 0; v < n; v++)
            {
                int newRank = ws.FromRanks[baseIdx + v];
                if (newRank != ranks[v]) { ranks[v] = newRank; changed = true; }
            }
            return changed;
        }

        // ── Path-multiset signatures ───────────────────────────────────────────
        // Cell (from, to) signature at depth d, slot 0 = ranks[to] (endpoint type).
        // Depth 0:
        //   from == to: slot 1 = ranks[from], length 2 (encodes the BottomPathSegment)
        //   from != to: length 1 (empty connectedSubPaths)
        // Depth d > 0:
        //   slots 1..n: sorted (ascending) packed longs ((subRank << 32) | edge)
        //   over each mid in 0..n; length n + 1.
        // Two cells with the same signature land in the same equivalence class.
        private static void BuildBetweenSignatures(int n, int d, int[] adj, int[] ranks, Workspace ws)
        {
            long[] sigBuf = ws.SigBuf;
            int stride = ws.SigStride;
            int[] sigLen = ws.SigLen;

            if (d == 0)
            {
                for (int from = 0; from < n; from++)
                {
                    long fromTypeLong = ranks[from];
                    for (int to = 0; to < n; to++)
                    {
                        int cell = from * n + to;
                        int baseIdx = cell * stride;
                        sigBuf[baseIdx] = ranks[to];
                        if (from == to) { sigBuf[baseIdx + 1] = fromTypeLong; sigLen[cell] = 2; }
                        else sigLen[cell] = 1;
                    }
                }
                return;
            }

            int prevDepthBase = (d - 1) * n * n;
            for (int from = 0; from < n; from++)
            {
                int prevFromBase = prevDepthBase + from * n;
                for (int to = 0; to < n; to++)
                {
                    int cell = from * n + to;
                    int baseIdx = cell * stride;
                    sigBuf[baseIdx] = ranks[to];
                    for (int mid = 0; mid < n; mid++)
                    {
                        int subRank = ws.BetweenRanks[prevFromBase + mid];
                        int edge = adj[mid * n + to];
                        sigBuf[baseIdx + 1 + mid] = ((long)subRank << 32) | (uint)edge;
                    }
                    Array.Sort(sigBuf, baseIdx + 1, n);
                    sigLen[cell] = n + 1;
                }
            }
        }

        private static void AssignBetweenRanks(int n, int d, Workspace ws)
        {
            int total = n * n;
            int[] idx = ws.CellIdx;
            for (int i = 0; i < total; i++) idx[i] = i;
            Array.Sort(idx, 0, total, ws.CellComparer);

            int[] betweenRanks = ws.BetweenRanks;
            int dBase = d * n * n;
            int rank = 0;
            betweenRanks[dBase + idx[0]] = 0;
            for (int i = 1; i < total; i++)
            {
                if (ws.CellComparer.Compare(idx[i - 1], idx[i]) != 0) rank++;
                betweenRanks[dBase + idx[i]] = rank;
            }
        }

        // From-vertex signature at depth d:
        //   slot 0 = ranks[from]
        //   slots 1..n: sorted (ascending) betweenRanks[d, from, to] for each to.
        private static void BuildFromSignatures(int n, int d, int[] ranks, Workspace ws)
        {
            long[] sig = ws.FromSigBuf;
            int stride = ws.FromSigStride;
            int dBase = d * n * n;
            for (int from = 0; from < n; from++)
            {
                int baseIdx = from * stride;
                sig[baseIdx] = ranks[from];
                int rowBase = dBase + from * n;
                for (int to = 0; to < n; to++)
                    sig[baseIdx + 1 + to] = ws.BetweenRanks[rowBase + to];
                Array.Sort(sig, baseIdx + 1, n);
            }
        }

        private static void AssignFromRanks(int n, int d, Workspace ws)
        {
            int[] idx = ws.FromIdx;
            for (int i = 0; i < n; i++) idx[i] = i;
            Array.Sort(idx, 0, n, ws.FromComparer);

            int[] fromRanks = ws.FromRanks;
            int dBase = d * n;
            int rank = 0;
            fromRanks[dBase + idx[0]] = 0;
            for (int i = 1; i < n; i++)
            {
                if (ws.FromComparer.Compare(idx[i - 1], idx[i]) != 0) rank++;
                fromRanks[dBase + idx[i]] = rank;
            }
        }

        // ── BreakTie ───────────────────────────────────────────────────────────
        // Fused ShiftAbove + BreakTiePromote, in place. Skipped when the target
        // class has fewer than 2 occurrences (preserves dense-rank invariant).
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
        // Replaces n × SwapVertexLabels (each O(n²)) with a single O(n²) pass.
        // perm[origVertex] = newPosition, derived from ranks with index ties
        // broken by original index ascending (matches ComputeDenseRanks).
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
