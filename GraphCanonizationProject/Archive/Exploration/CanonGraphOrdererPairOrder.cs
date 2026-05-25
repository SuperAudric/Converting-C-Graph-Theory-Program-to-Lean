using System;
using System.Collections.Generic;

// Partial pair-ordering canonizer (1-WL discriminator, no supplant).
//
// The minimal distillation of the pair-event idea from
// docs/supplant-strategy.md: each tiebreak event individualizes a pair
// (A, B) at a fresh layer with roles low/high; 1-WL refines using the full
// rank tuple as the per-vertex key; the loop runs until every class is a
// singleton; final output is the dense-rank of the full tuple.
//
// No supplant machinery (no atom classification, no signatures, no
// forced completion, no multi-pass sort). The whole algorithm fits in
// one file and is meant to be the smallest reproducer for partial-
// pair-ordering bugs separate from supplant bugs.
//
// Pair-selection rule: lex-min by (cross-component, non-adjacent,
// smallest A index, smallest B index) within the lowest tuple-tied
// class. Cross-component pairs come first, then within-component
// non-adjacent, then adjacent. This is iso-invariant on inputs whose
// component partition and adjacency relation are themselves iso-
// invariant (which is everything 1-WL sees).
//
// Where this differs from CanonGraphOrdererSupplant: the latter has the
// supplant scaffolding (which is not yet doing real work) and uses
// "smallest two indices" as PickPair. Comparing the two on the same
// inputs isolates which failures are pair-selection vs supplant issues.

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    public sealed class CanonGraphOrdererPairOrder : ICanonGraphOrderer
    {
        public AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            var s = Setup(vertexTypes, G);
            EventLoop(s);
            int[] canonicalRanks = ComputeTupleDenseRank(s, s.L);
            return PermuteByDenseRanks(G, canonicalRanks);
        }

        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // ── Roles ──────────────────────────────────────────────────────────────
        //
        // Lex order: Untouched < Cascaded(0) < Cascaded(1) < … < Low < High.

        private enum RoleKind : byte { Untouched = 0, Cascaded = 1, Low = 2, High = 3 }

        private readonly struct Role : IComparable<Role>, IEquatable<Role>
        {
            public readonly RoleKind Kind;
            public readonly int CascadedRank;

            public Role(RoleKind k, int d = 0) { Kind = k; CascadedRank = d; }

            public static readonly Role Untouched = new Role(RoleKind.Untouched);
            public static readonly Role Low       = new Role(RoleKind.Low);
            public static readonly Role High      = new Role(RoleKind.High);
            public static Role Cascaded(int d)    => new Role(RoleKind.Cascaded, d);

            public int CompareTo(Role o)
            {
                int kc = ((byte)Kind).CompareTo((byte)o.Kind);
                if (kc != 0) return kc;
                return CascadedRank.CompareTo(o.CascadedRank);
            }

            public bool Equals(Role o) => Kind == o.Kind && CascadedRank == o.CascadedRank;
            public override bool Equals(object? obj) => obj is Role r && Equals(r);
            public override int GetHashCode() => ((byte)Kind, CascadedRank).GetHashCode();
        }

        // ── State + workspace ──────────────────────────────────────────────────

        private sealed class State
        {
            public int N;
            public int[] Adj = [];
            public int[] R0 = [];
            public int[] Components = [];
            public List<Role[]> Layers = [];
            public Workspace WS = new(0);

            public int L => Layers.Count;
        }

        private sealed class Workspace
        {
            public readonly int N;
            public readonly long[] RankPairs;
            public readonly int[] VertexIdx;
            public readonly long[] SigBuf;
            public readonly int SigStride;
            public readonly Comparer<int> SigComparer;
            public readonly int[] NewKeys;

            public Workspace(int n)
            {
                N = n;
                RankPairs = n > 0 ? new long[n] : [];
                VertexIdx = n > 0 ? new int[n] : [];
                SigStride = n + 1;
                SigBuf    = n > 0 ? new long[n * SigStride] : [];
                NewKeys   = n > 0 ? new int[n] : [];

                long[] sigBuf = SigBuf;
                int sigStride = SigStride;
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

        // ── Setup ──────────────────────────────────────────────────────────────

        private static State Setup(VertexType[] vertexTypes, AdjMatrix G)
        {
            int n = G.VertexCount;
            var adj = new int[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    adj[i * n + j] = G[i, j];

            var ws = new Workspace(n);
            var r0 = new int[n];
            DenseRankInto(vertexTypes, r0, ws);
            OneWlFixedPoint(n, adj, r0, ws);

            return new State
            {
                N          = n,
                Adj        = adj,
                R0         = r0,
                Components = ComputeConnectedComponents(n, adj),
                Layers     = [],
                WS         = ws,
            };
        }

        // ── Event loop ─────────────────────────────────────────────────────────

        private static void EventLoop(State s)
        {
            while (true)
            {
                var pair = PickPair(s);
                if (pair is null) break;

                var layer = new Role[s.N];
                layer[pair.Value.A] = Role.Low;
                layer[pair.Value.B] = Role.High;
                s.Layers.Add(layer);

                Discriminate(s);
            }
        }

        // ── Pair selection ─────────────────────────────────────────────────────
        //
        // Within the lowest tuple-tied class, prefer pairs in this order:
        //   1. cross-component                    (most informative cascade)
        //   2. within-component, non-adjacent
        //   3. within-component, adjacent
        // Tiebreak on (smallest A index, smallest B index).
        //
        // Rationale: across all input scramblings of the same graph, the
        // pair structurally selected at this rule is automorphism-equivalent
        // (because component partition and adjacency are 1-WL invariants).
        // Smallest indices is iso-invariant *within* the chosen structural
        // class, since members of an automorphism orbit yield equivalent
        // cascades regardless of which specific vertex pair is picked.

        private static (int A, int B)? PickPair(State s)
        {
            int n = s.N;
            if (n < 2) return null;

            int[] keys = ComputeTupleDenseRank(s, s.L);

            // Group vertex indices by current full-tuple key.
            var groups = new Dictionary<int, List<int>>();
            for (int i = 0; i < n; i++)
            {
                if (!groups.TryGetValue(keys[i], out var lst))
                    groups[keys[i]] = lst = [];
                lst.Add(i);
            }

            // Find the lowest key whose class has size ≥ 2.
            int lowestKey = int.MaxValue;
            bool found = false;
            foreach (var kvp in groups)
            {
                if (kvp.Value.Count < 2) continue;
                if (!found || kvp.Key < lowestKey) { lowestKey = kvp.Key; found = true; }
            }
            if (!found) return null;

            var members = groups[lowestKey];
            members.Sort();

            // Search for the best pair under the structural ordering above.
            // We score each pair (A, B) with A < B as a tuple
            //   (sameComponent ? 1 : 0,  adjacent ? 1 : 0,  A,  B)
            // and pick lex-min.
            int bestSameComp = 2, bestAdj = 2, bestA = -1, bestB = -1;
            for (int i = 0; i < members.Count; i++)
            {
                int a = members[i];
                for (int j = i + 1; j < members.Count; j++)
                {
                    int b = members[j];
                    int sameComp = s.Components[a] == s.Components[b] ? 1 : 0;
                    int adj      = s.Adj[a * n + b] != 0 ? 1 : 0;

                    if (sameComp <  bestSameComp ||
                       (sameComp == bestSameComp && adj <  bestAdj) ||
                       (sameComp == bestSameComp && adj == bestAdj && a < bestA) ||
                       (sameComp == bestSameComp && adj == bestAdj && a == bestA && b < bestB))
                    {
                        bestSameComp = sameComp;
                        bestAdj      = adj;
                        bestA        = a;
                        bestB        = b;
                    }
                }
            }

            return (bestA, bestB);
        }

        // ── Discriminate (1-WL refinement over rank tuples) ────────────────────

        private static void Discriminate(State s)
        {
            int n = s.N;
            int L = s.L;
            if (L == 0) return;

            int[] preEventKeys = ComputeTupleDenseRank(s, L - 1);
            int[] currentKeys  = ComputeTupleDenseRank(s, L);

            for (int iter = 0; iter < n; iter++)
            {
                BuildVertexSignatures(n, s.Adj, currentKeys, s.WS);
                AssignVertexRanks(n, s.WS);
                if (!RanksDiffer(n, currentKeys, s.WS.NewKeys)) break;
                Array.Copy(s.WS.NewKeys, currentKeys, n);
            }

            DecodeLayerRoles(s, L - 1, preEventKeys, currentKeys);
        }

        private static int[] ComputeTupleDenseRank(State s, int layerCount)
        {
            int n = s.N;
            int[] order = new int[n];
            for (int i = 0; i < n; i++) order[i] = i;

            int Compare(int a, int b)
            {
                int c = s.R0[a].CompareTo(s.R0[b]);
                if (c != 0) return c;
                for (int k = 0; k < layerCount; k++)
                {
                    c = s.Layers[k][a].CompareTo(s.Layers[k][b]);
                    if (c != 0) return c;
                }
                return 0;
            }

            Array.Sort(order, Compare);

            int[] keys = new int[n];
            if (n == 0) return keys;
            keys[order[0]] = 0;
            int rank = 0;
            for (int i = 1; i < n; i++)
            {
                if (Compare(order[i - 1], order[i]) != 0) rank++;
                keys[order[i]] = rank;
            }
            return keys;
        }

        // For each pre-event class C:
        //   - {A} and {B} singleton sub-classes keep their explicit Low / High.
        //   - If non-tagged members all stay in one sub-class equal to C \ {A, B},
        //     they remain Untouched (cascade did not split them).
        //   - Otherwise non-tagged members are assigned Cascaded(d), with d the
        //     dense-rank of the post-event key within C.
        private static void DecodeLayerRoles(State s, int layerIdx, int[] preEventKeys, int[] currentKeys)
        {
            int n = s.N;
            Role[] layer = s.Layers[layerIdx];

            int aIdx = -1, bIdx = -1;
            for (int i = 0; i < n; i++)
            {
                if (layer[i].Kind == RoleKind.Low)  aIdx = i;
                else if (layer[i].Kind == RoleKind.High) bIdx = i;
            }

            var preMembers = new Dictionary<int, List<int>>();
            for (int i = 0; i < n; i++)
            {
                if (!preMembers.TryGetValue(preEventKeys[i], out var lst))
                    preMembers[preEventKeys[i]] = lst = [];
                lst.Add(i);
            }

            foreach (var kvp in preMembers)
            {
                var members = kvp.Value;
                var subClasses = new Dictionary<int, List<int>>();
                int aInClass = 0, bInClass = 0;
                for (int idx = 0; idx < members.Count; idx++)
                {
                    int v = members[idx];
                    if (v == aIdx) { aInClass = 1; continue; }
                    if (v == bIdx) { bInClass = 1; continue; }
                    int postKey = currentKeys[v];
                    if (!subClasses.TryGetValue(postKey, out var lst))
                        subClasses[postKey] = lst = [];
                    lst.Add(v);
                }

                int adjustedPreSize = members.Count - aInClass - bInClass;
                if (adjustedPreSize == 0) continue;
                if (subClasses.Count == 1) continue;       // no split → stay Untouched

                var sortedKeys = new List<int>(subClasses.Keys);
                sortedKeys.Sort();
                for (int d = 0; d < sortedKeys.Count; d++)
                {
                    var sub = subClasses[sortedKeys[d]];
                    for (int j = 0; j < sub.Count; j++)
                        layer[sub[j]] = Role.Cascaded(d);
                }
            }
        }

        // ── 1-WL primitives ────────────────────────────────────────────────────

        private static void OneWlFixedPoint(int n, int[] adj, int[] ranks, Workspace ws)
        {
            for (int iter = 0; iter < n; iter++)
            {
                BuildVertexSignatures(n, adj, ranks, ws);
                AssignVertexRanks(n, ws);
                if (!RanksDiffer(n, ranks, ws.NewKeys)) return;
                Array.Copy(ws.NewKeys, ranks, n);
            }
        }

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

        private static void AssignVertexRanks(int n, Workspace ws)
        {
            int[] idx = ws.VertexIdx;
            for (int i = 0; i < n; i++) idx[i] = i;
            Array.Sort(idx, 0, n, ws.SigComparer);

            int[] target = ws.NewKeys;
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

        // ── Connected components ───────────────────────────────────────────────

        private static int[] ComputeConnectedComponents(int n, int[] adj)
        {
            var components = new int[n];
            for (int i = 0; i < n; i++) components[i] = -1;

            var queue = new Queue<int>();
            int next = 0;
            for (int start = 0; start < n; start++)
            {
                if (components[start] != -1) continue;
                components[start] = next;
                queue.Enqueue(start);
                while (queue.Count > 0)
                {
                    int v = queue.Dequeue();
                    int rowBase = v * n;
                    for (int u = 0; u < n; u++)
                    {
                        if (adj[rowBase + u] != 0 && components[u] == -1)
                        {
                            components[u] = next;
                            queue.Enqueue(u);
                        }
                    }
                }
                next++;
            }
            return components;
        }

        // ── Permutation / dense-rank utilities ─────────────────────────────────

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
    }
}
