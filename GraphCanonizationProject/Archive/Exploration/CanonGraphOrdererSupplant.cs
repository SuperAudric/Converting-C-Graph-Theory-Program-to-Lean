using System;
using System.Collections.Generic;

// Layered Tiebreak with Supplant — distilled v2.
//
// Driving principle (reset to first principles): a tiebreak event is a
// guess A<B encoded as Low/High at a fresh layer. After all events run,
// each layer is classified into one of two outcomes:
//
//   (S) Supplanted. Removing the layer entirely (zero out every role)
//       still leaves every vertex's full tuple distinct from every other
//       vertex's. The layer's information is now implied by other layers
//       + r₀ — it was a guess that later refinement made redundant.
//
//   (F) Flip. Removing the layer collapses some pair into a tie. The
//       layer is essential; only the per-layer Z/2 freedom (Low ↔ High at
//       A, B) remains. Flip-canonicalize at the end by lex-min.
//
// (S) is decided post-hoc, greedily late-to-early. The check "during the
// loop" of the previous draft was unsound: a freshly added layer is the
// only refinement past r₀ at that moment, so removing it always reties
// A and B; (S) can only fire once subsequent layers' cascades exist.
//
// (X) — load-bearing pair-choice freedom that 1-WL cannot resolve — is
// out of scope. StructuralPick is iso-invariant up to ties between
// structurally-equivalent pairs; for inputs whose tied class admits
// multiple iso-equivalent pair choices (e.g., the two diagonals of a
// 4-cycle), the resulting layer-creation order is not iso-invariant and
// the canonical bytes diverge across scramblings. Layer-permutation
// canonicalization (the multi-pass sort the prior design proposed) is
// future work.
//
// What was removed vs the prior file:
//   * Atom classification (within-class / cross-class / cross-component).
//   * Per-event Signature multisets.
//   * ForcedCompletion (no padding events).
//   * Multi-pass structural sort over layer indices.
//
// Layer order is content-determined: a layer exists exactly when the input
// genuinely needed a structural decision at that point.

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    public sealed class CanonGraphOrdererSupplant : ICanonGraphOrderer
    {
        public AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            var s = Setup(vertexTypes, G);
            EventLoop(s);
            PostProcessSupplant(s);
            FlipCanonicalize(s);
            int[] canonicalRanks = ComputeTupleDenseRank(s, s.L);
            return PermuteByDenseRanks(G, canonicalRanks);
        }

        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // ── Roles ──────────────────────────────────────────────────────────────
        // Lex order: Untouched < Cascaded(0) < Cascaded(1) < … < Low < High.
        // Low and High are adjacent so the per-layer flip is a Z/2 involution
        // that touches only the (A, B) cells of a Flip layer.

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

        private enum LayerKind : byte
        {
            Flip       = 0,
            Supplanted = 1,
        }

        // ── State ──────────────────────────────────────────────────────────────

        private sealed class State
        {
            public int N;
            public int[] Adj = [];
            public int[] R0  = [];
            public List<Role[]>   Layers     = [];
            public List<LayerKind> LayerKinds = [];
            public Workspace WS = new(0);
            public int L => Layers.Count;
        }

        private sealed class Workspace
        {
            public readonly int N;
            public readonly long[] RankPairs;
            public readonly int[]  VertexIdx;
            public readonly long[] SigBuf;
            public readonly int    SigStride;
            public readonly Comparer<int> SigComparer;
            public readonly int[]  NewKeys;

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
                Layers     = [],
                LayerKinds = [],
                WS         = ws,
            };
        }

        // ── Event loop ─────────────────────────────────────────────────────────

        private static void EventLoop(State s)
        {
            while (true)
            {
                var pair = StructuralPick(s);
                if (pair is null) break;

                int aIdx = pair.Value.A;
                int bIdx = pair.Value.B;

                // Append a fresh layer with the explicit guess A=Low, B=High.
                var layer = new Role[s.N];   // default Untouched
                layer[aIdx] = Role.Low;
                layer[bIdx] = Role.High;
                s.Layers.Add(layer);
                s.LayerKinds.Add(LayerKind.Flip);

                // 1-WL Discriminate over full tuples; decode others into
                // Cascaded(d) / Untouched while preserving A=Low, B=High.
                Discriminate(s, aIdx, bIdx);
            }
        }

        // ── Post-process supplant ──────────────────────────────────────────────
        //
        // Greedy late-to-early: for each layer k still marked Flip, try setting
        // every role at that layer to Untouched. If every pair of vertices
        // remains in distinct full tuples after the removal, layer k was
        // redundant — its information is implied by other layers + r₀. Mark
        // Supplanted (the layer stays at all-Untouched). Otherwise restore the
        // layer's roles.
        //
        // The greedy direction matters: removing a later layer can only make
        // earlier layers more essential, never less. Walking backwards lets
        // each decision stand without re-checking.

        private static void PostProcessSupplant(State s)
        {
            int n = s.N;
            int L = s.L;
            for (int k = L - 1; k >= 0; k--)
            {
                if (s.LayerKinds[k] != LayerKind.Flip) continue;

                Role[] layer = s.Layers[k];
                Role[] saved = (Role[])layer.Clone();
                for (int i = 0; i < n; i++) layer[i] = Role.Untouched;

                int[] keys = ComputeTupleDenseRank(s, L);
                bool allDistinct = true;
                if (n > 1)
                {
                    var seen = new HashSet<int>();
                    for (int i = 0; i < n; i++)
                    {
                        if (!seen.Add(keys[i])) { allDistinct = false; break; }
                    }
                }

                if (allDistinct)
                    s.LayerKinds[k] = LayerKind.Supplanted;
                else
                    Array.Copy(saved, layer, n);
            }
        }

        // ── Structural pair pick (iso-invariant) ──────────────────────────────
        //
        // Within the lowest tuple-tied class C, pick the pair (A, B) whose joint
        // adjacency multiset over u — the sorted list of
        //     (currentKey[u], min(adj[A,u], adj[B,u]), max(adj[A,u], adj[B,u]))
        // — is lex-smallest. The pair signature is symmetric in A, B, so it is
        // unchanged under the (A ↔ B) relabel; that means orbit-equivalent pairs
        // produce the same signature regardless of which physical vertices the
        // input scramble names them by, so the lex-min is iso-invariant.
        //
        // Within the picked pair, A is assigned Low and B High by index order.
        // That intra-pair choice is NOT iso-invariant under input scrambling,
        // but flip-canonicalization at the end of the run resolves it: a Flip
        // layer is exactly the case where A and B are interchangeable up to
        // Z/2, so the lex-min flip is canonical regardless of intra-pair pick.

        private static (int A, int B)? StructuralPick(State s)
        {
            int n = s.N;
            if (n < 2) return null;

            int[] keys = ComputeTupleDenseRank(s, s.L);

            var groups = new Dictionary<int, List<int>>();
            for (int i = 0; i < n; i++)
            {
                if (!groups.TryGetValue(keys[i], out var lst))
                    groups[keys[i]] = lst = [];
                lst.Add(i);
            }

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

            long[]? bestSig = null;
            int bestA = -1, bestB = -1;
            var sig = new long[n];
            for (int i = 0; i < members.Count; i++)
            {
                int A = members[i];
                int rowA = A * n;
                for (int j = i + 1; j < members.Count; j++)
                {
                    int B = members[j];
                    int rowB = B * n;
                    for (int u = 0; u < n; u++)
                    {
                        int aAdj = s.Adj[rowA + u];
                        int bAdj = s.Adj[rowB + u];
                        int mn = aAdj < bAdj ? aAdj : bAdj;
                        int mx = aAdj < bAdj ? bAdj : aAdj;
                        sig[u] = ((long)keys[u] << 32) | ((long)(uint)mn << 16) | (uint)(mx & 0xFFFF);
                    }
                    Array.Sort(sig);
                    if (bestSig is null || CompareLongArrays(sig, bestSig) < 0)
                    {
                        bestSig = (long[])sig.Clone();
                        bestA = A;
                        bestB = B;
                    }
                }
            }
            return (bestA, bestB);
        }

        // ── Discriminate (1-WL refinement over rank tuples) ────────────────────

        private static void Discriminate(State s, int aIdx, int bIdx)
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

            DecodeLayerRolesPair(s.Layers[L - 1], preEventKeys, currentKeys, n, aIdx, bIdx);
        }


        // ── Tuple key / role decoding ──────────────────────────────────────────

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

        // Pair-aware decode: keep A=Low, B=High. Other vertices in A and B's
        // pre-event class are split into sub-classes by their post-event keys
        // and assigned Cascaded(d) by ascending sub-class key. Vertices in
        // pre-event classes that did not split stay Untouched.
        private static void DecodeLayerRolesPair(
            Role[] layer, int[] preEventKeys, int[] currentKeys, int n, int aIdx, int bIdx)
        {
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
                foreach (int v in members)
                {
                    if (v == aIdx) { aInClass = 1; continue; }
                    if (v == bIdx) { bInClass = 1; continue; }
                    int postKey = currentKeys[v];
                    if (!subClasses.TryGetValue(postKey, out var lst))
                        subClasses[postKey] = lst = [];
                    lst.Add(v);
                }
                int adjustedPreSize = members.Count - aInClass - bInClass;
                if (adjustedPreSize == 0) continue;
                if (subClasses.Count == 1) continue;

                var sortedKeys = new List<int>(subClasses.Keys);
                sortedKeys.Sort();
                for (int d = 0; d < sortedKeys.Count; d++)
                {
                    var sub = subClasses[sortedKeys[d]];
                    foreach (int v in sub) layer[v] = Role.Cascaded(d);
                }
            }
        }

        // ── Flip canonicalization (NOT IMPLEMENTED in v1) ──────────────────────
        //
        // The intended end-of-run pass: for each Flip layer, lex-min over the
        // (Low ↔ High) swap at A and B. The simple version — swap labels in
        // place and compare canonical bytes — is *unsound*. Cascaded(d) values
        // on third parties were assigned under one direction of the guess; a
        // raw label swap leaves them inconsistent with the alternative cascade.
        //
        // A correct implementation has to re-run Discriminate per flip choice
        // (and propagate to subsequent layers, since their pair picks depend
        // on this layer's Cascaded(d) labels). That is brute-force territory.
        //
        // Consequence for v1: within-orbit pairs whose canonicalization needs
        // the Z/2 swap are not resolved. Same scope as the layer-permutation
        // gap noted in the file header.

        private static void FlipCanonicalize(State s) { _ = s; }

        private static int CompareLongArrays(long[] a, long[] b)
        {
            int len = a.Length < b.Length ? a.Length : b.Length;
            for (int i = 0; i < len; i++)
            {
                if (a[i] < b[i]) return -1;
                if (a[i] > b[i]) return 1;
            }
            return a.Length.CompareTo(b.Length);
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
