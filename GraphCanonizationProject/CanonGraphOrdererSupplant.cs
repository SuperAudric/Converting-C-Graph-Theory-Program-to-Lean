using System;
using System.Collections.Generic;

// Layered Tiebreak with Supplant (pair-event variant).
// See docs/supplant-strategy.md for the algorithm specification.
//
// Each tiebreak event individualizes a *pair* (A, B) with roles low/high
// — a binary, invertible commitment. Reconciliation across input scrambles
// happens after all events run, via a multi-pass canonicalization that
// resolves:
//   - flip dimension      (Z/2 inverse on role labels, layer-local)
//   - atom-multiset dim   (forced completion)
//   - layer-position dim  (multi-pass structural sort, outer to inner)
//
// Discriminator: 1-WL (color refinement). Same shape as
// CanonGraphOrdererOneWL, but extended to operate over rank tuples
// instead of single integer ranks. Layer 0 holds r₀ (1-WL fixed-point);
// layers 1..L hold one Role value per vertex per event.
//
// Status: first-pass implementation. EventLoop, Discriminate, PickPair,
// ClassifyAtom, ComputeSignature, and the connected-component helper are
// fleshed out. ForcedCompletion is a no-op (§6.1 not yet wired). Supplant
// is a baseline dense-rank of the final full tuple — multi-pass sort and
// flip-canonicalization (§6.3) are not yet implemented; the baseline is
// canonical for §7-style inputs only when the natural event sequence
// already matches across scrambles.

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    public sealed class CanonGraphOrdererSupplant : ICanonGraphOrderer
    {
        // ── Public API ──────────────────────────────────────────────────────────

        public AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            var s = Setup(vertexTypes, G);
            EventLoop(s);
            ForcedCompletion(s);
            int[] canonicalRanks = Supplant(s);
            return PermuteByDenseRanks(G, canonicalRanks);
        }

        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // ── Role values (per layer, per vertex) ─────────────────────────────────
        //
        // Lex order:
        //   Untouched < Cascaded(0) < Cascaded(1) < … < Low < High
        //
        // Adjacency of Low and High in this order is what makes the per-layer
        // flip a Z/2 involution that does not perturb any cascaded vertex's
        // value: swapping Low ↔ High moves only A and B's role at this layer.

        private enum RoleKind : byte
        {
            Untouched = 0,
            Cascaded  = 1,
            Low       = 2,
            High      = 3,
        }

        private readonly struct Role : IComparable<Role>, IEquatable<Role>
        {
            public readonly RoleKind Kind;
            public readonly int CascadedRank;       // valid only when Kind == Cascaded

            public Role(RoleKind kind, int cascadedRank = 0)
            {
                Kind = kind;
                CascadedRank = cascadedRank;
            }

            public static readonly Role Untouched = new Role(RoleKind.Untouched);
            public static readonly Role Low       = new Role(RoleKind.Low);
            public static readonly Role High      = new Role(RoleKind.High);
            public static Role Cascaded(int d)    => new Role(RoleKind.Cascaded, d);

            public Role Flipped() => Kind switch
            {
                RoleKind.Low  => High,
                RoleKind.High => Low,
                _             => this,
            };

            public int CompareTo(Role other)
            {
                int kc = ((byte)Kind).CompareTo((byte)other.Kind);
                if (kc != 0) return kc;
                return CascadedRank.CompareTo(other.CascadedRank);
            }

            public bool Equals(Role other) =>
                Kind == other.Kind && CascadedRank == other.CascadedRank;

            public override bool Equals(object? obj) => obj is Role r && Equals(r);
            public override int GetHashCode() => ((byte)Kind, CascadedRank).GetHashCode();
        }

        // ── Atom classification ────────────────────────────────────────────────

        private enum AtomType
        {
            WithinClass,                  // cascade refines source class internally
            CrossClassSameComponent,      // cascade orders two same-component classes
            CrossComponent,               // cascade orders two disjoint-component classes
            Redundant,                    // forced-completion event with no new info
        }

        private sealed class EventRecord
        {
            public int LayerIndex;
            public int A;
            public int B;
            public AtomType Type;
            public long[] Signature = [];                   // sorted multiset, encoded
            public bool IsRedundant;
        }

        // ── Algorithm state ────────────────────────────────────────────────────

        private sealed class State
        {
            public int N;
            public int[] Adj = [];                           // n*n flattened, row-major
            public int[] R0  = [];                           // 1-WL fixed-point rank per vertex
            public int[] Components = [];                    // BFS connected-component id per vertex
            public List<Role[]> Layers = [];                 // Layers[k][v] = role at layer (k+1) for vertex v
            public List<EventRecord> Events = [];
            public Workspace WS = new(0);

            public int L => Layers.Count;                    // number of completed events
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
                SigBuf = n > 0 ? new long[n * SigStride] : [];
                NewKeys = n > 0 ? new int[n] : [];

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

        // ── Phase 1: Setup ─────────────────────────────────────────────────────

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

            // 1-WL refinement on bare integer ranks → r₀ (frozen for the run).
            OneWlFixedPoint(n, adj, r0, ws);

            var components = ComputeConnectedComponents(n, adj);

            return new State
            {
                N          = n,
                Adj        = adj,
                R0         = r0,
                Components = components,
                Layers     = [],
                Events     = [],
                WS         = ws,
            };
        }

        // ── Phase 2: Event loop ────────────────────────────────────────────────

        private static void EventLoop(State s)
        {
            while (true)
            {
                var pair = PickPair(s);
                if (pair is null) break;
                AppendEvent(s, pair.Value.A, pair.Value.B, isRedundant: false);
            }
        }

        private static void AppendEvent(State s, int a, int b, bool isRedundant)
        {
            // Append a fresh layer initialized to Untouched, then tag (A, B).
            var layer = new Role[s.N];          // default = Role(Untouched)
            layer[a] = Role.Low;
            layer[b] = Role.High;
            s.Layers.Add(layer);
            int layerIndex = s.L - 1;

            Discriminate(s);                    // refines layer at layerIndex

            s.Events.Add(new EventRecord
            {
                LayerIndex  = layerIndex,
                A           = a,
                B           = b,
                Type        = isRedundant ? AtomType.Redundant : ClassifyAtom(s, layerIndex),
                Signature   = ComputeSignature(s, layerIndex),
                IsRedundant = isRedundant,
            });
        }

        // ── Phase 3: Forced completion ─────────────────────────────────────────

        private static void ForcedCompletion(State s)
        {
            // First-prototype simplification: no-op. The baseline EventLoop
            // already collects events that suffice when the "natural" event
            // sequence matches across scrambles; forced completion is needed
            // only to canonicalize event-count differences across scrambles.
            //
            // TODO (docs/supplant-strategy.md §6.1): walk each tuple-tied
            // class encountered during EventLoop, run an event for every
            // pair-rank class not already explored, and tag IsRedundant when
            // Discriminate adds no new split.
            _ = s;
        }

        // ── Phase 4: Supplant ──────────────────────────────────────────────────

        private static int[] Supplant(State s)
        {
            // Baseline: dense-rank vertices by their final full tuple
            // (r₀, role_1, …, role_L) under Role's IComparable. Skips the
            // multi-pass sort and flip-canonicalization (§6.3) — those make
            // the algorithm canonical on §8-class inputs and are TODO.
            return ComputeTupleDenseRank(s, s.L);
        }

        // ── Discriminate (1-WL refinement over rank tuples) ────────────────────

        private static void Discriminate(State s)
        {
            int n = s.N;
            int L = s.L;
            if (L == 0) return;

            // Pre-event partition: tuple keys excluding the just-added layer.
            int[] preEventKeys = ComputeTupleDenseRank(s, layerCount: L - 1);

            // Initial post-event partition: tuple keys including the new
            // layer (whose Roles are A=Low, B=High, others=Untouched).
            int[] currentKeys = ComputeTupleDenseRank(s, layerCount: L);

            // 1-WL fixed point on the integer keys.
            for (int iter = 0; iter < n; iter++)
            {
                BuildVertexSignatures(n, s.Adj, currentKeys, s.WS);
                AssignVertexRanks(n, s.WS);
                if (!RanksDiffer(n, currentKeys, s.WS.NewKeys)) break;
                Array.Copy(s.WS.NewKeys, currentKeys, n);
            }

            // Decode the converged partition back to layer-L Role values.
            DecodeLayerRoles(s, L - 1, preEventKeys, currentKeys);
        }

        // Compute integer dense-ranks of vertices keyed on their tuple
        // (r₀, role_1, …, role_{layerCount-1}). When layerCount == 0 this
        // dense-ranks r₀ alone.
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

        // ── Decode 1-WL output to layer-L roles ────────────────────────────────
        //
        // For each pre-event class C:
        //   - {A} and {B} singleton sub-classes keep their explicit Low / High.
        //   - Among the remaining sub-classes:
        //       · if there is exactly one and it equals C \ {A, B}, the
        //         cascade did not split the non-tagged members — they stay
        //         Untouched.
        //       · otherwise the non-tagged members were split; assign each
        //         sub-class a Cascaded(d) value, with d = dense-rank of the
        //         sub-class's post-event key within C.

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

            // Group vertices by pre-event class.
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

                // Within this pre-event class, group non-tagged members by post-event key.
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

                if (subClasses.Count == 1)
                {
                    // Pre-event class minus tagged singletons did not split:
                    // those vertices stay Untouched (already the layer default).
                    continue;
                }

                // Multiple sub-classes: assign Cascaded(d) by ascending post-event key.
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

        // ── Pair selection ─────────────────────────────────────────────────────

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

            // Lowest key with size ≥ 2.
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
            return (members[0], members[1]);
        }

        // ── Atom classification ────────────────────────────────────────────────

        private static AtomType ClassifyAtom(State s, int layerIndex)
        {
            int n = s.N;
            Role[] layer = s.Layers[layerIndex];

            // Pre-event keys = tuple keys excluding this layer.
            int[] preEventKeys = ComputeTupleDenseRank(s, layerIndex);

            int aIdx = -1;
            for (int i = 0; i < n; i++)
            {
                if (layer[i].Kind == RoleKind.Low) { aIdx = i; break; }
            }
            if (aIdx < 0) return AtomType.WithinClass;     // degenerate

            int sourceClass     = preEventKeys[aIdx];
            int sourceComponent = s.Components[aIdx];

            bool reachedOtherClass     = false;
            bool reachedOtherComponent = false;

            for (int i = 0; i < n; i++)
            {
                if (layer[i].Kind != RoleKind.Cascaded) continue;
                if (preEventKeys[i] != sourceClass)     reachedOtherClass = true;
                if (s.Components[i] != sourceComponent) reachedOtherComponent = true;
            }

            if (reachedOtherComponent) return AtomType.CrossComponent;
            if (reachedOtherClass)     return AtomType.CrossClassSameComponent;
            return AtomType.WithinClass;
        }

        // ── Signature ──────────────────────────────────────────────────────────
        //
        // Sorted multiset over affected vertices, each entry packed as
        //   [pre-event class id (32 bits)] [role kind (8 bits)] [cascaded rank (24 bits)]
        // High 32 bits put pre-event class first in lex order; within a
        // class, role kind and cascaded rank determine sub-class identity.

        private static long[] ComputeSignature(State s, int layerIndex)
        {
            int n = s.N;
            Role[] layer = s.Layers[layerIndex];
            int[] preEventKeys = ComputeTupleDenseRank(s, layerIndex);

            int count = 0;
            for (int i = 0; i < n; i++)
                if (layer[i].Kind != RoleKind.Untouched) count++;

            var entries = new long[count];
            int idx = 0;
            for (int i = 0; i < n; i++)
            {
                if (layer[i].Kind == RoleKind.Untouched) continue;
                long packed =
                    ((long)preEventKeys[i] << 32) |
                    ((long)(byte)layer[i].Kind << 24) |
                    (uint)(layer[i].CascadedRank & 0xFFFFFF);
                entries[idx++] = packed;
            }
            Array.Sort(entries);
            return entries;
        }

        // ── 1-WL primitives (lifted from CanonGraphOrdererOneWL) ───────────────

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

        // sig[v]: slot 0 = ranks[v]; slots 1..n = sorted longs encoding
        // ((ranks[u] * 2 + (u == v ? 1 : 0)) << 32) | adj[v, u] for each u.
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

        // ── Connected components (BFS) ─────────────────────────────────────────

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

        // ── Permute by dense ranks ─────────────────────────────────────────────
        // Same as TwoWL/OneWL/V4Fast.

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
    }
}
