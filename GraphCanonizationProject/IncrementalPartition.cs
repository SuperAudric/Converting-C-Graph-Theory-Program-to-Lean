using System;
using System.Collections.Generic;

namespace Canonizer
{
    // Coloured-graph partition with warm-started refinement. State is a
    // per-vertex CellOf array; Refine() runs 1-WL color refinement to
    // fixpoint, but starting from the existing CellOf rather than from an
    // all-zero coloring. When CellOf is already a refinement of (or equal
    // to) the correct partition for (adj, P) — which is the case after a
    // small P mutation from a converged state — refinement converges in a
    // few rounds instead of O(n) rounds. Worst case is identical to cold
    // refinement.
    //
    // Cell IDs are assigned by canonical lex-sort of (own-color, sorted
    // neighbour-tuple multiset). Because cold refinement uses the same sort
    // and starts from the canonical all-zero coloring, two scramblings that
    // both warm-refine from a canonical state to the same target partition
    // arrive at the same numbering. That preserves the iso-invariance of
    // cell IDs that the canonizer's between-cell guess selection depends on.
    internal sealed class WarmPartition
    {
        public readonly int N;
        public readonly int[] CellOf;
        public int NumCells { get; private set; }

        public WarmPartition(int n)
        {
            N = n;
            CellOf = new int[n];   // all zero: one big cell, will refine to coarsest equitable partition on first call
            NumCells = 1;
        }

        private WarmPartition(int n, int[] cellOf, int numCells)
        {
            N = n;
            CellOf = cellOf;
            NumCells = numCells;
        }

        public WarmPartition Clone() => new(N, (int[])CellOf.Clone(), NumCells);

        // Refine to fixpoint, warm-starting from current CellOf.
        public void Refine(int[] adj, sbyte[] p)
        {
            while (RefineRound(adj, p)) { }
        }

        // One round of refinement. Returns true if the partition changed
        // (i.e. another round is needed).
        private bool RefineRound(int[] adj, sbyte[] p)
        {
            // Per-vertex signature: [own-color, sorted neighbour tuples].
            // Each neighbour tuple packs (neighbour-color, edge-label, Prel)
            // into a single long for cheap sorting and comparison.
            var sigs = new long[N][];
            for (int v = 0; v < N; v++)
            {
                var tuples = new long[N];
                tuples[0] = CellOf[v];
                int k = 1;
                for (int u = 0; u < N; u++)
                {
                    if (u == v) continue;
                    tuples[k++] = ((long)CellOf[u] << 24)
                                  | ((long)(uint)adj[v * N + u] << 8)
                                  | ((long)(p[v * N + u] + 1) & 0xFF);
                }
                Array.Sort(tuples, 1, N - 1);
                sigs[v] = tuples;
            }

            // Canonical ranking: lex-sorted distinct signatures get sequential
            // ids. The lex sort is what makes the ids iso-invariant.
            var distinct = new SortedSet<long[]>(LongArrayLex.Instance);
            for (int v = 0; v < N; v++) distinct.Add(sigs[v]);
            var rank = new Dictionary<long[], int>(distinct.Count, LongArrayEq.Instance);
            int r = 0;
            foreach (var sig in distinct) rank[sig] = r++;

            bool changed = false;
            for (int v = 0; v < N; v++)
            {
                int newColor = rank[sigs[v]];
                if (newColor != CellOf[v]) changed = true;
                CellOf[v] = newColor;
            }
            NumCells = distinct.Count;
            return changed;
        }

        private sealed class LongArrayEq : IEqualityComparer<long[]>
        {
            public static readonly LongArrayEq Instance = new();
            public bool Equals(long[]? a, long[]? b)
            {
                if (ReferenceEquals(a, b)) return true;
                if (a is null || b is null || a.Length != b.Length) return false;
                for (int i = 0; i < a.Length; i++) if (a[i] != b[i]) return false;
                return true;
            }
            public int GetHashCode(long[] a)
            {
                unchecked
                {
                    ulong h = 14695981039346656037UL;
                    for (int i = 0; i < a.Length; i++)
                    {
                        h ^= (ulong)a[i];
                        h *= 1099511628211UL;
                    }
                    return (int)h;
                }
            }
        }

        private sealed class LongArrayLex : IComparer<long[]>
        {
            public static readonly LongArrayLex Instance = new();
            public int Compare(long[]? a, long[]? b)
            {
                if (ReferenceEquals(a, b)) return 0;
                if (a is null) return -1;
                if (b is null) return 1;
                int min = a.Length < b.Length ? a.Length : b.Length;
                for (int i = 0; i < min; i++)
                {
                    if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
                }
                return a.Length.CompareTo(b.Length);
            }
        }
    }
}
