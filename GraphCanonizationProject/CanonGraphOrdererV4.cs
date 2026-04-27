using System.Collections.Generic;
using System;

// Graph canonizer based on path multisets between vertices.
// Paths from A→B are a different "type" from C→D when composed of different subpath-type
// multisets, or when endpoint vertex types differ. Vertex types are refined iteratively
// until a fixed point is reached.
// Intended for translation to Lean 4; refactored toward pure/functional style accordingly.

namespace Canonizer
{
    using VertexType = int; //Used semantically to help keep track of what's being referred to.
    using EdgeType = int;

    // Lean translation: structure AdjMatrix (vertexCount : Nat) where adj : Fin vc → Fin vc → EdgeType.
    // The C# version wraps a square EdgeType[,] and exposes a read-only indexer plus the
    // immutable swapVertexLabels and ToString operations. Construction clones the input so
    // callers' arrays are never aliased into the matrix.
    public sealed class AdjMatrix
    {
        public readonly int VertexCount;
        private readonly EdgeType[,] _adj;

        public AdjMatrix(EdgeType[,] adj)
        {
            if (adj.GetLength(0) != adj.GetLength(1))
                throw new Exception("Edges must be a square matrix");
            VertexCount = adj.GetLength(0);
            _adj = (EdgeType[,])adj.Clone();
        }

        private AdjMatrix(EdgeType[,] adj, bool takeOwnership)
        {
            VertexCount = adj.GetLength(0);
            _adj = takeOwnership ? adj : (EdgeType[,])adj.Clone();
        }

        public EdgeType this[int fromVertex, int toVertex] => _adj[fromVertex, toVertex];

        // Lean: AdjMatrix.swapVertexLabels. Swaps rows and columns of vertex1 and vertex2.
        public AdjMatrix SwapVertexLabels(int vertex1, int vertex2)
        {
            if (vertex1 == vertex2) return this;
            var result = new EdgeType[VertexCount, VertexCount];
            for (int x = 0; x < VertexCount; x++)
                for (int y = 0; y < VertexCount; y++)
                    result[x, y] = _adj[
                        x == vertex1 ? vertex2 : x == vertex2 ? vertex1 : x,
                        y == vertex1 ? vertex2 : y == vertex2 ? vertex1 : y];
            return new AdjMatrix(result, takeOwnership: true);
        }

        public EdgeType[,] ToArray() => (EdgeType[,])_adj.Clone();

        // Lean: adjToString. Rows separated by '\n', cells in a row separated by a single space.
        public override string ToString() =>
            string.Join("\n", Enumerable.Range(0, VertexCount).Select(x =>
                string.Join(" ", Enumerable.Range(0, VertexCount).Select(y =>
                    _adj[x, y].ToString()))));
    }

    public class CanonGraphOrdererV4
    {
        // Lean: run. Pure pipeline returning the canonicalized AdjMatrix.
        public AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");
            VertexType[] vertexRankings = GetArrayRank(vertexTypes.ToArray());
            PathState state = InitializePaths(G);
            vertexRankings = OrderVertices(state, vertexRankings);
            return LabelEdgesAccordingToRankings(vertexRankings, G);
        }

        // Convenience wrapper that takes a raw EdgeType[,] and returns the formatted string.
        // Most existing tests call this form. New code should prefer Run + ToString.
        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // Lean translation: a pure record threaded through all functions.
        // PathState holds only structural (edge-derived) information; vertex types are
        // passed separately and never cached inside path objects.
        private record PathState(PathsByLength[] PathsOfLength, int VertexCount);

        // Rank lookup tables produced by CalculatePathRankings.
        // Lean translation: returned as immutable values from a pure function.
        //   BetweenRanks[depth, fromVertex, toVertex] = rank of all depth-length paths between those vertices
        //   FromRanks[depth, fromVertex]               = rank of all depth-length paths from that vertex
        private record RankState(int[,,] BetweenRanks, int[,] FromRanks);

        // PathState is built once from the AdjMatrix alone; vertex types are never stored inside it.
        private static PathState InitializePaths(AdjMatrix G)
        {
            int n = G.VertexCount;
            var pathsOfLength = new PathsByLength[n];
            for (int depth = 0; depth < n; depth++)
            {
                pathsOfLength[depth] = new PathsByLength(n);
                for (int from = 0; from < n; from++)
                {
                    pathsOfLength[depth].pathsFromVertex[from] = new AllPathsFrom(depth, from, n);
                    for (int to = 0; to < n; to++)
                    {
                        pathsOfLength[depth].pathsFromVertex[from].pathsToVertex[to] =
                            new AllPathsBetween(depth, from, to, n);
                        if (depth == 0)
                        {
                            pathsOfLength[depth].pathsFromVertex[from].pathsToVertex[to].connectedSubPaths =
                                from == to ? [new BottomPathSegment(from)] : [];
                            continue;
                        }
                        for (int mid = 0; mid < n; mid++)
                        {
                            pathsOfLength[depth].pathsFromVertex[from].pathsToVertex[to].connectedSubPaths[mid] =
                                new InnerPathSegment(
                                    G[mid, to],
                                    pathsOfLength[depth - 1].pathsFromVertex[from].pathsToVertex[mid]);
                        }
                    }
                }
            }
            return new PathState(pathsOfLength, n);
        }

        // Position permutation: ties in vertexRankings are broken by original index.
        // output[v] = position of v in the sort by (vertexRankings[v], v).
        // Lean: computeDenseRanks (name kept for symmetry; this is a permutation, not a
        // dense rank in the rank-statistics sense — see GetArrayRank for the proper dense rank).
        private static int[] ComputeDenseRanks(VertexType[] vertexRankings) =>
            vertexRankings
                .Select((v, i) => (v, i))
                .OrderBy(p => p)
                .Select((p, rank) => (rank, p.i))
                .OrderBy(x => x.i)
                .Select(x => x.rank)
                .ToArray();

        // Relabels the adjacency matrix so vertex positions match the given rankings.
        public static AdjMatrix LabelEdgesAccordingToRankings(VertexType[] vertexRankings, AdjMatrix G)
        {
            int[] rankings = ComputeDenseRanks(vertexRankings);
            AdjMatrix orderedGraph = G;
            for (int i = 0; i < rankings.Length; i++)
            {
                int j = Array.IndexOf(rankings, i);
                orderedGraph = orderedGraph.SwapVertexLabels(i, j);
                (rankings[j], rankings[i]) = (rankings[i], rankings[j]);
            }
            return orderedGraph;
        }

        // Backward-compat overload retained for existing tests that pass raw EdgeType[,].
        public static EdgeType[,] LabelEdgesAccordingToRankings(VertexType[] vertexRankings, EdgeType[,] edges) =>
            LabelEdgesAccordingToRankings(vertexRankings, new AdjMatrix(edges)).ToArray();

        // One pass of ranking propagation. Lean: convergeOnce
        private static (VertexType[] rankings, bool changed) ConvergeOnce(PathState state, VertexType[] vertexRankings)
        {
            RankState ranks = CalculatePathRankings(state, vertexRankings);
            int n = state.VertexCount;
            bool changed = false;
            var updated = vertexRankings.ToArray();
            for (int v = 0; v < n; v++)
            {
                int newRank = ranks.FromRanks[n - 1, v];
                if (newRank != updated[v]) { updated[v] = newRank; changed = true; }
            }
            return (updated, changed);
        }

        // Runs ConvergeOnce until stable or fuel is exhausted. Lean: convergeLoop
        private static VertexType[] ConvergeLoop(PathState state, VertexType[] vertexRankings, int fuel)
        {
            for (int i = 0; i < fuel; i++)
            {
                var (updated, changed) = ConvergeOnce(state, vertexRankings);
                vertexRankings = updated;
                if (!changed) break;
            }
            return vertexRankings;
        }

        // Lean: shiftAbove. Bumps every value strictly greater than `target` up by one,
        // opening a one-slot gap at `target + 1`. Required because dense ranks leave no
        // gap between consecutive equivalence classes.
        private static VertexType[] ShiftAbove(VertexType[] vertexRankings, int target)
        {
            var result = new VertexType[vertexRankings.Length];
            for (int i = 0; i < vertexRankings.Length; i++)
                result[i] = vertexRankings[i] > target ? vertexRankings[i] + 1 : vertexRankings[i];
            return result;
        }

        // Promotes all-but-the-first occurrence of `target` to `target + 1`. Caller must
        // ensure no existing `target + 1` class collides (BreakTie handles this via ShiftAbove).
        // Lean: breakTiePromote
        private static (VertexType[] rankings, bool changed) BreakTiePromote(VertexType[] vertexRankings, int target)
        {
            bool firstAppearance = true;
            bool changed = false;
            var updated = vertexRankings.ToArray();
            for (int i = 0; i < updated.Length; i++)
            {
                if (updated[i] != target) continue;
                if (firstAppearance) { firstAppearance = false; continue; }
                updated[i] = target + 1;
                changed = true;
            }
            return (updated, changed);
        }

        // Top-level tiebreak: if at least two vertices share value `target`, open a gap
        // above `target` (ShiftAbove) and promote all-but-one to `target + 1`. Otherwise
        // return the input unchanged. The gating preserves dense typings as input/output.
        // Lean: breakTie
        private static (VertexType[] rankings, bool changed) BreakTie(VertexType[] vertexRankings, int target)
        {
            int count = 0;
            for (int i = 0; i < vertexRankings.Length; i++)
                if (vertexRankings[i] == target) count++;
            if (count < 2) return (vertexRankings.ToArray(), false);
            return BreakTiePromote(ShiftAbove(vertexRankings, target), target);
        }

        // Lean: orderVertices
        private static VertexType[] OrderVertices(PathState state, VertexType[] vertexRankings)
        {
            int n = state.VertexCount;
            for (int targetPosition = 0; targetPosition < n; targetPosition++)
            {
                vertexRankings = ConvergeLoop(state, vertexRankings, n);
                (vertexRankings, _) = BreakTie(vertexRankings, targetPosition);
            }
            return vertexRankings;
        }

        // Computes ranks for every (depth, from, to) triple and every (depth, from) pair.
        // Does not mutate any PathState objects; produces fresh rank tables.
        private static RankState CalculatePathRankings(PathState state, VertexType[] vertexTypes)
        {
            int n = state.VertexCount;
            var betweenRanks = new int[n, n, n];
            var fromRanks = new int[n, n];
            for (int depth = 0; depth < n; depth++)
            {
                RankPathsBetween(
                    state.PathsOfLength[depth].pathsFromVertex.SelectMany(x => x.pathsToVertex).ToArray(),
                    vertexTypes, depth, betweenRanks);
                RankPathsFrom(state.PathsOfLength[depth].pathsFromVertex, vertexTypes, depth, betweenRanks, fromRanks);
            }
            return new RankState(betweenRanks, fromRanks);
        }

        // Dense ranks: each equivalence class gets a unique consecutive ordinal 0, 1, 2, …
        // E.g. sorted [a,a,b,c] → [(a,0),(a,0),(b,1),(c,2)]. Lean: assignRanks.
        // [sparse→dense] Was previously sparse (counter = i on transition). Dense form is
        // what BreakTie's gap-opening logic now relies on.
        private static (T item, int rank)[] AssignRanks<T>(T[] sorted, Comparison<T> compare)
        {
            var result = new (T, int)[sorted.Length];
            int counter = 0;
            for (int i = 0; i < sorted.Length; i++)
            {
                if (i > 0 && compare(sorted[i - 1], sorted[i]) != 0)
                    counter++;
                result[i] = (sorted[i], counter);
            }
            return result;
        }

        // Sorts all (from, to) path-sets at the given depth and writes their ranks into
        // betweenRanks[depth, from, to].  Reads betweenRanks for depth-1 (already filled).
        private static void RankPathsBetween(AllPathsBetween[] paths, VertexType[] vertexTypes, int depth, int[,,] betweenRanks)
        {
            int compare(AllPathsBetween x, AllPathsBetween y) => ComparePathsBetween(x, y, vertexTypes, betweenRanks);
            var sorted = paths.ToArray();
            Array.Sort(sorted, compare);
            foreach (var (path, rank) in AssignRanks(sorted, compare))
                betweenRanks[depth, path.startVertexIndex, path.endVertexIndex] = rank;
        }

        // Sorts all from-vertex path-sets at the given depth and writes their ranks into
        // fromRanks[depth, from].  Reads betweenRanks for depth-1 (via ComparePathsBetween).
        private static void RankPathsFrom(AllPathsFrom[] paths, VertexType[] vertexTypes, int depth, int[,,] betweenRanks, int[,] fromRanks)
        {
            int compare(AllPathsFrom x, AllPathsFrom y) => ComparePathsFrom(x, y, vertexTypes, betweenRanks);
            var sorted = paths.ToArray();
            Array.Sort(sorted, compare);
            foreach (var (path, rank) in AssignRanks(sorted, compare))
                fromRanks[depth, path.startVertexIndex] = rank;
        }

        // Lean translation: inductive PathSegment
        //   | bottom (vertexIndex : Nat) : PathSegment
        //   | inner  (edgeType : EdgeType) (subPath : AllPathsBetween) : PathSegment
        public abstract class PathSegment { }

        public sealed class BottomPathSegment(int vertexIndex) : PathSegment
        {
            public readonly int vertexIndex = vertexIndex;
        }

        public sealed class InnerPathSegment(EdgeType edgeType, AllPathsBetween subPath) : PathSegment
        {
            public readonly EdgeType edgeType = edgeType;
            public readonly AllPathsBetween subPath = subPath;
        }

        // Lean translation: these three become Ord instances (or explicit compare functions).
        // vertexTypes supplies the current ranking for each vertex index.

        // betweenRanks supplies the pre-computed rank of each subPath referenced by InnerPathSegments.
        public static int ComparePathSegments(PathSegment x, PathSegment y, VertexType[] vertexTypes, int[,,] betweenRanks)
        {
            if (x is BottomPathSegment bx && y is BottomPathSegment by)
            {
                VertexType tx = vertexTypes[bx.vertexIndex];
                VertexType ty = vertexTypes[by.vertexIndex];
                return tx != ty ? (tx > ty ? 1 : -1) : 0;
            }
            if (x is InnerPathSegment ix && y is InnerPathSegment iy)
            {
                int rx = betweenRanks[ix.subPath.depth, ix.subPath.startVertexIndex, ix.subPath.endVertexIndex];
                int ry = betweenRanks[iy.subPath.depth, iy.subPath.startVertexIndex, iy.subPath.endVertexIndex];
                if (rx != ry) return rx < ry ? 1 : -1;
                if (ix.edgeType != iy.edgeType) return ix.edgeType < iy.edgeType ? 1 : -1;
                return 0;
            }
            // Mixed bottom/inner does not arise in practice (connectedSubPaths is uniform per
            // call). Lean picks a definite ordering here so the comparator is a total preorder;
            // in C# we mirror that with `bottom < inner`.
            if (x is BottomPathSegment) return -1;
            return 1;
        }

        public static int ComparePathsBetween(AllPathsBetween x, AllPathsBetween y, VertexType[] vertexTypes, int[,,] betweenRanks)
        {
            VertexType ex = vertexTypes[x.endVertexIndex];
            VertexType ey = vertexTypes[y.endVertexIndex];
            if (ex != ey) return ex > ey ? 1 : -1;
            return OrderInsensitiveListComparison(x.connectedSubPaths, y.connectedSubPaths,
                (a, b) => ComparePathSegments(a, b, vertexTypes, betweenRanks));
        }

        public static int ComparePathsFrom(AllPathsFrom x, AllPathsFrom y, VertexType[] vertexTypes, int[,,] betweenRanks)
        {
            VertexType sx = vertexTypes[x.startVertexIndex];
            VertexType sy = vertexTypes[y.startVertexIndex];
            if (sx != sy) return sx > sy ? 1 : -1;
            return OrderInsensitiveListComparison(x.pathsToVertex, y.pathsToVertex,
                (a, b) => ComparePathsBetween(a, b, vertexTypes, betweenRanks));
        }

        // All paths of a given length between two specific vertices.
        public class AllPathsBetween
        {
            public readonly int depth;            // index into BetweenRanks first dimension
            public readonly int startVertexIndex; // index into BetweenRanks second dimension
            public readonly int endVertexIndex;   // index into BetweenRanks third dimension
            public PathSegment[] connectedSubPaths;

            public AllPathsBetween(int depth, int startVertexIndex, int endVertexIndex, int n)
            {
                this.depth = depth;
                this.startVertexIndex = startVertexIndex;
                this.endVertexIndex = endVertexIndex;
                this.connectedSubPaths = new PathSegment[n];
            }
        }

        // All paths of a given length starting from one specific vertex.
        public class AllPathsFrom
        {
            public readonly int startVertexIndex; // index into FromRanks second dimension
            public readonly int depth;            // index into FromRanks first dimension
            public AllPathsBetween[] pathsToVertex;

            public AllPathsFrom(int depth, int startVertexIndex, int n)
            {
                this.depth = depth;
                this.startVertexIndex = startVertexIndex;
                this.pathsToVertex = new AllPathsBetween[n];
            }
        }

        private class PathsByLength(int vertexCount)
        {
            public AllPathsFrom[] pathsFromVertex = new AllPathsFrom[vertexCount];
        }

        // Compares two arrays by their sorted contents rather than element order.
        // E.g. [a,b,b,c] == [a,b,c,b].
        public static int OrderInsensitiveListComparison<T>(T[] arr1, T[] arr2, Comparison<T> compare)
        {
            if (arr1.Length != arr2.Length)
                return arr1.Length < arr2.Length ? 1 : -1;
            T[] s1 = arr1.ToArray();
            T[] s2 = arr2.ToArray();
            Array.Sort(s1, compare);
            Array.Sort(s2, compare);
            for (int i = 0; i < s1.Length; i++)
            {
                int cmp = compare(s1[i], s2[i]);
                if (cmp != 0) return cmp;
            }
            return 0;
        }

        // Dense rank: replaces each value with the number of *distinct* values strictly
        // less than it (ties preserved). E.g. [5, 0, 5, 3] → [2, 0, 2, 1].
        // Lean: getArrayRank.
        // [sparse→dense] Was previously "count of strictly smaller values" (sparse, e.g.
        // [5,0,5,3]→[3,0,3,1]). Dense form keeps the IsPrefixTyping invariant true at
        // entry; both forms preserve the partition and downstream comparison behavior.
        private static VertexType[] GetArrayRank(VertexType[] arr)
        {
            if (arr.Length < 2) return arr;
            var sortedByValue = arr.Select((v, i) => (v, i)).OrderBy(x => x.v).ToArray();
            int counter = 0;
            var output = new (VertexType rank, int original)[sortedByValue.Length];
            output[0] = (0, sortedByValue[0].i);
            for (int i = 1; i < sortedByValue.Length; i++)
            {
                if (sortedByValue[i - 1].v != sortedByValue[i].v)
                    counter++;
                output[i] = ((VertexType)counter, sortedByValue[i].i);
            }
            return output.OrderBy(x => x.original).Select(x => x.rank).ToArray();
        }

        // Debug helper: displays the ranked path structure at a given depth.
        private static string LayerToString(PathState state, RankState ranks, VertexType[] vertexTypes, int depth = 0) =>
            string.Join("\n", state.PathsOfLength[depth].pathsFromVertex.Select(pathStart =>
                ranks.FromRanks[depth, pathStart.startVertexIndex] + ". " + pathStart.pathsToVertex.Length + " paths:(" +
                string.Join(",", pathStart.pathsToVertex.Select(pb =>
                    "<" + string.Join("    ", pb.connectedSubPaths.Select(seg =>
                        seg is InnerPathSegment s
                            ? "[" + ranks.BetweenRanks[s.subPath.depth, s.subPath.startVertexIndex, s.subPath.endVertexIndex] + "," + s.edgeType + "]"
                            : "[bottom:" + vertexTypes[((BottomPathSegment)seg).vertexIndex] + "]")) +
                    ">")) + ")"));
    }
}
