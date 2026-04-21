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

    public class CanonGraphOrdererV4
    {
        public string Run(VertexType[] vertexTypes, EdgeType[,] edges)
        {
            ValidateInputs(vertexTypes, edges);
            VertexType[] vertexRankings = GetVertexTypeRankings(vertexTypes);
            PathState state = InitializePaths(edges);
            vertexRankings = OrderVertices(state, vertexRankings);
            EdgeType[,] canonicalOrdering = LabelEdgesAccordingToRankings(vertexRankings, edges);
            return AdjMatrixToString(canonicalOrdering);
        }

        private static void ValidateInputs(VertexType[] vertexTypes, EdgeType[,] edges)
        {
            if (edges.GetLength(0) != edges.GetLength(1))
                throw new Exception("Edges must be a square matrix");
            if (vertexTypes.Length != edges.GetLength(0))
                throw new Exception("Every vertex must be given a type. They may all be given the same type");
        }

        private static VertexType[] GetVertexTypeRankings(VertexType[] vertexTypes) =>
            GetArrayRank(vertexTypes.ToArray());

        // Replaces each value with the count of strictly smaller values in the array.
        // E.g. [0,10,5,5,11] → [0,3,1,1,4].  (Non-dense ranking.)
        private static VertexType[] GetArrayRank(VertexType[] arr)
        {
            if (arr.Length < 2) return arr;
            var sortedByValue = arr.Select((v, i) => (v, i)).OrderBy(x => x.v).ToArray();
            int counter = 0;
            List<(VertexType rank, int original)> output = [(0, sortedByValue[0].i)];
            for (int i = 1; i < sortedByValue.Length; i++)
            {
                if (sortedByValue[i - 1].v != sortedByValue[i].v)
                    counter = i;
                output.Add(((VertexType)counter, sortedByValue[i].i));
            }
            return output.OrderBy(x => x.original).Select(x => x.rank).ToArray();
        }

        // Lean translation: a pure record threaded through all functions.
        // PathState holds only structural (edge-derived) information; vertex types are
        // passed separately and never cached inside path objects.
        private record PathState(PathsByLength[] PathsOfLength, int VertexCount);

        // Rank lookup tables produced by CalculatePathRankings.
        // Lean translation: returned as immutable values from a pure function.
        //   BetweenRanks[depth, fromVertex, toVertex] = rank of all depth-length paths between those vertices
        //   FromRanks[depth, fromVertex]               = rank of all depth-length paths from that vertex
        private record RankState(int[,,] BetweenRanks, int[,] FromRanks);

        // PathState is built once from edges alone; vertex types are never stored inside it.
        private static PathState InitializePaths(EdgeType[,] edges)
        {
            int n = edges.GetLength(0);
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
                                    edges[mid, to],
                                    pathsOfLength[depth - 1].pathsFromVertex[from].pathsToVertex[mid]);
                        }
                    }
                }
            }
            return new PathState(pathsOfLength, n);
        }

        // Dense ranking: ties in vertexRankings are broken by original index.
        // Lean: computeDenseRanks
        private static int[] ComputeDenseRanks(VertexType[] vertexRankings) =>
            vertexRankings
                .Select((v, i) => (v, i))
                .OrderBy(p => p)
                .Select((p, rank) => (rank, p.i))
                .OrderBy(x => x.i)
                .Select(x => x.rank)
                .ToArray();

        // Relabels the adjacency matrix so vertex positions match the given rankings.
        public static EdgeType[,] LabelEdgesAccordingToRankings(VertexType[] vertexRankings, EdgeType[,] edges)
        {
            int[] rankings = ComputeDenseRanks(vertexRankings);
            EdgeType[,] orderedEdges = (EdgeType[,])edges.Clone();
            for (int i = 0; i < rankings.Length; i++)
            {
                int j = Array.IndexOf(rankings, i);
                orderedEdges = SwapVertexLabelling(orderedEdges, i, j);
                (rankings[j], rankings[i]) = (rankings[i], rankings[j]);
            }
            return orderedEdges;
        }

        // Swaps rows and columns of v1 and v2 — an isomorphism-preserving relabelling.
        public static EdgeType[,] SwapVertexLabelling(EdgeType[,] edges, int v1, int v2)
        {
            if (v1 == v2)
                return (EdgeType[,])edges.Clone();
            int n = edges.GetLength(0);
            var result = new EdgeType[n, n];
            for (int x = 0; x < n; x++)
                for (int y = 0; y < n; y++)
                    result[x, y] = edges[
                        x == v1 ? v2 : x == v2 ? v1 : x,
                        y == v1 ? v2 : y == v2 ? v1 : y];
            return result;
        }

        public static string AdjMatrixToString(EdgeType[,] edges) =>
            string.Join("\n", Enumerable.Range(0, edges.GetLength(0)).Select(x =>
                string.Join(", ", Enumerable.Range(0, edges.GetLength(1)).Select(y =>
                    edges[x, y].ToString()))));

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

        // Promotes the second occurrence of `target` to `target+1`.
        // Two vertices tied after full convergence are symmetric; this arbitrarily distinguishes them.
        // Lean: breakTie
        private static (VertexType[] rankings, bool changed) BreakTie(VertexType[] vertexRankings, int target)
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

        // Rank = index of first element in each equivalence class.
        // E.g. sorted [a,a,b,c] → [(a,0),(a,0),(b,2),(c,3)]. Lean: assignRanks
        private static (T item, int rank)[] AssignRanks<T>(T[] sorted, Comparison<T> compare)
        {
            var result = new (T, int)[sorted.Length];
            int counter = 0;
            for (int i = 0; i < sorted.Length; i++)
            {
                if (i > 0 && compare(sorted[i - 1], sorted[i]) != 0)
                    counter = i;
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
            throw new Exception("Cannot compare BottomPathSegment with InnerPathSegment");
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
