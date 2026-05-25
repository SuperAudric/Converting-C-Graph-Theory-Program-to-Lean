using System;
using System.Linq;

namespace Canonizer
{
    using EdgeType = int;

    // Lean translation: structure AdjMatrix (vertexCount : Nat) where adj : Fin vc → Fin vc → EdgeType.
    // Wraps a square EdgeType[,] and exposes a read-only indexer plus the immutable
    // SwapVertexLabels and ToString operations. Construction clones the input so
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
}
