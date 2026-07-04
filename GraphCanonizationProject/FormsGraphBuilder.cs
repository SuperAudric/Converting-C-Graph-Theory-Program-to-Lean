using System;

namespace Canonizer
{
    // Route C — shared construction of a family's STANDARD (canonical) graph. Every node-4 family's
    // standard graph is a translation (Cayley) graph on (F_q)^dim whose connection set is the joint zero
    // of the family's standard forms. This factors that boilerplate out of each handler's StandardGraph,
    // so a per-family StandardGraph is: `StandardCayleyGraph(q, dim, diff => allStandardFormsVanish(diff))`.
    internal static class FormsGraphBuilder
    {
        // The Cayley graph on (F_q)^dim (natural vertex order, vertex 0 = zero) with u ~ v iff
        // `inConnectionSet(u - v)`. `inConnectionSet` receives the nonzero difference vector (mod q).
        public static int[] StandardCayleyGraph(int q, int dim, Func<int[], bool> inConnectionSet)
        {
            int n = IPow(q, dim);
            var vecs = new int[n][];
            for (int v = 0; v < n; v++) { var x = new int[dim]; int t = v; for (int i = 0; i < dim; i++) { x[i] = t % q; t /= q; } vecs[v] = x; }
            var adj = new int[n * n];
            var d = new int[dim];
            for (int u = 0; u < n; u++)
                for (int v = u + 1; v < n; v++)
                {
                    for (int i = 0; i < dim; i++) d[i] = ((vecs[u][i] - vecs[v][i]) % q + q) % q;
                    if (inConnectionSet(d)) { adj[u * n + v] = 1; adj[v * n + u] = 1; }
                }
            return adj;
        }

        static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }
    }
}
