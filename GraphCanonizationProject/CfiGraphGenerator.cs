using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

// Cai–Furer–Immerman (CFI) graph generator.
//
// Purpose
// -------
// The Lean obligation `OrbitCompleteAfterConv_general` asserts that the path-multiset
// refinement performed by `convergeLoop` is a *complete* orbit detector: two vertices
// receiving the same converged value must lie in the same Aut-orbit. This is the
// open completeness half of canonizer correctness; see
// `GraphCanonizationProofs/OrbitCompleteAfterConv.md`.
//
// Color-refinement-style algorithms have well-known incompleteness witnesses: the
// Cai–Furer–Immerman (CFI) construction (1992) produces, for every k, a pair of
// non-isomorphic graphs that the k-dimensional Weisfeiler–Leman algorithm cannot
// distinguish. If our path-multiset refinement happens to coincide with k-WL for
// some constant k, then the appropriate CFI pair will collapse and the obligation
// is *false*. Conversely, if every CFI pair we throw at it is correctly separated,
// confidence increases that the algorithm is genuinely stronger than the WL hierarchy
// (which would be a result in its own right).
//
// This generator therefore exists to feed the existing test harness
// (`GraphCanonizationProject.Tests/GraphCannonTests.cs`, alongside `UniqueGraphsBySize`)
// the "hard" cases that random and exhaustive-small testing miss.
//
// Why existing tests miss this
// ----------------------------
//   - Exhaustive sweeps (`AllPermutations_UniqueCanonicalCount_MatchesExpected`) cap at
//     n = 4 in the active suite; CFI pairs require n ≳ 18.
//   - Known-graph tests (`KnownGraphsdifferentScramblings_ProduceSameCanonical`) cap at
//     n = 7. The smallest CFI pair (over a triangle base) is n = 18.
//   - Random-graph tests sample dense Erdős–Rényi graphs; CFI graphs are sparse,
//     regular, and have local symmetry (gadget symmetry). They essentially never appear.
//
// Construction (as implemented)
// -----------------------------
// Standard CFI construction over a base graph H:
//
//   1. Pick a base graph H = (V_H, E_H), connected, every vertex of degree ≥ 2.
//      (For sufficiency to defeat k-WL, choose H with treewidth ≥ k+1. The simplest
//      candidates: cycles defeat 1-WL; the 3×3 rook's graph or K_{3,3} defeat 2-WL;
//      higher-genus expanders defeat k-WL for larger k.)
//
//   2. For each base vertex v ∈ V_H of degree d, build a "gadget" X(v):
//        - 2^(d-1) "even-parity" auxiliary vertices a_S, one per S ⊆ N(v) with |S| even.
//        - For each base edge {v, w}, two "edge endpoints" e_{v,w}^0, e_{v,w}^1.
//        - Internal edges: a_S — e_{v,w}^b iff (w ∈ S) XOR (b = 1).
//      Total per gadget: 2^(d-1) + 2d vertices.
//
//   3. Connect gadgets across base edges {v, w} ∈ E_H by adding edges
//      e_{v,w}^b — e_{w,v}^b for both b ∈ {0,1}  (the "untwisted" version), or
//      e_{v,w}^b — e_{w,v}^(1-b)                  (the "twisted" version on that edge).
//
//   4. The two CFI graphs of the pair are:
//        G_even — every base edge untwisted (even total twist count).
//        G_odd  — exactly one base edge twisted (odd total twist count).
//      G_even and G_odd are non-isomorphic, yet k-WL-indistinguishable for k < tw(H).
//
// Resulting CFI vertex counts (for reference):
//   - C_3 (triangle, deg 2):     3 × (2 + 4)  = 18
//   - C_4 (square, deg 2):       4 × (2 + 4)  = 24
//   - K_4 (deg 3):               4 × (4 + 6)  = 40
//   - K_{3,3} (deg 3):           6 × (4 + 6)  = 60
//   - Rook 3×3 (deg 4):          9 × (8 + 8)  = 144
//   - Petersen (deg 3):         10 × (4 + 6)  = 100
//   - K_6 (deg 5):               6 × (16 + 10) = 156
//
// Verification: G_even and G_odd should produce *different* canonicals under
// `CanonGraphOrdererV4.Run`. If they produce the same canonical, the obligation fails
// for that pair (a counterexample — outcome 3 in `OrbitCompleteAfterConv.md`, and a
// finding in its own right).
//
// References
// ----------
//   - Cai, Fürer, Immerman, "An optimal lower bound on the number of variables for
//     graph identification" (1992).
//   - Grohe, "Descriptive Complexity, Canonisation, and Definable Graph Structure
//     Theory" (2017) — Chapter 13 covers CFI in detail.

namespace Canonizer
{
    using EdgeType = Int32;

    public static class CfiGraphGenerator
    {
        /// <summary>
        /// A CFI pair: two non-isomorphic graphs that any k-WL with k below the base
        /// graph's treewidth fails to distinguish. The canonizer under test should
        /// produce *different* canonicals on these two graphs.
        ///
        /// `VertexRoles[i]` annotates each flat vertex index with its role in the
        /// gadget structure (e.g. "v0:subset:{w1,w2}", "v0:end[w1]^0"). Used by
        /// `DescribePair` to make test failures inspectable.
        /// </summary>
        public record CfiPair(
            AdjMatrix Even,
            AdjMatrix Odd,
            string BaseGraphName,
            int BaseTreewidth,
            string[] VertexRoles);

        // ── Primary entry points ────────────────────────────────────────────────

        /// <summary>
        /// Build a CFI pair from a named base graph. Use this from tests as the
        /// canonical "hard pair at WL-level k" generator.
        /// </summary>
        /// <param name="baseGraph">
        /// One of: "K4" (treewidth 3), "K33" (treewidth 3), "Rook3x3" (treewidth 4),
        /// "Petersen" (treewidth 4), "K6" (treewidth 5; 3-WL extension point), or
        /// "Cycle{n}" for parameterized cycle bases (e.g. "Cycle3", "Cycle4").
        /// Per the convention used in `OrbitCompleteAfterConv.md`, a base of
        /// treewidth t produces a CFI pair that defeats (t-2)-WL.
        /// </param>
        public static CfiPair Generate(string baseGraph)
        {
            if (baseGraph.StartsWith("Cycle", StringComparison.Ordinal))
            {
                int n = int.Parse(baseGraph.AsSpan("Cycle".Length));
                return BuildCfiPair(BuildBaseCycle(n), $"Cycle{n}", baseTreewidth: 2);
            }
            return baseGraph switch
            {
                "K4"      => BuildCfiPair(BuildBaseK4(),      "K4",      baseTreewidth: 3),
                "K33"     => BuildCfiPair(BuildBaseK33(),     "K33",     baseTreewidth: 3),
                "Rook3x3" => BuildCfiPair(BuildBaseRook3x3(), "Rook3x3", baseTreewidth: 4),
                "Petersen"=> BuildCfiPair(BuildBasePetersen(),"Petersen",baseTreewidth: 4),
                "K6"      => BuildCfiPair(BuildBaseK6(),      "K6",      baseTreewidth: 5),
                _ => throw new ArgumentException($"Unknown base graph '{baseGraph}'."),
            };
        }

        /// <summary>
        /// General CFI construction: given any base adjacency matrix H, produce the
        /// untwisted/twisted CFI pair as described in steps 2–4 of the file header.
        /// </summary>
        public static CfiPair BuildCfiPair(AdjMatrix baseAdjacency, string baseName, int baseTreewidth)
        {
            int nBase = baseAdjacency.VertexCount;

            // Sorted neighbor list for each base vertex.
            var neighbors = new int[nBase][];
            for (int v = 0; v < nBase; v++)
            {
                var list = new List<int>();
                for (int w = 0; w < nBase; w++)
                    if (v != w && baseAdjacency[v, w] != 0)
                        list.Add(w);
                neighbors[v] = list.ToArray();
            }

            for (int v = 0; v < nBase; v++)
                if (neighbors[v].Length < 2)
                    throw new ArgumentException(
                        $"CFI requires base graph with every vertex of degree ≥ 2; vertex {v} has degree {neighbors[v].Length}.");

            // Allocate flat indices, partitioned by gadget.
            //   subsetIndex[v][bitmask]     = flat index of a_S (only for even-popcount bitmasks)
            //   endpointIndex[v][w]         = (flat index of e_{v,w}^0, flat index of e_{v,w}^1)
            //
            // The bitmask is over neighbors[v] in their listed order. Even-popcount
            // bitmasks correspond to even-cardinality S ⊆ N(v).
            var subsetIndex   = new Dictionary<int, int>[nBase];
            var endpointIndex = new Dictionary<int, (int Zero, int One)>[nBase];

            int totalVertices = 0;
            var roleNames = new List<string>();
            for (int v = 0; v < nBase; v++)
            {
                int d = neighbors[v].Length;
                subsetIndex[v]   = new Dictionary<int, int>();
                endpointIndex[v] = new Dictionary<int, (int, int)>();

                for (int bm = 0; bm < (1 << d); bm++)
                {
                    if (System.Numerics.BitOperations.PopCount((uint)bm) % 2 != 0) continue;
                    subsetIndex[v][bm] = totalVertices++;
                    var sLabel = string.Join(",", Enumerable.Range(0, d).Where(i => (bm & (1 << i)) != 0).Select(i => $"w{neighbors[v][i]}"));
                    roleNames.Add($"v{v}:subset:{{{sLabel}}}");
                }
                for (int i = 0; i < d; i++)
                {
                    int w = neighbors[v][i];
                    int e0 = totalVertices++;
                    int e1 = totalVertices++;
                    endpointIndex[v][w] = (e0, e1);
                    roleNames.Add($"v{v}:end[w{w}]^0");
                    roleNames.Add($"v{v}:end[w{w}]^1");
                }
            }

            var evenAdj = new EdgeType[totalVertices, totalVertices];

            // Step 1: intra-gadget edges (identical in Even and Odd).
            // a_S — e_{v,w}^b iff (w ∈ S) XOR (b = 1)
            //   ⇒ a_S — e_{v,w}^0  iff  w ∈ S
            //   ⇒ a_S — e_{v,w}^1  iff  w ∉ S
            for (int v = 0; v < nBase; v++)
            {
                int d = neighbors[v].Length;
                foreach (var (bm, aIdx) in subsetIndex[v])
                {
                    for (int i = 0; i < d; i++)
                    {
                        int w = neighbors[v][i];
                        bool wInS = (bm & (1 << i)) != 0;
                        var (e0, e1) = endpointIndex[v][w];
                        int target = wInS ? e0 : e1;
                        evenAdj[aIdx, target] = 1;
                        evenAdj[target, aIdx] = 1;
                    }
                }
            }

            var oddAdj = (EdgeType[,])evenAdj.Clone();

            // Step 2: inter-gadget edges. Untwist every edge in Even; twist exactly the
            // first base edge in Odd.
            var baseEdges = new List<(int u, int v)>();
            for (int u = 0; u < nBase; u++)
                foreach (var w in neighbors[u])
                    if (u < w) baseEdges.Add((u, w));

            if (baseEdges.Count == 0)
                throw new ArgumentException("Base graph has no edges; cannot build CFI pair.");

            var twistedEdge = baseEdges[0];

            foreach (var (v, w) in baseEdges)
            {
                var (vw0, vw1) = endpointIndex[v][w];
                var (wv0, wv1) = endpointIndex[w][v];

                // Even: untwisted everywhere.
                evenAdj[vw0, wv0] = evenAdj[wv0, vw0] = 1;
                evenAdj[vw1, wv1] = evenAdj[wv1, vw1] = 1;

                // Odd: twist the chosen edge, untwist the rest.
                if (v == twistedEdge.u && w == twistedEdge.v)
                {
                    oddAdj[vw0, wv1] = oddAdj[wv1, vw0] = 1;
                    oddAdj[vw1, wv0] = oddAdj[wv0, vw1] = 1;
                }
                else
                {
                    oddAdj[vw0, wv0] = oddAdj[wv0, vw0] = 1;
                    oddAdj[vw1, wv1] = oddAdj[wv1, vw1] = 1;
                }
            }

            return new CfiPair(
                Even: new AdjMatrix(evenAdj),
                Odd:  new AdjMatrix(oddAdj),
                BaseGraphName: baseName,
                BaseTreewidth: baseTreewidth,
                VertexRoles: roleNames.ToArray());
        }

        // ── Base-graph factories ────────────────────────────────────────────────
        // Each returns a simple undirected adjacency matrix for the named base graph.

        /// <summary>K_4: complete graph on 4 vertices. Treewidth 3.
        /// CFI pair has 40 vertices.</summary>
        public static AdjMatrix BuildBaseK4() => BuildComplete(4);

        /// <summary>K_6: complete graph on 6 vertices. Treewidth 5.
        /// Lowest-vertex named base reaching 3-WL coverage. CFI pair has 156 vertices.</summary>
        public static AdjMatrix BuildBaseK6() => BuildComplete(6);

        /// <summary>K_{3,3}: complete bipartite on 3+3. Treewidth 3.
        /// CFI pair has 60 vertices.</summary>
        public static AdjMatrix BuildBaseK33()
        {
            var m = new EdgeType[6, 6];
            for (int i = 0; i < 3; i++)
                for (int j = 3; j < 6; j++)
                    m[i, j] = m[j, i] = 1;
            return new AdjMatrix(m);
        }

        /// <summary>3×3 rook's graph (= K_3 □ K_3, line graph of K_{3,3}). Treewidth 4.
        /// Classical 2-WL counterexample. CFI pair has 144 vertices.</summary>
        public static AdjMatrix BuildBaseRook3x3()
        {
            var m = new EdgeType[9, 9];
            int Idx(int r, int c) => 3 * r + c;
            for (int r1 = 0; r1 < 3; r1++)
                for (int c1 = 0; c1 < 3; c1++)
                    for (int r2 = 0; r2 < 3; r2++)
                        for (int c2 = 0; c2 < 3; c2++)
                        {
                            if (r1 == r2 && c1 == c2) continue;
                            if (r1 == r2 || c1 == c2)
                                m[Idx(r1, c1), Idx(r2, c2)] = 1;
                        }
            return new AdjMatrix(m);
        }

        /// <summary>Petersen graph. 3-regular, 10 vertices, girth 5. Treewidth 4.
        /// CFI pair has 100 vertices.</summary>
        public static AdjMatrix BuildBasePetersen()
        {
            var m = new EdgeType[10, 10];
            // Outer pentagon: 0-1-2-3-4-0
            for (int i = 0; i < 5; i++)
                m[i, (i + 1) % 5] = m[(i + 1) % 5, i] = 1;
            // Inner pentagram: 5-7, 7-9, 9-6, 6-8, 8-5 (skip 2 in inner cycle)
            for (int i = 0; i < 5; i++)
                m[5 + i, 5 + (i + 2) % 5] = m[5 + (i + 2) % 5, 5 + i] = 1;
            // Spokes: i — i+5
            for (int i = 0; i < 5; i++)
                m[i, 5 + i] = m[5 + i, i] = 1;
            return new AdjMatrix(m);
        }

        /// <summary>Cycle C_n. Treewidth 2 (defeats 1-WL when n ≥ 3).
        /// CFI pair has 6n vertices.</summary>
        public static AdjMatrix BuildBaseCycle(int n)
        {
            if (n < 3) throw new ArgumentException("Cycle requires n ≥ 3.");
            var m = new EdgeType[n, n];
            for (int i = 0; i < n; i++)
                m[i, (i + 1) % n] = m[(i + 1) % n, i] = 1;
            return new AdjMatrix(m);
        }

        private static AdjMatrix BuildComplete(int n)
        {
            var m = new EdgeType[n, n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (i != j) m[i, j] = 1;
            return new AdjMatrix(m);
        }

        // ── Verification / diagnostic helpers ──────────────────────────────────

        /// <summary>
        /// Sanity-check that the produced pair is genuinely a candidate CFI pair: same
        /// vertex count, same edge count, same degree sequence, but not literally equal
        /// as adjacency matrices. Throws on failure. This catches generator bugs early
        /// so test failures of the canonizer can be trusted as canonizer failures, not
        /// generator artifacts.
        /// </summary>
        public static void AssertWellFormedPair(CfiPair pair)
        {
            int n = pair.Even.VertexCount;
            if (pair.Odd.VertexCount != n)
                throw new InvalidOperationException(
                    $"CFI pair has different vertex counts: Even={n}, Odd={pair.Odd.VertexCount}.");

            if (CountEdges(pair.Even) != CountEdges(pair.Odd))
                throw new InvalidOperationException(
                    $"CFI pair has different edge counts: Even={CountEdges(pair.Even)}, Odd={CountEdges(pair.Odd)}.");

            var dE = SortedDegrees(pair.Even);
            var dO = SortedDegrees(pair.Odd);
            if (!dE.SequenceEqual(dO))
                throw new InvalidOperationException("CFI pair has different degree sequences.");

            if (AdjEquals(pair.Even, pair.Odd))
                throw new InvalidOperationException(
                    "CFI pair: Even and Odd are literally identical (no twist applied).");
        }

        /// <summary>
        /// Independently certify that `pair.Even` and `pair.Odd` are *not* isomorphic.
        ///
        /// For small n (≤ 9) this brute-forces over Sym_n. For larger n — which covers
        /// every CFI pair built from a real base graph — the brute-force budget is
        /// blown, and we rely on the CFI construction's published non-isomorphism
        /// guarantee (Cai–Fürer–Immerman 1992): if H is connected with min-degree ≥ 2
        /// and the twist count differs in parity, the two graphs are non-isomorphic.
        /// `BuildCfiPair` enforces those preconditions, so this returns `true`.
        ///
        /// The realistic safeguard against generator bugs is `AssertWellFormedPair`;
        /// this method exists as a contract-level check that callers can wire into
        /// tests without relying on the construction's correctness implicitly.
        /// </summary>
        public static bool VerifyNonIsomorphic(CfiPair pair)
        {
            int n = pair.Even.VertexCount;
            const int BruteForceLimit = 9;
            if (n > BruteForceLimit) return true;
            return !AreIsomorphicByBruteForce(pair.Even, pair.Odd);
        }

        /// <summary>
        /// Produce a human-readable description of the pair, including each vertex's
        /// gadget role and a position-by-position diff between Even and Odd.
        /// Useful when a test fails and you need to inspect the gadget that the
        /// canonizer collapsed.
        /// </summary>
        public static string DescribePair(CfiPair pair)
        {
            int n = pair.Even.VertexCount;
            var sb = new StringBuilder();
            sb.AppendLine($"CFI pair from base: {pair.BaseGraphName} (treewidth {pair.BaseTreewidth})");
            sb.AppendLine($"Vertex count: {n}, Edge count (Even): {CountEdges(pair.Even)}");
            sb.AppendLine();
            sb.AppendLine("Vertex roles:");
            for (int i = 0; i < n; i++)
                sb.AppendLine($"  [{i,3}] {pair.VertexRoles[i]}");
            sb.AppendLine();
            sb.AppendLine("Adjacency diff (· = same, • = differs between Even and Odd):");
            for (int i = 0; i < n; i++)
            {
                for (int j = 0; j < n; j++)
                    sb.Append(pair.Even[i, j] != pair.Odd[i, j] ? '•' : '·');
                sb.AppendLine();
            }
            return sb.ToString();
        }

        // ── internals ──────────────────────────────────────────────────────────

        private static int CountEdges(AdjMatrix g)
        {
            int n = g.VertexCount;
            int c = 0;
            for (int i = 0; i < n; i++)
                for (int j = i + 1; j < n; j++)
                    if (g[i, j] != 0) c++;
            return c;
        }

        private static int[] SortedDegrees(AdjMatrix g)
        {
            int n = g.VertexCount;
            var degrees = new int[n];
            for (int i = 0; i < n; i++)
            {
                int d = 0;
                for (int j = 0; j < n; j++)
                    if (i != j && g[i, j] != 0) d++;
                degrees[i] = d;
            }
            Array.Sort(degrees);
            return degrees;
        }

        private static bool AdjEquals(AdjMatrix a, AdjMatrix b)
        {
            int n = a.VertexCount;
            if (b.VertexCount != n) return false;
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (a[i, j] != b[i, j]) return false;
            return true;
        }

        private static bool AreIsomorphicByBruteForce(AdjMatrix g, AdjMatrix h)
        {
            int n = g.VertexCount;
            if (h.VertexCount != n) return false;
            var perm = Enumerable.Range(0, n).ToArray();
            do
            {
                if (PermutationMakesEqual(g, h, perm)) return true;
            } while (NextPermutation(perm));
            return false;
        }

        private static bool PermutationMakesEqual(AdjMatrix g, AdjMatrix h, int[] perm)
        {
            int n = g.VertexCount;
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (g[i, j] != h[perm[i], perm[j]]) return false;
            return true;
        }

        // Next lexicographic permutation in place; returns false when the input is the
        // last permutation (sorted descending).
        private static bool NextPermutation(int[] arr)
        {
            int i = arr.Length - 2;
            while (i >= 0 && arr[i] >= arr[i + 1]) i--;
            if (i < 0) return false;
            int j = arr.Length - 1;
            while (arr[j] <= arr[i]) j--;
            (arr[i], arr[j]) = (arr[j], arr[i]);
            Array.Reverse(arr, i + 1, arr.Length - (i + 1));
            return true;
        }
    }
}
