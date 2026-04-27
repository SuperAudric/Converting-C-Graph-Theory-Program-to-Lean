using System;
using System.Collections.Generic;

// Cai–Furer–Immerman (CFI) graph generator — STUB.
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
//     n = 4 in the active suite; CFI pairs require n ≳ 10.
//   - Known-graph tests (`KnownGraphs_DifferentScramblings_ProduceSameCanonical`) cap at
//     n = 7. The smallest CFI pair derived from K_4 is n = 12.
//   - Random-graph tests sample dense Erdős–Rényi graphs; CFI graphs are sparse,
//     regular, and have local symmetry (gadget symmetry). They essentially never appear.
//
// Construction (reference, for the implementer)
// ---------------------------------------------
// Standard CFI construction over a base graph H:
//
//   1. Pick a base graph H = (V_H, E_H), connected, every vertex of degree ≥ 2.
//      (For sufficiency to defeat k-WL, choose H with treewidth ≥ k. The simplest
//      candidates: cycles defeat 1-WL; the 3×3 rook's graph or K_{3,3} defeat 2-WL;
//      higher-genus expanders defeat k-WL for larger k.)
//
//   2. For each base vertex v ∈ V_H of degree d, build a "gadget" X(v):
//        - 2^(d-1) "even-parity" auxiliary vertices a_S, one per S ⊆ N(v) with |S| even.
//        - For each base edge {v, w}, two "edge endpoints" e_{v,w}^0, e_{v,w}^1.
//        - Internal edges: a_S is connected to e_{v,w}^b iff (w ∈ S) XOR (b = 1).
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
//
// Status: STUB. Method bodies not yet implemented.

namespace Canonizer
{
    using EdgeType = Int32;

    public static class CfiGraphGenerator
    {
        /// <summary>
        /// A CFI pair: two non-isomorphic graphs that any k-WL with k below the base
        /// graph's treewidth fails to distinguish. The canonizer under test should
        /// produce *different* canonicals on these two graphs.
        /// </summary>
        public record CfiPair(
            EdgeType[,] Even,
            EdgeType[,] Odd,
            string BaseGraphName,
            int BaseTreewidth);

        // ── Primary entry points ────────────────────────────────────────────────

        /// <summary>
        /// Build a CFI pair from a named base graph. Use this from tests as the
        /// canonical "hard pair at WL-level k" generator.
        ///
        /// TODO: implement. Should dispatch on `baseGraph` to one of the BuildBase*
        /// helpers below, then call `BuildCfiPair(baseAdjacency)`.
        /// </summary>
        /// <param name="baseGraph">
        /// One of: "K4" (defeats 1-WL, smallest), "K33" (defeats 2-WL),
        /// "Rook3x3" (defeats 2-WL), "Petersen" (defeats 2-WL), or
        /// "Cycle{n}"/"Mobius{n}" for parameterized cases.
        /// </param>
        public static CfiPair Generate(string baseGraph)
            => throw new NotImplementedException("CFI generation not yet implemented.");

        /// <summary>
        /// General CFI construction: given any base adjacency matrix `H`, produce the
        /// untwisted/twisted CFI pair as described in steps 2–4 of the file header.
        ///
        /// TODO: implement. Steps:
        ///   (a) For each base vertex v with degree d_v, allocate 2^(d_v - 1) gadget
        ///       vertices for the even-parity subsets, plus 2 edge-endpoint vertices
        ///       per incident base edge.
        ///   (b) Wire intra-gadget edges per the parity rule.
        ///   (c) Wire inter-gadget edges untwisted everywhere (G_even), and again with
        ///       a single base edge twisted (G_odd).
        ///   (d) Return both as adjacency matrices over the flattened gadget-vertex
        ///       indexing. Vertex types should all be 0 (the canonizer will derive
        ///       structure from edges alone).
        ///
        /// The implementer should keep an explicit mapping
        ///   (baseVertex, gadgetRole) → flatIndex
        /// to make debugging output readable; see DescribePair below.
        /// </summary>
        public static CfiPair BuildCfiPair(EdgeType[,] baseAdjacency, string baseName, int baseTreewidth)
            => throw new NotImplementedException();

        // ── Base-graph factories ────────────────────────────────────────────────
        // Each returns a simple undirected adjacency matrix for the named base graph.
        // Implementations are short; kept separate so each can be sanity-checked
        // independently before being fed into BuildCfiPair.

        /// <summary>K_4: complete graph on 4 vertices. Treewidth 3. Use as the
        /// minimum-size sanity pair; resulting CFI pair has 12 vertices.</summary>
        public static EdgeType[,] BuildBaseK4()
            => throw new NotImplementedException();

        /// <summary>K_{3,3}: complete bipartite on 3+3. Treewidth 3.</summary>
        public static EdgeType[,] BuildBaseK33()
            => throw new NotImplementedException();

        /// <summary>3×3 rook's graph (= K_3 □ K_3, line graph of K_{3,3}). Treewidth 4.
        /// Classical 2-WL counterexample.</summary>
        public static EdgeType[,] BuildBaseRook3x3()
            => throw new NotImplementedException();

        /// <summary>Petersen graph. 3-regular, 10 vertices, girth 5. Treewidth 4.</summary>
        public static EdgeType[,] BuildBasePetersen()
            => throw new NotImplementedException();

        /// <summary>Cycle C_n. Treewidth 2 (defeats 1-WL when n ≥ 4 and even).</summary>
        public static EdgeType[,] BuildBaseCycle(int n)
            => throw new NotImplementedException();

        // ── Verification / diagnostic helpers ──────────────────────────────────

        /// <summary>
        /// Sanity check that the produced pair is genuinely a CFI pair: same number of
        /// vertices, same degree sequence, same number of edges, but not literally
        /// equal as adjacency matrices. If `Even` and `Odd` are equal, the construction
        /// has a bug and the test cannot conclude anything about the canonizer.
        ///
        /// TODO: implement. This catches generator bugs early so test failures of the
        /// canonizer can be trusted as canonizer failures, not generator artifacts.
        /// </summary>
        public static void AssertWellFormedPair(CfiPair pair)
            => throw new NotImplementedException();

        /// <summary>
        /// Independently certify that `pair.Even` and `pair.Odd` are *not* isomorphic.
        /// For small n this can be brute-forced over Sym_n; for larger n, defer to a
        /// trusted external canonizer (e.g. shell out to nauty/bliss) or rely on the
        /// CFI construction's published non-isomorphism proof.
        ///
        /// Without this guarantee, a "canonicals are equal" test result is ambiguous:
        /// it could mean the canonizer is incomplete, OR that we accidentally generated
        /// two isomorphic graphs.
        ///
        /// TODO: implement, at least for n ≤ ~12 via brute force.
        /// </summary>
        public static bool VerifyNonIsomorphic(CfiPair pair)
            => throw new NotImplementedException();

        /// <summary>
        /// Produce a human-readable diff of `Even` vs `Odd` highlighting the twisted
        /// edge. Useful when a test fails and you need to inspect the gadget that the
        /// canonizer collapsed.
        ///
        /// TODO: implement. Annotate each row/column with its (baseVertex, role).
        /// </summary>
        public static string DescribePair(CfiPair pair)
            => throw new NotImplementedException();

        // ── Suggested test entry point (to be written in GraphCannonTests.cs) ───
        //
        // [Theory]
        // [InlineData("K4")]
        // [InlineData("K33")]
        // [InlineData("Rook3x3")]
        // [InlineData("Petersen")]
        // public void CfiPair_ProducesDifferentCanonical(string baseName)
        // {
        //     var pair = CfiGraphGenerator.Generate(baseName);
        //     CfiGraphGenerator.AssertWellFormedPair(pair);
        //     Assert.True(CfiGraphGenerator.VerifyNonIsomorphic(pair),
        //         "Generator bug: produced isomorphic pair.");
        //
        //     var verts = new int[pair.Even.GetLength(0)];
        //     string evenCanon = new CanonGraphOrdererV4().Run(verts, pair.Even);
        //     string oddCanon  = new CanonGraphOrdererV4().Run(verts, pair.Odd);
        //
        //     Assert.NotEqual(evenCanon, oddCanon);
        //     // If this assertion fails: outcome 3 in OrbitCompleteAfterConv.md.
        //     // The pair is a falsifying counterexample and should be recorded.
        // }
    }
}
