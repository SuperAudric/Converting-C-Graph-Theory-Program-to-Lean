using System.Collections.Generic;

namespace Canonizer
{
    // M3 — candidate twist construction for the linear oracle
    // (docs/chain-descent-linear-oracle.md §4.2).
    //
    // Given the refinement footprint of an explored representative r₁ and the
    // refined partition of an unexplored representative rⱼ, construct the
    // candidate path-fixing automorphism t : V → V carrying r₁ ↦ rⱼ.
    //
    // The construction is **canonical-colour matching**. If branch-r₁ and
    // branch-rⱼ are isomorphic via t, the 1-WL fixpoint assigns *identical*
    // canonical colour ids to t-corresponding vertices (the id is the signature's
    // rank in the global sorted set, an iso-invariant). So on the coupled
    // component K, t maps branch-r₁'s colour-c vertex to branch-rⱼ's colour-c
    // vertex; off K it is the identity. For CFI this is the gadget-parity flip.
    //
    // Scope (docs/chain-descent-extended-twist-viability.md): only the
    // **all-singletons** footprint is handled — there each footprint colour is
    // unique, so the match is a forced bijection and is iso-invariant. A
    // non-singleton sub-cell is refinement-indistinguishable, so no iso-invariant
    // within-cell match exists; those return `null` and the descent recurses
    // (the normal k-way branch). Correctness of any returned t is *not* assumed
    // here — it is established by the caller's edge-by-edge IsAutomorphism check
    // (§4.5). This routine only proposes; verification disposes.
    internal static class TwistConstruction
    {
        // Returns the candidate permutation, or null when the footprint is not
        // all-singletons or the two branches' footprint colours do not match up
        // into a bijection (⇒ the branches are not isomorphic this way; the
        // caller falls back). A returned array is always a permutation of
        // {0..n-1}; whether it is an automorphism is the caller's verify step.
        public static int[]? TryConstruct(
            int n, RefinementFootprint footprint1, int[] branch1CellOf, int[] branchJCellOf)
        {
            // Forced-matching gate: every coupled sub-cell must be a singleton.
            foreach (var sc in footprint1.SplitCells)
                if (!sc.AllSingletons) return null;

            int[] coupled = footprint1.CoupledVertices();
            if (coupled.Length == 0) return null;

            // colour → vertex on K, for branch-rⱼ. All-singletons ⇒ each colour
            // occurs once; a collision means rⱼ's footprint is shaped
            // differently (not the mirror) ⇒ no candidate.
            var byColourJ = new Dictionary<int, int>(coupled.Length);
            foreach (int v in coupled)
                if (!byColourJ.TryAdd(branchJCellOf[v], v)) return null;

            var t = Perm.Identity(n); // identity off the coupled component
            foreach (int v in coupled)
            {
                // match branch-r₁'s colour-c vertex to branch-rⱼ's colour-c vertex
                if (!byColourJ.TryGetValue(branch1CellOf[v], out int image)) return null;
                t[v] = image;
            }

            // A well-formed match is a bijection; reject anything else outright
            // (e.g. two K-vertices sharing a branch-r₁ colour — not all-singletons
            // within K — would collide here).
            return Perm.IsPermutation(t) ? t : null;
        }
    }
}
