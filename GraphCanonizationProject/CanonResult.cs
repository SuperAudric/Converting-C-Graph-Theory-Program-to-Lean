namespace Canonizer
{
    // Instrumentation gathered over a chain-descent run — the cost quantities
    // the polynomial argument reasons about (docs/chain-descent-strategy.md §8).
    internal sealed record DescentStats(
        long NodeCount,        // descent-tree nodes visited
        int MaxDepth,          // deepest individualisation path
        int LeafCount,         // discrete leaves reached
        int PrunedBranches,    // branches skipped by a-posteriori orbit pruning
        long Budget,           // the node budget this run carried
        int[] NodesByDepth,    // node count per depth — the cost shape: a flat
                               // all-ones profile is a single descent path
                               // (the Tier-1 ideal), a growing profile a
                               // fanning tree.
        // ── Phase-0 branch profile (recovery route T0: leaves ≤ B^L) ──────────
        // The poly-leaf-count target is leaves ≤ B^L with B = max branching
        // factor and L = max branching nodes on any root→leaf path. A branching
        // node explores b_i > 1 representatives AFTER a-posteriori harvest
        // pruning, so b_i = #Stab(path)-orbits in the selected cell (the open
        // content the recovery doc must bound by poly(q), uniformly in d).
        int MaxBranchFactor,   // B = max_i b_i (1 ⟺ a true single path)
        int MaxBranchPathDepth,// L = max branching nodes on a single path (exact,
                               // bottom-up; NOT the aggregate BranchingNodes)
        int[] BranchFactors,   // b_i at each branching node (the distribution)
        int[] BranchDepths,    // ... and its descent depth (parallel to BranchFactors)
        CascadeStats Cascade); // a-priori cascade/linear oracle harvest attribution

    // Harvest attribution from the a-priori cascade oracle
    // (docs/chain-descent-cascade-oracle.md). At each branching node the explored
    // representatives that REMAIN after a-priori harvesting are classified by the
    // footprint the harvest saw: all-singleton (linear oracle, depth 0), resolved
    // (the cascade recursion deepened to all-singleton), or starved (still
    // non-singleton past the depth bound). A clean cascade run drives
    // BranchingNodes → ~0 (leaves → O(beta)); residual branching attributed to
    // Starved is the genuine open content. MaxRecursionDepth tracks the single-
    // path deepening — it bottoms out near tw(H) on CFI (theorem_1_HOR_cfi_oddDeg),
    // far below the n depth bound.
    internal sealed record CascadeStats(
        long DecisionNodes,        // branch nodes reached (target cell had > 1 rep)
        long BranchingNodes,       // ... that still branched (> 1 rep explored)
        long BranchAllSingleton,   // branched with a depth-0 all-singleton footprint
        long BranchResolved,       // branched after the recursion reached all-singleton
        long BranchStarved,        // branched still non-singleton past the depth bound
        long GeneratorsHarvested,  // verified path-fixing automorphisms harvested
        long ResolvedByRecursion,  // harvest calls the recursion deepened (depth >= 1)
        int MaxRecursionDepth,     // deepest single-path recursion (~ tw(H) on CFI)
        // Deferred-decision scheduling (docs/chain-descent-deferred-decisions.md):
        long DeferralActiveNodes,  // nodes where deferral consumed a non-lowest-id
                                   // symmetric cell, deferring a lower-id real one
        long Phase2Nodes,          // nodes where every cell was a real decision —
                                   // the rigid residue is branched (Phase 2)
        long CachedRealSkips,      // harvests skipped because the cell was already
                                   // known-real (real-stays-real cache) — the oracle
                                   // work detached from the Phase-2 enumeration
        // ── Resolution-mechanism histogram (Route A — how single-path cells resolve) ──
        // Footprint class of every ClassifyCell harvest (NOT just branching nodes —
        // these tally the symmetric-consumption path the single-path descent takes).
        long ClassifyClass1,       // all-singleton footprint at depth 0 (linear/forced)
        long ClassifyClass3,       // resolved by the cascade recursion (depth >= 1)
        long ClassifyStarved,      // class 2 — STARVED, harvest recovered nothing for
                                   // the anchor. The Route-A breaker: if this is ever
                                   // > 0 the existing harvest is NOT provably complete.
        long ConsumedSymmetric)    // cells consumed as a single orbit (single-path steps)
    {
        public static readonly CascadeStats Empty =
            new(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    }

    // The outcome of a chain-descent run (docs/chain-descent-strategy.md §4, §6):
    // either a canonical form, or a flag. A flag is produced when the run
    // exhausts the polynomial node budget — an honest "not handled", never a
    // wrong answer.
    internal sealed class CanonResult
    {
        public bool Flagged { get; private init; }

        // Canonical adjacency matrix, flat row-major; null when Flagged.
        public int[]? Matrix { get; private init; }

        // The residual automorphism group harvested during the descent. On a
        // flag its order tells the two flag causes apart: non-trivial ⇒ a
        // genuine Tier-2-like symmetry wall, trivial ⇒ an IR blind spot
        // (docs/chain-descent-strategy.md §15).
        public PermutationGroup ResidualGroup { get; private init; } = null!;

        public string? FlagReason { get; private init; }

        // Descent instrumentation.
        public DescentStats Stats { get; private init; } = null!;

        public static CanonResult Canonical(int[] matrix, PermutationGroup group, DescentStats stats)
            => new()
            {
                Flagged = false,
                Matrix = matrix,
                ResidualGroup = group,
                Stats = stats,
            };

        public static CanonResult Flag(string reason, PermutationGroup group, DescentStats stats)
            => new()
            {
                Flagged = true,
                FlagReason = reason,
                ResidualGroup = group,
                Stats = stats,
            };
    }
}
