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
        int MaxRecursionDepth)     // deepest single-path recursion (~ tw(H) on CFI)
    {
        public static readonly CascadeStats Empty = new(0, 0, 0, 0, 0, 0, 0, 0);
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
