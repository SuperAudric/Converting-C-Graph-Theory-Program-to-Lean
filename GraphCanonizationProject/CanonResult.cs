namespace Canonizer
{
    // Instrumentation gathered over a chain-descent run — the cost quantities
    // the polynomial argument reasons about (docs/chain-descent-overview.md §6).
    internal sealed record DescentStats(
        long NodeCount,        // descent-tree nodes visited
        int MaxDepth,          // deepest individualisation path
        int LeafCount,         // discrete leaves reached
        int PrunedBranches,    // branches skipped by a-posteriori orbit pruning
        long Budget,           // the node budget this run carried
        int[] NodesByDepth);   // node count per depth — the cost shape: a flat
                               // all-ones profile is a single descent path
                               // (the Tier-1 ideal), a growing profile a
                               // fanning tree.

    // The outcome of a chain-descent run (docs/chain-descent-overview.md §4):
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
        // (docs/chain-descent-overview.md §9 gap 9).
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
