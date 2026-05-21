namespace Canonizer
{
    // The outcome of a chain-descent run (docs/chain-descent-design.md §4):
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
        // genuine Tier-2 symmetry wall, trivial ⇒ an IR blind spot (§9 gap 9).
        public PermutationGroup ResidualGroup { get; private init; } = null!;

        public string? FlagReason { get; private init; }

        // Instrumentation — the proof's cost quantities (§6).
        public long NodeCount { get; private init; }
        public int MaxDepth { get; private init; }
        public int LeafCount { get; private init; }
        public int PrunedBranches { get; private init; }

        public static CanonResult Canonical(int[] matrix, PermutationGroup group,
                                             long nodeCount, int maxDepth,
                                             int leafCount, int prunedBranches)
            => new()
            {
                Flagged = false,
                Matrix = matrix,
                ResidualGroup = group,
                NodeCount = nodeCount,
                MaxDepth = maxDepth,
                LeafCount = leafCount,
                PrunedBranches = prunedBranches,
            };

        public static CanonResult Flag(string reason, PermutationGroup group,
                                        long nodeCount, int maxDepth,
                                        int leafCount, int prunedBranches)
            => new()
            {
                Flagged = true,
                FlagReason = reason,
                ResidualGroup = group,
                NodeCount = nodeCount,
                MaxDepth = maxDepth,
                LeafCount = leafCount,
                PrunedBranches = prunedBranches,
            };
    }
}
