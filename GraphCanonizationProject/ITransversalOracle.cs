using System.Collections.Generic;

namespace Canonizer
{
    // The transversal oracle — the chain-descent design's T-C seam
    // (docs/chain-descent-simplified-overview.md §4.1). At a branch node the harness must
    // decide which target-cell vertices to descend into; the oracle returns
    // that representative list.
    //
    // Soundness contract: the representatives MUST cover every orbit of the
    // target cell. Over-splitting (more than one representative per orbit) is
    // sound — it only costs extra branches. Under-merging (dropping an orbit)
    // is not — it can skip the true lexicographic minimum.
    //
    // Phase 1 ships only CascadeOracle, which certifies nothing a priori and
    // returns the whole cell; the harness then prunes a posteriori from the
    // automorphisms it harvests. The deferred LinearOracle (§7) will be a
    // second implementation that returns a certified, much shorter list.
    internal interface ITransversalOracle
    {
        TransversalDecision Classify(
            int n,
            int[] adj,
            IReadOnlyList<int> targetCell,
            IReadOnlyList<int> path,
            PermutationGroup knownGroup);
    }

    // The oracle's verdict for one branch node: the vertices the harness should
    // descend into, in canonical (ascending) order.
    internal sealed class TransversalDecision
    {
        public IReadOnlyList<int> Representatives { get; }

        public TransversalDecision(IReadOnlyList<int> representatives)
        {
            Representatives = representatives;
        }
    }
}
