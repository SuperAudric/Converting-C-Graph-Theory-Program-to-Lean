using System.Collections.Generic;
using System.Linq;

namespace Canonizer
{
    // Phase-1 transversal oracle (docs/chain-descent-design.md §6, §9 gap 6).
    //
    // It certifies nothing a priori: Classify returns every vertex of the
    // target cell, in ascending order. The actual orbit pruning is the
    // harness's a-posteriori mechanism — ChainDescent skips a candidate once a
    // harvested, verified automorphism shows it redundant. Together, harness
    // search + this oracle are the doc's "cascade oracle": they finish within
    // the node budget exactly on graphs that cascade, and flag otherwise.
    //
    // The non-trivial a-priori oracle — discovering twists from propagation
    // patterns — is the deferred LinearOracle (§7).
    internal sealed class CascadeOracle : ITransversalOracle
    {
        public TransversalDecision Classify(
            int n,
            int[] adj,
            IReadOnlyList<int> targetCell,
            IReadOnlyList<int> path,
            PermutationGroup knownGroup)
        {
            var reps = targetCell.OrderBy(v => v).ToArray();
            return new TransversalDecision(reps);
        }
    }
}
