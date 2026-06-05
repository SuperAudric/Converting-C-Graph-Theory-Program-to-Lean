using System;
using System.Numerics;

namespace Canonizer
{
    // How a chain-descent flag is classified (docs/chain-descent-strategy.md
    // §15). The flagged region is larger than Tier 2; the order of the
    // automorphism group harvested before the budget ran out tells the two
    // flag causes apart.
    public enum FlagKind
    {
        // The run produced a canonical form — not a flag.
        None,

        // Flagged with a non-trivial, *non-abelian* harvested residual: the
        // genuine Tier-2 / Cameron-section candidate (docs/chain-descent-
        // exhaustive-obstruction.md §0.6: "non-trivial non-abelian ⟹ Cameron").
        // This is the only flag cause leg C must classify.
        Tier2Like,

        // Flagged with a non-trivial but *abelian* harvested residual: a hidden
        // abelian symmetry (a CFI gauge Z_2^d over an unbounded-treewidth base,
        // the §2 gap-(B) region) the harvest did not consume within budget. It is
        // NOT a Cameron section — a complete linear / cross-branch harvest absorbs
        // it. Splitting this out of Tier2Like is the "F2" correction
        // (docs/chain-descent-exhaustive-obstruction.md §0.6): the operational
        // flag signal must test abelian-ness, not just order, before routing to
        // leg C.
        AbelianUnconsumed,

        // Flagged with a trivial harvested group: an IR blind spot — a rigid,
        // refinement-resistant graph (the multipede family). Hard for the
        // individualization-refinement method, though not for graph
        // isomorphism in general.
        IrBlindSpot,
    }

    // Thrown by the chain-descent canonizer when a run exceeds the polynomial
    // node budget without producing a canonical form. A flag is an honest
    // "not handled within the budget" — it is never a wrong answer.
    public sealed class CanonizationFlaggedException : Exception
    {
        public string Reason { get; }

        // Order of the automorphism group harvested before the budget ran out.
        public BigInteger ResidualGroupOrder { get; }

        // The flag classification (docs/chain-descent-strategy.md §15,
        // docs/chain-descent-exhaustive-obstruction.md §0.6). Computed from the
        // harvested residual group at throw time — order AND abelian-ness — never
        // None (an exception is always a flag).
        public FlagKind Kind { get; }

        public CanonizationFlaggedException(string reason, PermutationGroup residual)
            : base($"Canonization flagged: {reason}")
        {
            Reason = reason;
            ResidualGroupOrder = residual.Order;
            Kind = ClassifyFlag(residual);
        }

        // Classify a flag by its harvested residual group. The trichotomy mirrors
        // the seal's two flag causes refined by F2: trivial residual ⟹ IR blind
        // spot (no symmetry — multipede); non-trivial abelian ⟹ an unconsumed
        // abelian symmetry (CFI gauge, not Cameron); non-trivial non-abelian ⟹
        // the Tier-2 / Cameron-section candidate. Order alone cannot separate the
        // middle two — testing abelian-ness is exactly the F2 fix.
        public static FlagKind ClassifyFlag(PermutationGroup residual) =>
            residual.IsTrivial ? FlagKind.IrBlindSpot
            : residual.IsAbelian ? FlagKind.AbelianUnconsumed
            : FlagKind.Tier2Like;
    }
}
