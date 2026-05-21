using System;
using System.Numerics;

namespace Canonizer
{
    // How a chain-descent flag is classified (docs/chain-descent-overview.md
    // §9 gap 9). The flagged region is larger than Tier 2; the order of the
    // automorphism group harvested before the budget ran out tells the two
    // flag causes apart.
    public enum FlagKind
    {
        // The run produced a canonical form — not a flag.
        None,

        // Flagged with a non-trivial harvested automorphism group: a genuine
        // symmetry the cascade oracle could not consume. Covers the abelian
        // CFI case (which the deferred linear oracle, §7, will absorb) as well
        // as the genuine non-abelian Tier-2 wall.
        Tier2Like,

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

        // The flag classification (§9 gap 9) — heuristic, read off
        // ResidualGroupOrder. Never None (an exception is always a flag).
        public FlagKind Kind =>
            ResidualGroupOrder.IsOne ? FlagKind.IrBlindSpot : FlagKind.Tier2Like;

        public CanonizationFlaggedException(string reason, BigInteger residualGroupOrder)
            : base($"Canonization flagged: {reason}")
        {
            Reason = reason;
            ResidualGroupOrder = residualGroupOrder;
        }
    }
}
