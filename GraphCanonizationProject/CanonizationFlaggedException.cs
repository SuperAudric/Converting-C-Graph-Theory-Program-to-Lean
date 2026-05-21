using System;
using System.Numerics;

namespace Canonizer
{
    // Thrown by the chain-descent canonizer when a run exceeds the polynomial
    // node budget without producing a canonical form. A flag is an honest
    // "not handled within the budget" — it is never a wrong answer. See
    // docs/chain-descent-design.md §4.2 (the budget) and §9 gap 9 (the flagged
    // region: a genuine Tier-2 wall vs. an IR blind spot, told apart by
    // ResidualGroupOrder — non-trivial ⇒ Tier-2-like, trivial ⇒ IR blind spot).
    public sealed class CanonizationFlaggedException : Exception
    {
        public string Reason { get; }

        // Order of the automorphism group harvested before the budget ran out.
        public BigInteger ResidualGroupOrder { get; }

        public CanonizationFlaggedException(string reason, BigInteger residualGroupOrder)
            : base($"Canonization flagged: {reason}")
        {
            Reason = reason;
            ResidualGroupOrder = residualGroupOrder;
        }
    }
}
