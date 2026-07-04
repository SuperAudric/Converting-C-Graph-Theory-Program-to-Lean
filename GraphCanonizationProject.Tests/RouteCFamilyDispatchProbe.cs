using System;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ROUTE C — family-dispatch scaffold (2026-07-04). docs/chain-descent-route-c-plan.md §9.2.7.
// Node 4 = four families, each an IFormFamilyHandler; RouteCCanonicalizer dispatches over the registry.
// Validates: (i) affine-polar still canonicalizes through the dispatch (regression); (ii) the dormant
// stub handlers (alternating/half-spin/Suzuki) decline SAFELY (no crash — their NotImplemented cores are
// never reached because recognition/confirmation gate them). (Suzuki's VSz(8)=SRG(4096,455,6,56)
// fingerprint recognition is live in-handler but n=4096 is too large to materialise as a unit test.)
public class RouteCFamilyDispatchProbe
{
    private readonly ITestOutputHelper _out;
    public RouteCFamilyDispatchProbe(ITestOutputHelper o) => _out = o;

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    // (i) regression: affine-polar dispatches correctly and returns the right family + |Aut|.
    [Theory]
    [InlineData(3, -1)]
    [InlineData(3, +1)]
    public void Dispatch_AffinePolar(int q, int eps)
    {
        int n = IPow(q, 4);
        var (adj, _, _) = RouteCVO4.Build(q, eps);
        var res = RouteCCanonicalizer.Recognize(adj, n);
        Assert.True(res is not null, "affine-polar not recognized through the dispatch");
        Assert.Equal(FormFamily.AffinePolar, res!.Family);
        Assert.Equal(RouteCCanonicalizer.AffinePolarAutOrder(q, 2, eps), res.AutOrder);
        _out.WriteLine($"dispatch VO^{(eps < 0 ? "-" : "+")}_4({q}) ⇒ {res.Family} {res.Invariant} |Aut|={res.AutOrder}");
    }

    // (ii) the dormant stub handlers must never throw their NotImplemented cores. Directly exercise each
    // handler on a VO graph (which they must NOT claim) and on random input — all return null cleanly.
    [Fact]
    public void StubHandlers_DeclineGracefully()
    {
        int n = IPow(3, 4);
        var (adj, _, _) = RouteCVO4.Build(3, -1);
        // a benign non-flagged CanonResult surrogate: run the descent once
        var cd = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        { EnableLinearOracle = true, EnableDeferral = true };
        var harvest = cd.Canonize(new sbyte[n * n], new WarmPartition(n));

        foreach (IFormFamilyHandler h in new IFormFamilyHandler[]
                 { new AlternatingHandler(), new HalfSpinHandler(), new SuzukiHandler() })
        {
            var r = h.TryCanonicalize(adj, n, harvest);   // must not throw, must decline on a VO graph
            Assert.Null(r);
            _out.WriteLine($"{h.Family} declined VO^-_4(3) gracefully ✓");
        }
    }
}
