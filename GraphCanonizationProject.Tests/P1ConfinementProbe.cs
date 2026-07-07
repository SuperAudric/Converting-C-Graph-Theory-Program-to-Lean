using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ─────────────────────────────────────────────────────────────────────────────
// P1 CONFINEMENT PROBE (2026-07-07) — step-1 de-risk of the confinement lemma
// (docs/chain-descent-route-c-plan.md §7c, sub-obligation P1).
//
// THE CLAIM UNDER TEST (P1 — the soundness linchpin of the assume-VT poly mechanism, §7b).
// The mechanism prunes a Phase-1 over-budget flag by ASSUMING vertex-transitivity (VT). That
// is sound ONLY if such a flag never lands on a NON-vertex-transitive residue. P1 says it
// cannot: a small-Aut residue harvests within the per-node budget (short base, O(log|Aut|)),
// so it NEVER flags; only large-Aut residues flag, and a large-Aut rank-3 residue is primitive
// ⟹ transitive ⟹ VT. The sharpest danger is therefore a SMALL-Aut, NON-Schurian, NON-VT SRG —
// locally as regular as a Cameron/node-4 family, yet not VT. If one of these FLAGS or STARVES in
// Phase 1, assume-VT would mis-prune it ⟹ a CORRECTNESS bug. P1 predicts instead: it resolves
// cheaply within budget, or its rigid decisions defer to Phase 2, and it produces NO Phase-1
// starve/flag.
//
// THE WITNESS. Chang graphs — SRG(28,12,6,4) obtained by Seidel-switching the triangular graph
// T(8)=J(8,2) with respect to a regular vertex set (a perfect matching, and the edges of an
// 8-cycle, of K8). They are the classic small-Aut NON-Schurian SRGs: |Aut| ∈ {96,360,384}, none
// divisible by 28 ⟹ NOT vertex-transitive; and T(8) is the unique rank-3 graph on these
// parameters ⟹ the Chang graphs are non-schurian. CONTROL = T(8) itself (VT, schurian, rank-3,
// |Aut|=8!=40320) — the "genuine node-4-like VT family" the mechanism is meant to KEEP.
// Faithfulness is self-checked: SRG(28,12,6,4) is asserted for every graph; non-transitivity is
// read off the harvested automorphism group's orbits (a subgroup of Aut ⟹ orbits ≥ Aut-orbits,
// so orbits>1 robustly certifies non-VT even if the harvest is incomplete).
//
// READINGS (per graph, default + deferral modes):
//   • Flagged? (budget-exhaustion flag)     — P1: NO for the Chang graphs.
//   • |Aut|, #orbits of the harvested group — small-Aut + NON-transitive (Chang) vs VT (T(8)).
//   • ClassifyStarved / BranchStarved       — the harvest-incompleteness breaker. P1: 0.
//   • Phase2Nodes / DeferralActiveNodes      — rigid decisions deferred to Phase 2 (obligation P2).
//   • NodeCount / LeafCount / MaxDepth       — resolves cheaply (short base ⟹ within budget).
//   • ISO-INVARIANCE  canon(G)==canon(πG)    — soundness anchor on a random relabel π.
public class P1ConfinementProbe
{
    private readonly ITestOutputHelper _out;
    public P1ConfinementProbe(ITestOutputHelper output) => _out = output;

    // ── graph builders ─────────────────────────────────────────────────────
    static (int[][] pairs, Dictionary<(int, int), int> idx) Pairs8()
    {
        var pairs = new List<int[]>();
        var idx = new Dictionary<(int, int), int>();
        for (int a = 0; a < 8; a++)
            for (int b = a + 1; b < 8; b++) { idx[(a, b)] = pairs.Count; pairs.Add(new[] { a, b }); }
        return (pairs.ToArray(), idx);
    }

    // T(8) = J(8,2): the 28 2-subsets of {0..7}, adjacent iff they meet in exactly one point.
    static int[] Triangular8(out int n)
    {
        var (pairs, _) = Pairs8(); n = pairs.Length; // 28
        var adj = new int[n * n];
        for (int u = 0; u < n; u++)
            for (int v = u + 1; v < n; v++)
            {
                int inter = ((pairs[u][0] == pairs[v][0] || pairs[u][0] == pairs[v][1]) ? 1 : 0)
                          + ((pairs[u][1] == pairs[v][0] || pairs[u][1] == pairs[v][1]) ? 1 : 0);
                if (inter == 1) { adj[u * n + v] = 1; adj[v * n + u] = 1; }
            }
        return adj;
    }

    // Seidel switch `adj` w.r.t. the vertex set S (mask): flip (u,v) iff exactly one endpoint ∈ S.
    static int[] SeidelSwitch(int[] adj, int n, bool[] inS)
    {
        var b = (int[])adj.Clone();
        for (int u = 0; u < n; u++)
            for (int v = u + 1; v < n; v++)
                if (inS[u] != inS[v]) { int f = 1 - b[u * n + v]; b[u * n + v] = f; b[v * n + u] = f; }
        return b;
    }

    static bool[] MaskFromPairs(Dictionary<(int, int), int> idx, int n, (int, int)[] ps)
    {
        var m = new bool[n];
        foreach (var p in ps) m[idx[p]] = true;
        return m;
    }

    // ── SRG(n,k,λ,μ) verification (faithfulness of the witness) ──────────────
    static (bool ok, string why) VerifySRG(int[] adj, int n, int k, int lam, int mu)
    {
        for (int u = 0; u < n; u++)
        {
            int deg = 0; for (int v = 0; v < n; v++) if (v != u) deg += adj[u * n + v];
            if (deg != k) return (false, $"deg[{u}]={deg}≠{k}");
        }
        for (int u = 0; u < n; u++)
            for (int v = u + 1; v < n; v++)
            {
                int common = 0;
                for (int w = 0; w < n; w++) if (w != u && w != v) common += adj[u * n + w] & adj[v * n + w];
                int want = adj[u * n + v] == 1 ? lam : mu;
                if (common != want) return (false, $"common[{u},{v}]={common}≠{want} (edge={adj[u * n + v]})");
            }
        return (true, $"SRG({n},{k},{lam},{mu})");
    }

    // ── canonize / orbit / relabel helpers ──────────────────────────────────
    static CanonResult Canon(int[] adj, int n, bool defer)
    {
        var d = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        { EnableLinearOracle = true, EnableDeferral = defer };
        return d.Canonize(new sbyte[n * n], new WarmPartition(n));
    }

    static (int orbits, int firstLen) OrbitProfile(PermutationGroup g, int n)
    {
        var seen = new bool[n]; int orbits = 0, first = -1;
        for (int i = 0; i < n; i++)
        {
            if (seen[i]) continue;
            var orb = g.Orbit(i);
            if (first < 0) first = orb.Length;
            orbits++;
            foreach (var x in orb) seen[x] = true;
        }
        return (orbits, first);
    }

    static int[] RandomPerm(int n, int seed)
    {
        var p = Enumerable.Range(0, n).ToArray();
        var r = new Random(seed);
        for (int i = n - 1; i > 0; i--) { int j = r.Next(i + 1); (p[i], p[j]) = (p[j], p[i]); }
        return p;
    }

    static int[] Relabel(int[] adj, int n, int[] pi)
    {
        var b = new int[n * n];
        for (int u = 0; u < n; u++)
            for (int v = 0; v < n; v++)
                b[pi[u] * n + pi[v]] = adj[u * n + v];
        return b;
    }

    void ReportGraph(string name, int[] adj, int n, bool expectVT)
    {
        _out.WriteLine($"── {name}  (n={n}) ──");
        var srg = VerifySRG(adj, n, 12, 6, 4);
        _out.WriteLine($"   SRG check: {(srg.ok ? "OK" : "FAIL")} — {srg.why}");
        Assert.True(srg.ok, $"{name}: {srg.why}");

        foreach (var defer in new[] { false, true })
        {
            var r = Canon(adj, n, defer);
            var c = r.Stats.Cascade;
            var (orbits, firstLen) = OrbitProfile(r.ResidualGroup, n);
            bool vt = orbits == 1 && firstLen == n;
            string tag = defer ? "deferral" : "default ";
            _out.WriteLine($"   [{tag}] {(r.Flagged ? "FLAG(" + r.FlagReason + ")" : "CANON")}  " +
                           $"|Aut|={r.ResidualGroup.Order}  orbits={orbits} (VT={vt})  |Aut|%n={r.ResidualGroup.Order % n}");
            _out.WriteLine($"        nodes={r.Stats.NodeCount} leaves={r.Stats.LeafCount} maxDepth={r.Stats.MaxDepth} " +
                           $"pruned={r.Stats.PrunedBranches} budget={r.Stats.Budget}");
            _out.WriteLine($"        branchingNodes={c.BranchingNodes} harvested={c.GeneratorsHarvested} resolvedByRec={c.ResolvedByRecursion}");
            _out.WriteLine($"        STARVE branch={c.BranchStarved} classify={c.ClassifyStarved}   " +
                           $"Phase2Nodes={c.Phase2Nodes} deferralActive={c.DeferralActiveNodes}");

            // Non-VT confirmation for the danger witnesses (harvested ≤ Aut ⟹ orbits ≥ Aut-orbits).
            if (!expectVT && !r.Flagged)
                Assert.True(orbits > 1, $"{name}: expected NON-vertex-transitive but harvested group is transitive");

            // ISO-INVARIANCE (soundness anchor): canon(G) == canon(π G).
            if (!r.Flagged)
            {
                var pi = RandomPerm(n, 12345 + (defer ? 1 : 0));
                var r2 = Canon(Relabel(adj, n, pi), n, defer);
                Assert.False(r2.Flagged, $"{name}: relabelled copy flagged while original canonized");
                Assert.True(r.Matrix!.SequenceEqual(r2.Matrix!),
                    $"{name}: canonical form NOT iso-invariant under relabelling — SOUNDNESS FAILURE");
                _out.WriteLine($"        iso-invariance: OK (canon(G)==canon(πG))");
            }

            // P1 verdict for the danger witnesses.
            if (!expectVT)
            {
                bool p1ok = !r.Flagged && c.ClassifyStarved == 0 && c.BranchStarved == 0;
                _out.WriteLine($"        P1 verdict [{tag}]: " +
                    (p1ok ? "SUPPORTED (non-VT small-Aut resolved; no flag; no Phase-1 starve)"
                          : "⚠ CHECK (flag or starve — inspect phase attribution)"));
            }
        }
        _out.WriteLine("");
    }

    [Fact]
    [Trait("Category", "LongRunning")]
    public void P1_SmallAutNonVT_DoesNotPhase1Flag()
    {
        _out.WriteLine("P1 CONFINEMENT PROBE — a small-Aut non-Schurian SRG must not Phase-1-flag (route-c-plan §7c, P1).");
        _out.WriteLine("Witnesses: Chang graphs SRG(28,12,6,4) [non-VT, non-schurian]; control T(8)=J(8,2) [VT, schurian].\n");

        var t8 = Triangular8(out int n);
        var (_, idx) = Pairs8();

        // Chang-A: switch T(8) w.r.t. a perfect matching of K8 (|S|=4 coclique; every outside vertex meets 2 of S).
        var changA = SeidelSwitch(t8, n, MaskFromPairs(idx, n, new (int, int)[] { (0, 1), (2, 3), (4, 5), (6, 7) }));
        // Chang-B: switch T(8) w.r.t. the edges of the 8-cycle 0-1-…-7-0 (|S|=8; every outside vertex meets 4 of S).
        var changB = SeidelSwitch(t8, n, MaskFromPairs(idx, n, new (int, int)[] { (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (0, 7) }));

        ReportGraph("T(8) control  [VT, schurian]", t8, n, expectVT: true);
        ReportGraph("Chang-A (perfect-matching switch)  [non-VT]", changA, n, expectVT: false);
        ReportGraph("Chang-B (8-cycle switch)  [non-VT]", changB, n, expectVT: false);

        // Confirm the switches produced genuine non-VT witnesses (non-isomorphic to the T(8) control).
        var cT = Canon(t8, n, false); var cA = Canon(changA, n, false); var cB = Canon(changB, n, false);
        if (!cT.Flagged && !cA.Flagged && !cB.Flagged)
        {
            bool niA = !cT.Matrix!.SequenceEqual(cA.Matrix!);
            bool niB = !cT.Matrix!.SequenceEqual(cB.Matrix!);
            bool niAB = !cA.Matrix!.SequenceEqual(cB.Matrix!);
            _out.WriteLine($"non-iso(T8,ChangA)={niA}  non-iso(T8,ChangB)={niB}  non-iso(ChangA,ChangB)={niAB}");
            Assert.True(niA, "Chang-A switch reproduced T(8) — no genuine non-VT witness");
            Assert.True(niB, "Chang-B switch reproduced T(8) — no genuine non-VT witness");
        }
    }
}
