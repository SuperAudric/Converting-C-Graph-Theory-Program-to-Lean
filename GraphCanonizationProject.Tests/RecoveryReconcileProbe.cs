using System;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// RESIDUAL RECONCILIATION PROBE (2026-06-30).
//
// Goal: resolve the probe-vs-C# discrepancy at the heart of the recovery route.
//   - descent_probe.py run()  (greedy first-cell, true Stab(S)-orbit count) → 2-4 BRANCH nodes
//   - route #5 (the actual canonizer) reportedly → leaves=1, BranchingNodes=0, full |Aut|
// Those can't both be the whole story. This runs the REAL canonizer on VO^ε_4(q) and reads
// the ground-truth CascadeStats in BOTH modes:
//   DEFAULT  (EnableDeferral=false) — the canonical-form-preserving path that the Lean
//            spine substrate (spine_branch_independent) actually certifies.
//   DEFERRAL (EnableDeferral=true)  — the production recovery path (off by default; changes
//            the canonical form).
//
// The DECISIVE metric is BranchStarved / ClassifyStarved — CanonResult.cs documents it as
// "the Route-A breaker: if this is ever > 0 the existing harvest is NOT provably complete."
// That is the exact C# counterpart of the seal's open RelCountsDetermineOrbit / hFormCert.
// If starved == 0 on this family, the existing harvest is empirically complete (recovery
// route works for VO^ε_4(q)); if > 0, the residue is precisely what the recovery core must
// handle. BranchingNodes>0 with starved==0 means "branches but resolves" (reconciles the
// Python: the cell IS multi-orbit, but the harvest recovers the auts — no flag, |Aut| full).
public class RecoveryReconcileProbe
{
    private readonly ITestOutputHelper _out;
    public RecoveryReconcileProbe(ITestOutputHelper output) => _out = output;

    static int IPow(int b, int e) { int r = 1; for (int i = 0; i < e; i++) r *= b; return r; }

    // VO^ε_4(q) adjacency as a flat int[n*n], q PRIME (mod-q arithmetic).
    // Replicates A2MonovariantProbe.AffinePolar(q, m=2, eps): x~y iff Q(x-y)=0, x≠y.
    static int[] AffinePolar4(int q, int eps)
    {
        int m = 2, dim = 4, n = IPow(q, dim);
        int bb = 0, cc = 0;
        if (eps == -1) // anisotropic binary tail y²+b·yz+c·z² (zero only at 0)
        {
            bool found = false;
            for (int b = 0; b < q && !found; b++)
                for (int c = 0; c < q && !found; c++)
                {
                    bool aniso = true;
                    for (int y = 0; y < q && aniso; y++)
                        for (int z = 0; z < q; z++)
                        {
                            if (y == 0 && z == 0) continue;
                            int g = ((y * y + b * y % q * z) % q + c * (z * z % q)) % q;
                            if (g % q == 0) { aniso = false; break; }
                        }
                    if (aniso) { bb = b; cc = c; found = true; }
                }
            if (!found) throw new Exception($"no anisotropic binary form over GF({q})");
        }
        int[] Vec(int v) { var x = new int[dim]; for (int i = 0; i < dim; i++) { x[i] = v % q; v /= q; } return x; }
        int Q(int[] x)
        {
            int s = 0, hyp = eps == -1 ? m - 1 : m;
            for (int i = 0; i < hyp; i++) s = (s + x[2 * i] * x[2 * i + 1]) % q;
            if (eps == -1)
            {
                int y = x[2 * (m - 1)], z = x[2 * (m - 1) + 1];
                s = (s + (y * y + bb * y % q * z) % q + cc * (z * z % q)) % q;
            }
            return ((s % q) + q) % q;
        }
        var vecs = new int[n][]; for (int v = 0; v < n; v++) vecs[v] = Vec(v);
        var adj = new int[n * n];
        var d = new int[dim];
        for (int u = 0; u < n; u++)
            for (int v = u + 1; v < n; v++)
            {
                for (int i = 0; i < dim; i++) d[i] = ((vecs[u][i] - vecs[v][i]) % q + q) % q;
                if (Q(d) == 0) { adj[u * n + v] = 1; adj[v * n + u] = 1; }
            }
        return adj;
    }

    static void Report(ITestOutputHelper o, string tag, CanonResult r)
    {
        var c = r.Stats.Cascade;
        o.WriteLine($"  [{tag}] {(r.Flagged ? "FLAG (" + r.FlagReason + ")" : "CANON")}  " +
                    $"leaves={r.Stats.LeafCount} nodes={r.Stats.NodeCount} pruned={r.Stats.PrunedBranches} |Aut|={r.ResidualGroup.Order}");
        // ── Phase-0 branch profile (T0: leaves ≤ B^L) ────────────────────────
        // B = MaxBranchFactor (≤ poly(q)?), L = MaxBranchPathDepth (= O(d)?).
        // The decisive pair: if B stays ≤ q-ish and L stays ~d as (q,d) grow,
        // leaves = B^L = q^{O(d)} = poly(n) and T0 holds; if B grows super-poly
        // in q or L super-linearly in d, T0 fails on this family.
        string bf = r.Stats.BranchFactors.Length == 0 ? "[]"
            : "[" + string.Join(",", System.Linq.Enumerable.Zip(
                r.Stats.BranchFactors, r.Stats.BranchDepths, (b, d) => $"{b}@d{d}")) + "]";
        o.WriteLine($"        PHASE0  B(maxBranchFactor)={r.Stats.MaxBranchFactor} " +
                    $"L(maxBranchPathDepth)={r.Stats.MaxBranchPathDepth} maxDepth={r.Stats.MaxDepth} " +
                    $"branchFactors={bf}");
        o.WriteLine($"        nodesByDepth=[{string.Join(",", r.Stats.NodesByDepth)}]");
        o.WriteLine($"        decisionNodes={c.DecisionNodes} branchingNodes={c.BranchingNodes} " +
                    $"harvested={c.GeneratorsHarvested} resolvedByRec={c.ResolvedByRecursion} maxRecDepth={c.MaxRecursionDepth}");
        o.WriteLine($"        branch[allSingleton]={c.BranchAllSingleton} branch[resolved]={c.BranchResolved} " +
                    $"branch[STARVED]={c.BranchStarved}");
        o.WriteLine($"        classify[class1]={c.ClassifyClass1} classify[class3]={c.ClassifyClass3} " +
                    $"classify[STARVED]={c.ClassifyStarved} consumedSymmetric={c.ConsumedSymmetric}");
        o.WriteLine($"        deferralActiveNodes={c.DeferralActiveNodes} phase2Nodes={c.Phase2Nodes}");
    }

    // VO^ε_{2m}(q) adjacency, general even dim = 2m, q PRIME. Same Q as AffinePolar4.
    static int[] AffinePolar(int q, int m, int eps)
    {
        int dim = 2 * m, n = IPow(q, dim);
        int bb = 0, cc = 0;
        if (eps == -1)
        {
            bool found = false;
            for (int b = 0; b < q && !found; b++)
                for (int c = 0; c < q && !found; c++)
                {
                    bool aniso = true;
                    for (int y = 0; y < q && aniso; y++)
                        for (int z = 0; z < q; z++)
                        {
                            if (y == 0 && z == 0) continue;
                            int g = ((y * y + b * y % q * z) % q + c * (z * z % q)) % q;
                            if (g % q == 0) { aniso = false; break; }
                        }
                    if (aniso) { bb = b; cc = c; found = true; }
                }
            if (!found) throw new Exception($"no anisotropic binary form over GF({q})");
        }
        int[] Vec(int v) { var x = new int[dim]; for (int i = 0; i < dim; i++) { x[i] = v % q; v /= q; } return x; }
        int Q(int[] x)
        {
            int s = 0, hyp = eps == -1 ? m - 1 : m;
            for (int i = 0; i < hyp; i++) s = (s + x[2 * i] * x[2 * i + 1]) % q;
            if (eps == -1)
            {
                int y = x[2 * (m - 1)], z = x[2 * (m - 1) + 1];
                s = (s + (y * y + bb * y % q * z) % q + cc * (z * z % q)) % q;
            }
            return ((s % q) + q) % q;
        }
        var vecs = new int[n][]; for (int v = 0; v < n; v++) vecs[v] = Vec(v);
        var adj = new int[n * n];
        var d = new int[dim];
        for (int u = 0; u < n; u++)
            for (int v = u + 1; v < n; v++)
            {
                for (int i = 0; i < dim; i++) d[i] = ((vecs[u][i] - vecs[v][i]) % q + q) % q;
                if (Q(d) == 0) { adj[u * n + v] = 1; adj[v * n + u] = 1; }
            }
        return adj;
    }

    // d-SCALING: the open question is the UNBOUNDED-d residue. Does STARVED stay 0 as d grows?
    // Deferral-only (single-path mode, fewest nodes). n=2401 (VO^-_4(7)) was dropped — infeasible
    // wall-clock; VO^-_6(3) n=729 is the real d=6-vs-d=4 signal. Re-add larger cases only if STARVED
    // appears at d=6 (then the residue is genuine and worth the cost).
    [Theory]
    [Trait("Category", "LongRunning")]
    [InlineData(3, 3, -1)] // VO^-_6(3) n=729
    public void Reconcile_dScaling(int q, int m, int eps)
    {
        int n = IPow(q, 2 * m);
        var adj = AffinePolar(q, m, eps);
        string nm = $"VO^{(eps < 0 ? "-" : "+")}_{2 * m}({q}) n={n}";
        _out.WriteLine(nm);
        var dDefer = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        {
            EnableLinearOracle = true,
            EnableDeferral = true
        };
        Report(_out, "deferral", dDefer.Canonize(new sbyte[n * n], new WarmPartition(n)));
    }

    // PHASE 0 — the T0 GATE. leaves ≤ B^L with B = max branching factor,
    // L = max branching nodes on a root→leaf path. T0 (poly leaf count) holds iff
    // B ≤ poly(q) uniformly in d AND L = O(d); then B^L = q^{O(d)} = poly(n).
    // This sweep reads B and L (now reported by Report) in DEFAULT (branch-but-
    // resolve) mode — the canonical-form-preserving path the Lean spine certifies,
    // and the only mode where the poly-leaf-count target is non-trivial.
    //   • q-SWEEP at fixed d=4 (m=2): is B bounded, or does it grow with q? This is
    //     the under-measured axis — model_gap.py shows the cell/orbit gap grows
    //     with q, so B vs q is the open question §4's "b_i ≤ q" heuristic asserts.
    //   • d-SWEEP at fixed q=2 (m=2,3,4 ⟹ d=4,6,8, n=16,64,256): does leaves stay
    //     poly and L track d (≈ the Θ(d) group base), or does either blow up?
    // Deferral mode is reported alongside for the single-path (leaves=1) baseline.
    // FEASIBILITY (measured 2026-06-30): default (no-deferral) mode at large n is
    // SLOW — VO^-_4(3) n=81 is instant and single-path (B=1), but VO^-_4(5) n=625
    // default mode runs for many minutes (the per-node harvest cost at large n, not
    // the tree). So read the B/L scaling from the small/feasible cells (q=2,3 and the
    // q=2 d-sweep n=16,64,256); for q≥5 prefer the deferral-mode line or budget time.
    [Theory]
    [Trait("Category", "LongRunning")]
    // q-sweep, fixed d=4
    [InlineData(2, 2, -1)]
    [InlineData(3, 2, -1)]
    [InlineData(5, 2, -1)]
    [InlineData(2, 2, +1)]
    [InlineData(3, 2, +1)]
    [InlineData(5, 2, +1)]
    // d-sweep, fixed q=2 (d=6,8 add to the d=4 cases above; d=8/n=256 is slow ~min)
    [InlineData(2, 3, -1)]
    [InlineData(2, 4, -1)]
    [InlineData(2, 3, +1)]
    [InlineData(2, 4, +1)]
    public void Phase0_BranchProfile(int q, int m, int eps)
    {
        int n = IPow(q, 2 * m);
        var adj = AffinePolar(q, m, eps);
        string nm = $"VO^{(eps < 0 ? "-" : "+")}_{2 * m}({q}) n={n}  [d={2 * m}, q={q}]";
        _out.WriteLine(nm);

        // DEFAULT mode (deferral off) — the branch-but-resolve path T0 targets.
        var dDefault = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        {
            EnableLinearOracle = true,
            EnableDeferral = false
        };
        Report(_out, "default(no-defer)", dDefault.Canonize(new sbyte[n * n], new WarmPartition(n)));

        // DEFERRAL mode — the single-path baseline (expect leaves=1, B=1, L=0).
        var dDefer = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        {
            EnableLinearOracle = true,
            EnableDeferral = true
        };
        Report(_out, "deferral", dDefer.Canonize(new sbyte[n * n], new WarmPartition(n)));
    }

    [Theory]
    [Trait("Category", "LongRunning")]
    [InlineData(3, -1)]
    [InlineData(3, +1)]
    [InlineData(5, -1)]
    [InlineData(5, +1)]
    public void Reconcile_VO4(int q, int eps)
    {
        int n = IPow(q, 4);
        var adj = AffinePolar4(q, eps);
        string nm = $"VO^{(eps < 0 ? "-" : "+")}_4({q}) n={n}";
        _out.WriteLine(nm);

        // DEFAULT mode (deferral off) — the path Lean's spine substrate certifies.
        var dDefault = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        {
            EnableLinearOracle = true,
            EnableDeferral = false
        };
        Report(_out, "default(no-defer)", dDefault.Canonize(new sbyte[n * n], new WarmPartition(n)));

        // DEFERRAL mode (production recovery path).
        var dDefer = new ChainDescent(n, adj, new CascadeOracle(), ChainDescent.DefaultBudget(n))
        {
            EnableLinearOracle = true,
            EnableDeferral = true
        };
        Report(_out, "deferral", dDefer.Canonize(new sbyte[n * n], new WarmPartition(n)));
    }
}
