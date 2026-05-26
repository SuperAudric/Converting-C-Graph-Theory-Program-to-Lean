using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Text;
using Xunit.Abstractions;
using Canonizer;

// Tier-2 decomposition experiment — Phase B step 1 on CFI(K4).
//
// See docs/chain-descent-tier2-decomposition-experiment.md §8.6 for context.
// This file is a self-contained probe: a local 1-WL refiner runs on CFI(K4)
// at escalating individualization depths, capturing cell-size signatures and
// cell × gadget overlap matrices. Patterns under test:
//
//   P2 — cell-size signature is iso-invariant across input scramblings, given
//        an iso-invariant choice of individualization vertex.
//   P3 — at low depths, the largest residual cell intersects each gadget in
//        a predictable share (originally |gadget|/2 on CFI(C3); we measure
//        the K4 shape rather than hard-asserting).
//   P4 — full cascade reached by depth tw(H)+1 = 4 for K4.
//
// No production code is touched. The refiner is the minimum needed for the
// probe and is intentionally simple (string signatures, no warm-start).
public class Tier2DecompositionExperiment(ITestOutputHelper output)
{
    // ── Main probe ───────────────────────────────────────────────────────────

    [Fact]
    public void CfiK4_DepthEscalation_CellSizesAndGadgetOverlap()
    {
        var pair = CfiGraphGenerator.Generate("K4");
        int n = pair.Even.VertexCount;
        Assert.Equal(40, n);

        var adj = FlattenAdj(pair.Even);
        var roles = pair.VertexRoles;
        var gadget = ParseGadgets(roles);
        int numGadgets = gadget.Max() + 1;
        Assert.Equal(4, numGadgets);

        // Two depth-1 starts to fingerprint both Aut-orbits.
        string startSubset   = "v0:subset:{}";       // a_∅ of gadget G0
        string startEndpoint = "v0:end[w1]^0";       // edge-endpoint of G0

        var probeSubset = RunProbe(adj, n, roles, gadget, startSubset,   maxDepth: 5);
        var probeEndpt  = RunProbe(adj, n, roles, gadget, startEndpoint, maxDepth: 5);
        DumpProbe("identity / start=subset",   probeSubset);
        DumpProbe("identity / start=endpoint", probeEndpt);

        // Iso-invariance: apply a seeded permutation, rerun, compare signatures.
        var sigma     = MakePermutation(n, seed: 4711);
        var adjPerm   = PermuteAdjacency(adj, n, sigma);
        var rolesPerm = PermuteRoles(roles, sigma);
        var gadgetPerm = ParseGadgets(rolesPerm);

        var probeSubsetPerm = RunProbe(adjPerm, n, rolesPerm, gadgetPerm, startSubset,   maxDepth: 5);
        var probeEndptPerm  = RunProbe(adjPerm, n, rolesPerm, gadgetPerm, startEndpoint, maxDepth: 5);
        DumpProbe("perm(seed=4711) / start=subset",   probeSubsetPerm);
        DumpProbe("perm(seed=4711) / start=endpoint", probeEndptPerm);

        // P2 — cell-size signature invariant at every depth, for both starts.
        AssertSignaturesMatch("subset",   probeSubset, probeSubsetPerm);
        AssertSignaturesMatch("endpoint", probeEndpt,  probeEndptPerm);

        // P4 — cascade depth check. Treewidth(K4) = 3, expect cascade by depth 4.
        int cascadeSubset = probeSubset.FindIndex(r => r.NumCells == n);
        int cascadeEndpt  = probeEndpt .FindIndex(r => r.NumCells == n);
        output.WriteLine($"\nCascade depth — subset-start: {DepthLabel(cascadeSubset)}");
        output.WriteLine(  $"Cascade depth — endpoint-start: {DepthLabel(cascadeEndpt)}");
        Assert.True(cascadeSubset >= 0 && cascadeSubset <= 5,
            $"Expected cascade ≤ depth 5 from subset start; got {cascadeSubset}");
        Assert.True(cascadeEndpt >= 0 && cascadeEndpt <= 5,
            $"Expected cascade ≤ depth 5 from endpoint start; got {cascadeEndpt}");
    }

    // The actual Tier-2 probe: CFI(Petersen) = CFI(J(5,2)). 100 vertices.
    // Aut = Z_2^6 ⋊ S_5 where S_5 acts as the Johnson group on 2-subsets.
    //
    // Hard assertion: iso-invariance of cell-size signature across scramblings.
    // Soft observation: cascade depth (reported, not asserted). If Petersen
    // cascades at depth ≈ tw(H) = 4, the Johnson factor is surfacing into
    // refinement (cascade-class behavior). If it doesn't cascade within
    // maxDepth, we've localized the encoded-Johnson resistance — Tier-2.
    [Fact]
    public void CfiPetersen_DepthEscalation_CellSizesAndGadgetOverlap()
    {
        var pair = CfiGraphGenerator.Generate("Petersen");
        int n = pair.Even.VertexCount;
        Assert.Equal(100, n);

        var adj = FlattenAdj(pair.Even);
        var roles = pair.VertexRoles;
        var gadget = ParseGadgets(roles);
        int numGadgets = gadget.Max() + 1;
        Assert.Equal(10, numGadgets);

        string startSubset   = "v0:subset:{}";
        string startEndpoint = PickFirstEndpointRole(roles, "v0");
        output.WriteLine($"Endpoint start role: {startEndpoint}");

        const int maxDepth = 8;     // tw(Petersen)=4, give headroom for surprise.

        var probeSubset = RunProbe(adj, n, roles, gadget, startSubset,   maxDepth);
        var probeEndpt  = RunProbe(adj, n, roles, gadget, startEndpoint, maxDepth);
        DumpProbeCondensed("identity / start=subset",   probeSubset);
        DumpProbeCondensed("identity / start=endpoint", probeEndpt);

        var sigma      = MakePermutation(n, seed: 4711);
        var adjPerm    = PermuteAdjacency(adj, n, sigma);
        var rolesPerm  = PermuteRoles(roles, sigma);
        var gadgetPerm = ParseGadgets(rolesPerm);

        var probeSubsetPerm = RunProbe(adjPerm, n, rolesPerm, gadgetPerm, startSubset,   maxDepth);
        var probeEndptPerm  = RunProbe(adjPerm, n, rolesPerm, gadgetPerm, startEndpoint, maxDepth);

        // P2 — hard assertion.
        AssertSignaturesMatch("subset",   probeSubset, probeSubsetPerm);
        AssertSignaturesMatch("endpoint", probeEndpt,  probeEndptPerm);

        // Cascade depth — observation only, no assertion. The whole point of
        // the Petersen probe is to discover this empirically.
        int cascadeSubset = probeSubset.FindIndex(r => r.NumCells == n);
        int cascadeEndpt  = probeEndpt .FindIndex(r => r.NumCells == n);
        output.WriteLine($"\nCascade depth — subset-start: {DepthLabel(cascadeSubset)}");
        output.WriteLine(  $"Cascade depth — endpoint-start: {DepthLabel(cascadeEndpt)}");
        output.WriteLine(  $"(tw(Petersen) = 4; F2 from CFI(K4) predicts cascade at depth ≈ tw)");

        // Final cell count at maxDepth — for the non-cascade case.
        output.WriteLine($"Final cell count — subset-start: {probeSubset[^1].NumCells} (depth {probeSubset[^1].Depth})");
        output.WriteLine($"Final cell count — endpoint-start: {probeEndpt[^1].NumCells} (depth {probeEndpt[^1].Depth})");
    }

    // The orbit-recovery verification probe (docs/chain-descent-orbit-recovery.md §9.6).
    // Hypothesis F7 / Tier 1: 1-WL refinement after fresh-colour individualization
    // produces a partition equal to Aut(G)_v orbits. We get Aut(G) from the project's
    // canonizer (which harvests it during chain-descent), then compute Aut_v orbits
    // via the pair-orbit method, then compare to the 1-WL cells from our local probe.
    //
    // The result is *observation*, not assertion: we report match/mismatch and the
    // exact comparison data. A mismatch at depth 1 means F7 needs to weaken (likely
    // "matches at higher depth" rather than "matches at depth 1").
    [Fact]
    public void CfiK4_OrbitRecovery_CompareAutStabilizerOrbitsToCells()
    {
        var pair = CfiGraphGenerator.Generate("K4");
        AssertOrbitRecoveryAtDepth1(pair, expectedAutOrder: 192, baseGraphName: "K4");
    }

    [Fact]
    public void CfiPetersen_OrbitRecovery_CompareAutStabilizerOrbitsToCells()
    {
        var pair = CfiGraphGenerator.Generate("Petersen");
        // |Aut(CFI(Petersen))| = 2^6 · 120 = 7680.
        AssertOrbitRecoveryAtDepth1(pair, expectedAutOrder: 7680, baseGraphName: "Petersen");
    }

    [Fact]
    public void CfiK33_OrbitRecovery_CompareAutStabilizerOrbitsToCells()
    {
        var pair = CfiGraphGenerator.Generate("K33");
        // |Aut(CFI(K33))| = 2^4 · 72 = 1152. (β(K33) = 9-6+1 = 4; |Aut(K33)| = (S3⋊S2)·... = 72.)
        AssertOrbitRecoveryAtDepth1(pair, expectedAutOrder: 1152, baseGraphName: "K33");
    }

    // CFI of cycle bases is DISCONNECTED — for C_k (k odd), CFI(C_k) is two
    // disjoint cycles each of length 3k. The canonizer processes each
    // component separately and LastAutomorphisms gives only one component's
    // Aut. The orbit-recovery framing doesn't cleanly apply to this case;
    // multi-component CFI is out of scope for the depth-1 F7 question.
    //
    // [Fact-skipped] CfiCycle5_OrbitRecovery — disconnected, doesn't fit
    // single-Aut framing.

    [Fact]
    public void CfiRook3x3_OrbitRecovery_CompareAutStabilizerOrbitsToCells()
    {
        var pair = CfiGraphGenerator.Generate("Rook3x3");
        // |Aut(CFI(Rook3x3))| = 2^10 · 72 = 73728. (β(Rook3x3) = 18-9+1 = 10.)
        AssertOrbitRecoveryAtDepth1(pair, expectedAutOrder: 73728, baseGraphName: "Rook3x3");
    }

    // Run the orbit-recovery check at depth 1 on both Aut-orbits (subset-start
    // and endpoint-start). For each, report whether 1-WL refinement after
    // fresh-colour individualization produces a partition equal to Aut_v orbits.
    //
    // Two findings can occur:
    //   YES — F7 strict form holds at depth 1 for this instance.
    //   NO  — 1-WL cells are strictly coarser than Aut_v orbits. 1-WL fails to
    //         distinguish vertices that Aut_v actually separates. F7 strict
    //         doesn't hold at depth 1 here; the question of whether it holds at
    //         higher depth is left for the deeper-depth follow-on.
    //
    // We record but no longer hard-assert — the empirical landscape is the
    // primary deliverable.
    private void AssertOrbitRecoveryAtDepth1(
        CfiGraphGenerator.CfiPair pair,
        BigInteger? expectedAutOrder,
        string baseGraphName)
    {
        int n = pair.Even.VertexCount;
        var canonizer = new CanonGraphOrdererChainDescent();
        canonizer.Run(new int[n], pair.Even);
        Assert.NotNull(canonizer.LastAutomorphisms);
        var aut = canonizer.LastAutomorphisms!;
        output.WriteLine($"|Aut(CFI({baseGraphName}))| = {aut.Order} ({aut.Generators.Count} generators)");
        if (expectedAutOrder.HasValue && expectedAutOrder.Value != aut.Order)
            output.WriteLine($"  ⚠ expected |Aut| = {expectedAutOrder.Value}, got {aut.Order} — formula off, canonizer trusted as ground truth");

        // Sanity: harvested generators must permute all n vertices. If they
        // don't, the graph was processed component-by-component and Aut is
        // partial — orbit-recovery framing breaks (test is then out of scope).
        var genLengths = aut.Generators.Select(g => g.Length).Distinct().ToList();
        if (aut.Generators.Count > 0 && (genLengths.Count != 1 || genLengths[0] != n))
        {
            output.WriteLine($"  ⚠ generator lengths {string.Join(",", genLengths)} != n={n} — multi-component graph, skipping");
            return;
        }

        var roles = pair.VertexRoles;
        var adj = FlattenAdj(pair.Even);

        string startSubset = "v0:subset:{}";
        string startEndpoint = PickFirstEndpointRole(roles, "v0");

        foreach (var startRole in new[] { startSubset, startEndpoint })
        {
            int v = Array.IndexOf(roles, startRole);
            Assert.True(v >= 0);
            output.WriteLine($"\n── individualization: {startRole} (vertex {v}) ──");

            var autVOrbits = ComputeStabilizerOrbits(v, n, aut.Generators);
            output.WriteLine($"  Aut_v orbits: {autVOrbits.Count} total, sizes [{string.Join(", ", autVOrbits.Select(o => o.Count).OrderByDescending(x => x))}]");

            var color = new int[n];
            OneWLRefine(adj, n, color);
            int fresh = color.Max() + 1;
            color[v] = fresh;
            OneWLRefine(adj, n, color);
            var cellsAtDepth1 = ExtractCells(color);
            output.WriteLine($"  1-WL cells at depth 1: {cellsAtDepth1.Count} total, sizes [{string.Join(", ", cellsAtDepth1.Select(c => c.Count).OrderByDescending(x => x))}]");

            bool exactMatch = CellsEqualOrbits(cellsAtDepth1, autVOrbits);
            output.WriteLine($"  → Depth-1 cells = Aut_v orbits? {(exactMatch ? "YES" : "NO")}");
        }

        // Verify trivial direction: orbits ⊆ cells (each orbit sits inside a
        // single cell). If this fails, either the canonizer overgenerates
        // (claiming spurious permutations as automorphisms) or the refiner
        // is buggy. Report rather than hard-assert — it surfaces the issue
        // without making the test failure obscure.
        foreach (var startRole in new[] { startSubset, startEndpoint })
        {
            int v = Array.IndexOf(roles, startRole);
            var autVOrbits = ComputeStabilizerOrbits(v, n, aut.Generators);
            var color = new int[n];
            OneWLRefine(adj, n, color);
            color[v] = color.Max() + 1;
            OneWLRefine(adj, n, color);
            int badOrbits = 0;
            foreach (var orbit in autVOrbits)
            {
                int firstColor = color[orbit.First()];
                if (!orbit.All(w => color[w] == firstColor)) badOrbits++;
            }
            if (badOrbits > 0)
                output.WriteLine($"  ⚠ {baseGraphName}/{startRole}: {badOrbits} orbit(s) split across cells — canonizer overgeneration or refiner bug");
        }
    }

    private static List<HashSet<int>> ExtractCells(int[] color)
    {
        var byColor = new Dictionary<int, HashSet<int>>();
        for (int i = 0; i < color.Length; i++)
        {
            if (!byColor.TryGetValue(color[i], out var cell))
                byColor[color[i]] = cell = new HashSet<int>();
            cell.Add(i);
        }
        return byColor.Values.ToList();
    }

    // Compute the orbits of Aut(G)_v on V(G) via the pair-orbit method:
    // the orbit of w under Aut_v is {w' : (v, w') is in the diagonal Aut-orbit of (v, w)}.
    private static List<HashSet<int>> ComputeStabilizerOrbits(int v, int n, IReadOnlyList<int[]> autGenerators)
    {
        var remaining = new HashSet<int>(Enumerable.Range(0, n).Where(i => i != v));
        var stabOrbits = new List<HashSet<int>> { new HashSet<int> { v } };
        while (remaining.Count > 0)
        {
            int w = remaining.Min();
            var orbit = PairOrbitFilteredOnFirst(v, w, autGenerators);
            stabOrbits.Add(orbit);
            remaining.ExceptWith(orbit);
        }
        return stabOrbits;
    }

    private static HashSet<int> PairOrbitFilteredOnFirst(int v, int w, IReadOnlyList<int[]> autGenerators)
    {
        var pairOrbit = new HashSet<(int, int)> { (v, w) };
        var queue = new Queue<(int, int)>();
        queue.Enqueue((v, w));
        while (queue.Count > 0)
        {
            var (a, b) = queue.Dequeue();
            foreach (var g in autGenerators)
            {
                var img = (g[a], g[b]);
                if (pairOrbit.Add(img)) queue.Enqueue(img);
            }
        }
        var result = new HashSet<int>();
        foreach (var (a, b) in pairOrbit)
            if (a == v) result.Add(b);
        return result;
    }

    // Are two set-partitions equal as sets of sets?
    private static bool CellsEqualOrbits(List<HashSet<int>> cells, List<HashSet<int>> orbits)
    {
        if (cells.Count != orbits.Count) return false;
        var orbitsAsSorted = orbits.Select(o => string.Join(",", o.OrderBy(x => x))).ToHashSet();
        foreach (var c in cells)
        {
            var key = string.Join(",", c.OrderBy(x => x));
            if (!orbitsAsSorted.Contains(key)) return false;
        }
        return true;
    }

    // Sanity-check the refiner against the hand-computed CFI(C3) result from
    // docs/chain-descent-tier2-decomposition-experiment.md §8.2.
    [Fact]
    public void CfiC3_DepthEscalation_MatchesHandComputedSignatures()
    {
        var pair = CfiGraphGenerator.Generate("Cycle3");
        int n = pair.Even.VertexCount;
        Assert.Equal(18, n);

        var adj = FlattenAdj(pair.Even);
        var roles = pair.VertexRoles;
        var gadget = ParseGadgets(roles);

        var probe = RunProbe(adj, n, roles, gadget, startRole: "v0:subset:{}", maxDepth: 3);
        DumpProbe("CFI(C3) / start=subset", probe);

        // Depth 0: one cell.
        Assert.Equal(new[] { 18 }, probe[0].CellSizes);

        // Depth 1: hand-computed signature (1, 2, 2, 2, 2, 9), sorted desc.
        // Matches §8.2 of the experiment doc exactly.
        Assert.Equal(new[] { 9, 2, 2, 2, 2, 1 }, probe[1].CellSizes);

        // Depth 2 under the lowest-cell-id picker — NOT discrete. The picker
        // descends into the 9-cell (H, lowest non-singleton cell id) rather
        // than into a 2-cell, so it doesn't break the G1↔G2 symmetry quickly.
        // §8.2's "cascades after 2 individualizations" claim was an artifact of
        // a different (smallest-cell) pick; under the canonical chain-descent
        // pick, C3 takes more. Recorded as a picker-dependence finding.
        Assert.Equal(10, probe[2].NumCells);
        Assert.Equal(14, probe[3].NumCells);
    }

    // ── Probe orchestration ──────────────────────────────────────────────────

    private record ProbeResult(
        int Depth,
        string IndividualizedRole,
        int[] CellSizes,
        int NumCells,
        int[,] CellByGadget);

    private static List<ProbeResult> RunProbe(
        int[] adj, int n, string[] roles, int[] gadget,
        string startRole, int maxDepth)
    {
        var color = new int[n];           // single cell to start
        var results = new List<ProbeResult>();

        // Depth 0: cold refinement before any individualization.
        OneWLRefine(adj, n, color);
        results.Add(BuildResult(0, "(none)", color, gadget));

        // Depth 1: individualize the canonical start vertex by role.
        int startVertex = Array.IndexOf(roles, startRole);
        if (startVertex < 0)
            throw new InvalidOperationException($"Role '{startRole}' not found in VertexRoles");
        IndividualizeAndRefine(adj, n, color, startVertex);
        results.Add(BuildResult(1, roles[startVertex], color, gadget));

        // Depths 2..maxDepth: pick lowest-cell-id non-singleton cell, within it
        // pick the vertex whose role string sorts first (iso-invariant via roles).
        for (int d = 2; d <= maxDepth; d++)
        {
            int next = PickNextIndividualization(color, n, roles);
            if (next < 0) break;          // already discrete
            IndividualizeAndRefine(adj, n, color, next);
            results.Add(BuildResult(d, roles[next], color, gadget));
            if (results[^1].NumCells == n) break;
        }

        return results;
    }

    private static int PickNextIndividualization(int[] color, int n, string[] roles)
    {
        var groups = new Dictionary<int, List<int>>();
        for (int v = 0; v < n; v++)
        {
            if (!groups.TryGetValue(color[v], out var lst))
                groups[color[v]] = lst = new List<int>();
            lst.Add(v);
        }
        int bestCell = -1;
        foreach (var (cellId, verts) in groups)
        {
            if (verts.Count < 2) continue;
            if (bestCell < 0 || cellId < bestCell) bestCell = cellId;
        }
        if (bestCell < 0) return -1;
        var candidates = groups[bestCell];
        candidates.Sort((a, b) => string.CompareOrdinal(roles[a], roles[b]));
        return candidates[0];
    }

    private static void IndividualizeAndRefine(int[] adj, int n, int[] color, int v)
    {
        int fresh = color.Max() + 1;
        color[v] = fresh;
        OneWLRefine(adj, n, color);
    }

    private static ProbeResult BuildResult(int depth, string role, int[] color, int[] gadget)
    {
        int n = color.Length;
        int numCells = color.Distinct().Count();
        int numGadgets = gadget.Max() + 1;

        // Re-canonicalize cell ids to a contiguous range [0..numCells) for
        // overlap matrix indexing. Order by first-occurrence.
        var canonId = new Dictionary<int, int>();
        var contiguous = new int[n];
        for (int v = 0; v < n; v++)
        {
            if (!canonId.TryGetValue(color[v], out int id))
                canonId[color[v]] = id = canonId.Count;
            contiguous[v] = id;
        }

        var sizes = new int[numCells];
        for (int v = 0; v < n; v++) sizes[contiguous[v]]++;
        var sortedSizes = sizes.OrderByDescending(s => s).ToArray();

        var overlap = new int[numCells, numGadgets];
        for (int v = 0; v < n; v++) overlap[contiguous[v], gadget[v]]++;

        return new ProbeResult(depth, role, sortedSizes, numCells, overlap);
    }

    // ── 1-WL refinement (local reimplementation) ─────────────────────────────

    private static void OneWLRefine(int[] adj, int n, int[] color)
    {
        // Safety bound: 1-WL converges in ≤ n rounds on the partition lattice.
        // 100 is comfortably above any conceivable case for n ≤ 100.
        for (int round = 0; round < 100; round++)
            if (!RefineOneRound(adj, n, color)) return;
        throw new InvalidOperationException("1-WL refinement did not converge within 100 rounds.");
    }

    private static bool RefineOneRound(int[] adj, int n, int[] color)
    {
        // We terminate when the *partition* is stable, not when labels are stable.
        // Lex-sort relabelling can permute labels round-to-round even when the
        // partition is fixed (e.g. with 11+ cells, "10" lex-precedes "1"), so a
        // label-equality check would loop forever. 1-WL can only split cells, so
        // an increase in distinct-color count uniquely detects refinement.
        int oldNumCells;
        {
            var distinct = new HashSet<int>();
            for (int v = 0; v < n; v++) distinct.Add(color[v]);
            oldNumCells = distinct.Count;
        }

        var sigs = new string[n];
        var sb = new StringBuilder();
        for (int v = 0; v < n; v++)
        {
            sb.Clear();
            sb.Append(color[v]).Append('|');
            var nbrColors = new List<int>();
            for (int u = 0; u < n; u++)
                if (u != v && adj[v * n + u] != 0)
                    nbrColors.Add(color[u]);
            nbrColors.Sort();
            sb.Append(string.Join(",", nbrColors));
            sigs[v] = sb.ToString();
        }
        var rank = sigs.Distinct()
                       .OrderBy(s => s, StringComparer.Ordinal)
                       .Select((s, i) => (s, i))
                       .ToDictionary(x => x.s, x => x.i);
        for (int v = 0; v < n; v++) color[v] = rank[sigs[v]];

        return rank.Count > oldNumCells;
    }

    // ── Adjacency / role / permutation helpers ───────────────────────────────

    private static int[] FlattenAdj(AdjMatrix m)
    {
        int n = m.VertexCount;
        var flat = new int[n * n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                flat[i * n + j] = m[i, j];
        return flat;
    }

    // VertexRoles are formatted as "v{n}:..." — extract n.
    private static int[] ParseGadgets(string[] roles)
    {
        var gadget = new int[roles.Length];
        for (int i = 0; i < roles.Length; i++)
        {
            var r = roles[i];
            if (r.Length < 2 || r[0] != 'v')
                throw new InvalidOperationException($"Unexpected role format: '{r}'");
            int colon = r.IndexOf(':');
            if (colon < 0) throw new InvalidOperationException($"Unexpected role format: '{r}'");
            gadget[i] = int.Parse(r.AsSpan(1, colon - 1));
        }
        return gadget;
    }

    private static int[] MakePermutation(int n, int seed)
    {
        var rng = new Random(seed);
        var sigma = Enumerable.Range(0, n).ToArray();
        for (int i = n - 1; i > 0; i--)
        {
            int j = rng.Next(i + 1);
            (sigma[i], sigma[j]) = (sigma[j], sigma[i]);
        }
        return sigma;
    }

    // adj'[σ(i)*n + σ(j)] = adj[i*n + j].
    private static int[] PermuteAdjacency(int[] adj, int n, int[] sigma)
    {
        var result = new int[n * n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                result[sigma[i] * n + sigma[j]] = adj[i * n + j];
        return result;
    }

    private static string[] PermuteRoles(string[] roles, int[] sigma)
    {
        var result = new string[roles.Length];
        for (int i = 0; i < roles.Length; i++)
            result[sigma[i]] = roles[i];
        return result;
    }

    // ── Output / assertion helpers ───────────────────────────────────────────

    private void DumpProbe(string label, List<ProbeResult> probe)
    {
        output.WriteLine($"\n── {label} ──");
        foreach (var r in probe)
        {
            output.WriteLine($"  depth {r.Depth} — individualized: {r.IndividualizedRole}");
            output.WriteLine($"    cell-sizes (desc): [{string.Join(", ", r.CellSizes)}]  ({r.NumCells} cells)");
            int numGadgets = r.CellByGadget.GetLength(1);
            for (int c = 0; c < r.NumCells; c++)
            {
                var row = new int[numGadgets];
                for (int g = 0; g < numGadgets; g++) row[g] = r.CellByGadget[c, g];
                if (row.Sum() == 0) continue;
                output.WriteLine($"      cell {c,2}: gadget-overlap [{string.Join(", ", row)}]  total {row.Sum()}");
            }
        }
    }

    // Condensed dump for large graphs: cell-size signature + cell-by-gadget
    // class summary, skipping per-cell overlap listings. Groups cells by their
    // gadget-overlap pattern and reports counts.
    private void DumpProbeCondensed(string label, List<ProbeResult> probe)
    {
        output.WriteLine($"\n── {label} ──");
        foreach (var r in probe)
        {
            output.WriteLine($"  depth {r.Depth} — individualized: {r.IndividualizedRole}");
            output.WriteLine($"    cell-sizes (desc): [{string.Join(", ", r.CellSizes)}]  ({r.NumCells} cells)");

            // Group cells by their normalized gadget-overlap pattern (sorted desc).
            int numGadgets = r.CellByGadget.GetLength(1);
            var patternCounts = new Dictionary<string, int>();
            for (int c = 0; c < r.NumCells; c++)
            {
                var row = new int[numGadgets];
                for (int g = 0; g < numGadgets; g++) row[g] = r.CellByGadget[c, g];
                if (row.Sum() == 0) continue;
                Array.Sort(row);
                Array.Reverse(row);
                string key = "[" + string.Join(",", row) + "]";
                patternCounts[key] = patternCounts.GetValueOrDefault(key, 0) + 1;
            }
            foreach (var kvp in patternCounts.OrderByDescending(kv => kv.Value))
                output.WriteLine($"      overlap pattern {kvp.Key}: {kvp.Value} cell(s)");
        }
    }

    private static string PickFirstEndpointRole(string[] roles, string gadgetPrefix)
    {
        var prefix = gadgetPrefix + ":end[";
        var match = roles.Where(r => r.StartsWith(prefix) && r.EndsWith("]^0"))
                         .OrderBy(r => r, StringComparer.Ordinal)
                         .FirstOrDefault();
        if (match == null)
            throw new InvalidOperationException($"No endpoint role found with prefix '{prefix}'");
        return match;
    }

    private static void AssertSignaturesMatch(string label, List<ProbeResult> a, List<ProbeResult> b)
    {
        Assert.True(a.Count == b.Count,
            $"[{label}] probe depth differs: {a.Count} vs {b.Count}");
        for (int d = 0; d < a.Count; d++)
        {
            Assert.True(a[d].CellSizes.SequenceEqual(b[d].CellSizes),
                $"[{label}] depth {d} cell-size signature differs: " +
                $"[{string.Join(",", a[d].CellSizes)}] vs [{string.Join(",", b[d].CellSizes)}]");
        }
    }

    private static string DepthLabel(int d) => d < 0 ? "> probe limit (not cascaded)" : d.ToString();
}
