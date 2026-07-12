using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

namespace Canonizer
{
    /// <summary>
    /// Option-2 rigid ring solver — the Phase-2 canonizer for a rigid native-A-multipede
    /// residue (docs/chain-descent-ir-blindspot-solver.md §11.12, build track B1).
    ///
    /// B1a (this step): RECOVER the residue's algebraic structure — segments, the value
    /// group A, and the constraint incidence M — recognition-free from a refined partition.
    /// Ported from the validated RM probes (RingWlExtractionProbe RM-1/RM-3/RM-4):
    ///   · RM-1  segments = the uniform-size non-singleton cells (here: on the segment
    ///           side of the multipede's bipartition, since production has no type colouring);
    ///   · RM-3  ring A via a degree-3 gadget's sum-zero Latin square (Albert's theorem:
    ///           the row-permutation cycle structure yields the order-profile fingerprint);
    ///   · RM-4  incidence M (which segments each gadget constrains).
    /// Returns null (= FLAG) when the partition is not a clean native-A-multipede residue.
    ///
    /// Solve (B1b: kernel/Smith + SolveA/CosetMinA) and the self-verifying emit
    /// (B1c: RM-5/RM-6) build on this. See §11.13a for the full validated pipeline.
    /// </summary>
    internal sealed class Option2Solver
    {
        /// <summary>The recovered algebraic residue: A ≅ (order-profile), segments, incidence M.</summary>
        internal sealed class RingResidue
        {
            public int ASize;                          // |A| (the segment/cell size)
            public string OrderProfile = "";           // canonical A-fingerprint (RM-3)
            public List<int[]> Segments = new();       // sorted state-vertices per segment, cell-id order
            public long[,] Incidence = new long[0, 0]; // M[gadget, segment] ∈ {0,1}
        }

        /// <summary>
        /// Recover (segments, ring A, incidence M) from a refined partition, recognition-free.
        /// Null ⟹ not a clean native-A-multipede residue (the caller flags / falls through).
        /// </summary>
        public static RingResidue? Recover(int[] adj, int n, int[] cellOf, int numCells, int? forceSide = null)
        {
            var side = Bipartition(adj, n);
            if (side == null) return null;                       // not bipartite ⟹ not a multipede

            var members = new List<int>[numCells];
            for (int c = 0; c < numCells; c++) members[c] = new List<int>();
            for (int v = 0; v < n; v++) members[cellOf[v]].Add(v);

            // Which bipartition class holds the segments? `forceSide` (B1d try-both-sides) fixes it;
            // otherwise fall back to the AVERAGE-per-vertex-degree HEURISTIC (segment-states touch many
            // gadget-tuples = high degree; gadget-tuples touch only their arity of segments = low degree;
            // total degree per side is equal in a bipartite graph, so the average is the discriminator).
            // The heuristic is SOUND (a wrong pick makes the φ-search find no labelling ⟹ FLAG, never a
            // wrong answer) but can cost COMPLETENESS. B1d removes that risk: SearchCanonicalViaSolve calls
            // Recover with BOTH forceSide values and lets the self-verifying emit select (min-form, iso-inv).
            int segSide;
            if (forceSide is int fs) segSide = fs;
            else
            {
                var totalDeg = new long[2]; var count = new long[2];
                for (int v = 0; v < n; v++)
                {
                    int d = 0; for (int w = 0; w < n; w++) d += adj[v * n + w];
                    totalDeg[side[v]] += d; count[side[v]]++;
                }
                double avg0 = count[0] > 0 ? (double)totalDeg[0] / count[0] : 0;
                double avg1 = count[1] > 0 ? (double)totalDeg[1] / count[1] : 0;
                segSide = avg0 >= avg1 ? 0 : 1;
            }

            // Segments = non-singleton cells wholly on the segment side, all of one size |A| ≥ 2.
            var segCells = new List<int[]>();
            int aSize = -1;
            for (int c = 0; c < numCells; c++)
            {
                var cell = members[c];
                if (cell.Count < 2) continue;
                if (!cell.All(v => side[v] == segSide)) continue;
                if (aSize == -1) aSize = cell.Count;
                else if (cell.Count != aSize) return null;       // non-uniform ⟹ not clean
                var arr = cell.ToArray(); Array.Sort(arr);
                segCells.Add(arr);
            }
            if (aSize < 2 || segCells.Count == 0) return null;
            segCells = segCells.OrderBy(s => cellOf[s[0]]).ToList();   // canonical order by cell-id

            var segOf = new int[n]; Array.Fill(segOf, -1);
            var localOf = new int[n];
            for (int si = 0; si < segCells.Count; si++)
                for (int k = 0; k < segCells[si].Length; k++) { segOf[segCells[si][k]] = si; localOf[segCells[si][k]] = k; }
            int nW = segCells.Count;

            var profile = InferOrderProfile(adj, n, segOf, localOf, aSize);
            if (profile == null) return null;                    // no degree-3 gadget ⟹ ring not inferable here
            var incidence = ExtractIncidence(adj, n, segOf, nW);

            return new RingResidue { ASize = aSize, OrderProfile = profile, Segments = segCells, Incidence = incidence };
        }

        // ── B1c: the self-verifying canonical emit (RM-5/RM-6) ────────────────────
        // Search a state-labelling φ (states → A) making every gadget's neighbours sum to 0
        // (a valid trivialisation of the untwisted native-A-multipede) from a resolving base;
        // EMIT the canonical adjacency under the min such labelling. A consistent complete
        // labelling exists IFF the residue reconstructs ⟹ success is the verification, failure
        // is the flag (verify-by-reconstruction unified with the emit). Returns null = FLAG.
        //
        // ⚠ SCOPE: this emit is poly-or-flag only for BOUNDED |A|. The base-labelling enumeration is
        // brute (|A|!² over the 2-segment base), which is not polynomial in n if |A| grows with n
        // (the design allows |A| up to n). The B1b primitives (SolveOverA/CosetMin, both poly) are the
        // poly path: extract the per-segment torsor (from RM-3's Latin-square translations), fix the
        // translation gauge by SolveOverA, min over the global Aut(A) — collapsing the |A|! enumeration.
        // Until that is wired, the poly guarantee is bounded-|A|; larger |A| still FLAGS (sound).
        public static string? TryCanonicalForm(int[] adj, int n, int[] cellOf, int numCells)
            => SearchCanonical(adj, n, cellOf, numCells)?.Form;

        /// <summary>
        /// B2 entry: the canonical vertex ORDER (<c>order[rank]</c> = original vertex) that the descent's
        /// <c>BuildPermutedMatrix</c> consumes, or null (= FLAG) if this is not a clean full-graph
        /// native-A residue. Returns null unless the emitted order covers ALL n vertices — i.e. every
        /// vertex is a segment-state or a gadget (the pristine whole-graph multipede the RM/D-M probes
        /// validate). A mixed / partially-pinned residue (pinned singletons left over) is NOT handled
        /// here: it returns null and the caller falls through to the exhaustive branch (sound; the σ-fold
        /// for mixed residues is B4). The emitted form agrees byte-for-byte with the descent's leaf
        /// convention (row-major, 0/1), so the caller can lex-min the permuted matrix against `_bestMatrix`.
        /// </summary>
        public static int[]? TryCanonicalOrder(int[] adj, int n, int[] cellOf, int numCells)
        {
            var best = SearchCanonicalViaSolve(adj, n, cellOf, numCells);
            if (best == null || best.Order.Length != n) return null;   // not a clean full-graph residue ⟹ flag
            return best.Order;
        }

        /// <summary>
        /// B4 entry: canonical order for a clean full multipede OR its **matched double** (σ-fold).
        /// First tries the plain single-multipede order (B2). If that flags, it detects the copy-swap
        /// involution `σ` STRUCTURALLY at the root — `σ(v)` = `v`'s UNIQUE same-cell neighbour (a matched
        /// double's only same-colour edge per vertex is its matching edge) — verifies `σ` is a free
        /// automorphism, splits the graph (minus the matching) into the two σ-swapped copies, canonicalizes
        /// ONE copy (the rigid core) via B2, and lifts to a whole-graph order `[core-order] ++ σ(core-order)`.
        /// The emitted matrix `[[Core, D],[D, Core]]` is fixed by the core's iso-invariant form, so the whole
        /// is iso-invariant; sound because `σ` is a verified automorphism and the copies split cleanly. Any
        /// deviation (σ not unique / not an automorphism / copies don't split / core flags) ⟹ null (fall-through).
        /// Fires at the SAME iso-invariant root hook as B2 — no Phase-1 σ-harvest needed. Mixed residues that
        /// are neither a single multipede nor a matched double still return null (B4 handles the doubled case).
        /// </summary>
        public static int[]? TryCanonicalOrderWithFold(int[] adj, int n, int[] cellOf, int numCells)
        {
            var plain = TryCanonicalOrder(adj, n, cellOf, numCells);
            if (plain != null) return plain;

            var sigma = SameCellNeighborInvolution(adj, n, cellOf);
            if (sigma == null) return null;
            if (!IsInvolutionAutomorphism(sigma, adj, n)) return null;      // soundness: σ must be a genuine automorphism

            var copyA = SplitMatchedCopies(adj, n, sigma);                  // one σ-swapped component (matching removed)
            if (copyA == null) return null;

            int coreN = copyA.Length;
            var coreIdxOf = new int[n]; Array.Fill(coreIdxOf, -1);
            for (int i = 0; i < coreN; i++) coreIdxOf[copyA[i]] = i;

            var coreAdj = new int[coreN * coreN];
            for (int i = 0; i < coreN; i++)
                for (int j = 0; j < coreN; j++)
                    coreAdj[i * coreN + j] = adj[copyA[i] * n + copyA[j]];

            // Core cell ids = the doubled partition's ids, kept AS-IS (they are iso-invariant — the
            // WarmPartition's canonical numbering). Do NOT renumber by first-occurrence: that ordering
            // is labelling-dependent, and Recover orders segments by cell-id, so it would de-invariant
            // the form. Each doubled cell is σ-fused (spans both copies), so every id 0..numCells-1 is
            // present in this copy ⟹ passing the original numCells is safe (absent ids ⟹ empty, skipped).
            var coreCellOf = new int[coreN];
            for (int i = 0; i < coreN; i++) coreCellOf[i] = cellOf[copyA[i]];

            var coreOrder = TryCanonicalOrder(coreAdj, coreN, coreCellOf, numCells);
            if (coreOrder == null) return null;

            // lift: copy A in the core's canonical order, then their σ-partners in the same order.
            var whole = new int[n];
            for (int rank = 0; rank < coreN; rank++)
            {
                int origVertex = copyA[coreOrder[rank]];
                whole[rank] = origVertex;
                whole[coreN + rank] = sigma[origVertex];
            }
            return whole;
        }

        // σ(v) = v's unique neighbour in its own WL cell; null unless EVERY vertex has exactly one such
        // neighbour and the resulting map is a fixed-point-free involution (the matched-double signature).
        private static int[]? SameCellNeighborInvolution(int[] adj, int n, int[] cellOf)
        {
            var sigma = new int[n];
            for (int v = 0; v < n; v++)
            {
                int partner = -1, cnt = 0;
                for (int w = 0; w < n; w++)
                    if (adj[v * n + w] != 0 && cellOf[w] == cellOf[v]) { partner = w; cnt++; }
                if (cnt != 1 || partner == v) return null;
                sigma[v] = partner;
            }
            for (int v = 0; v < n; v++) if (sigma[sigma[v]] != v) return null;   // genuine involution
            return sigma;
        }

        private static bool IsInvolutionAutomorphism(int[] sigma, int[] adj, int n)
        {
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (adj[i * n + j] != adj[sigma[i] * n + sigma[j]]) return false;
            return true;
        }

        // Remove the intra-orbit (matching) edges {v, σv}; the rest must be EXACTLY two σ-swapped
        // components of equal size. Returns the component containing vertex 0 (either works — the two
        // are σ-isomorphic, so the lifted matrix is identical), or null if it doesn't split cleanly.
        private static int[]? SplitMatchedCopies(int[] adj, int n, int[] sigma)
        {
            var comp = new int[n]; Array.Fill(comp, -1);
            int nComp = 0;
            var queue = new Queue<int>();
            for (int s = 0; s < n; s++)
            {
                if (comp[s] != -1) continue;
                if (nComp >= 2) return null;                       // more than two components
                comp[s] = nComp; queue.Enqueue(s);
                while (queue.Count > 0)
                {
                    int v = queue.Dequeue();
                    for (int w = 0; w < n; w++)
                    {
                        if (adj[v * n + w] == 0 || w == sigma[v]) continue;   // skip the matching edge
                        if (comp[w] == -1) { comp[w] = nComp; queue.Enqueue(w); }
                    }
                }
                nComp++;
            }
            if (nComp != 2) return null;
            for (int v = 0; v < n; v++) if (comp[sigma[v]] == comp[v]) return null;   // σ must swap the two copies
            var copyA = new List<int>();
            for (int v = 0; v < n; v++) if (comp[v] == 0) copyA.Add(v);
            if (copyA.Count != n - copyA.Count) return null;       // equal-size copies
            return copyA.ToArray();
        }

        /// <summary>The min self-verified labelling's vertex order + its serialized canonical form.</summary>
        private sealed class CanonCandidate { public int[] Order = Array.Empty<int>(); public string Form = ""; }

        // Shared core of B1c: recover → RecoverRing → search a state-labelling φ making every gadget sum
        // to 0 from a 2-segment base, keeping the labelling whose canonical form is lexicographically
        // least. A consistent complete φ exists IFF the residue reconstructs ⟹ success is the verification.
        private static CanonCandidate? SearchCanonical(int[] adj, int n, int[] cellOf, int numCells)
        {
            var res = Recover(adj, n, cellOf, numCells);
            if (res == null) return null;
            var A = RecoverRing(res.ASize, res.OrderProfile);
            if (A == null) return null;
            var segCells = res.Segments;
            int nW = segCells.Count;
            if (nW < 2) return null;

            var segOf = new int[n]; Array.Fill(segOf, -1);
            for (int si = 0; si < nW; si++) foreach (int v in segCells[si]) segOf[v] = si;

            var gVerts = new List<int>(); var gNbr = new List<List<(int seg, int v)>>();
            for (int v = 0; v < n; v++)
            {
                if (segOf[v] != -1) continue;
                var nb = new List<(int, int)>();
                for (int w = 0; w < n; w++) if (adj[v * n + w] == 1 && segOf[w] != -1) nb.Add((segOf[w], w));
                if (nb.Count >= 2) { gVerts.Add(v); gNbr.Add(nb); }
            }

            int Asz = res.ASize;
            var perms = Permutations(Asz);
            CanonCandidate? best = null;
            foreach (var p0 in perms)
                foreach (var p1 in perms)
                {
                    var phi = new int[n]; Array.Fill(phi, -1);
                    for (int k = 0; k < Asz; k++) { phi[segCells[0][k]] = p0[k]; phi[segCells[1][k]] = p1[k]; }
                    if (!PropagateSumZero(phi, gVerts, gNbr, A)) continue;
                    if (!LabellingComplete(phi, segCells, Asz)) continue;
                    var order = EmitOrder(segCells, gVerts, gNbr, phi);
                    var form = EmitForm(n, adj, order);
                    if (best == null || string.CompareOrdinal(form, best.Form) < 0)
                        best = new CanonCandidate { Order = order, Form = form };
                }
            return best;
        }

        // B1d: the SolveOverA emit — pin an AFFINE-FRAME base on the lowest-cell-id segment (r+1 of its
        // states → {0, e_0..e_{r-1}}, the generators of A ≅ ⊕Z/Inv[i]), then LINEAR-solve every other
        // state value over A via `SolveOverA`. Anchoring an affine frame + one bijective segment forces
        // every connected segment to a bijection (the gadget Latin structure), and the linear solve CLOSES
        // cyclic constraint graphs that unit-propagation stalls on (the production circulant at m≥8).
        // The base enumeration is over ordered (r+1)-subsets of the base segment's states — `|A|^{r+1}`,
        // POLY for bounded rank r (was `|A|!²` brute), and it sweeps every affine frame (which states are
        // 0/e_0/…) so the min stays iso-invariant.
        private static CanonCandidate? SearchCanonicalViaSolve(int[] adj, int n, int[] cellOf, int numCells)
        {
            // B1d try-both-sides: run the recover+solve+emit on EACH bipartition class and take the
            // iso-invariant min canonical form. Only the true segment side self-verifies (VerifyGadgets +
            // LabellingComplete); the other yields null and is skipped. This removes the average-degree
            // heuristic's completeness risk (a mis-pick no longer flags a canonicalisable residue).
            CanonCandidate? best = null;
            for (int forceSide = 0; forceSide < 2; forceSide++)
            {
                var cand = SolveEmitForSide(adj, n, cellOf, numCells, forceSide);
                if (cand != null && (best == null || string.CompareOrdinal(cand.Form, best.Form) < 0))
                    best = cand;
            }
            return best;
        }

        private static CanonCandidate? SolveEmitForSide(int[] adj, int n, int[] cellOf, int numCells, int forceSide)
        {
            var res = Recover(adj, n, cellOf, numCells, forceSide);
            if (res == null) return null;
            var A = RecoverRing(res.ASize, res.OrderProfile);
            if (A == null) return null;
            var segCells = res.Segments;
            int nW = segCells.Count;
            if (nW < 1) return null;
            int Asz = res.ASize;

            var segOf = new int[n]; Array.Fill(segOf, -1);
            for (int si = 0; si < nW; si++) foreach (int v in segCells[si]) segOf[v] = si;

            var gVerts = new List<int>(); var gNbr = new List<List<(int seg, int v)>>();
            for (int v = 0; v < n; v++)
            {
                if (segOf[v] != -1) continue;
                var nb = new List<(int, int)>();
                for (int w = 0; w < n; w++) if (adj[v * n + w] == 1 && segOf[w] != -1) nb.Add((segOf[w], w));
                if (nb.Count >= 2) { gVerts.Add(v); gNbr.Add(nb); }
            }
            if (gVerts.Count == 0) return null;

            // Anchor values: {0} ∪ generators e_0..e_{r-1}. Pin one distinct base-segment state to each.
            var anchors = new List<int> { 0 }; anchors.AddRange(A.Generators());
            var seg0 = segCells[0];
            if (seg0.Length < anchors.Count) return null;      // segment too small to anchor the frame

            int rows = gVerts.Count;
            CanonCandidate? best = null;
            foreach (var pick in OrderedSubsets(seg0.Length, anchors.Count))
            {
                // pinned states = seg0[pick[t]] → anchors[t]; unknowns = all other states.
                var pinVal = new int[n]; var isPinned = new bool[n];
                for (int t = 0; t < anchors.Count; t++) { int v = seg0[pick[t]]; pinVal[v] = anchors[t]; isPinned[v] = true; }

                var colOf = new int[n]; Array.Fill(colOf, -1);
                int cols = 0;
                for (int si = 0; si < nW; si++) foreach (int v in segCells[si]) if (!isPinned[v]) colOf[v] = cols++;
                var M = new long[rows, cols];
                var rhs = new int[rows];
                for (int gi = 0; gi < rows; gi++)
                {
                    int s = 0;
                    foreach (var (seg, v) in gNbr[gi])
                        if (isPinned[v]) s = A.Add(s, pinVal[v]); else M[gi, colOf[v]] += 1;
                    rhs[gi] = A.Neg(s);
                }
                var sol = SolveOverA(M, rhs, A);
                if (sol == null) continue;                       // anchor frame inconsistent ⟹ skip

                var phi = new int[n]; Array.Fill(phi, -1);
                for (int v = 0; v < n; v++) phi[v] = isPinned[v] ? pinVal[v] : (colOf[v] != -1 ? sol[colOf[v]] : -1);
                if (!VerifyGadgets(phi, gVerts, gNbr, A)) continue;   // every gadget sums to 0 (belt-and-braces)
                if (!LabellingComplete(phi, segCells, Asz)) continue;
                var order = EmitOrder(segCells, gVerts, gNbr, phi);
                var form = EmitForm(n, adj, order);
                if (best == null || string.CompareOrdinal(form, best.Form) < 0)
                    best = new CanonCandidate { Order = order, Form = form };
            }
            return best;
        }

        // Every gadget middle's incident state values sum to 0 in A — the untwisted trivialisation check.
        private static bool VerifyGadgets(int[] phi, List<int> gVerts, List<List<(int seg, int v)>> gNbr, Ring A)
        {
            for (int gi = 0; gi < gVerts.Count; gi++)
            {
                int s = 0;
                foreach (var (seg, v) in gNbr[gi]) { if (phi[v] == -1) return false; s = A.Add(s, phi[v]); }
                if (s != 0) return false;
            }
            return true;
        }


        // All ordered k-subsets (injective k-tuples) of {0..m-1}; count m·(m−1)···(m−k+1).
        private static IEnumerable<int[]> OrderedSubsets(int m, int k)
        {
            var cur = new int[k]; var used = new bool[m];
            IEnumerable<int[]> Rec(int d)
            {
                if (d == k) { yield return (int[])cur.Clone(); yield break; }
                for (int v = 0; v < m; v++)
                {
                    if (used[v]) continue;
                    used[v] = true; cur[d] = v;
                    foreach (var r in Rec(d + 1)) yield return r;
                    used[v] = false;
                }
            }
            return Rec(0);
        }

        private static bool PropagateSumZero(int[] phi, List<int> gVerts, List<List<(int seg, int v)>> gNbr, Ring A)
        {
            bool changed = true;
            while (changed)
            {
                changed = false;
                for (int gi = 0; gi < gVerts.Count; gi++)
                {
                    int unknownV = -1, unknownCnt = 0, s = 0;
                    foreach (var x in gNbr[gi]) { if (phi[x.v] == -1) { unknownCnt++; unknownV = x.v; } else s = A.Add(s, phi[x.v]); }
                    if (unknownCnt == 0) { if (s != 0) return false; }
                    else if (unknownCnt == 1) { phi[unknownV] = A.Neg(s); changed = true; }
                }
            }
            return true;
        }

        private static bool LabellingComplete(int[] phi, List<int[]> segCells, int Asz)
        {
            foreach (var seg in segCells)
            {
                var vals = seg.Select(v => phi[v]).ToList();
                if (vals.Any(x => x == -1) || vals.Distinct().Count() != Asz) return false;
            }
            return true;
        }

        // The canonical vertex order under labelling φ: segments (states by φ-value), then gadgets
        // (by their φ-tuple key). Full permutation of [0,n) iff every vertex is a segment or a gadget.
        private static int[] EmitOrder(List<int[]> segCells, List<int> gVerts,
                                       List<List<(int seg, int v)>> gNbr, int[] phi)
        {
            var order = new List<int>();
            foreach (var seg in segCells) order.AddRange(seg.OrderBy(v => phi[v]));
            var keyed = new List<(string key, int v)>();
            for (int gi = 0; gi < gVerts.Count; gi++)
                keyed.Add((string.Join("|", gNbr[gi].OrderBy(x => x.seg).Select(x => $"{x.seg}:{phi[x.v]}")), gVerts[gi]));
            foreach (var kv in keyed.OrderBy(x => x.key, StringComparer.Ordinal)) order.Add(kv.v);
            return order.ToArray();
        }

        // Serialize adj under a vertex order (row-major, 0/1) = BuildPermutedMatrix(inverse(order)).
        private static string EmitForm(int n, int[] adj, int[] order)
        {
            var sb = new System.Text.StringBuilder(order.Length * order.Length);
            for (int i = 0; i < order.Length; i++)
                for (int j = 0; j < order.Length; j++)
                    sb.Append(adj[order[i] * n + order[j]] != 0 ? '1' : '0');
            return sb.ToString();
        }

        private static List<int[]> Permutations(int k)
        {
            var res = new List<int[]>(); var a = Enumerable.Range(0, k).ToArray();
            void Rec(int i)
            {
                if (i == k) { res.Add((int[])a.Clone()); return; }
                for (int j = i; j < k; j++) { (a[i], a[j]) = (a[j], a[i]); Rec(i + 1); (a[i], a[j]) = (a[j], a[i]); }
            }
            Rec(0); return res;
        }

        // ── segment/gadget bipartition (BFS 2-colouring); null on an odd cycle ────────
        private static int[]? Bipartition(int[] adj, int n)
        {
            var color = new int[n]; Array.Fill(color, -1);
            var queue = new Queue<int>();
            for (int s = 0; s < n; s++)
            {
                if (color[s] != -1) continue;
                color[s] = 0; queue.Enqueue(s);
                while (queue.Count > 0)
                {
                    int v = queue.Dequeue();
                    for (int w = 0; w < n; w++)
                    {
                        if (adj[v * n + w] == 0) continue;
                        if (color[w] == -1) { color[w] = color[v] ^ 1; queue.Enqueue(w); }
                        else if (color[w] == color[v]) return null;
                    }
                }
            }
            return color;
        }

        // ── RM-3: ring order-profile from a gadget line's sum-zero Latin square (any arity ≥ 3) ─
        // For a degree-3 line, read its |A|² sum-zero relation directly. For a degree-d line (d > 3),
        // REDUCE to degree 3 by PINNING the d−3 highest-id segments to their local-index-0 state (NOT
        // marginalising — the sub-relation over the 3 free segments is a full |A|² constant-sum square,
        // a group Latin square of A). The constant offset is an isotopy, so Albert's cycle-structure
        // read (R_x∘R_x'⁻¹ = translation by x'−x, constant-independent) still recovers A exactly.
        private static string? InferOrderProfile(int[] adj, int n, int[] segOf, int[] localOf, int Asz)
        {
            // Group gadget middles by the SET of segments they touch (a "line"); need arity ≥ 3.
            var byLine = new Dictionary<string, List<int>>();
            for (int v = 0; v < n; v++)
            {
                if (segOf[v] != -1) continue;
                var segSet = new SortedSet<int>();
                for (int w = 0; w < n; w++) if (adj[v * n + w] == 1 && segOf[w] != -1) segSet.Add(segOf[w]);
                if (segSet.Count < 3) continue;
                var key = string.Join(",", segSet);
                if (!byLine.TryGetValue(key, out var l)) byLine[key] = l = new List<int>();
                l.Add(v);
            }

            foreach (var kv in byLine.OrderBy(k => k.Key, StringComparer.Ordinal))   // deterministic
            {
                var sids = kv.Key.Split(',').Select(int.Parse).ToArray();
                // 3 FREE segments (lowest ids) read the Latin square; the rest are PINNED to local-0.
                int s0 = sids[0], s1 = sids[1], s2 = sids[2];
                var pinned = new HashSet<int>(sids.Skip(3));
                var L = new int[Asz, Asz];
                var filled = new bool[Asz, Asz];
                bool ok = true;
                foreach (int gv in kv.Value)
                {
                    int x = -1, y = -1, z = -1; bool keep = true;
                    for (int w = 0; w < n; w++)
                    {
                        if (adj[gv * n + w] != 1 || segOf[w] == -1) continue;
                        int sg = segOf[w], lo = localOf[w];
                        if (sg == s0) x = lo; else if (sg == s1) y = lo; else if (sg == s2) z = lo;
                        else if (pinned.Contains(sg) && lo != 0) keep = false;   // pinned segment off local-0 ⟹ skip
                    }
                    if (!keep) continue;
                    if (x < 0 || y < 0 || z < 0 || filled[x, y]) { ok = false; break; }
                    L[x, y] = z; filled[x, y] = true;
                }
                if (!ok) continue;
                // require a FULL reduced Latin square (every (x,y) present).
                bool full = true;
                for (int x = 0; x < Asz && full; x++) for (int y = 0; y < Asz; y++) if (!filled[x, y]) { full = false; break; }
                if (!full) continue;

                var hist = new SortedDictionary<int, int>();
                for (int x = 0; x < Asz; x++)
                    for (int xp = 0; xp < Asz; xp++)
                    {
                        if (x == xp) continue;
                        var rinv = new int[Asz]; for (int y = 0; y < Asz; y++) rinv[L[xp, y]] = y;
                        var perm = new int[Asz]; for (int z = 0; z < Asz; z++) perm[z] = L[x, rinv[z]];
                        int ord = PermOrder(perm);
                        hist[ord] = hist.TryGetValue(ord, out var c) ? c + 1 : 1;
                    }

                var parts = new List<string> { "1^1" };
                foreach (var kv2 in hist) parts.Add($"{kv2.Key}^{kv2.Value / Asz}");
                return string.Join(",", parts);
            }
            return null;
        }

        // ── RM-4: incidence M (gadget × segment), recognition-free ────────────────────
        private static long[,] ExtractIncidence(int[] adj, int n, int[] segOf, int nW)
        {
            var seen = new HashSet<string>();
            var rows = new List<int[]>();
            for (int v = 0; v < n; v++)
            {
                if (segOf[v] != -1) continue;
                var set = new SortedSet<int>();
                for (int w = 0; w < n; w++) if (adj[v * n + w] == 1 && segOf[w] != -1) set.Add(segOf[w]);
                if (set.Count < 2) continue;
                var key = string.Join(",", set);
                if (seen.Add(key)) rows.Add(set.ToArray());
            }
            var M = new long[rows.Count, nW];
            for (int r = 0; r < rows.Count; r++) foreach (int j in rows[r]) M[r, j] = 1;
            return M;
        }

        // ── B1b: the ring A + the solve primitives (extended Smith, poly) ─────────

        /// <summary>A finite abelian value group A ≅ ⊕ Z/Inv[i], with the arithmetic the solve needs.</summary>
        internal sealed class Ring
        {
            public readonly int[] Inv; public readonly int N;
            public Ring(int[] inv) { Inv = inv; N = inv.Aggregate(1, (a, b) => a * b); }
            public int[] Tuple(int idx) { var t = new int[Inv.Length]; for (int i = Inv.Length - 1; i >= 0; i--) { t[i] = idx % Inv[i]; idx /= Inv[i]; } return t; }
            private int Ix(int[] t) { int x = 0; for (int i = 0; i < Inv.Length; i++) { int c = ((t[i] % Inv[i]) + Inv[i]) % Inv[i]; x = x * Inv[i] + c; } return x; }
            // The r generators e_0..e_{r-1} (e_i = 1 in invariant-factor slot i, 0 elsewhere); together with 0 they
            // anchor an affine frame for the emit's base segment. Rank r = Inv.Length.
            public int[] Generators() { var g = new int[Inv.Length]; for (int i = 0; i < Inv.Length; i++) { var t = new int[Inv.Length]; t[i] = 1; g[i] = Ix(t); } return g; }
            public int Add(int a, int b) { var ta = Tuple(a); var tb = Tuple(b); var tc = new int[Inv.Length]; for (int i = 0; i < Inv.Length; i++) tc[i] = ta[i] + tb[i]; return Ix(tc); }
            public int Neg(int a) { var ta = Tuple(a); var tc = new int[Inv.Length]; for (int i = 0; i < Inv.Length; i++) tc[i] = -ta[i]; return Ix(tc); }
            public int ScalarMul(int a, long k) { var ta = Tuple(a); var tc = new int[Inv.Length]; for (int i = 0; i < Inv.Length; i++) tc[i] = (int)(((k % Inv[i]) * ta[i]) % Inv[i]); return Ix(tc); }
            public int Order(int a) { int o = 1, x = a; while (x != 0) { x = Add(x, a); o++; } return o; }
            public int Annih(long d) { int c = 0; for (int a = 0; a < N; a++) if (d % Order(a) == 0) c++; return c; }
            public string OrderProfile()
            {
                var h = new SortedDictionary<int, int>();
                for (int a = 0; a < N; a++) { int o = Order(a); h[o] = h.TryGetValue(o, out var c) ? c + 1 : 1; }
                return string.Join(",", h.Select(kv => $"{kv.Key}^{kv.Value}"));
            }
            /// <summary>The min y with d·y = b in A (componentwise), or null if unsolvable.</summary>
            public int? SolveScalar(long d, int b)
            {
                var tb = Tuple(b); var ty = new int[Inv.Length];
                for (int i = 0; i < Inv.Length; i++)
                {
                    int e = Inv[i]; int di = (int)(((d % e) + e) % e);
                    int g = Gcd(di, e);
                    if (tb[i] % g != 0) return null;
                    int ep = e / g;
                    int inv = ModInv(((di / g) % ep + ep) % ep, ep);
                    ty[i] = (int)((long)(tb[i] / g % ep) * inv % ep);
                }
                return Ix(ty);
            }
        }

        // recover A ≅ ⊕Z/Inv from the order-profile fingerprint (RM-3): enumerate the
        // abelian groups of order |A| and return the one whose profile matches.
        internal static Ring? RecoverRing(int aSize, string orderProfile)
        {
            foreach (var inv in AbelianGroupsOfOrder(aSize))
            {
                var r = new Ring(inv);
                if (r.OrderProfile() == orderProfile) return r;
            }
            return null;
        }

        // U·M·V = D (diagonal invariant factors d[0]|d[1]|…), U ∈ GL_m(Z), V ∈ GL_nW(Z).
        // BigInteger arithmetic: integer Smith's transform entries can explode past `long` on the large
        // (all-middles) constraint systems the ring emit builds; they are reduced mod |A| only when applied.
        internal static (BigInteger[,] U, BigInteger[,] V, BigInteger[] d, int rank) SmithWithTransforms(long[,] M0)
        {
            int m = M0.GetLength(0), nn = M0.GetLength(1);
            var M = new BigInteger[m, nn];
            for (int i = 0; i < m; i++) for (int j = 0; j < nn; j++) M[i, j] = M0[i, j];
            var U = Identity(m); var V = Identity(nn);
            int t = 0;
            while (t < Math.Min(m, nn))
            {
                int pi = -1, pj = -1;
                for (int i = t; i < m && pi < 0; i++) for (int j = t; j < nn; j++) if (M[i, j] != 0) { pi = i; pj = j; break; }
                if (pi < 0) break;
                if (pi != t) { SwapRows(M, t, pi, nn); SwapRows(U, t, pi, m); }
                if (pj != t) { SwapCols(M, t, pj, m); SwapCols(V, t, pj, nn); }

                bool clean = false;
                while (!clean)
                {
                    clean = true;
                    for (int i = t + 1; i < m; i++)
                        if (M[i, t] != 0)
                        {
                            BigInteger q = M[i, t] / M[t, t];
                            for (int k = 0; k < nn; k++) M[i, k] -= q * M[t, k];
                            for (int k = 0; k < m; k++) U[i, k] -= q * U[t, k];
                            if (M[i, t] != 0) { SwapRows(M, t, i, nn); SwapRows(U, t, i, m); clean = false; }
                        }
                    for (int j = t + 1; j < nn; j++)
                        if (M[t, j] != 0)
                        {
                            BigInteger q = M[t, j] / M[t, t];
                            for (int k = 0; k < m; k++) M[k, j] -= q * M[k, t];
                            for (int k = 0; k < nn; k++) V[k, j] -= q * V[k, t];
                            if (M[t, j] != 0) { SwapCols(M, t, j, m); SwapCols(V, t, j, nn); clean = false; }
                        }
                }
                bool div = true;
                for (int i = t + 1; i < m && div; i++)
                    for (int j = t + 1; j < nn && div; j++)
                        if (M[i, j] % M[t, t] != 0)
                        {
                            for (int k = 0; k < nn; k++) M[t, k] += M[i, k];
                            for (int k = 0; k < m; k++) U[t, k] += U[i, k];
                            div = false;
                        }
                if (!div) continue;
                t++;
            }
            var d = new BigInteger[t];
            for (int i = 0; i < t; i++) d[i] = BigInteger.Abs(M[i, i]);
            // fold sign of |d[i]| back into U so U·M·V = D exactly with nonneg diagonal.
            for (int i = 0; i < t; i++) if (M[i, i] < 0) for (int k = 0; k < m; k++) U[i, k] = -U[i, k];
            return (U, V, d, t);
        }

        /// <summary>|{x ∈ A^nW : Mx = 0}| via Smith: Π annih_A(d_i) · |A|^(nW−rank). Rigid ⟺ 1.</summary>
        internal static long KernelSizeOverA(long[,] M, Ring A)
        {
            int nW = M.GetLength(1);
            var (_, _, d, rank) = SmithWithTransforms(M);
            long size = 1;
            for (int i = 0; i < nW - rank; i++) size *= A.N;
            foreach (var di in d) size *= A.Annih((long)di);
            return size;
        }

        /// <summary>Solve M x = target over A (one solution; unique when rigid), or null if unsolvable.</summary>
        internal static int[]? SolveOverA(long[,] M, int[] target, Ring A)
        {
            int m = M.GetLength(0), nW = M.GetLength(1);
            var (U, V, d, rank) = SmithWithTransforms(M);
            var tprime = MatVecZ(U, target, A);          // U·target ∈ A^m
            var y = new int[nW];
            for (int i = 0; i < rank; i++)
            {
                var yi = A.SolveScalar((long)d[i], tprime[i]);
                if (yi == null) return null;
                y[i] = yi.Value;
            }
            for (int i = rank; i < m; i++) if (tprime[i] != 0) return null;   // inconsistent
            return MatVecZ(V, y, A);                      // x = V·y ∈ A^nW
        }

        // integer-matrix × A-vector (Σ scalar-muls); entries reduced mod |A| (safe: scalar-mult in A
        // depends only on the coefficient mod each invariant factor, and Inv[i] | N).
        private static int[] MatVecZ(BigInteger[,] Mz, int[] x, Ring A)
        {
            int r = Mz.GetLength(0), c = Mz.GetLength(1);
            var res = new int[r];
            for (int i = 0; i < r; i++)
            {
                int s = 0;
                for (int j = 0; j < c; j++)
                {
                    if (Mz[i, j].IsZero) continue;
                    long k = (long)(((Mz[i, j] % A.N) + A.N) % A.N);
                    if (k != 0) s = A.Add(s, A.ScalarMul(x[j], k));
                }
                res[i] = s;
            }
            return res;
        }

        private static BigInteger[,] Identity(int k) { var a = new BigInteger[k, k]; for (int i = 0; i < k; i++) a[i, i] = 1; return a; }
        private static void SwapRows(BigInteger[,] M, int a, int b, int cols) { for (int k = 0; k < cols; k++) (M[a, k], M[b, k]) = (M[b, k], M[a, k]); }
        private static void SwapCols(BigInteger[,] M, int a, int b, int rows) { for (int k = 0; k < rows; k++) (M[k, a], M[k, b]) = (M[k, b], M[k, a]); }
        private static int ModInv(int a, int m) { if (m == 1) return 0; int g = m, x = 0, x1 = 1, aa = a; while (aa > 1) { int q = aa / g; (aa, g) = (g, aa - q * g); (x1, x) = (x, x1 - q * x); } return (x1 % m + m) % m; }

        // abelian groups of order N, as invariant-factor sequences (d_0 | d_1 | …).
        private static IEnumerable<int[]> AbelianGroupsOfOrder(int N)
        {
            var primePowers = new List<(int p, int e)>();
            int nn = N;
            for (int p = 2; p * p <= nn; p++) { int e = 0; while (nn % p == 0) { nn /= p; e++; } if (e > 0) primePowers.Add((p, e)); }
            if (nn > 1) primePowers.Add((nn, 1));
            // per prime: each partition of e ⟹ a descending list of exponents.
            var perPrime = primePowers.Select(pe => Partitions(pe.e).Select(part => (pe.p, part)).ToList()).ToList();
            foreach (var combo in CartesianProduct(perPrime))
            {
                // merge into invariant factors: d_k = Π_p p^{k-th largest part of p} (pad with 0).
                int len = combo.Max(c => c.part.Count);
                var d = new int[len];
                for (int k = 0; k < len; k++) { int f = 1; foreach (var (p, part) in combo) { int ex = k < part.Count ? part[k] : 0; for (int t = 0; t < ex; t++) f *= p; } d[k] = f; }
                Array.Reverse(d);   // invariant factors ascending (d_0 | d_1 | …)
                yield return d.Where(x => x > 1).DefaultIfEmpty(N).ToArray();
            }
        }
        private static IEnumerable<List<int>> Partitions(int e) => PartitionsFrom(e, e);
        private static IEnumerable<List<int>> PartitionsFrom(int e, int max)
        {
            if (e == 0) { yield return new List<int>(); yield break; }
            for (int first = Math.Min(e, max); first >= 1; first--)
                foreach (var rest in PartitionsFrom(e - first, first)) { var l = new List<int> { first }; l.AddRange(rest); yield return l; }
        }
        private static IEnumerable<List<(int p, List<int> part)>> CartesianProduct(List<List<(int p, List<int> part)>> lists)
        {
            var acc = new List<List<(int, List<int>)>> { new List<(int, List<int>)>() };
            foreach (var list in lists)
            {
                var next = new List<List<(int, List<int>)>>();
                foreach (var a in acc) foreach (var item in list) { var l = new List<(int, List<int>)>(a) { item }; next.Add(l); }
                acc = next;
            }
            return acc;
        }

        private static int PermOrder(int[] perm)
        {
            int n = perm.Length; var seen = new bool[n]; int ord = 1;
            for (int i = 0; i < n; i++)
            {
                if (seen[i]) continue;
                int len = 0, j = i;
                while (!seen[j]) { seen[j] = true; j = perm[j]; len++; }
                ord = Lcm(ord, len);
            }
            return ord;
        }
        private static int Gcd(int a, int b) { while (b != 0) { (a, b) = (b, a % b); } return a < 0 ? -a : a; }
        private static int Lcm(int a, int b) => a / Gcd(a, b) * b;
    }
}
