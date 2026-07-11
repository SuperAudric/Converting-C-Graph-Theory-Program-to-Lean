using System;
using System.Collections.Generic;
using System.Linq;

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
        public static RingResidue? Recover(int[] adj, int n, int[] cellOf, int numCells)
        {
            var side = Bipartition(adj, n);
            if (side == null) return null;                       // not bipartite ⟹ not a multipede

            var members = new List<int>[numCells];
            for (int c = 0; c < numCells; c++) members[c] = new List<int>();
            for (int v = 0; v < n; v++) members[cellOf[v]].Add(v);

            // Segment side = the higher AVERAGE-per-vertex-degree side: segment-states touch many
            // gadget-tuples (high degree); gadget-tuples touch only their arity of segments (low
            // degree). NB total degree per side is equal in a bipartite graph — the average is the
            // discriminator (fewer high-degree segments vs many low-degree tuples).
            var totalDeg = new long[2]; var count = new long[2];
            for (int v = 0; v < n; v++)
            {
                int d = 0; for (int w = 0; w < n; w++) d += adj[v * n + w];
                totalDeg[side[v]] += d; count[side[v]]++;
            }
            double avg0 = count[0] > 0 ? (double)totalDeg[0] / count[0] : 0;
            double avg1 = count[1] > 0 ? (double)totalDeg[1] / count[1] : 0;
            int segSide = avg0 >= avg1 ? 0 : 1;

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

        // ── RM-3: ring order-profile from one degree-3 gadget's sum-zero Latin square ─
        private static string? InferOrderProfile(int[] adj, int n, int[] segOf, int[] localOf, int Asz)
        {
            var byLine = new Dictionary<string, List<int>>();
            for (int v = 0; v < n; v++)
            {
                if (segOf[v] != -1) continue;
                var segSet = new SortedSet<int>();
                for (int w = 0; w < n; w++) if (adj[v * n + w] == 1 && segOf[w] != -1) segSet.Add(segOf[w]);
                if (segSet.Count != 3) continue;
                var key = string.Join(",", segSet);
                if (!byLine.TryGetValue(key, out var l)) byLine[key] = l = new List<int>();
                l.Add(v);
            }

            foreach (var kv in byLine)
            {
                if (kv.Value.Count != Asz * Asz) continue;       // a full degree-3 line
                var sids = kv.Key.Split(',').Select(int.Parse).ToArray();
                int s0 = sids[0], s1 = sids[1], s2 = sids[2];
                var L = new int[Asz, Asz];
                var filled = new bool[Asz, Asz];
                bool ok = true;
                foreach (int gv in kv.Value)
                {
                    int x = -1, y = -1, z = -1;
                    for (int w = 0; w < n; w++)
                    {
                        if (adj[gv * n + w] != 1 || segOf[w] == -1) continue;
                        if (segOf[w] == s0) x = localOf[w]; else if (segOf[w] == s1) y = localOf[w]; else if (segOf[w] == s2) z = localOf[w];
                    }
                    if (x < 0 || y < 0 || z < 0 || filled[x, y]) { ok = false; break; }
                    L[x, y] = z; filled[x, y] = true;
                }
                if (!ok) continue;

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
