using System;
using System.Collections.Generic;
using System.Linq;

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    // Flip-validation canonizer: a two-pass design aimed at polynomial worst-
    // case time. See docs/flip-validation-strategy.md for the full design.
    //
    // ── Algorithm at a glance ────────────────────────────────────────────────
    //   Forward pass: greedily walk the search tree. At each step pick one
    //     iso-invariant single-pair guess (within-cell if any cell has an
    //     internal Unknown pair, else between-cell on a P-incomparable cell
    //     pair), write it into P, run transitive closure, push a Primary
    //     record. Repeat until P is total.
    //   Backward pass: walk the primary stack deepest-to-shallowest. Each
    //     primary is validated by the transposition automorphism test; if it
    //     passes, the guess was an arbitrary tie-break of a true symmetry —
    //     lock. If it fails, flip the direction, attempt to keep the deeper
    //     primaries (a deeper primary may now have its pair pre-resolved or
    //     contradicted, in which case the deeper lock counts as broken and
    //     the forward pass is rerun from the breakage), lex-min the
    //     resulting canonical matrices, and adopt the winner.
    //
    // ── v1 simplifications (see §10/§11 of the strategy doc) ────────────────
    //   - DERIVED closure records are not tracked; transitive closure is
    //     re-run from scratch on each replay. Constant-factor cost increase,
    //     polynomial preserved.
    //   - The local orbit test is exactly the transposition test (§3.6
    //     practical note: single-pair guesses always individualise both
    //     endpoints into singleton sub-cells, so the sub-tree pairing
    //     collapses to (a, b)).
    //   - When a shallow flip invalidates a deeper guess's pair, the
    //     algorithm re-runs ContinueForward from the breakage. The more
    //     surgical "detect-and-redo only affected locks" fallback from
    //     §6.3 is deferred to a later version.
    //
    // ── Diagnostic counters ─────────────────────────────────────────────────
    //   Public properties below are updated by Run() and reflect the LAST
    //   run, cumulative across forward pass plus backward-pass re-runs.
    //   The locked-then-invalidated counter is the single most diagnostic
    //   per §9 of the strategy doc.
    public sealed class CanonGraphOrdererFlipValidation : ICanonGraphOrderer
    {
        private const sbyte LESS = -1, UNKNOWN = 0, GREATER = 1;

        // Diagnostic counters from the last Run() call.
        public int LastPrimaryCount { get; private set; }
        public int LastWithinCellGuesses { get; private set; }
        public int LastBetweenCellGuesses { get; private set; }
        public int LastBackwardFlips { get; private set; }
        public int LastLockedThenInvalidated { get; private set; }

        public AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            int n = G.VertexCount;
            int[] adj = ExtractAdj(G);

            LastWithinCellGuesses = 0;
            LastBetweenCellGuesses = 0;
            LastBackwardFlips = 0;
            LastLockedThenInvalidated = 0;

            // Forward pass.
            sbyte[] p = SeedFromTypes(n, vertexTypes);
            List<Primary> record = ContinueForward(n, adj, p);

            // Backward pass.
            record = BackwardPass(n, adj, vertexTypes, record);
            LastPrimaryCount = record.Count;

            // Replay the (possibly updated) record and read off the canonical
            // form.
            sbyte[] pFinal = ReplayRecord(n, vertexTypes, record, record.Count)
                ?? throw new InvalidOperationException(
                    "FlipValidation: final replay produced a contradiction");
            if (!IsTotal(n, pFinal))
                throw new InvalidOperationException("FlipValidation: final P not total");

            return PermuteByPartialOrder(G, pFinal, n);
        }

        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // ── Internal record ──────────────────────────────────────────────────

        private struct Primary
        {
            public int A, B;
            public sbyte Direction;   // LESS (A<B) or GREATER (A>B)
            public bool BetweenCell;  // false = within-cell, true = between-cell
        }

        // ── Forward pass ─────────────────────────────────────────────────────

        // Walk P toward total via single-pair guesses; mutate p, return the
        // primaries pushed (in order).
        private List<Primary> ContinueForward(int n, int[] adj, sbyte[] p)
        {
            var record = new List<Primary>();
            while (!IsTotal(n, p))
            {
                if (!PickAndApplyGuess(n, adj, p, record))
                    throw new InvalidOperationException(
                        "FlipValidation: P not total but no guess candidate found");
            }
            return record;
        }

        // Pick the next primary guess (within-cell first, else between-cell),
        // apply it to p, and push it onto record. Returns false only if there
        // really is no candidate, which is a bug given P is not total.
        private bool PickAndApplyGuess(int n, int[] adj, sbyte[] p, List<Primary> record)
        {
            int[] cellOf = Refine(n, adj, p);
            int numCells = cellOf.Max() + 1;
            var cells = new List<List<int>>(numCells);
            for (int c = 0; c < numCells; c++) cells.Add(new List<int>());
            for (int v = 0; v < n; v++) cells[cellOf[v]].Add(v);

            if (TryFindWithinCellGuess(n, p, cells, numCells, out int a, out int b))
            {
                var prim = new Primary { A = a, B = b, Direction = LESS, BetweenCell = false };
                if (!ApplyOne(p, n, prim))
                    throw new InvalidOperationException(
                        "FlipValidation: within-cell guess produced a contradiction");
                record.Add(prim);
                LastWithinCellGuesses++;
                return true;
            }

            if (TryFindBetweenCellGuess(n, p, cellOf, cells, numCells, out a, out b))
            {
                var prim = new Primary { A = a, B = b, Direction = LESS, BetweenCell = true };
                if (!ApplyOne(p, n, prim))
                    return false; // contradiction on between-cell closure; caller decides
                record.Add(prim);
                LastBetweenCellGuesses++;
                return true;
            }

            return false;
        }

        // Lex-min cell (by canonical id) that holds an internal Unknown pair;
        // within it, lex-min (a, b) by vertex index.
        //
        // This rule is NOT iso-invariant on cells that contain multiple pair-
        // orbits — different input scramblings can pick representatives in
        // different pair-orbits and the backward pass cannot recover from
        // that with direction flips alone. See the strategy doc §6.1 / §11
        // for the limitation; the planned future mechanism is to ensure
        // every canonical form is reachable from any pair selection (the
        // "one guess per symmetry" invariant), which is not yet
        // implemented. The current rule is left simple on purpose so that
        // the failure pattern is visible in the test bed.
        private static bool TryFindWithinCellGuess(int n, sbyte[] p,
                                                   List<List<int>> cells, int numCells,
                                                   out int a, out int b)
        {
            a = -1; b = -1;
            for (int c = 0; c < numCells; c++)
            {
                var mem = cells[c];
                if (mem.Count < 2) continue;
                for (int i = 0; i < mem.Count; i++)
                    for (int j = i + 1; j < mem.Count; j++)
                        if (p[mem[i] * n + mem[j]] == UNKNOWN)
                        {
                            a = mem[i]; b = mem[j];
                            return true;
                        }
            }
            return false;
        }

        // Lex-min P-incomparable cell pair (by canonical cell id), then lex-min
        // representative pair (x, y) within it by vertex index. Same iso-
        // invariance limitation as the within-cell case.
        private static bool TryFindBetweenCellGuess(int n, sbyte[] p, int[] cellOf,
                                                    List<List<int>> cells, int numCells,
                                                    out int a, out int b)
        {
            int bestCA = -1, bestCB = -1;
            for (int u = 0; u < n; u++)
                for (int v = 0; v < n; v++)
                {
                    if (cellOf[u] == cellOf[v] || p[u * n + v] != UNKNOWN) continue;
                    int c1 = Math.Min(cellOf[u], cellOf[v]);
                    int c2 = Math.Max(cellOf[u], cellOf[v]);
                    if (bestCA < 0 || c1 < bestCA || (c1 == bestCA && c2 < bestCB))
                    {
                        bestCA = c1; bestCB = c2;
                    }
                }

            if (bestCA < 0) { a = -1; b = -1; return false; }

            int xMin = -1, yMin = -1;
            foreach (int x in cells[bestCA])
                foreach (int y in cells[bestCB])
                {
                    if (p[x * n + y] != UNKNOWN) continue;
                    if (xMin < 0 || x < xMin || (x == xMin && y < yMin))
                    {
                        xMin = x; yMin = y;
                    }
                }

            a = xMin; b = yMin;
            return xMin >= 0;
        }

        // ── Backward pass ────────────────────────────────────────────────────

        // For each primary in reverse: validate via the transposition test; on
        // failure, try the flipped direction, take lex-min of the two resulting
        // canonical matrices. Deeper guesses are preserved when their pairs
        // remain applicable; broken deeper guesses bump the diagnostic counter
        // and the forward pass is re-run from the break point.
        private List<Primary> BackwardPass(int n, int[] adj, VertexType[] vertexTypes,
                                           List<Primary> record)
        {
            var current = new List<Primary>(record);

            for (int i = current.Count - 1; i >= 0; i--)
            {
                var primI = current[i];

                // P just after primary i was applied.
                sbyte[]? pAtI = ReplayRecord(n, vertexTypes, current, i + 1);
                if (pAtI == null) continue;

                // Transposition test on the current state. If σ = (a b) is an
                // automorphism of (adj, P_at_i), the guess was an arbitrary
                // tie-break of a true two-element orbit — lock it.
                if (TranspositionTest(primI.A, primI.B, pAtI, adj, n))
                    continue;

                // Otherwise, try the flipped direction.
                var flippedPrim = primI;
                flippedPrim.Direction = (sbyte)(-primI.Direction);

                var prefix = current.Take(i).ToList();
                prefix.Add(flippedPrim);

                var deeper = current.Skip(i + 1).ToList();
                var flippedFull = TryReplayWithDeeper(n, adj, vertexTypes, prefix, deeper,
                                                     out bool deeperBroken);
                if (flippedFull == null) continue; // flipped branch dead

                if (deeperBroken) LastLockedThenInvalidated++;

                // Compare canonical matrices and adopt the lex-smaller.
                sbyte[]? pCur = ReplayRecord(n, vertexTypes, current, current.Count);
                sbyte[]? pFlip = ReplayRecord(n, vertexTypes, flippedFull, flippedFull.Count);
                if (pCur == null || pFlip == null) continue;

                int[] permCur = ReadPermutation(n, pCur);
                int[] permFlip = ReadPermutation(n, pFlip);
                int[] matCur = BuildPermutedMatrix(adj, permCur, n);
                int[] matFlip = BuildPermutedMatrix(adj, permFlip, n);

                if (LexLess(matFlip, matCur))
                {
                    current = flippedFull;
                    LastBackwardFlips++;
                }
            }

            return current;
        }

        // Apply prefix; then try to apply deeper guesses one by one. If a
        // deeper guess can't be applied (its pair is no longer Unknown in the
        // current P), bump the broken flag and re-run ContinueForward to fill
        // out the remainder. The strategy doc allows this — the polynomial
        // bound costs more constant factor than the surgical §6.3 alt.
        private List<Primary>? TryReplayWithDeeper(int n, int[] adj, VertexType[] vertexTypes,
                                                   List<Primary> prefix, List<Primary> deeper,
                                                   out bool anyBroken)
        {
            anyBroken = false;
            sbyte[] p = SeedFromTypes(n, vertexTypes);
            var result = new List<Primary>(prefix.Count + deeper.Count);

            foreach (var prim in prefix)
            {
                if (!ApplyOne(p, n, prim)) return null;
                result.Add(prim);
            }

            foreach (var prim in deeper)
            {
                if (!ApplyOne(p, n, prim))
                {
                    anyBroken = true;
                    break;
                }
                result.Add(prim);
            }

            while (!IsTotal(n, p))
            {
                if (!PickAndApplyGuess(n, adj, p, result))
                    return null;
            }

            return result;
        }

        // ── Helpers ──────────────────────────────────────────────────────────

        // σ = (a b) — does swapping rows/columns a and b leave both the
        // adjacency matrix and the partial-order matrix unchanged? O(n²).
        // Sound but incomplete as an orbit test; incompleteness only triggers
        // a lex-min recompute that yields the same canonical form either way.
        private static bool TranspositionTest(int a, int b, sbyte[] p, int[] adj, int n)
        {
            for (int u = 0; u < n; u++)
            {
                int su = (u == a) ? b : (u == b ? a : u);
                for (int v = 0; v < n; v++)
                {
                    int sv = (v == a) ? b : (v == b ? a : v);
                    if (adj[u * n + v] != adj[su * n + sv]) return false;
                    if (p[u * n + v] != p[su * n + sv]) return false;
                }
            }
            return true;
        }

        // Apply one primary to p, transitively closing. Returns false on
        // contradiction (cycle or direction conflict). A "match in the same
        // direction" is treated as a no-op success (closure may have already
        // implied it).
        private static bool ApplyOne(sbyte[] p, int n, Primary prim)
        {
            sbyte cur = p[prim.A * n + prim.B];
            if (cur == prim.Direction) return true;
            if (cur != UNKNOWN) return false;
            p[prim.A * n + prim.B] = prim.Direction;
            p[prim.B * n + prim.A] = (sbyte)(-prim.Direction);
            return TransitiveClose(p, n);
        }

        // Replay the first `count` primaries from a record into a fresh P.
        // Returns null on contradiction.
        private static sbyte[]? ReplayRecord(int n, VertexType[] vertexTypes,
                                             List<Primary> record, int count)
        {
            sbyte[] p = SeedFromTypes(n, vertexTypes);
            int end = Math.Min(count, record.Count);
            for (int j = 0; j < end; j++)
                if (!ApplyOne(p, n, record[j])) return null;
            return p;
        }

        // Build the permuted adjacency matrix as a flat int[].
        private static int[] BuildPermutedMatrix(int[] adj, int[] perm, int n)
        {
            int[] m = new int[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    m[perm[i] * n + perm[j]] = adj[i * n + j];
            return m;
        }

        private static AdjMatrix PermuteByPartialOrder(AdjMatrix G, sbyte[] p, int n)
        {
            int[] perm = ReadPermutation(n, p);
            var result = new EdgeType[n, n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    result[perm[i], perm[j]] = G[i, j];
            return new AdjMatrix(result);
        }

        // ── Mirrored from CanonGraphOrdererPartialOrderSinglePair ────────────
        //
        // Refine / TransitiveClose / SeedFromTypes / IsTotal / ReadPermutation
        // / LexLess kept locally so this class is self-contained.

        private static int[] ExtractAdj(AdjMatrix G)
        {
            int n = G.VertexCount;
            var adj = new int[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    adj[i * n + j] = G[i, j];
            return adj;
        }

        private static sbyte[] SeedFromTypes(int n, int[] types)
        {
            var p = new sbyte[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (i != j && types[i] < types[j]) { p[i * n + j] = LESS; p[j * n + i] = GREATER; }
            TransitiveClose(p, n);
            return p;
        }

        private static bool TransitiveClose(sbyte[] p, int n)
        {
            for (int k = 0; k < n; k++)
                for (int i = 0; i < n; i++)
                {
                    if (p[i * n + k] != LESS) continue;
                    for (int j = 0; j < n; j++)
                    {
                        if (p[k * n + j] != LESS) continue;
                        if (i == j) return false;
                        sbyte cur = p[i * n + j];
                        if (cur == GREATER) return false;
                        if (cur == UNKNOWN) { p[i * n + j] = LESS; p[j * n + i] = GREATER; }
                    }
                }
            return true;
        }

        private static int[] Refine(int n, int[] adj, sbyte[] p)
        {
            int[] color = new int[n];
            while (true)
            {
                int[] next = RefineRound(n, adj, p, color);
                bool same = SamePartition(n, color, next);
                color = next;
                if (same) break;
            }
            return color;
        }

        private static int[] RefineRound(int n, int[] adj, sbyte[] p, int[] color)
        {
            var sigs = new string[n];
            for (int v = 0; v < n; v++)
            {
                var parts = new List<string>(n);
                for (int u = 0; u < n; u++)
                {
                    if (u == v) continue;
                    parts.Add(color[u] + "." + adj[v * n + u] + "." + ((int)p[v * n + u]));
                }
                parts.Sort(StringComparer.Ordinal);
                sigs[v] = color[v] + "/" + string.Join(",", parts);
            }

            var distinct = new List<string>(new HashSet<string>(sigs));
            distinct.Sort(StringComparer.Ordinal);
            var rank = new Dictionary<string, int>(distinct.Count);
            for (int i = 0; i < distinct.Count; i++) rank[distinct[i]] = i;

            var nextColor = new int[n];
            for (int v = 0; v < n; v++) nextColor[v] = rank[sigs[v]];
            return nextColor;
        }

        private static bool SamePartition(int n, int[] a, int[] b)
        {
            for (int i = 0; i < n; i++)
                for (int j = i + 1; j < n; j++)
                    if ((a[i] == a[j]) != (b[i] == b[j])) return false;
            return true;
        }

        private static bool IsTotal(int n, sbyte[] p)
        {
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if (i != j && p[i * n + j] == UNKNOWN) return false;
            return true;
        }

        private static int[] ReadPermutation(int n, sbyte[] p)
        {
            var perm = new int[n];
            for (int v = 0; v < n; v++)
            {
                int r = 0;
                for (int u = 0; u < n; u++)
                    if (p[u * n + v] == LESS) r++;
                perm[v] = r;
            }
            return perm;
        }

        private static bool LexLess(int[] a, int[] b)
        {
            for (int i = 0; i < a.Length; i++)
                if (a[i] != b[i]) return a[i] < b[i];
            return false;
        }
    }
}
