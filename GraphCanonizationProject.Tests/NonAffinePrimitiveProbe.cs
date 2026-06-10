using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Xunit;
using Xunit.Abstractions;

// ─────────────────────────────────────────────────────────────────────────────
// Non-affine primitive probe — the LAST untested empirical axis for G2-B
// (docs/chain-descent-seal-handoff.md §G2 board step 2.4 strand (b);
//  chain-descent-self-detection-plan.md §12.4).
//
// CONTEXT.  The oracle-capability seal closes iff the leak quadrant G2-B is empty:
// a *small, primitive, non-abelian, non-recovering* schurian scheme.  Two prior
// instruments found NO witness — the Hanaki–Miyamoto catalogue (CatalogueSchemeProbe,
// orders 5–30, all 481 primitives recover) and the affine sweep (AffineSchemeProbe,
// ΓL(1,2^d) + non-solvable A_n deleted modules).  But BOTH sweep the `G0` axis of
// *affine / translation* schemes V⋊G0; they do NOT test the non-affine *action* axis
// (almost-simple primitive groups acting on a structured point set, not on a vector
// space).  A second deep-research literature pass (2026-06-10) confirmed the depth
// bound is uncited and witnessless through the 2-closure / algebraic-gap framings too,
// leaving this empirical axis as the only remaining cheap lever.
//
// THE TEST.  For each almost-simple primitive group G acting on Ω (here PGL(2,p) on
// 2-subsets of the projective line — non-affine, poly-order |G|=p(p²−1)≈n^1.5,
// non-abelian) build its ORBITAL scheme (the G-orbits on
// Ω×Ω) and measure recovery, with the SAME proxies as the affine/catalogue probes:
//   • EdgeGenerates  — depth-1 algebraic recovery (intersection-number isolation).
//   • WLDepth        — # individualizations to discretize by 1-WL (the s(C) / WL-dim proxy).
//   • SeparatesAtBoundedBase — warmRefine from a base of size ≤ ⌈log₂n⌉+2 reaches discrete
//     (the EXACT Lean object; primitive ⟹ separates is the open G2-B kernel).
// A *primitive, non-abelian, non-separating* orbital scheme would be a non-affine G2-B
// witness (a seal counterexample / statement change).  Finding NONE strengthens
// G2-B emptiness on the one axis the affine + catalogue probes left untested.
//
// The general relation-table measurement core (BuildScheme / Primitive / EdgeGenerates /
// WLDepth / DiscretizePath / HasProperBlock) is the same logic as CatalogueSchemeProbe
// (each probe is self-contained by convention); the ONE new piece is OrbitalTable —
// orbits of the diagonal group action on ordered pairs → relation matrix (the "general
// 2D-orbital infra" the docs flag).  No production code is touched.
// ─────────────────────────────────────────────────────────────────────────────
public class NonAffinePrimitiveProbe(ITestOutputHelper output)
{
    sealed class Scheme
    {
        public required int N;
        public required int Rank;
        public required int[,] Rel;        // Rel[i,j] = relation index of pair (i,j)
        public required int[] Valency;
        public required int[,,] P;         // P[k,i,j] = p^k_{ij}
        public required bool Symmetric;
    }

    // ── THE NEW PIECE: orbital relation table from permutation-group generators ──
    // Orbits of the diagonal action g·(i,j) = (g(i), g(j)) of ⟨gens⟩ on ordered pairs.
    // For a transitive group the diagonal {(i,i)} is a single orbital ⟹ a valid
    // homogeneous coherent configuration; BuildScheme relabels the diagonal to R_0.
    static int[,] OrbitalTable(List<int[]> gens, int n)
    {
        var rel = new int[n, n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) rel[i, j] = -1;
        int next = 0;
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
            {
                if (rel[i, j] != -1) continue;
                int id = next++;
                var q = new Queue<(int, int)>(); q.Enqueue((i, j)); rel[i, j] = id;
                while (q.Count > 0)
                {
                    var (a, b) = q.Dequeue();
                    foreach (var g in gens)
                    {
                        int ga = g[a], gb = g[b];
                        if (rel[ga, gb] == -1) { rel[ga, gb] = id; q.Enqueue((ga, gb)); }
                    }
                }
            }
        return rel;
    }

    // Symmetrize the directed orbital scheme to the UNDIRECTED scheme: G-orbits on
    // *unordered* pairs (merge each relation with its transpose).  This is the
    // symmetric association scheme that is the seal's actual residual object for an
    // undirected graph; BuildScheme then validates it is a coherent (well-defined
    // intersection numbers) homogeneous scheme.
    static int[,] Symmetrize(int[,] rel, int n)
    {
        var trans = new Dictionary<int, int>();     // orbital k ↦ its transpose orbital
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) trans[rel[i, j]] = rel[j, i];
        var canon = new Dictionary<int, int>();
        foreach (var kv in trans) canon[kv.Key] = Math.Min(kv.Key, kv.Value);
        var sym = new int[n, n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) sym[i, j] = canon[rel[i, j]];
        return sym;
    }

    // ── General-scheme measurement core (same logic as CatalogueSchemeProbe) ────
    static Scheme? BuildScheme(int[,] M, int n)
    {
        int diag = M[0, 0];
        var labels = new SortedSet<int>();
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) labels.Add(M[i, j]);
        var remap = new Dictionary<int, int> { [diag] = 0 };
        int next = 1;
        foreach (var v in labels) if (v != diag) remap[v] = next++;
        int rank = remap.Count;
        var rel = new int[n, n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) rel[i, j] = remap[M[i, j]];

        for (int i = 0; i < n; i++)
        {
            if (rel[i, i] != 0) return null;
            for (int j = 0; j < n; j++) if (i != j && rel[i, j] == 0) return null;
        }

        var val = new int[rank];
        for (int j = 0; j < n; j++) val[rel[0, j]]++;
        for (int i = 1; i < n; i++)
        {
            var v = new int[rank];
            for (int j = 0; j < n; j++) v[rel[i, j]]++;
            for (int k = 0; k < rank; k++) if (v[k] != val[k]) return null;
        }

        var P = new int[rank, rank, rank];
        for (int k = 0; k < rank; k++)
        {
            int rx = -1, ry = -1;
            for (int x = 0; x < n && rx < 0; x++) for (int y = 0; y < n; y++) if (rel[x, y] == k) { rx = x; ry = y; break; }
            for (int z = 0; z < n; z++) P[k, rel[rx, z], rel[z, ry]]++;
            for (int x = 0; x < n; x++)
            {
                for (int y = 0; y < n; y++)
                {
                    if (rel[x, y] != k || (x == rx && y == ry)) continue;
                    var qq = new int[rank, rank];
                    for (int z = 0; z < n; z++) qq[rel[x, z], rel[z, y]]++;
                    for (int i = 0; i < rank; i++) for (int j = 0; j < rank; j++) if (qq[i, j] != P[k, i, j]) return null;
                    goto nextK;
                }
            }
            nextK:;
        }

        bool sym = true;
        for (int i = 0; i < n && sym; i++) for (int j = 0; j < n; j++) if (rel[i, j] != rel[j, i]) { sym = false; break; }

        return new Scheme { N = n, Rank = rank, Rel = rel, Valency = val, P = P, Symmetric = sym };
    }

    // Primitive ⟺ every non-diagonal relation graph is connected (relation-graph form).
    static bool Primitive(Scheme s)
    {
        for (int k = 1; k < s.Rank; k++)
        {
            var seen = new bool[s.N]; var st = new Stack<int>(); st.Push(0); seen[0] = true; int c = 1;
            while (st.Count > 0) { int x = st.Pop(); for (int y = 0; y < s.N; y++) if (!seen[y] && s.Rel[x, y] == k) { seen[y] = true; c++; st.Push(y); } }
            if (c != s.N) return false;
        }
        return true;
    }

    // The smallest ClosedSubset containing {0,k}; ⟨0,k⟩ proper ⟺ R_k generates a block.
    static HashSet<int> GeneratedClosedSubset(Scheme s, int k)
    {
        var I = new HashSet<int> { 0, k };
        bool grew = true;
        while (grew)
        {
            grew = false;
            var add = new List<int>();
            foreach (int i in I) foreach (int j in I)
                for (int m = 0; m < s.Rank; m++)
                    if (s.P[m, i, j] != 0 && !I.Contains(m)) add.Add(m);
            foreach (int m in add) if (I.Add(m)) grew = true;
        }
        return I;
    }

    // ClosedSubset-primitivity (Lean IsPrimitive): no relation generates a proper block.
    static bool HasProperBlock(Scheme s)
    {
        for (int k = 1; k < s.Rank; k++)
            if (GeneratedClosedSubset(s, k).Count < s.Rank) return true;
        return false;
    }

    static bool EdgeGenerates(Scheme s, int j0)
    {
        var iso = new bool[s.Rank]; iso[0] = true; int count = 1;
        if (j0 != 0) { iso[j0] = true; count = 2; }
        bool progress = true;
        while (progress && count < s.Rank)
        {
            progress = false;
            var isoList = new List<int>(); for (int l = 0; l < s.Rank; l++) if (iso[l]) isoList.Add(l);
            string Sig(int i)
            {
                var sb = new StringBuilder();
                sb.Append(i == j0 ? '1' : '0');
                foreach (int l in isoList) { sb.Append(':'); sb.Append(s.P[i, l, j0]); }
                return sb.ToString();
            }
            var sig = new string[s.Rank];
            var seen = new Dictionary<string, int>();
            for (int i = 1; i < s.Rank; i++) { sig[i] = Sig(i); seen[sig[i]] = seen.GetValueOrDefault(sig[i], 0) + 1; }
            for (int i = 1; i < s.Rank; i++)
                if (!iso[i] && seen[sig[i]] == 1) { iso[i] = true; count++; progress = true; }
        }
        return count == s.Rank;
    }

    static bool Recovers(Scheme s) { for (int j0 = 1; j0 < s.Rank; j0++) if (EdgeGenerates(s, j0)) return true; return false; }

    static int[] Refine(Scheme s, List<int> ind)
    {
        int n = s.N;
        var color = new int[n];
        for (int i = 0; i < ind.Count; i++) color[ind[i]] = i + 1;
        int prev = color.Distinct().Count();
        while (true)
        {
            var sig = new (int, string)[n];
            for (int v = 0; v < n; v++)
            {
                var ms = new List<(int, int)>();
                for (int u = 0; u < n; u++) if (u != v) ms.Add((s.Rel[v, u], color[u]));
                ms.Sort();
                sig[v] = (color[v], string.Join(";", ms.Select(t => $"{t.Item1},{t.Item2}")));
            }
            var map = new Dictionary<(int, string), int>(); int next = 0; var nc = new int[n];
            foreach (var v in Enumerable.Range(0, n).OrderBy(v => sig[v].Item1).ThenBy(v => sig[v].Item2))
            { if (!map.TryGetValue(sig[v], out int c)) { c = next++; map[sig[v]] = c; } nc[v] = c; }
            int d2 = nc.Distinct().Count(); color = nc;
            if (d2 == prev) break;
            prev = d2;
        }
        return color;
    }

    static int WLDepth(Scheme s, int cap)
    {
        int n = s.N;
        var ind = new List<int>();
        for (int depth = 0; depth <= cap; depth++)
        {
            var color = Refine(s, ind);
            if (color.Distinct().Count() == n) return depth;
            var byColor = new Dictionary<int, List<int>>();
            for (int v = 0; v < n; v++) { if (!byColor.TryGetValue(color[v], out var lst)) { lst = new(); byColor[color[v]] = lst; } lst.Add(v); }
            int target = -1, best = 1;
            foreach (var kv in byColor) if (kv.Value.Count > best) { best = kv.Value.Count; target = kv.Value.Min(); }
            if (target < 0) return depth;
            ind.Add(target);
        }
        return cap + 1;
    }

    // ── Permutation-group plumbing ─────────────────────────────────────────────
    static int[] Compose(int[] g, int[] e) { var c = new int[e.Length]; for (int i = 0; i < e.Length; i++) c[i] = g[e[i]]; return c; }
    static string Key(int[] p) => string.Join(",", p);

    // Order of ⟨gens⟩ on L points by closure (returns -1 if it exceeds cap).
    static long GroupOrder(List<int[]> gens, int L, long cap)
    {
        var id = Enumerable.Range(0, L).ToArray();
        var seen = new HashSet<string> { Key(id) };
        var frontier = new List<int[]> { id };
        long total = 1;
        while (frontier.Count > 0)
        {
            var nf = new List<int[]>();
            foreach (var e in frontier)
                foreach (var g in gens)
                {
                    var c = Compose(g, e);
                    if (seen.Add(Key(c))) { nf.Add(c); if (++total > cap) return -1; }
                }
            frontier = nf;
        }
        return total;
    }

    static bool Commute(int[] a, int[] b)
    {
        for (int i = 0; i < a.Length; i++) if (a[b[i]] != b[a[i]]) return false;
        return true;
    }

    // ── PSL(2,p) on the projective line P^1(F_p) (points 0..p-1 = field, p = ∞) ──
    static int ModPow(long a, long e, long p) { long r = 1; a %= p; while (e > 0) { if ((e & 1) != 0) r = r * a % p; a = a * a % p; e >>= 1; } return (int)r; }
    static int ModInv(int a, int p) => ModPow(((a % p) + p) % p, p - 2, p);
    static int NonResidue(int p) { for (int g = 2; g < p; g++) if (ModPow(g, (p - 1) / 2, p) == p - 1) return g; return 1; }

    // Möbius map z ↦ (az+b)/(cz+d) as a permutation of the p+1 projective points.
    static int[] Mobius(int a, int b, int c, int d, int p)
    {
        int L = p + 1, inf = p;
        var perm = new int[L];
        for (int z = 0; z < p; z++)
        {
            int den = (((long)c * z + d) % p + p) % p == 0 ? 0 : (int)((((long)c * z + d) % p + p) % p);
            if (den == 0) perm[z] = inf;
            else { int num = (int)((((long)a * z + b) % p + p) % p); perm[z] = (int)((long)num * ModInv(den, p) % p); }
        }
        perm[inf] = (c == 0) ? inf : (int)((long)a % p * ModInv(((c % p) + p) % p, p) % p);
        return perm;
    }

    // Lift a permutation of the L line-points to the action on unordered 2-subsets.
    static int[] LiftToPairs(int[] linePerm, List<(int, int)> pairs, Dictionary<(int, int), int> idx)
    {
        var pp = new int[pairs.Count];
        for (int t = 0; t < pairs.Count; t++)
        {
            int x = linePerm[pairs[t].Item1], y = linePerm[pairs[t].Item2];
            var key = x < y ? (x, y) : (y, x);
            pp[t] = idx[key];
        }
        return pp;
    }

    static (List<(int, int)> pairs, Dictionary<(int, int), int> idx) Pairs(int L)
    {
        var pairs = new List<(int, int)>();
        var idx = new Dictionary<(int, int), int>();
        for (int x = 0; x < L; x++) for (int y = x + 1; y < L; y++) { idx[(x, y)] = pairs.Count; pairs.Add((x, y)); }
        return (pairs, idx);
    }

    // ── Self-test: S_m on 2-subsets = Johnson J(m,2) (rank-3, known valencies) ──
    [Fact]
    public void Probe_OrbitalBuilder_SelfTest()
    {
        output.WriteLine("── Orbital-builder self-test: S_m on 2-subsets = Johnson J(m,2) ──");
        foreach (int m in new[] { 5, 6, 7 })
        {
            var transp = Enumerable.Range(0, m).ToArray(); transp[0] = 1; transp[1] = 0; // (0 1)
            var cycle = new int[m]; for (int i = 0; i < m; i++) cycle[i] = (i + 1) % m;   // (0 1 .. m-1)
            var (pairs, idx) = Pairs(m);
            int deg = pairs.Count;
            var gens = new List<int[]> { LiftToPairs(transp, pairs, idx), LiftToPairs(cycle, pairs, idx) };
            var s = BuildScheme(OrbitalTable(gens, deg), deg);
            Assert.NotNull(s);
            int meet = 2 * (m - 2), disj = (m - 2) * (m - 3) / 2;
            var vals = s!.Valency.OrderByDescending(x => x).ToArray();
            output.WriteLine($"  m={m}  deg={deg}  rank={s.Rank}  symmetric={s.Symmetric}  valencies=[{string.Join(",", s.Valency)}]  (expect meet={meet}, disjoint={disj})");
            Assert.Equal(3, s.Rank);                       // J(m,2) is rank 3
            Assert.True(s.Symmetric);
            Assert.Contains(meet, s.Valency);
            Assert.Contains(disj, s.Valency);
            Assert.Equal(1, s.Valency[0]);                 // R_0 = diagonal
        }
    }

    // ── The probe: PSL(2,p) on 2-subsets — non-affine primitive, rank-sweeping ──
    [Fact]
    public void Probe_PGL2_OnPairs()
    {
        output.WriteLine("── Non-affine primitive G2-B probe: PGL(2,p) on 2-subsets of P^1(F_p) ──");
        output.WriteLine("    poly-order almost-simple, non-abelian; rank grows with p into the s(C)≥2 zone.");
        output.WriteLine($"    {"p",2} {"deg",5} {"|G|",8} {"dirR",5} {"symR",5} {"sym",4} {"primC",6} {"leanPrim",9} {"recov",6} {"WLdep",6} {"sepBnd",7} {"sepDep",7}  verdict");

        int witnesses = 0, primitiveTested = 0;
        foreach (int p in new[] { 5, 7, 11, 13, 17, 19, 23 })
        {
            int L = p + 1;
            // PGL(2,p) on P^1: z↦z+1, z↦-1/z, and z↦g·z (g a non-residue ⟹ PGL, which
            // is 3-transitive — more involutions, so its orbital scheme on unordered
            // pairs is more often a coherent symmetric scheme than PSL's).
            var A = Mobius(1, 1, 0, 1, p);
            var B = Mobius(0, p - 1, 1, 0, p);
            var D = Mobius(NonResidue(p), 0, 0, 1, p);
            var lineGens = new List<int[]> { A, B, D };
            long gOrder = GroupOrder(lineGens, L, 5_000_000);
            bool abelian = Commute(A, B);

            var (pairs, idx) = Pairs(L);
            int deg = pairs.Count;
            var pairGens = lineGens.Select(g => LiftToPairs(g, pairs, idx)).ToList();
            var directed = OrbitalTable(pairGens, deg);
            int dirRank = directed.Cast<int>().Max() + 1;     // rank of the directed orbital CC
            var s = BuildScheme(Symmetrize(directed, deg), deg);   // the seal-relevant UNDIRECTED scheme
            if (s is null) { output.WriteLine($"    {p,2} {deg,5} {gOrder,8} (dirRank {dirRank}) — symmetrized orbital scheme is not a coherent homogeneous scheme (skipped)"); continue; }

            bool primC = Primitive(s);
            bool leanPrim = !HasProperBlock(s);     // Lean IsPrimitive = no proper ClosedSubset
            bool recov = Recovers(s);
            int sepBound = (int)Math.Ceiling(Math.Log2(deg)) + 2;   // base+O(1), matches CatalogueSchemeProbe
            int wl = WLDepth(s, sepBound + 8);
            int sepDep = wl;   // greedy individualization-to-discreteness depth = SeparatesAtBoundedBase witness

            string verdict;
            if (leanPrim)
            {
                primitiveTested++;
                bool separates = sepDep <= sepBound;
                if (separates) verdict = abelian ? "tame (abelian)" : "RECOVERS (no witness)";
                else { verdict = "*** G2-B CANDIDATE (primitive, non-separating) ***"; witnesses++; }
            }
            else verdict = "imprimitive (→ hImprim, not G2-B)";

            output.WriteLine($"    {p,2} {deg,5} {gOrder,8} {dirRank,5} {s.Rank,5} {(s.Symmetric ? "y" : "n"),4} {(primC ? "y" : "n"),6} {(leanPrim ? "y" : "n"),9} {(recov ? "y" : "n"),6} {wl,6} {sepBound,7} {sepDep,7}  {verdict}");
        }

        output.WriteLine($"── primitive (Lean IsPrimitive) schemes tested: {primitiveTested};  G2-B witnesses (primitive + non-separating): {witnesses} ──");
        output.WriteLine("    A witness here would be a NON-AFFINE primitive seal counterexample (statement change).");
        output.WriteLine("    CAVEAT: these are HIGH-rank schemes (rank grows with p), so depth-2 recovery is partly");
        output.WriteLine("    'easy' (many colours). The result covers the non-affine ALMOST-SIMPLE axis at orders 28–276");
        output.WriteLine("    (beyond the catalogue's ≤30); the small-Aut RANK-4-AMORPHIC zone at large n stays the heavier");
        output.WriteLine("    follow-up (PSL(2,q) on A5/S4 cosets, or classical-group rank-3/4 geometries).");
        Assert.Equal(0, witnesses);   // every primitive non-affine orbital scheme separates at base+O(1)
    }
}
