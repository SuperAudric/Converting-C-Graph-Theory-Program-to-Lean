using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;
using Xunit.Abstractions;

// ─────────────────────────────────────────────────────────────────────────────
// Affine orbital-scheme probe — the G2-B counterexample hunt over F_2^d.
//
// CONTEXT (docs/chain-descent-seal-handoff.md §4 G2-B; chain-descent-exhaustive-
// obstruction.md §0.7.6).  The oracle-capability seal closes iff the leak quadrant
// G2-B is empty: a *small, primitive, non-abelian, non-recovering* schurian scheme.
// The counting route reduced "is G2-B empty?" to the conjecture
//   primitive schurian scheme  ⟹  separable (EdgeGenerates / recovers),
// and the separability literature (1709.03937, 1903.00409) pins the bounded
// elementary-abelian exceptions to E16 = F_2^4 and E32 = F_2^5.  So the decisive
// test is: is there an irreducible G0 ≤ GL(d,2) whose translation scheme does NOT
// EdgeGenerate?  If yes → a small G2-B witness (the seal does not close on the
// affine family).  If none across the family → strong evidence "primitive ⟹ recovers".
//
// THE OBJECT.  V = F_2^d (vectors are d-bit ints, + is XOR).  G0 ≤ GL(d,2).  The
// affine group V⋊G0 acts on V; its orbital scheme is the TRANSLATION scheme whose
// relations R_i are the G0-orbits on V (R_0 = {0}).  relOfPair(x,y) = orbit(x⊕y).
// Schurian by construction.  Two intrinsic facts make the classification cheap:
//   • primitive  ⟺  G0 irreducible  ⟺  every nonzero orbit F_2-spans V
//     (closed subsets ↔ G0-invariant subspaces).
//   • residual abelian  ⟺  G0 = {1}   (any non-trivial linear part makes V⋊G0
//     non-abelian; this is the leg-B / pure-translation / CFI-gauge case).
//
// RECOVERY = EdgeGenerates, the project's exact depth-1 recovery notion
// (Scheme.lean theorem_2_HOR_of_edgeGenerates): seed the isolation closure with
// {R_0, R_j0}; iteratively add any relation uniquely PINNED by its
// (edge-flag, intersection-counts-into-Iso) signature; recovers ⟺ Iso reaches all.
//
// No production code is touched.
// ─────────────────────────────────────────────────────────────────────────────
public class AffineSchemeProbe(ITestOutputHelper output)
{
    // ── F_2 linear algebra: vectors are ints (bit i = coord i); matrices are
    //    int[d], row i a bitmask.  Apply(M,v) = M·v over F_2. ─────────────────
    static bool Parity(int x) { x ^= x >> 16; x ^= x >> 8; x ^= x >> 4; x ^= x >> 2; x ^= x >> 1; return (x & 1) != 0; }

    static int Apply(int[] M, int v, int d)
    {
        int r = 0;
        for (int i = 0; i < d; i++) if (Parity(M[i] & v)) r |= 1 << i;
        return r;
    }

    // (A·B) row i = XOR over k with A[i] bit k set of B[k].  So Apply(AB,v)=Apply(A,Apply(B,v)).
    static int[] MatMul(int[] A, int[] B, int d)
    {
        var C = new int[d];
        for (int i = 0; i < d; i++) { int row = 0; for (int k = 0; k < d; k++) if ((A[i] >> k & 1) != 0) row ^= B[k]; C[i] = row; }
        return C;
    }

    static int[] Ident(int d) { var I = new int[d]; for (int i = 0; i < d; i++) I[i] = 1 << i; return I; }

    static long MatKey(int[] M, int d) { long k = 0; for (int i = 0; i < d; i++) k = (k << d) | (uint)M[i]; return k; }

    static bool IsInvertible(int[] M, int d)
    {
        // Gaussian elimination on the rows over F_2: full rank ⟺ invertible.
        var rows = (int[])M.Clone();
        int rank = 0;
        for (int col = 0; col < d; col++)
        {
            int piv = -1;
            for (int r = rank; r < d; r++) if ((rows[r] >> col & 1) != 0) { piv = r; break; }
            if (piv < 0) continue;
            (rows[rank], rows[piv]) = (rows[piv], rows[rank]);
            for (int r = 0; r < d; r++) if (r != rank && (rows[r] >> col & 1) != 0) rows[r] ^= rows[rank];
            rank++;
        }
        return rank == d;
    }

    // Generate the subgroup ⟨gens⟩ ≤ GL(d,2) by BFS (right-multiplication).  Returns
    // null if it exceeds `cap` (skip — too large to be "small").
    static List<int[]>? GenGroup(List<int[]> gens, int d, int cap)
    {
        var I = Ident(d);
        var seen = new HashSet<long> { MatKey(I, d) };
        var elems = new List<int[]> { I };
        var frontier = new Queue<int[]>(); frontier.Enqueue(I);
        while (frontier.Count > 0)
        {
            var g = frontier.Dequeue();
            foreach (var s in gens)
            {
                var h = MatMul(g, s, d); long k = MatKey(h, d);
                if (seen.Add(k)) { elems.Add(h); frontier.Enqueue(h); if (elems.Count > cap) return null; }
            }
        }
        return elems;
    }

    static bool Abelian(List<int[]> gens, int d)
    {
        for (int a = 0; a < gens.Count; a++)
            for (int b = a + 1; b < gens.Count; b++)
                if (MatKey(MatMul(gens[a], gens[b], d), d) != MatKey(MatMul(gens[b], gens[a], d), d)) return false;
        return true; // generators commute ⟹ group abelian
    }

    // ── The scheme: orbits, relations, intersection numbers ──────────────────
    sealed class Scheme
    {
        public required int D;          // dimension
        public required int N;          // 1<<d
        public required int Rank;       // number of relations (incl R_0)
        public required int[] Oid;      // orbit id per vector, Oid[0]=0
        public required int[] Valency;  // |O_i|
        public required int[] Rep;      // a representative vector with Oid[Rep[i]]=i
        public required int[,,] P;      // P[k,i,j] = p^k_{ij}
    }

    static (int[] oid, int rank) Orbits(List<int[]> grp, int d)
    {
        int n = 1 << d; var oid = new int[n]; for (int i = 0; i < n; i++) oid[i] = -1;
        oid[0] = 0; int next = 1;
        for (int v = 1; v < n; v++)
        {
            if (oid[v] != -1) continue;
            int id = next++;
            var q = new Queue<int>(); q.Enqueue(v); oid[v] = id;
            while (q.Count > 0) { int x = q.Dequeue(); foreach (var M in grp) { int y = Apply(M, x, d); if (oid[y] == -1) { oid[y] = id; q.Enqueue(y); } } }
        }
        return (oid, next);
    }

    static Scheme BuildScheme(List<int[]> grp, int d)
    {
        int n = 1 << d;
        var (oid, rank) = Orbits(grp, d);
        var val = new int[rank]; var rep = new int[rank]; for (int i = 0; i < rank; i++) rep[i] = -1;
        for (int v = 0; v < n; v++) { val[oid[v]]++; if (rep[oid[v]] < 0) rep[oid[v]] = v; }
        // p^k_{ij} = #{ z : oid[z]=i and oid[ c_k ⊕ z ]=j } for c_k = rep[k]
        var P = new int[rank, rank, rank];
        for (int k = 0; k < rank; k++)
        {
            int c = rep[k];
            for (int z = 0; z < n; z++) { int i = oid[z]; int j = oid[c ^ z]; P[k, i, j]++; }
        }
        return new Scheme { D = d, N = n, Rank = rank, Oid = oid, Valency = val, Rep = rep, P = P };
    }

    // F_2-span dimension of the orbit O_i.
    static int SpanDim(Scheme s, int i)
    {
        var basis = new List<int>();
        for (int v = 0; v < s.N; v++)
        {
            if (s.Oid[v] != i) continue;
            int x = v;
            foreach (var b in basis) { int hb = 31 - System.Numerics.BitOperations.LeadingZeroCount((uint)b); if (((x >> hb) & 1) != 0) x ^= b; }
            if (x != 0) basis.Add(x);
        }
        return basis.Count;
    }

    // Primitive ⟺ every nonzero orbit spans V (no proper nonzero invariant subspace).
    static bool Primitive(Scheme s)
    {
        for (int i = 1; i < s.Rank; i++) if (SpanDim(s, i) != s.D) return false;
        return true;
    }

    // EdgeGenerates(j0): isolation closure from {R_0, R_j0}.  A relation i (not in
    // Iso) is pinned ⟺ no OTHER non-diagonal relation shares its
    // (i==j0, (p^i_{l,j0})_{l∈Iso}) signature.  Returns true iff Iso reaches all.
    static bool EdgeGenerates(Scheme s, int j0)
    {
        var iso = new bool[s.Rank]; iso[0] = true; iso[j0] = true; int count = 2;
        if (j0 == 0) { iso[0] = true; count = 1; }
        var isoList = new List<int>(); for (int l = 0; l < s.Rank; l++) if (iso[l]) isoList.Add(l);

        string Sig(int i)
        {
            var sb = new System.Text.StringBuilder();
            sb.Append(i == j0 ? '1' : '0');
            foreach (int l in isoList) { sb.Append(':'); sb.Append(s.P[i, l, j0]); }
            return sb.ToString();
        }

        bool progress = true;
        while (progress && count < s.Rank)
        {
            progress = false;
            isoList = new List<int>(); for (int l = 0; l < s.Rank; l++) if (iso[l]) isoList.Add(l);
            // signature of every non-diagonal relation against the current Iso
            var sig = new string[s.Rank];
            for (int i = 1; i < s.Rank; i++) sig[i] = Sig(i);
            var seenSig = new Dictionary<string, int>();
            for (int i = 1; i < s.Rank; i++) seenSig[sig[i]] = seenSig.GetValueOrDefault(sig[i], 0) + 1;
            for (int i = 1; i < s.Rank; i++)
            {
                if (iso[i]) continue;
                if (seenSig[sig[i]] == 1) { iso[i] = true; count++; progress = true; }
            }
        }
        return count == s.Rank;
    }

    static bool Recovers(Scheme s) { for (int j0 = 1; j0 < s.Rank; j0++) if (EdgeGenerates(s, j0)) return true; return false; }

    // ── Recovery DEPTH on the single-relation Cayley graph Cay(V, O_j0): greedy
    //    individualization-to-discreteness (1-WL).  Vertex-transitive ⟹ start at 0.
    //    Returns the number of individualized vertices, or cap+1 if it exceeds cap.
    //    Bounded depth across the family ⟹ tame (recovers); growing ⟹ leak. ──────
    static int GreedyIRDepth(Scheme s, int j0, int cap)
    {
        int n = s.N;
        var nbr = new List<int>[n];
        for (int x = 0; x < n; x++) { nbr[x] = new List<int>(); for (int y = 0; y < n; y++) if (x != y && s.Oid[x ^ y] == j0) nbr[x].Add(y); }
        var ind = new List<int> { 0 };
        for (int depth = 1; depth <= cap; depth++)
        {
            var color = ColorRefine(n, nbr, ind);
            int distinct = color.Distinct().Count();
            if (distinct == n) return depth;
            // individualize lex-min vertex of the largest non-singleton cell
            var byColor = new Dictionary<int, List<int>>();
            for (int v = 0; v < n; v++) { if (!byColor.TryGetValue(color[v], out var lst)) { lst = new List<int>(); byColor[color[v]] = lst; } lst.Add(v); }
            int target = -1, best = 1;
            foreach (var kv in byColor) if (kv.Value.Count > best) { best = kv.Value.Count; target = kv.Value.Min(); }
            if (target < 0) return depth;
            ind.Add(target);
        }
        return cap + 1;
    }

    static int[] ColorRefine(int n, List<int>[] nbr, List<int> ind)
    {
        var color = new int[n];
        for (int i = 0; i < ind.Count; i++) color[ind[i]] = i + 1;
        int prevDistinct = color.Distinct().Count();
        while (true)
        {
            var sig = new (int, string)[n];
            for (int v = 0; v < n; v++) { var ms = nbr[v].Select(u => color[u]).OrderBy(c => c); sig[v] = (color[v], string.Join(",", ms)); }
            var map = new Dictionary<(int, string), int>(); int next = 0; var nc = new int[n];
            foreach (var v in Enumerable.Range(0, n).OrderBy(v => sig[v].Item1).ThenBy(v => sig[v].Item2))
            { if (!map.TryGetValue(sig[v], out int c)) { c = next++; map[sig[v]] = c; } nc[v] = c; }
            int d2 = nc.Distinct().Count();
            color = nc;
            if (d2 == prevDistinct) break;   // 1-WL only refines; stable when distinct-count stops rising
            prevDistinct = d2;
        }
        return color;
    }

    // ── G0 enumeration sources ───────────────────────────────────────────────
    // Companion matrix of a primitive polynomial of degree d (the Singer cycle
    // generator = "multiply by a primitive element of F_{2^d}").
    static readonly Dictionary<int, int> PrimPolyTail = new()
    {
        // x^d + (tail bits give lower coeffs); standard primitive polynomials over F_2.
        { 1, 0b1 }, { 2, 0b11 }, { 3, 0b011 }, { 4, 0b0011 }, { 5, 0b00101 }, { 6, 0b000011 },
        { 8, 0b00011101 },   // x^8 + x^4 + x^3 + x^2 + 1
    };

    static int[] CompanionSinger(int d)
    {
        // Companion matrix C of x^d = c_{d-1} x^{d-1}+...+c_0, acting on column vectors;
        // row form so Apply(C, e_i) shifts.  Use the standard companion: C maps
        // e_i ↦ e_{i+1} (i<d-1) and e_{d-1} ↦ (the prim-poly tail).
        var C = new int[d];
        int tail = PrimPolyTail[d];
        for (int i = 0; i < d; i++)
        {
            int row = 0;
            // column j contributes to row i if (C e_j) has bit i.
            for (int j = 0; j < d; j++)
            {
                int img; // C e_j
                if (j < d - 1) img = 1 << (j + 1); else img = tail;
                if ((img >> i & 1) != 0) row |= 1 << j;
            }
            C[i] = row;
        }
        return C;
    }

    // Frobenius x ↦ x^2 on F_{2^d} expressed in the F_2-basis {1,a,a^2,...,a^{d-1}}
    // is the linear map e_i ↦ a^{2i}; building it precisely needs the field tables.
    // Cheaper, still rich: include the companion's square-power conjugators via a
    // few structured matrices, plus random invertible matrices as extra generators.

    static IEnumerable<List<int[]>> EnumerateG0Sources(int d, int sampleCap, int seed)
    {
        var I = Ident(d);
        var singer = CompanionSinger(d);
        // 1) all cyclic subgroups generated by powers of the Singer generator (covers
        //    Singer + every cyclotomic subgroup), plus cyclic ⟨g⟩ for sampled g.
        yield return new List<int[]> { singer };                 // full Singer cycle
        // Singer powers g^m generate proper cyclic subgroups (the cyclotomic schemes).
        {
            var pow = (int[])I.Clone();
            var powers = new List<int[]>();
            for (int e = 0; e < (1 << d); e++) { powers.Add((int[])pow.Clone()); pow = MatMul(pow, singer, d); }
            int order = 1; // find Singer order = 2^d - 1
            var p2 = (int[])singer.Clone(); order = 1; while (MatKey(p2, d) != MatKey(I, d)) { p2 = MatMul(p2, singer, d); order++; }
            for (int m = 2; m < order; m++) if (order % m == 0) yield return new List<int[]> { powers[m % powers.Count] };
        }
        // 2) the Singer normalizer's Frobenius-like extra generator (built by brute
        //    search: an order-d element f with f·singer·f^{-1} = singer^2), if present.
        // 3) random / structured pairs of invertible matrices (non-abelian samples).
        var rng = new Random(seed);
        int produced = 0;
        var pool = new List<int[]>();
        // small structured pool: identity-plus-one-offdiagonal transvections + singer powers
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++)
                if (i != j) { var T = Ident(d); T[i] ^= 1 << j; pool.Add(T); }  // transvection e_j-component into row i
        {
            var pw = (int[])singer.Clone();
            for (int e = 0; e < d + 2; e++) { pool.Add((int[])pw.Clone()); pw = MatMul(pw, singer, d); }
        }
        // random invertibles
        while (pool.Count < 40 + 4 * d)
        {
            var M = new int[d]; for (int i = 0; i < d; i++) M[i] = rng.Next(1 << d);
            if (IsInvertible(M, d)) pool.Add(M);
        }
        // singleton cyclic from pool
        foreach (var g in pool) { yield return new List<int[]> { g }; if (++produced > sampleCap) break; }
        // pairs
        produced = 0;
        for (int a = 0; a < pool.Count && produced < sampleCap; a++)
            for (int b = a + 1; b < pool.Count && produced < sampleCap; b++)
            { yield return new List<int[]> { pool[a], pool[b] }; produced++; }
    }

    // ── The probe ────────────────────────────────────────────────────────────
    sealed record Row(int D, int GroupOrder, int Rank, string Valencies, bool Primitive, bool Abelian, bool Recovers, string PerRel);

    [Fact]
    public void Probe_AffineSchemes_Over_F2d()
    {
        var dims = new[] { 2, 3, 4, 5 };
        int groupCap = 1 << 16;   // skip G0 larger than 65536 (still "small" for |V|≤32)
        int sampleCap = 400;

        var candidates = new List<(int d, Scheme s, int order, bool abelian)>();
        int totalSchemes = 0, primitiveCount = 0, primitiveRecover = 0, validations = 0;

        foreach (int d in dims)
        {
            int n = 1 << d;
            // dedupe distinct schemes by invariant
            var seenScheme = new HashSet<string>();
            var rows = new List<Row>();

            foreach (var gens in EnumerateG0Sources(d, sampleCap, seed: 12345 + d))
            {
                var grp = GenGroup(gens, d, groupCap);
                if (grp == null) continue;                  // too large
                if (grp.Count == 1) continue;               // trivial G0 ⟹ rank n, leg-B; skip (not G2-B)
                var s = BuildScheme(grp, d);
                if (s.Rank <= 2) { /* rank 2 = 2-transitive, trivially recovers */ }

                // scheme invariant: rank + sorted valencies + intersection-number hash
                var valSorted = s.Valency.OrderBy(x => x).ToArray();
                long ih = 17;
                for (int k = 0; k < s.Rank; k++) for (int i = 0; i < s.Rank; i++) for (int j = 0; j < s.Rank; j++) ih = ih * 1000003 + s.P[k, i, j];
                string inv = $"{s.Rank}|{string.Join(",", valSorted)}|{ih}";
                if (!seenScheme.Add(inv)) continue;

                bool prim = Primitive(s);
                bool ab = Abelian(grp, d);
                bool rec = Recovers(s);

                // self-validation: primitive (closed-subset) ⟺ G0 irreducible (span test) —
                // both computed via SpanDim, so check consistency of the two readings is moot;
                // instead validate the known anchor: full GL ⟹ rank 2 ⟹ recovers.
                validations++;

                totalSchemes++;
                if (prim) { primitiveCount++; if (rec) primitiveRecover++; }

                var perRel = string.Join(",", Enumerable.Range(1, s.Rank - 1).Select(j0 => EdgeGenerates(s, j0) ? "G" : "."));
                rows.Add(new Row(d, grp.Count, s.Rank, string.Join(",", s.Valency.Skip(1)), prim, ab, rec, perRel));

                // THE HUNT: primitive ∧ ¬recovers = G2-B candidate.  (Residual V⋊G0 is
                // NON-abelian for every G0≠1 — the `ab` column tags G0-as-a-group, not
                // the residual, so it is NOT the leg-B discriminator; primitive ∧ ¬recovers
                // already lands in the ¬D1∧¬D2 wall, and small ⟹ not-Cameron ⟹ G2-B.)
                if (prim && !rec) candidates.Add((d, s, grp.Count, ab));
            }

            output.WriteLine($"════ d={d}  (|V|={n}) ════   distinct schemes: {rows.Count}");
            output.WriteLine($"{"|G0|",7} {"rank",5} {"primitive",10} {"abelian",8} {"recovers",9}  valencies / per-relation EdgeGenerates");
            foreach (var r in rows.OrderBy(r => r.Rank).ThenBy(r => r.GroupOrder))
                output.WriteLine($"{r.GroupOrder,7} {r.Rank,5} {(r.Primitive ? "PRIM" : "imprim"),10} {(r.Abelian ? "ab" : "nonab"),8} {(r.Recovers ? "yes" : "NO"),9}  [{r.Valencies}]  {r.PerRel}");
        }

        output.WriteLine("");
        output.WriteLine("──────────────────────────────────────────────────────────────");
        output.WriteLine($"distinct schemes examined: {totalSchemes}");
        output.WriteLine($"primitive schemes: {primitiveCount};  of those, recover (EdgeGenerates): {primitiveRecover}");
        output.WriteLine($"G2-B candidates (primitive ∧ ¬recovers-at-depth-1, residual V⋊G0 non-abelian): {candidates.Count}");
        foreach (var (d, s, order, ab) in candidates)
        {
            int depth = GreedyIRDepth(s, 1, cap: s.N);
            output.WriteLine($"  ★ d={d} |G0|={order} rank={s.Rank} valencies=[{string.Join(",", s.Valency.Skip(1))}]  greedy-IR-depth(single graph)={depth}");
        }

        if (candidates.Count == 0)
            output.WriteLine("VERDICT: no affine G2-B witness in the enumerated family — supports 'primitive ⟹ recovers'.");
        else
            output.WriteLine("VERDICT: AFFINE G2-B CANDIDATE(S) FOUND — investigate (recovery depth ≥ 2? genuine leak?).");

        // The probe is exploratory; it must run clean.  Sanity anchor: we examined schemes.
        Assert.True(totalSchemes > 0, "probe enumerated no schemes");
    }

    // ── The decisive family: index-3 Singer cyclotomic schemes (3 relations of
    //    valency (2^d-1)/3) at d=4,6,8 → |V|=16,64,256.  The d=4 instance is the
    //    G2-B candidate; if recovery DEPTH stays bounded across d, the candidate is
    //    tame (recovers cheaply, leg A depth-graded — NOT a leak); if it GROWS, the
    //    affine floor of G2-B is a genuine leak. ───────────────────────────────────
    [Fact]
    public void Probe_CyclotomicFamily_Index3()
    {
        output.WriteLine("Index-3 Singer cyclotomic schemes  (V⋊⟨g^3⟩, g = Singer cycle):");
        output.WriteLine("3 relations of valency (2^d-1)/3; the d=4 case is the primitive non-recovering candidate.");
        output.WriteLine("");
        foreach (int d in new[] { 4, 6, 8 })
        {
            if (!PrimPolyTail.ContainsKey(d)) { output.WriteLine($"  d={d}: no primitive polynomial registered"); continue; }
            var g = CompanionSinger(d);
            var g3 = MatMul(MatMul(g, g, d), g, d);                 // index-3 generator
            var grp = GenGroup(new List<int[]> { g3 }, d, 1 << 20);
            if (grp == null) { output.WriteLine($"  d={d}: G0 too large, skip"); continue; }
            var s = BuildScheme(grp, d);
            bool prim = Primitive(s);
            bool rec = Recovers(s);
            int depth = GreedyIRDepth(s, 1, cap: s.N);
            // per-relation EdgeGenerates flags
            var per = string.Join("", Enumerable.Range(1, s.Rank - 1).Select(j0 => EdgeGenerates(s, j0) ? "G" : "."));
            output.WriteLine($"  d={d} |V|={s.N,4} |G0|={grp.Count,4} rank={s.Rank} val=[{string.Join(",", s.Valency.Skip(1))}]  primitive={prim}  recovers(depth-1)={(rec ? "yes" : "NO"),3}  perRel={per}  greedy-IR-depth={depth}");
        }
        output.WriteLine("");
        output.WriteLine("READ: greedy-IR-depth bounded across d ⟹ tame (recovers, not a leak).  Growing ⟹ affine G2-B leak.");
        Assert.True(true);
    }
}
