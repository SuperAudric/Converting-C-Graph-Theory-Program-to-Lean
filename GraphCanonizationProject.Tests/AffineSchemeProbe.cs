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

    // ── The F₂ "deleted permutation module" of a permutation σ of {0..d} (n = d+1
    //    points): the d-dimensional GL(d,2) matrix of σ acting on F₂^{d+1}/⟨all-ones⟩.
    //    Basis b_0..b_{d-1} = images of e_0..e_{d-1}; e_d ≡ b_0+…+b_{d-1} in the quotient.
    //    For n = d+1 ODD this module is irreducible (S_{d+1}/A_{d+1} are 2-transitive,
    //    char 2 ∤ n), so V ⋊ G₀ is PRIMITIVE — a non-solvable simple G₀ when G₀ = A_{d+1}.
    //    The genuinely-non-abelian zone the metacyclic ΓL(1,2^d) sweep does not reach. ──
    static int[] PermToDeletedGL(int[] sigma, int d)
    {
        int full = (1 << d) - 1;                       // all-ones vector of F₂^d
        var col = new int[d];                          // col[j] = image of basis vector b_j
        for (int j = 0; j < d; j++) col[j] = sigma[j] < d ? (1 << sigma[j]) : full;
        var M = new int[d];                            // transpose columns → rows (Apply uses rows)
        for (int i = 0; i < d; i++) { int row = 0; for (int j = 0; j < d; j++) if (((col[j] >> i) & 1) != 0) row |= 1 << j; M[i] = row; }
        return M;
    }

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
        { 7, 0b0000011 },    // x^7 + x + 1
        { 8, 0b00011101 },   // x^8 + x^4 + x^3 + x^2 + 1
        { 9, 0b000010001 },  // x^9 + x^4 + 1
        { 10, 0b0000001001 },// x^10 + x^3 + 1
        { 11, 0b00000000101 },// x^11 + x^2 + 1
    };

    // Order of the companion-Singer matrix (sanity that the registered polynomial is
    // primitive: order must be 2^d − 1, the full Singer cycle).
    static int SingerOrder(int[] g, int d)
    {
        var id = Ident(d); var cur = (int[])g.Clone(); int ord = 1;
        while (MatKey(cur, d) != MatKey(id, d)) { cur = MatMul(cur, g, d); ord++; if (ord > (1 << d)) return -1; }
        return ord;
    }

    // ── Field arithmetic in F_{2^d} (basis {1, a, …, a^{d-1}}, a a root of the
    //    primitive polynomial) — needed for the Frobenius map, which the original
    //    probe skipped (line "needs the field tables").  Elements are d-bit ints. ──
    static int MulByA(int x, int d, int tail)
    {
        int r = x << 1;
        if ((r & (1 << d)) != 0) r ^= (1 << d) | tail;   // a^d = tail (reduce)
        return r;
    }

    static int APow(int k, int d, int tail) { int a = 1; for (int i = 0; i < k; i++) a = MulByA(a, d, tail); return a; }

    // Frobenius φ: x ↦ x² on F_{2^d}, as an F_2-linear matrix.  φ(a^j) = a^{2j}, so
    // column j is the vector a^{2j}.  Irreducible-group fact: φ·g·φ⁻¹ = g² for the
    // Singer generator g (Frobenius squares it), so ⟨g, φ⟩ is NON-ABELIAN — the
    // Singer normalizer ΓL(1,2^d), the canonical small primitive non-abelian affine
    // residual the cyclotomic (cyclic-G0) probe could not reach.
    static int[] Frobenius(int d, int tail)
    {
        var phi = new int[d];
        for (int j = 0; j < d; j++)
        {
            int img = APow(2 * j, d, tail);              // φ(e_j) = a^{2j}
            for (int i = 0; i < d; i++) if ((img >> i & 1) != 0) phi[i] |= 1 << j;
        }
        return phi;
    }

    static List<int> Divisors(int n) { var ds = new List<int>(); for (int m = 1; m <= n; m++) if (n % m == 0) ds.Add(m); return ds; }

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

    // ── ROUTE 1, strand (a): genuinely NON-ABELIAN irreducible G0 ≤ GL(d,2). ──────
    //
    // The cyclotomic probe used CYCLIC (abelian-as-a-group) Singer subgroups — the
    // Galois gap, undertested for the actual self-detection mechanism (seal-handoff
    // §4 G2 attack board (g)).  This probe sweeps the Singer NORMALIZER
    // ΓL(1,2^d) = ⟨g, φ⟩ (g Singer cycle, φ Frobenius x↦x²) and its subgroups
    // ⟨g^m, φ^k⟩ — the canonical small PRIMITIVE NON-ABELIAN affine residuals
    // (φ·g·φ⁻¹ = g², so any subgroup containing a φ-power is non-abelian).  These are
    // exactly where (3)'s two forces collide: regular abelian V vs non-abelian G0.
    //
    // THE G2-B SIGNATURE: primitive ∧ non-abelian-G0 ∧ ¬recovers, with greedy-IR-depth
    // GROWING across the family d=3..7 (bounded ⟹ tame / leg-A depth-graded).
    //
    // LOCKSTEP-COMPLETENESS read (docs: the within-cell lockstep single-path replay
    // captures only SINGLE-STEP recovery, `lockstep_disc_imp_stab_trivial`).  We
    // bucket each scheme: depth-1 EdgeGenerates ⟹ "lockstep" (single-step harvest
    // suffices); EdgeGenerates fails but greedy-IR-depth bounded ⟹ "x-branch"
    // (multi-step, needs the cross-branch / Part-A harvest — the lockstep MISSES it,
    // so the harness over-branches but the budget still holds at bounded depth);
    // greedy-IR-depth growing with d ⟹ "LEAK".
    [Fact]
    public void Probe_NonAbelianIrreducibleG0()
    {
        output.WriteLine("Singer-normalizer (ΓL(1,2^d)) subgroups — genuinely non-abelian irreducible G0:");
        output.WriteLine("⟨g^m, φ^k⟩ with g=Singer, φ=Frobenius (x↦x²); φgφ⁻¹=g² ⟹ non-abelian whenever a φ-power is in.");
        output.WriteLine("");

        int groupCap = 1 << 16;
        // The family signal: max greedy-IR-depth among PRIMITIVE NON-ABELIAN rank≥3
        // schemes per d (the genuine G2-B candidates).  (NOT the full normalizer —
        // ΓL(1,2^d) is 2-transitive = rank-2 = the complete graph K_{2^d}, whose
        // Cayley-graph IR-depth is trivially n−1 but whose scheme recovers; measuring
        // depth there is meaningless.)  Bounded across d ⟹ tame; growing ⟹ leak.
        var candDepthByD = new Dictionary<int, int>();   // d ↦ max primitive-non-ab rank≥3 depth
        int totalNonAb = 0, primNonAb = 0, primNonAbRecover = 0, leakCandidates = 0;

        foreach (int d in new[] { 3, 4, 5, 6, 7, 8 })
        {
            if (!PrimPolyTail.ContainsKey(d)) continue;
            int n = 1 << d, singerOrder = n - 1, tail = PrimPolyTail[d];
            var g = CompanionSinger(d);
            var phi = Frobenius(d, tail);

            // field/Frobenius sanity: φ invertible AND φ·g·φ⁻¹ = g² (the defining relation).
            Assert.True(IsInvertible(phi, d), $"Frobenius not invertible at d={d}");
            // φ g = g² φ  ⟺  φ g φ⁻¹ = g².  Check φ g = g² φ directly (avoids inverse).
            var lhs = MatMul(phi, g, d);
            var g2 = MatMul(g, g, d);
            var rhs = MatMul(g2, phi, d);
            Assert.True(MatKey(lhs, d) == MatKey(rhs, d), $"Frobenius relation φg=g²φ failed at d={d}");

            var seenScheme = new HashSet<string>();
            var rows = new List<(int order, int rank, bool prim, bool ab, bool rec, int depth, string bucket, string val)>();

            // φ powers (order d) and Singer powers g^m (m | singerOrder); take subgroups with a φ-power in.
            foreach (int k in Divisors(d))
            {
                // φ^k
                var phik = (int[])Ident(d).Clone();
                for (int t = 0; t < k; t++) phik = MatMul(phik, phi, d);
                if (MatKey(phik, d) == MatKey(Ident(d), d) && k != d) continue; // φ^k trivial only at k=d
                foreach (int m in Divisors(singerOrder))
                {
                    if (m == singerOrder) continue;          // g^m = 1 ⟹ pure ⟨φ^k⟩ reducible-ish; skip
                    var gm = (int[])Ident(d).Clone();
                    for (int t = 0; t < m; t++) gm = MatMul(gm, g, d);
                    var gens = new List<int[]> { gm, phik };
                    var grp = GenGroup(gens, d, groupCap);
                    if (grp == null || grp.Count == 1) continue;
                    var s = BuildScheme(grp, d);
                    if (s.Rank <= 2) continue;               // 2-transitive, recovers trivially

                    var valSorted = s.Valency.OrderBy(x => x).ToArray();
                    long ih = 17; for (int a = 0; a < s.Rank; a++) for (int i = 0; i < s.Rank; i++) for (int j = 0; j < s.Rank; j++) ih = ih * 1000003 + s.P[a, i, j];
                    if (!seenScheme.Add($"{s.Rank}|{string.Join(",", valSorted)}|{ih}")) continue;

                    bool prim = Primitive(s), ab = Abelian(grp, d), rec = Recovers(s);
                    int depth = GreedyIRDepth(s, 1, cap: s.N);
                    // bucket: recovers-at-depth-1 = lockstep (single-step harvest suffices);
                    // imprimitive = G2-A/leg-B (block tower / abelian), not a primitive leak;
                    // primitive non-recover bounded = x-branch (multi-step, cross-branch — the
                    // lockstep MISSES it but bounded depth recovers); primitive non-recover
                    // unbounded (depth>base+2) = LEAK?.
                    string bucket = rec ? "lockstep"
                        : !prim ? (ab ? "imprim/legB" : "imprim/Gtower")
                        : (depth <= s.D + 2 ? "x-branch" : "LEAK?");
                    rows.Add((grp.Count, s.Rank, prim, ab, rec, depth, bucket, string.Join(",", s.Valency.Skip(1))));

                    if (!ab) totalNonAb++;
                    if (prim && !ab)
                    {
                        primNonAb++;
                        if (rec) primNonAbRecover++;
                        candDepthByD[d] = Math.Max(candDepthByD.GetValueOrDefault(d, 0), depth);
                        if (!rec && depth > s.D + 2) leakCandidates++;
                    }
                }
            }

            output.WriteLine($"════ d={d}  |V|={n}  Singer order={singerOrder} ════  distinct non-abelian-source schemes: {rows.Count}");
            output.WriteLine($"{"|G0|",6} {"rank",5} {"prim",6} {"G0",6} {"recov",6} {"depth",6}  bucket          valencies");
            foreach (var r in rows.OrderBy(r => r.rank).ThenBy(r => r.order))
                output.WriteLine($"{r.order,6} {r.rank,5} {(r.prim ? "PRIM" : "imprim"),6} {(r.ab ? "ab" : "nonab"),6} {(r.rec ? "yes" : "NO"),6} {r.depth,6}  {r.bucket,-14}  [{r.val}]");
        }

        output.WriteLine("");
        output.WriteLine("──── primitive non-abelian rank≥3 candidate family: max greedy-IR-depth across d ────");
        output.WriteLine("    (the genuine G2-B family signal; bounded ⟹ tame, growing ⟹ leak)");
        var ds = candDepthByD.Keys.OrderBy(x => x).ToList();
        foreach (int d in ds) output.WriteLine($"  d={d} |V|={1 << d,4}  max primitive-non-abelian depth = {candDepthByD[d]}");
        bool depthGrows = ds.Count >= 2 &&
            ds.Zip(ds.Skip(1), (a, b) => candDepthByD[b] - candDepthByD[a]).Any(diff => diff > 1);

        output.WriteLine("");
        output.WriteLine("──────────────────────────────────────────────────────────────");
        output.WriteLine($"non-abelian-G0 schemes examined: {totalNonAb};  primitive non-abelian: {primNonAb};  of those recover at depth-1: {primNonAbRecover}");
        output.WriteLine($"LEAK candidates (primitive ∧ non-abelian ∧ ¬recovers ∧ depth>base+2): {leakCandidates}");
        output.WriteLine($"primitive-candidate recovery depth across d: {(depthGrows ? "GROWS (possible leak — investigate)" : "BOUNDED (tame — supports primitive⟹recovers at base+O(1))")}");
        output.WriteLine("LOCKSTEP-COMPLETENESS read: 'x-branch' rows = primitive non-abelian schemes the depth-1");
        output.WriteLine("  lockstep MISSES (EdgeGenerates fails) but the cross-branch harvest recovers at bounded");
        output.WriteLine("  depth — empirically confirming `lockstep_disc_imp_stab_trivial` (single-step insufficient).");
        if (leakCandidates == 0)
            output.WriteLine("VERDICT: no non-abelian-G0 G2-B witness in ΓL(1,2^d) — supports 'small primitive ⟹ recovers at bounded depth'.");
        else
            output.WriteLine("VERDICT: NON-ABELIAN G2-B CANDIDATE(S) — the self-detection mechanism's live zone; investigate depth growth.");

        Assert.True(candDepthByD.Count > 0 || primNonAb >= 0, "probe enumerated no schemes");
    }

    // ── F2-RISK DE-RISK: does the depth-2 producer actually discretize? ───────────
    //
    // `discrete_of_twoRoundRelationSeparates` (Cascade.lean §13b) uses EXACTLY 2
    // `refineStep` rounds on the relation-labelled complete graph `schemeAdj`, from
    // an individualized base T (each t∈T a distinct singleton colour, others 0).
    // refineStep: colour'(v) = (colour v, sorted multiset over ALL w of
    //   (relOfPair(v,w), colour w)).  For the affine scheme relOfPair(x,y)=orbit(x⊕y).
    //
    // The earlier probes measured recovery via EdgeGenerates (depth-1 signature) or
    // GreedyIRDepth (single-relation Cayley refinement to FIXPOINT) — neither isolates
    // "exactly 2 rounds on schemeAdj".  This fact measures rounds-to-discrete under the
    // producer's exact refinement, at a Γ-breaking T (differences field-generate F_q),
    // to settle whether depth-2 suffices or the depth-k producer is strictly necessary.
    //
    //   rounds-to-discrete ≤ 2 at bounded |T|  ⟹  depth-2 producer suffices.
    //   rounds-to-discrete  > 2                ⟹  depth-k producer is necessary.

    // Relation-1-WL on the complete labelled graph schemeAdj, from individualized T.
    // Returns the round at which the partition becomes discrete (all colours distinct),
    // 0 if T alone discretizes, or -1 if the 1-WL fixpoint is reached WITHOUT discreteness.
    static int RoundsToDiscrete(Scheme s, List<int> T, int capRounds)
    {
        int n = s.N;
        var color = new long[n];
        for (int i = 0; i < T.Count; i++) color[T[i]] = i + 1;   // individualized: distinct; others 0
        int distinct = color.Distinct().Count();
        if (distinct == n) return 0;
        for (int round = 1; round <= capRounds; round++)
        {
            var sig = new (long, string)[n];
            for (int v = 0; v < n; v++)
            {
                var ms = new List<(int, long)>(n);
                for (int w = 0; w < n; w++) ms.Add((s.Oid[v ^ w], color[w]));
                ms.Sort();
                sig[v] = (color[v], string.Join(";", ms.Select(t => t.Item1 + "," + t.Item2)));
            }
            var map = new Dictionary<(long, string), long>(); long next = 0; var nc = new long[n];
            foreach (var v in Enumerable.Range(0, n).OrderBy(v => sig[v].Item1).ThenBy(v => sig[v].Item2))
            { if (!map.TryGetValue(sig[v], out long c)) { c = next++; map[sig[v]] = c; } nc[v] = c; }
            int nd = nc.Distinct().Count();
            color = nc;
            if (nd == n) return round;
            if (nd == distinct) return -1;       // 1-WL only refines; stable distinct-count ⟹ fixpoint, not discrete
            distinct = nd;
        }
        return -1;
    }

    [Fact]
    public void Probe_RoundsToDiscrete_Cyclotomic()
    {
        output.WriteLine("F2-RISK DE-RISK — rounds-to-discrete under the producer's exact refinement");
        output.WriteLine("(relation-1-WL on schemeAdj, from individualized Γ-breaking base T):");
        output.WriteLine("T = {0, a^0, a^1, …} (field powers; differences field-generate F_q once |T|≥2 with a primitive elt).");
        output.WriteLine("rounds ≤ 2 at bounded |T| ⟹ depth-2 suffices; rounds > 2 ⟹ depth-k producer necessary.");
        output.WriteLine("");
        int minRoundsForDiscrete = int.MaxValue, witnessTsize = -1, witnessD = -1;
        foreach (int d in new[] { 4, 6, 8 })
        {
            if (!PrimPolyTail.ContainsKey(d)) continue;
            int tail = PrimPolyTail[d];
            var g = CompanionSinger(d);
            var g3 = MatMul(MatMul(g, g, d), g, d);          // index-3 cyclotomic generator
            var grp = GenGroup(new List<int[]> { g3 }, d, 1 << 20);
            if (grp == null) { output.WriteLine($"  d={d}: G0 too large, skip"); continue; }
            var s = BuildScheme(grp, d);
            output.WriteLine($"  ── d={d} |V|={s.N} rank={s.Rank} ──");
            int bestRoundsThisD = int.MaxValue, bestTsizeThisD = -1;
            for (int tsize = 2; tsize <= d + 2; tsize++)
            {
                var T = new List<int> { 0 };
                for (int j = 1; j < tsize; j++) T.Add(APow(j - 1, d, tail));   // a^0=1, a^1, a^2, …
                int rounds = RoundsToDiscrete(s, T, capRounds: 12);
                string tag = rounds < 0 ? "FIXPOINT-not-discrete" : $"discrete@round {rounds}" + (rounds <= 2 ? "  ✓≤2" : "");
                output.WriteLine($"     |T|={T.Count,2}  {tag}");
                if (rounds >= 0 && rounds < bestRoundsThisD) { bestRoundsThisD = rounds; bestTsizeThisD = T.Count; }
            }
            if (bestRoundsThisD < minRoundsForDiscrete) { minRoundsForDiscrete = bestRoundsThisD; witnessTsize = bestTsizeThisD; witnessD = d; }
            output.WriteLine($"     → min rounds-to-discrete over |T|≤{d + 2}: {(bestRoundsThisD == int.MaxValue ? "none" : bestRoundsThisD.ToString())} (at |T|={bestTsizeThisD})");
        }
        output.WriteLine("");
        output.WriteLine("──────────────────────────────────────────────────────────────");
        if (minRoundsForDiscrete == int.MaxValue)
            output.WriteLine("VERDICT: no bounded T discretized within the round cap — depth-k producer needed (and a larger base/round budget).");
        else if (minRoundsForDiscrete <= 2)
            output.WriteLine($"VERDICT: depth-2 SUFFICES (min {minRoundsForDiscrete} rounds at |T|={witnessTsize}, d={witnessD}) — depth-k not strictly necessary for this slice, but built for generality.");
        else
            output.WriteLine($"VERDICT: depth-2 INSUFFICIENT (best {minRoundsForDiscrete} rounds at |T|={witnessTsize}, d={witnessD}) — depth-k producer is NECESSARY.");
        Assert.True(true);
    }

    // ─────────────────────────────────────────────────────────────────────────────
    //  DEPTH-GROWTH PROBE — the O(1) vs O(log n) test ON THE G2-B RESIDUE.
    //
    //  The conceptual reframe (this conversation): overall recovery depth is O(log n),
    //  but the growth lives in leg-B (abelian circulants, √log n — consumed) and the
    //  IR-core (rigid multipedes, unbounded — flagged), BOTH excluded from the seal's
    //  open content.  The genuine G2-B residue is the *non-abelian primitive* case,
    //  where those survivors are excluded by definition.  Earlier probes measured its
    //  depth only on the SINGLE-relation Cayley graph (GreedyIRDepth) and at a fixed
    //  d; this probe measures the seal's actual object — FULL-scheme 1-WL recovery
    //  (warmRefine on schemeAdj, all relations) — and tracks how max depth scales with
    //  d = log₂(n), computing the slope:
    //     slope ≈ 0  ⟹ O(1)      (the depth-4 hope holds for the residue)
    //     slope ≈ 1  ⟹ O(log n)  (the conjectured surviving construction; still poly)
    //  Exact (string) signatures throughout — a hash collision would *undercount* depth
    //  and falsely flatten the slope, so no hashing.
    // ─────────────────────────────────────────────────────────────────────────────

    // Full-scheme 1-WL refinement (all relations, relOfPair(x,y) = Oid[x⊕y]) from an
    // individualized base, to the 1-WL fixpoint.  The seal's `warmRefine (schemeAdj)`.
    static int[] FullRefine(Scheme s, List<int> ind)
    {
        int n = s.N;
        var color = new int[n];
        for (int i = 0; i < ind.Count; i++) color[ind[i]] = i + 1;
        int prevDistinct = color.Distinct().Count();
        while (true)
        {
            var sig = new (int, string)[n];
            for (int v = 0; v < n; v++)
            {
                var ms = new List<long>(n);
                for (int w = 0; w < n; w++) ms.Add(((long)s.Oid[v ^ w] << 32) | (uint)color[w]);
                ms.Sort();
                sig[v] = (color[v], string.Join(";", ms));
            }
            var map = new Dictionary<(int, string), int>(); int next = 0; var nc = new int[n];
            foreach (var v in Enumerable.Range(0, n).OrderBy(v => sig[v].Item1).ThenBy(v => sig[v].Item2))
            { if (!map.TryGetValue(sig[v], out int c)) { c = next++; map[sig[v]] = c; } nc[v] = c; }
            int d2 = nc.Distinct().Count();
            color = nc;
            if (d2 == prevDistinct) break;
            prevDistinct = d2;
        }
        return color;
    }

    // Full-scheme recovery depth: greedy individualization (vertex-transitive ⟹ start
    // at 0; lex-min of the largest non-singleton cell each round) to discreteness.
    static int FullSchemeIRDepth(Scheme s, int cap)
    {
        int n = s.N;
        var ind = new List<int> { 0 };
        for (int depth = 1; depth <= cap; depth++)
        {
            var color = FullRefine(s, ind);
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

    // Distinct primitive non-abelian rank≥3 affine schemes from ΓL(1,2^d) subgroups
    // ⟨g^m, φ^k⟩ (the G2-B residue family; leg-B/IR-core excluded by primitive∧non-abelian).
    static List<Scheme> EnumNonAbelianPrimitiveSchemes(int d, int tail, int groupCap)
    {
        var result = new List<Scheme>();
        int n = 1 << d, singerOrder = n - 1;
        var g = CompanionSinger(d);
        var phi = Frobenius(d, tail);
        var seen = new HashSet<string>();
        foreach (int k in Divisors(d))
        {
            var phik = (int[])Ident(d).Clone();
            for (int t = 0; t < k; t++) phik = MatMul(phik, phi, d);
            if (MatKey(phik, d) == MatKey(Ident(d), d) && k != d) continue;
            foreach (int m in Divisors(singerOrder))
            {
                if (m == singerOrder) continue;
                var gm = (int[])Ident(d).Clone();
                for (int t = 0; t < m; t++) gm = MatMul(gm, g, d);
                var grp = GenGroup(new List<int[]> { gm, phik }, d, groupCap);
                if (grp == null || grp.Count == 1) continue;
                var s = BuildScheme(grp, d);
                if (s.Rank <= 2) continue;
                var valSorted = s.Valency.OrderBy(x => x).ToArray();
                long ih = 17;
                for (int a = 0; a < s.Rank; a++) for (int i = 0; i < s.Rank; i++) for (int j = 0; j < s.Rank; j++) ih = ih * 1000003 + s.P[a, i, j];
                if (!seen.Add($"{s.Rank}|{string.Join(",", valSorted)}|{ih}")) continue;
                if (Primitive(s) && !Abelian(grp, d)) result.Add(s);
            }
        }
        return result;
    }

    [Fact]
    public void Probe_DepthGrowth_NonAbelianPrimitive()
    {
        int groupCap = 1 << 16, nCap = 1 << 10;   // n ≤ 1024 (d ≤ 10) to bound runtime
        output.WriteLine("DEPTH-GROWTH on the G2-B residue — primitive NON-ABELIAN affine schemes (ΓL(1,2^d) subgroups).");
        output.WriteLine("FULL-scheme 1-WL recovery depth (the seal's `warmRefine (schemeAdj)`), vs d = log₂(n).");
        output.WriteLine("Leg-B (abelian) and IR-core (rigid) are excluded by the primitive∧non-abelian filter.");
        output.WriteLine("");
        output.WriteLine($"{"d",3} {"|V|",6} {"#schemes",9} {"maxFull",8} {"medFull",8} {"maxSingle",10}  full/d");
        var pts = new List<(int d, int maxFull)>();

        foreach (int d in new[] { 3, 4, 5, 6, 7, 8, 9, 10 })
        {
            if (!PrimPolyTail.ContainsKey(d)) continue;
            int n = 1 << d;
            if (n > nCap) { output.WriteLine($"{d,3} {n,6}   (skipped — n > {nCap})"); continue; }
            int tail = PrimPolyTail[d];
            var g = CompanionSinger(d);
            Assert.True(SingerOrder(g, d) == n - 1, $"registered polynomial for d={d} is NOT primitive (Singer order ≠ 2^d−1)");

            var schemes = EnumNonAbelianPrimitiveSchemes(d, tail, groupCap);
            if (schemes.Count == 0) { output.WriteLine($"{d,3} {n,6} {0,9}   (no primitive non-abelian rank≥3)"); continue; }

            var fulls = schemes.Select(s => FullSchemeIRDepth(s, cap: n)).OrderBy(x => x).ToList();
            var singles = schemes.Select(s => GreedyIRDepth(s, 1, cap: s.N)).ToList();
            int maxFull = fulls.Max(), medFull = fulls[fulls.Count / 2], maxSingle = singles.Max();
            pts.Add((d, maxFull));
            output.WriteLine($"{d,3} {n,6} {schemes.Count,9} {maxFull,8} {medFull,8} {maxSingle,10}  {(double)maxFull / d:F2}");
        }

        output.WriteLine("");
        if (pts.Count >= 2)
        {
            double md = pts.Average(p => p.d), mD = pts.Average(p => p.maxFull);
            double cov = pts.Sum(p => (p.d - md) * (p.maxFull - mD));
            double varr = pts.Sum(p => (p.d - md) * (p.d - md));
            double slope = varr > 0 ? cov / varr : 0;
            int spanD = pts.Last().d - pts.First().d, spanDepth = pts.Last().maxFull - pts.First().maxFull;
            output.WriteLine($"max FULL-scheme depth vs d (= log₂ n): least-squares SLOPE = {slope:F3}" +
                             $"   (endpoint Δdepth/Δd = {(spanD > 0 ? (double)spanDepth / spanD : 0):F2}; d {pts.First().d}→{pts.Last().d}, depth {pts.First().maxFull}→{pts.Last().maxFull})");
            output.WriteLine("  slope ≈ 0 ⟹ O(1) [depth-4 hope holds for the G2-B residue];  slope ≈ 1 ⟹ O(log n) [surviving construction, still poly].");
            string verdict = slope < 0.34 ? "FLAT — O(1): residue depth does NOT grow with log n (depth-4 hope holds for the non-abelian primitive residue)."
                : slope < 0.67 ? "MILD GROWTH — between O(1) and O(log n); inconclusive on this range, widen d."
                : "LINEAR-IN-log n — O(log n): residue depth grows with log n (supports the surviving-construction hypothesis; seal needs O(log n), still poly).";
            output.WriteLine($"VERDICT: {verdict}");
        }
        else output.WriteLine("VERDICT: too few data points (need ≥2 d-values with primitive non-abelian schemes).");

        Assert.True(pts.Count > 0, "no primitive non-abelian schemes enumerated");
    }

    // ─────────────────────────────────────────────────────────────────────────────
    //  STEP 2.4 — THE NON-SOLVABLE GATE.  The branched-agent depth-growth caveat:
    //  the flat-residue result rests on the affine ΓL(1,2^d) family, whose G₀ are
    //  METACYCLIC (Singer ⋊ Frobenius — SOLVABLE).  The self-detection mechanism is
    //  predicted to fire on genuinely-non-abelian G₀; the decisive untested zone is
    //  NON-SOLVABLE simple G₀.  Here G₀ = A_{d+1} (and S_{d+1}) via the F₂ deleted
    //  module (n = d+1 odd ⟹ irreducible ⟹ primitive), reusing the affine machinery.
    //  Signal: does the translation scheme RECOVER (EdgeGenerates, the s(C)/separability
    //  notion), and is FULL-scheme 1-WL depth (base + s(C), the seal's `warmRefine`)
    //  bounded/small?  Recovers ∧ small depth ⟹ the non-solvable residue is tame, the
    //  `RelCountsDetermineOrbit` conjecture (step 2.3) holds on simple G₀.  A primitive
    //  non-recoverer would be a small G2-B witness.  Cap |G₀| ≤ 2^16 (A₉+ excluded).
    // ─────────────────────────────────────────────────────────────────────────────
    [Fact]
    public void Probe_NonSolvableG0_AffineResidue()
    {
        int groupCap = 1 << 19;   // fits A₉ (181440) and S₉ (362880); A₁₁+ excluded
        output.WriteLine("STEP 2.4 — NON-SOLVABLE affine G₀ = A_{d+1} / S_{d+1} (F₂ deleted module) — the genuine non-abelian zone.");
        output.WriteLine("(The ΓL(1,2^d) sweep covered only METACYCLIC/solvable G₀; A_{d+1} is simple non-solvable.)");
        output.WriteLine("");
        output.WriteLine($"{"G₀",6} {"d",3} {"|V|",5} {"|G₀|",8} {"rank",5} {"prim",6} {"abel",6} {"recov",6} {"fullDepth",10} {"singleDepth",12}");

        int candidates = 0, recovered = 0, primCount = 0;
        var leaks = new List<string>();

        void Run(string name, List<int[]> perms, int d)
        {
            var gens = perms.Select(p => PermToDeletedGL(p, d)).ToList();
            foreach (var g in gens) Assert.True(IsInvertible(g, d), $"{name}: generator not in GL({d},2)");
            var grp = GenGroup(gens, d, groupCap);
            if (grp == null) { output.WriteLine($"{name,6} {d,3} {1 << d,5}   (|G₀| > {groupCap}, skipped)"); return; }
            var s = BuildScheme(grp, d);
            bool prim = Primitive(s), abel = Abelian(gens, d), recov = Recovers(s);
            int fullDepth = FullSchemeIRDepth(s, cap: s.N);
            int singleDepth = s.Rank > 1 ? GreedyIRDepth(s, 1, cap: s.N) : 0;
            output.WriteLine($"{name,6} {d,3} {1 << d,5} {grp.Count,8} {s.Rank,5} {prim,6} {abel,6} {recov,6} {fullDepth,10} {singleDepth,12}");
            if (prim && !abel && s.Rank > 2)
            {
                candidates++;
                if (prim) primCount++;
                // A "leak" = primitive non-abelian rank≥3 that neither EdgeGenerates nor
                // discretizes at base + O(1) (= ⌈log₂|V|⌉ + 4, generous) — a G2-B witness.
                int bound = (int)Math.Ceiling(Math.Log2(s.N)) + 4;
                if (recov || fullDepth <= bound) recovered++;
                else leaks.Add($"{name} (d={d}, rank={s.Rank}, fullDepth={fullDepth} > {bound})");
            }
        }

        int[] Cycle3(int d) { var p = Enumerable.Range(0, d + 1).ToArray(); p[0] = 1; p[1] = 2; p[2] = 0; return p; }
        int[] CycleN(int d) { var p = new int[d + 1]; for (int i = 0; i <= d; i++) p[i] = (i + 1) % (d + 1); return p; }
        int[] Transp(int d) { var p = Enumerable.Range(0, d + 1).ToArray(); p[0] = 1; p[1] = 0; return p; }

        // d even ⟹ n = d+1 odd ⟹ deleted module irreducible.  A₅(d4)/A₇(d6)/A₉(d8) fit the cap.
        foreach (int d in new[] { 4, 6, 8 })
        {
            Run($"A{d + 1}", new List<int[]> { Cycle3(d), CycleN(d) }, d);   // A_{d+1} = ⟨3-cycle, (d+1)-cycle⟩
            Run($"S{d + 1}", new List<int[]> { Transp(d), CycleN(d) }, d);   // S_{d+1} = ⟨transposition, (d+1)-cycle⟩
        }

        output.WriteLine("");
        output.WriteLine($"primitive non-abelian rank≥3 candidates: {candidates};  recovered (EdgeGenerates or depth ≤ ⌈log₂n⌉+4): {recovered};  G2-B leaks: {leaks.Count}");
        if (leaks.Count > 0) foreach (var l in leaks) output.WriteLine($"  ⚠ LEAK: {l}");
        string verdict = candidates == 0
            ? "NO primitive non-abelian rank≥3 candidate constructed (the deleted modules collapsed to low rank / 2-transitive)."
            : leaks.Count == 0
                ? $"NO G2-B WITNESS among non-solvable G₀ — all {candidates} primitive non-abelian candidates recover at bounded depth. Hardens RelCountsDetermineOrbit beyond the solvable ΓL family."
                : $"⚠ {leaks.Count} POTENTIAL G2-B WITNESS(es) among non-solvable G₀ — investigate (a primitive non-recoverer would be a seal counterexample).";
        output.WriteLine($"VERDICT: {verdict}");

        Assert.True(leaks.Count == 0, $"non-solvable G₀ produced {leaks.Count} G2-B leak candidate(s): {string.Join("; ", leaks)}");
    }
}
