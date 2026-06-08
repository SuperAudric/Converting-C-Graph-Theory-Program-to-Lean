using System;
using System.Collections.Generic;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using Xunit;
using Xunit.Abstractions;

// ─────────────────────────────────────────────────────────────────────────────
// Hanaki–Miyamoto catalogue falsifier — the DECISIVE G2-B test (board item (f)).
//
// CONTEXT (docs/chain-descent-seal-handoff.md §4 G2-B + §G2 board (f);
// chain-descent-exhaustive-obstruction.md §0.7.6).  The oracle-capability seal
// closes iff the leak quadrant G2-B is empty: a *small, primitive, non-abelian,
// non-recovering* SCHURIAN scheme.  The affine probe (AffineSchemeProbe.cs) swept
// the translation-scheme family V⋊G0 and found no witness; this probe is the
// SHARPER, EXHAUSTIVE instrument the docs single out as decisive — Akihide Hanaki
// & Izumi Miyamoto's complete enumeration of association schemes of small order
// (http://math.shinshu-u.ac.jp/~hanaki/as/).  It checks EVERY small association
// scheme directly, not a constructed family.
//
// THE TEST.  For each catalogue scheme: is it primitive?  schurian?  does it
// recover (separable / low s(C))?  A *primitive, schurian, non-abelian,
// non-recovering* scheme of small order is a 16-vertex (or similar) COUNTEREXAMPLE
// to the seal as stated (a statement change).  Finding NONE across the catalogue
// is empirical support for "primitive schurian ⟹ separable" = G2-B emptiness.
//
// DATA.  GraphCanonizationProject.Tests/data/hanaki/as<N>.gz — the catalogue's GAP
// data files (gzipped), one per order N, each a list of n×n relation matrices
// M[i][j] = index of the basis relation containing the ordered pair (i,j),
// M[i][i] = 0 (the diagonal relation R_0).  The files omit ONLY the thin
// regular-group scheme of each order (the "from groups" rep — regular ⟹ recovers
// at depth 1, abelian-or-thin ⟹ not a G2-B candidate), so the PRIMITIVE schemes
// (the only possible witnesses) are all present.  Validated below against the
// catalogue's published per-order primitive/commutative counts.
//
// RECOVERY proxies (mirroring AffineSchemeProbe / Scheme.lean theorem_2_HOR):
//   • EdgeGenerates(j0)  — the project's depth-1 algebraic recovery: the
//     intersection-number isolation closure seeded with {R_0, R_j0} reaches all
//     relations.  recovers ⟺ ∃ j0 EdgeGenerates(j0).
//   • WLDepth — the s(C)-aligned graded measure: # vertex individualizations to
//     discretize the full coloured scheme by 1-WL (the WL-dimension proxy).
//     Bounded (≤ base+O(1)) ⟹ separable / tame; growing ⟹ high s(C).
//
// No production code is touched.
// ─────────────────────────────────────────────────────────────────────────────
public class CatalogueSchemeProbe(ITestOutputHelper output)
{
    // Published per-order counts from the catalogue index (http://math.shinshu-u.ac.jp/~hanaki/as/),
    // columns: [#assocSchemes, #fromGroups, #primitive, #noncommutative, #nonSchurian].
    // The DATA files omit the #fromGroups thin schemes, so data-primitive ==
    // index-primitive for composite orders and index-primitive−1 for primes (the
    // omitted thin Z_p scheme is primitive but recovers trivially).
    static readonly Dictionary<int, int[]> IndexCounts = new()
    {
        [5] = [3, 1, 3, 0, 0], [6] = [8, 2, 1, 1, 0], [7] = [4, 1, 4, 0, 0],
        [8] = [21, 5, 1, 2, 0], [9] = [12, 2, 2, 0, 0], [10] = [13, 2, 2, 2, 0],
        [11] = [4, 1, 4, 0, 0], [12] = [59, 5, 1, 12, 0], [13] = [6, 1, 6, 0, 0],
        [14] = [16, 2, 1, 2, 0], [15] = [25, 1, 3, 1, 1], [16] = [222, 14, 6, 49, 16],
        [17] = [5, 1, 5, 0, 0], [18] = [95, 5, 1, 22, 2], [19] = [7, 1, 7, 0, 1],
        [20] = [95, 5, 1, 22, 0], [21] = [32, 2, 3, 3, 0], [22] = [16, 2, 1, 2, 0],
        [23] = [22, 1, 22, 0, 18], [24] = [750, 15, 1, 242, 81], [25] = [45, 2, 16, 0, 13],
        [26] = [34, 2, 11, 4, 10], [27] = [502, 5, 378, 10, 380], [28] = [185, 4, 8, 22, 61],
        [29] = [26, 1, 26, 0, 20], [30] = [243, 4, 1, 66, 15],
    };

    // ── A parsed association scheme: relOf[i,j] ∈ {0..rank-1}, relOf[i,i]=0. ────
    sealed class Scheme
    {
        public required int N;             // points
        public required int Rank;          // number of basis relations (incl R_0)
        public required int[,] Rel;        // Rel[i,j] = relation index of pair (i,j)
        public required int[] Valency;     // |{j : Rel[i,j]=k}| (constant over i)
        public required int[,,] P;         // P[k,i,j] = p^k_{ij}
        public required bool Symmetric;    // every relation equals its transpose
        public required bool Commutative;  // p^k_{ij} = p^k_{ji}
    }

    // ── GAP parser: split the file on "# No. <k>", take the last n*n integers of
    //    each block as the row-major relation matrix. ─────────────────────────────
    static List<int[,]> ParseCatalogue(string gzPath, int n)
    {
        string raw;
        using (var fs = File.OpenRead(gzPath))
        using (var gz = new GZipStream(fs, CompressionMode.Decompress))
        using (var sr = new StreamReader(gz))
            raw = sr.ReadToEnd();

        var schemes = new List<int[,]>();
        // blocks between "# No." markers; the file preamble (before the first marker)
        // has no matrix and is dropped because it has < n*n ints.
        var blocks = Regex.Split(raw, @"#\s*No\.\s*\d+");
        foreach (var b in blocks)
        {
            // strip any residual comment lines, then pull integers
            var clean = string.Join("\n", b.Split('\n').Where(l => !l.TrimStart().StartsWith("#")));
            var ints = Regex.Matches(clean, @"-?\d+").Select(m => int.Parse(m.Value)).ToList();
            if (ints.Count < n * n) continue;
            var vals = ints.Skip(ints.Count - n * n).ToArray();   // last n*n = the matrix
            var M = new int[n, n];
            for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) M[i, j] = vals[i * n + j];
            schemes.Add(M);
        }
        return schemes;
    }

    // Build a Scheme from a raw relation matrix; returns null if it is not a valid
    // homogeneous association scheme (diagonal R_0, constant valencies, well-defined
    // intersection numbers).  The validity check is the parsing/correctness gate.
    static Scheme? BuildScheme(int[,] M, int n)
    {
        // relabel relation values to 0..rank-1, forcing the diagonal value to 0
        int diag = M[0, 0];
        var labels = new SortedSet<int>();
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) labels.Add(M[i, j]);
        var remap = new Dictionary<int, int> { [diag] = 0 };
        int next = 1;
        foreach (var v in labels) if (v != diag) remap[v] = next++;
        int rank = remap.Count;
        var rel = new int[n, n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) rel[i, j] = remap[M[i, j]];

        // R_0 must be exactly the diagonal
        for (int i = 0; i < n; i++)
        {
            if (rel[i, i] != 0) return null;
            for (int j = 0; j < n; j++) if (i != j && rel[i, j] == 0) return null;
        }

        // valencies constant over the base point (homogeneity)
        var val = new int[rank];
        for (int j = 0; j < n; j++) val[rel[0, j]]++;
        for (int i = 1; i < n; i++)
        {
            var v = new int[rank];
            for (int j = 0; j < n; j++) v[rel[i, j]]++;
            for (int k = 0; k < rank; k++) if (v[k] != val[k]) return null;
        }

        // intersection numbers p^k_{ij} from a representative pair of each relation k,
        // validated against a second representative (well-definedness).
        var P = new int[rank, rank, rank];
        for (int k = 0; k < rank; k++)
        {
            // first representative pair (x,y) with rel[x,y]=k
            int rx = -1, ry = -1;
            for (int x = 0; x < n && rx < 0; x++) for (int y = 0; y < n; y++) if (rel[x, y] == k) { rx = x; ry = y; break; }
            for (int z = 0; z < n; z++) P[k, rel[rx, z], rel[z, ry]]++;
            // validate against a different representative if one exists
            for (int x = 0; x < n; x++)
            {
                for (int y = 0; y < n; y++)
                {
                    if (rel[x, y] != k || (x == rx && y == ry)) continue;
                    var q = new int[rank, rank];
                    for (int z = 0; z < n; z++) q[rel[x, z], rel[z, y]]++;
                    for (int i = 0; i < rank; i++) for (int j = 0; j < rank; j++) if (q[i, j] != P[k, i, j]) return null;
                    goto nextK;   // one extra representative suffices as a guard
                }
            }
            nextK:;
        }

        bool sym = true;
        for (int i = 0; i < n && sym; i++) for (int j = 0; j < n; j++) if (rel[i, j] != rel[j, i]) { sym = false; break; }
        bool comm = true;
        for (int k = 0; k < rank && comm; k++) for (int i = 0; i < rank && comm; i++) for (int j = 0; j < rank; j++) if (P[k, i, j] != P[k, j, i]) { comm = false; break; }

        return new Scheme { N = n, Rank = rank, Rel = rel, Valency = val, P = P, Symmetric = sym, Commutative = comm };
    }

    // Primitive ⟺ every non-diagonal relation graph is connected (no proper closed
    // subset / block system).
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

    // EdgeGenerates(j0): the project's depth-1 recovery (isolation closure from
    // {R_0, R_j0}); identical logic to AffineSchemeProbe.EdgeGenerates.
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

    // WLDepth: # vertex individualizations to discretize the full coloured scheme by
    // 1-WL (the s(C) / WL-dimension proxy).  Greedy: individualize the lex-min vertex
    // of the largest non-singleton cell each round.  Returns depth, or cap+1.
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

    // 1-WL on the coloured scheme: each vertex's colour is refined by the sorted
    // multiset of (relation, neighbour-colour) over all other vertices.
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

    // ── Automorphism group of the coloured scheme (only run on candidates / self-test).
    //    Backtracking with relation-consistency pruning; enumerates all automorphisms
    //    up to `cap` (returns null if it exceeds cap = "large").  An automorphism is a
    //    permutation π with Rel[π i, π j] = Rel[i, j] for all i,j. ──────────────────
    static List<int[]>? AutGroup(Scheme s, int cap)
    {
        int n = s.N;
        var autos = new List<int[]>();
        var img = new int[n]; var used = new bool[n];
        for (int i = 0; i < n; i++) img[i] = -1;

        bool Extend(int k)
        {
            if (k == n) { autos.Add((int[])img.Clone()); return autos.Count <= cap; }
            for (int w = 0; w < n; w++)
            {
                if (used[w]) continue;
                bool ok = true;
                for (int a = 0; a < k && ok; a++)
                    if (s.Rel[k, a] != s.Rel[w, img[a]] || s.Rel[a, k] != s.Rel[img[a], w]) ok = false;
                if (s.Rel[k, k] != s.Rel[w, w]) ok = false;
                if (!ok) continue;
                img[k] = w; used[w] = true;
                if (!Extend(k + 1)) return false;     // cap exceeded — bail
                img[k] = -1; used[w] = false;
            }
            return true;
        }
        bool completed = Extend(0);
        return completed ? autos : null;
    }

    // From the full automorphism list: vertex-transitive?, #2-orbitals, schurian
    // (vertex-transitive ∧ #orbitals == rank), abelian (a generating subset commutes).
    static (bool transitive, int orbitals, bool schurian, bool abelian, long order) Analyze(Scheme s, List<int[]> autos)
    {
        int n = s.N;
        // vertex orbit of 0
        var vseen = new bool[n];
        foreach (var g in autos) vseen[g[0]] = true;
        bool transitive = vseen.Count(b => b) == n && autos.All(g => true);
        // proper transitivity: orbit of 0 under the group = all (use union-find over generators ≈ all elements)
        var reach = new bool[n]; reach[0] = true;
        foreach (var g in autos) reach[g[0]] = true;
        transitive = reach.Count(b => b) == n;

        // 2-orbitals: orbit of each ordered pair under the group
        var pairOrbit = new int[n, n]; for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) pairOrbit[i, j] = -1;
        int orb = 0;
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++)
        {
            if (pairOrbit[i, j] != -1) continue;
            int id = orb++;
            foreach (var g in autos) pairOrbit[g[i], g[j]] = id;
        }
        bool schurian = transitive && orb == s.Rank;

        // abelian: extract a small generating set by closure-growth, then check it commutes
        bool abelian = GeneratorsCommute(autos, n);
        return (transitive, orb, schurian, abelian, autos.Count);
    }

    static int[] Compose(int[] a, int[] b) { var c = new int[a.Length]; for (int i = 0; i < a.Length; i++) c[i] = a[b[i]]; return c; }
    static string PKey(int[] p) => string.Join(",", p);

    static bool GeneratorsCommute(List<int[]> autos, int n)
    {
        var id = Enumerable.Range(0, n).ToArray();
        var closure = new HashSet<string> { PKey(id) };
        var elems = new List<int[]> { id };
        var gens = new List<int[]>();
        foreach (var g in autos)
        {
            if (closure.Contains(PKey(g))) continue;
            gens.Add(g);
            // recompute closure of current gens (small)
            closure = new HashSet<string> { PKey(id) }; elems = new List<int[]> { id };
            var q = new Queue<int[]>(); q.Enqueue(id);
            while (q.Count > 0)
            {
                var x = q.Dequeue();
                foreach (var t in gens) { var h = Compose(x, t); var key = PKey(h); if (closure.Add(key)) { elems.Add(h); q.Enqueue(h); } }
            }
            if (closure.Count >= autos.Count) break;   // gens already generate everything
        }
        for (int a = 0; a < gens.Count; a++) for (int b = a + 1; b < gens.Count; b++)
            if (PKey(Compose(gens[a], gens[b])) != PKey(Compose(gens[b], gens[a]))) return false;
        return true;
    }

    static string DataPath(int n)
    {
        string fn = $"as{n:D2}.gz";
        // probe a few roots so the test works from bin/ or the project dir
        foreach (var root in new[]
        {
            Path.Combine(AppContext.BaseDirectory, "data", "hanaki"),
            Path.Combine(AppContext.BaseDirectory, "..", "..", "..", "data", "hanaki"),
            Path.Combine(Directory.GetCurrentDirectory(), "data", "hanaki"),
        })
        {
            var p = Path.GetFullPath(Path.Combine(root, fn));
            if (File.Exists(p)) return p;
        }
        return "";
    }

    // ── The falsifier ─────────────────────────────────────────────────────────
    [Fact]
    public void Probe_HanakiMiyamotoCatalogue()
    {
        int autCap = 200_000;                       // |Aut| enumeration cap ("large" above this)
        var orders = Enumerable.Range(5, 26).ToArray();   // 5..30

        int totalParsed = 0, totalValid = 0, totalPrimitive = 0, primRecover = 0;
        int edgeFailButBoundedWL = 0;   // primitives that fail depth-1 EdgeGenerates yet recover at bounded WL-depth
        var candidates = new List<(int n, int idx, Scheme s, int wl, bool edge)>();
        int validationMismatches = 0;

        foreach (int n in orders)
        {
            var path = DataPath(n);
            if (path == "") { output.WriteLine($"order {n}: data file missing — skip"); continue; }

            var raw = ParseCatalogue(path, n);
            int parsed = 0, valid = 0, primitive = 0, recov = 0, nonComm = 0, symmetric = 0;
            int wlMax = 0;
            var primRows = new List<string>();

            for (int idx = 0; idx < raw.Count; idx++)
            {
                parsed++;
                var s = BuildScheme(raw[idx], n);
                if (s is null) { output.WriteLine($"  ⚠ order {n} scheme #{idx + 1}: NOT a valid association scheme (parse/validity gate failed)"); continue; }
                valid++;
                if (!s.Commutative) nonComm++;
                if (s.Symmetric) symmetric++;
                if (s.Rank <= 2) continue;                 // rank-2 = complete graph, trivially recovers
                if (!Primitive(s)) continue;
                primitive++;

                bool edge = Recovers(s);
                int wl = WLDepth(s, cap: n);
                wlMax = Math.Max(wlMax, wl);
                bool tame = edge || wl <= (int)Math.Ceiling(Math.Log2(n)) + 2;
                if (tame) recov++;
                else candidates.Add((n, idx + 1, s, wl, edge));
                if (!edge && tame) edgeFailButBoundedWL++;

                primRows.Add($"#{idx + 1} rank={s.Rank} val=[{string.Join(",", s.Valency.Skip(1))}] " +
                             $"{(s.Symmetric ? "sym" : "asym")} {(s.Commutative ? "comm" : "NONcomm")} " +
                             $"edgeGen={(edge ? "yes" : "NO")} WLdepth={wl} {(tame ? "" : "★CANDIDATE")}");
            }

            totalParsed += parsed; totalValid += valid; totalPrimitive += primitive; primRecover += recov;

            // cross-check primitive + noncommutative counts against the published index
            string vnote = "";
            if (IndexCounts.TryGetValue(n, out var ic))
            {
                bool prime = ic[0] >= 0 && IsPrime(n);
                int expectPrim = ic[2] - (prime ? 1 : 0);   // data omits the thin Z_p (primitive) for primes
                // rank-2 complete-graph scheme is primitive in the index but skipped here (rank≤2):
                // it is present in the data for composite orders, omitted (thin) reasoning aside, so
                // compare primitive-with-rank≥3 against index-primitive minus the rank-2 trivial.
                int primGe3 = primitive;
                int idxPrimGe3 = expectPrim - 1;            // minus the rank-2 complete-graph scheme
                string flag = (primGe3 == idxPrimGe3) ? "ok" : "DIFFERS";
                if (primGe3 != idxPrimGe3) validationMismatches++;
                int idxNonComm = ic[3];
                string ncflag = (nonComm == idxNonComm) ? "ok" : (nonComm <= idxNonComm ? "≤(thin omitted)" : "DIFFERS");
                if (nonComm > idxNonComm) validationMismatches++;
                vnote = $"  [validate: primitive(rank≥3) {primGe3} vs index {idxPrimGe3} {flag}; noncomm {nonComm} vs index {idxNonComm} {ncflag}]";
            }

            output.WriteLine($"════ order {n} ════ parsed={parsed} valid={valid} primitive(rank≥3)={primitive} recover={recov} WLdepth≤{wlMax}{vnote}");
            foreach (var r in primRows) output.WriteLine($"      {r}");
        }

        output.WriteLine("");
        output.WriteLine("──────────────────────────────────────────────────────────────");
        output.WriteLine($"orders swept: {orders.First()}..{orders.Last()}");
        output.WriteLine($"schemes parsed: {totalParsed};  valid association schemes: {totalValid}");
        output.WriteLine($"primitive (rank≥3) schemes examined: {totalPrimitive};  of those tame/recover: {primRecover}");
        output.WriteLine($"  of which fail depth-1 EdgeGenerates but recover at bounded WL-depth: {edgeFailButBoundedWL}");
        output.WriteLine($"    (these confirm the 'corrected target': bounded-depth recovery, base+O(1), NOT depth-1 — seal-handoff §G2 board)");
        output.WriteLine($"validation mismatches vs published catalogue counts: {validationMismatches}");
        output.WriteLine("");

        // ── classify the non-recovering primitive candidates (compute Aut) ──────
        output.WriteLine($"G2-B CANDIDATES (primitive ∧ ¬recover ∧ WLdepth>base+O(1)): {candidates.Count}");
        int genuineWitness = 0;
        foreach (var (n, idx, s, wl, edge) in candidates)
        {
            var autos = AutGroup(s, autCap);
            if (autos is null)
            {
                output.WriteLine($"  ★ order {n} #{idx} rank={s.Rank} WLdepth={wl}: |Aut|>{autCap} (LARGE ⟹ Cameron-side, not a small-Aut leak)");
                continue;
            }
            var (trans, orb, schurian, abelian, ord) = Analyze(s, autos);
            int basebound = (int)Math.Floor(Math.Log2(Math.Max(1, ord))) + 2;
            bool genuine = schurian && !abelian && wl > basebound;
            if (genuine) genuineWitness++;
            output.WriteLine($"  ★ order {n} #{idx} rank={s.Rank} WLdepth={wl} edgeGen={edge}: " +
                             $"|Aut|={ord} {(trans ? "transitive" : "INTRANSITIVE")} orbitals={orb} " +
                             $"{(schurian ? "SCHURIAN" : "non-Schurian")} {(abelian ? "abelian" : "non-abelian")} " +
                             $"⟹ {(genuine ? "‼ GENUINE G2-B WITNESS (seal counterexample)" : "not a witness")}");
        }

        output.WriteLine("");
        if (candidates.Count == 0)
            output.WriteLine("VERDICT: every primitive scheme in the catalogue (orders 5..30) RECOVERS — no G2-B candidate. " +
                             "Decisive empirical support for 'primitive schurian ⟹ separable' = G2-B EMPTINESS.");
        else if (genuineWitness == 0)
            output.WriteLine("VERDICT: candidates found but NONE is a genuine witness (all large-Aut/Cameron-side or non-Schurian/abelian) — " +
                             "seal stands; G2-B emptiness supported.");
        else
            output.WriteLine($"VERDICT: {genuineWitness} GENUINE G2-B WITNESS(ES) — the seal as stated is FALSE on the catalogue; STATEMENT CHANGE REQUIRED.");

        // ── self-test of the Aut/schurian machinery on a known scheme (pentagon C5,
        //    the order-5 rank-3 scheme: Aut = D5, |Aut|=10, schurian, non-abelian). ──
        var p5path = DataPath(5);
        if (p5path != "")
        {
            var c5 = ParseCatalogue(p5path, 5).Select(M => BuildScheme(M, 5)!).First(x => x.Rank == 3);
            var a5 = AutGroup(c5, 1000)!;
            var (t5, o5, sch5, ab5, ord5) = Analyze(c5, a5);
            output.WriteLine($"[self-test] order-5 rank-3 scheme (pentagon C5): |Aut|={ord5} (expect 10), schurian={sch5} (expect True), abelian={ab5} (expect False)");
            Assert.Equal(10, ord5);
            Assert.True(sch5);
            Assert.False(ab5);
        }

        Assert.True(totalValid > 0, "no schemes parsed");
        Assert.Equal(0, genuineWitness);   // the falsifier's headline assertion: no seal counterexample in the catalogue
    }

    static bool IsPrime(int x) { if (x < 2) return false; for (int d = 2; d * d <= x; d++) if (x % d == 0) return false; return true; }
}
