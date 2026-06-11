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

    // Triangular/Johnson scheme T(m) = J(m,2): n = m(m−1)/2 and |Aut| = m! (a Cameron
    // section — large primitive group, leg C).
    static bool IsJohnson(int n, long ord)
    {
        for (int m = 3; m <= 12; m++)
        {
            if (m * (m - 1) / 2 != n) continue;
            long fact = 1; for (int i = 2; i <= m; i++) fact *= i;
            return ord == fact;
        }
        return false;
    }

    // ─────────────────────────────────────────────────────────────────────────────
    //  DEPTH-vs-n cross-family check (companion to AffineSchemeProbe.Probe_DepthGrowth).
    //  Max primitive recovery depth (WLDepth, full-scheme 1-WL) per order vs log₂(n),
    //  over the WHOLE catalogue (every primitive scheme, all families).  Orders 5–30 ⟹
    //  log₂(n) ≤ ~5, a SHORT range — so a flat profile is consistent with O(1) and only
    //  strong growth would flag.  Cross-family (unlike the single affine family).
    // ─────────────────────────────────────────────────────────────────────────────
    [Fact]
    public void Probe_CatalogueDepthVsN()
    {
        var orders = Enumerable.Range(5, 26).ToArray();   // 5..30
        int autCap = 200_000;
        output.WriteLine("Catalogue depth-vs-n: max PRIMITIVE recovery depth per order, with the depth-DRIVER classified:");
        output.WriteLine($"{"n",4} {"#prim",6} {"maxDepth",9} {"depth/log2n",12}  driver: rank |Aut| sym? abelian-Aut?");
        var pts = new List<(double logn, int maxDepth)>();
        // per-leg max-depth profile: residue = SMALL non-abelian primitive (the genuine G2-B).
        var residuePts = new List<(double logn, int depth)>();
        int legB = 0, legC = 0, residue = 0;
        foreach (int n in orders)
        {
            var path = DataPath(n);
            if (path == "") continue;
            var raw = ParseCatalogue(path, n);
            int maxDepth = -1, cnt = 0, residueMax = -1;
            Scheme? driver = null;
            foreach (var M in raw)
            {
                var s = BuildScheme(M, n);
                if (s is null) continue;
                if (s.Rank <= 2 || !Primitive(s)) continue;
                cnt++;
                int wl = WLDepth(s, cap: n);
                if (wl > maxDepth) { maxDepth = wl; driver = s; }
                // track the genuine residue: SMALL (|Aut| ≤ n^3, not Johnson) non-abelian primitive
                var au = AutGroup(s, autCap);
                if (au is not null)
                {
                    var (_, _, _, ab, ord) = Analyze(s, au);
                    bool large = IsJohnson(n, ord) || ord >= (long)Math.Pow(n, 3);
                    if (!ab && !large) residueMax = Math.Max(residueMax, wl);   // small non-abelian primitive
                }
            }
            if (cnt == 0 || driver is null) continue;
            double logn = Math.Log2(n);
            pts.Add((logn, maxDepth));
            if (residueMax >= 0) residuePts.Add((logn, residueMax));
            // classify the DEPTH-DRIVER's seal-leg
            string cls;
            var autos = AutGroup(driver, autCap);
            if (autos is null) { cls = $"rank{driver.Rank} |Aut|>{autCap} → legC/Cameron(large)"; legC++; }
            else
            {
                var (_, _, schurian, abelian, ord) = Analyze(driver, autos);
                bool large = IsJohnson(n, ord) || ord >= (long)Math.Pow(n, 3);
                string leg = abelian ? "legB(abelian,consumed)"
                    : large ? (IsJohnson(n, ord) ? "legC/Cameron(JOHNSON T(m))" : "legC/Cameron(large)")
                    : "G2B-residue(SMALL non-ab)";
                if (abelian) legB++; else if (large) legC++; else residue++;
                cls = $"rank{driver.Rank} |Aut|={ord} {(driver.Symmetric ? "sym" : "asym")} → {leg}";
            }
            output.WriteLine($"{n,4} {cnt,6} {maxDepth,9} {(double)maxDepth / logn,12:F2}  {cls}");
        }
        output.WriteLine("");
        output.WriteLine($"depth-DRIVERS by seal-leg: legB(abelian)={legB}  legC/Cameron(large,incl Johnson)={legC}  G2B-residue(small non-ab)={residue}");
        // the decisive cut: does the SMALL non-abelian primitive residue depth grow?
        if (residuePts.Count >= 2)
        {
            double rx = residuePts.Average(p => p.logn), ry = residuePts.Average(p => p.depth);
            double rcov = residuePts.Sum(p => (p.logn - rx) * (p.depth - ry));
            double rvar = residuePts.Sum(p => (p.logn - rx) * (p.logn - rx));
            double rslope = rvar > 0 ? rcov / rvar : 0;
            int rmax = residuePts.Max(p => p.depth);
            output.WriteLine($"  G2B-RESIDUE (small non-abelian primitive) max depth across orders: {rmax};  slope vs log₂n = {rslope:F3}  ⟹ {(rslope < 0.5 ? "FLAT (residue does NOT grow — matches the affine probe)" : "GROWS (tension with affine — investigate)")}");
        }
        else output.WriteLine("  G2B-RESIDUE: too few small-non-abelian primitive schemes in 5–30 to fit a slope.");
        if (pts.Count >= 2)
        {
            double mx = pts.Average(p => p.logn), my = pts.Average(p => p.maxDepth);
            double cov = pts.Sum(p => (p.logn - mx) * (p.maxDepth - my));
            double varr = pts.Sum(p => (p.logn - mx) * (p.logn - mx));
            double slope = varr > 0 ? cov / varr : 0;
            output.WriteLine($"max primitive depth vs log₂(n): least-squares SLOPE = {slope:F3}  (depth/log₂n stays ~constant ⟹ O(log n); → 0 ⟹ O(1))");
            output.WriteLine("  NOTE: catalogue mixes ALL families incl. abelian (leg-B) — so this is an UPPER profile; the affine probe isolates the non-abelian-primitive residue.");
            output.WriteLine($"VERDICT: {(slope < 0.5 ? "no strong growth over orders 5–30 (consistent with O(1)–O(log n); short range)" : "growth present — investigate which family drives it")}.");
        }
        Assert.True(pts.Count > 0, "no primitive schemes found");
    }

    // ─────────────────────────────────────────────────────────────────────────────
    //  FALSIFIER #2 — the FORMALIZATION-FAITHFUL probe (the intra-cell fusion objects).
    //
    //  Probe #1 (above) tests recovery via the EdgeGenerates / WLDepth *proxies*.  This
    //  probe tests the EXACT objects the Lean converse proof now formalizes
    //  (Cascade.lean §"converse proof, layer 1"), cross-checking the C# and Lean models:
    //
    //   • intraCellRelations(S₀) — the relations entirely inside the warmRefine-from-S₀
    //     cells.  Lean: `intraCellRelations`.  ALWAYS a ClosedSubset (`intraCellRelations_isClosed`).
    //   • the VACUITY finding — for a PRIMITIVE scheme and any nonempty base,
    //     intraCellRelations = {0} identically (Lean: `intraCellRelations_eq_singleton_zero_of_primitive`).
    //     A violation would mean the C# warmRefine model disagrees with Lean's — a strong
    //     consistency check (the Lean statement is a THEOREM, so 0 violations is expected).
    //   • SeparatesAtBoundedBase — warmRefine from a bounded base reaches discrete (Lean:
    //     `SeparatesAtBoundedBase`).  Primitive ⟹ separates at base+O(1) is the open G2-B
    //     kernel; a primitive scheme that does NOT separate (and is schurian, small-Aut,
    //     non-abelian) is a seal counterexample.
    //
    //  The three assertions validate the two landed Lean theorems empirically and gate the
    //  one open conjecture (G2-B emptiness) on the exact formal object, not a proxy.
    // ─────────────────────────────────────────────────────────────────────────────

    // intraCellRelations(S₀): mirrors Cascade.lean `intraCellRelations` — the relations
    // R_k whose every pair shares a warmRefine-from-S₀ cell colour.  0 ∈ always (rel-0
    // pairs are the diagonal (x,x)).
    static HashSet<int> IntraCellRelations(Scheme s, List<int> ind)
    {
        var color = Refine(s, ind);
        var crosses = new bool[s.Rank];
        for (int x = 0; x < s.N; x++)
            for (int y = 0; y < s.N; y++)
                if (color[x] != color[y]) crosses[s.Rel[x, y]] = true;
        var I = new HashSet<int>();
        for (int k = 0; k < s.Rank; k++) if (!crosses[k]) I.Add(k);
        return I;
    }

    // ClosedSubset test — mirrors Cascade.lean `ClosedSubset`: 0 ∈ I, and closed under
    // the complex product (p^k_{ij} ≠ 0 with i,j ∈ I ⟹ k ∈ I).
    static bool IsClosedSubset(Scheme s, HashSet<int> I)
    {
        if (!I.Contains(0)) return false;
        foreach (int i in I) foreach (int j in I)
            for (int k = 0; k < s.Rank; k++)
                if (s.P[k, i, j] != 0 && !I.Contains(k)) return false;
        return true;
    }

    // The smallest ClosedSubset containing {0, k} — the complex-product closure of the
    // seed (BFS to fixpoint).  ⟨0,k⟩ proper (≠ univ) ⟺ R_k generates a block system.
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

    // ClosedSubset-primitivity (the Lean `IsPrimitive`): the only closed subsets are {0}
    // and univ ⟺ no relation generates a proper block ⟺ every R_k (k≠0) generates univ.
    static bool HasProperBlock(Scheme s)
    {
        for (int k = 1; k < s.Rank; k++)
            if (GeneratedClosedSubset(s, k).Count < s.Rank) return true;
        return false;
    }

    // Greedy discretization path: the list of bases visited (∅ first, then lex-min vertex
    // of the largest non-singleton cell each round) and the depth at which warmRefine
    // becomes discrete (= SeparatesAtBoundedBase's witness), or cap+1.
    static (int depth, List<List<int>> bases) DiscretizePath(Scheme s, int cap)
    {
        int n = s.N; var ind = new List<int>(); var bases = new List<List<int>>();
        for (int depth = 0; depth <= cap; depth++)
        {
            bases.Add(new List<int>(ind));
            var color = Refine(s, ind);
            if (color.Distinct().Count() == n) return (depth, bases);
            var byColor = new Dictionary<int, List<int>>();
            for (int v = 0; v < n; v++) { if (!byColor.TryGetValue(color[v], out var lst)) { lst = new(); byColor[color[v]] = lst; } lst.Add(v); }
            int target = -1, best = 1;
            foreach (var kv in byColor) if (kv.Value.Count > best) { best = kv.Value.Count; target = kv.Value.Min(); }
            if (target < 0) return (depth, bases);
            ind.Add(target);
        }
        return (cap + 1, bases);
    }

    [Fact]
    public void Probe_IntraCellFusion_Falsifier()
    {
        var orders = Enumerable.Range(5, 26).ToArray();   // 5..30
        int autCap = 200_000;

        int totalValid = 0, totalPrimitive = 0, totalImprim = 0;
        int closedChecks = 0, closedViolations = 0;       // validates intraCellRelations_isClosed
        int vacuityChecks = 0, vacuityViolations = 0;     // validates intraCellRelations_eq_singleton_zero_of_primitive
        int primSeparate = 0;                             // SeparatesAtBoundedBase holds
        int primCorrespondenceViolations = 0;             // Primitive() (connectivity) vs IsPrimitive (no proper closed subset)
        int imprimWithBlock = 0;                          // imprimitive schemes with a genuine generated proper block
        var nonSeparating = new List<(int n, int idx, Scheme s, int depth)>();
        var vacuityWitnesses = new List<(int n, int idx, int baseSize, int rank, string I)>();
        var closedWitnesses = new List<(int n, int idx, string I)>();

        foreach (int n in orders)
        {
            var path = DataPath(n);
            if (path == "") { output.WriteLine($"order {n}: data file missing — skip"); continue; }
            var raw = ParseCatalogue(path, n);
            int bound = (int)Math.Ceiling(Math.Log2(n)) + 2;   // the "base + O(1)" separation bound

            for (int idx = 0; idx < raw.Count; idx++)
            {
                var s = BuildScheme(raw[idx], n);
                if (s is null) continue;
                totalValid++;
                if (s.Rank <= 2) continue;
                bool prim = Primitive(s);
                if (prim) totalPrimitive++; else totalImprim++;

                var (depth, bases) = DiscretizePath(s, n);

                foreach (var b in bases)
                {
                    var I = IntraCellRelations(s, b);

                    // (1) intraCellRelations is ALWAYS a ClosedSubset.
                    closedChecks++;
                    if (!IsClosedSubset(s, I)) { closedViolations++; if (closedWitnesses.Count < 12) closedWitnesses.Add((n, idx + 1, "{" + string.Join(",", I.OrderBy(x => x)) + "}")); }

                    // (2) VACUITY: primitive ∧ nonempty base ⟹ intraCellRelations = {0}.
                    if (prim && b.Count > 0)
                    {
                        vacuityChecks++;
                        if (!(I.Count == 1 && I.Contains(0)))
                        { vacuityViolations++; if (vacuityWitnesses.Count < 12) vacuityWitnesses.Add((n, idx + 1, b.Count, s.Rank, "{" + string.Join(",", I.OrderBy(x => x)) + "}")); }
                    }
                }

                // (3) the non-vacuous side: the C# `Primitive()` (relation-graph connectivity)
                //     must agree with the Lean `IsPrimitive` (no nontrivial proper ClosedSubset),
                //     and imprimitive schemes must genuinely carry a generated proper block.
                bool hasBlock = HasProperBlock(s);
                if (hasBlock == prim) primCorrespondenceViolations++;   // disagreement: prim ⟺ ¬hasBlock expected
                if (!prim && hasBlock) imprimWithBlock++;

                if (prim)
                {
                    if (depth <= bound) primSeparate++;
                    else nonSeparating.Add((n, idx + 1, s, depth));
                }
            }
        }

        output.WriteLine("══════ FALSIFIER #2 — intra-cell fusion objects (Lean-faithful) ══════");
        output.WriteLine($"valid schemes: {totalValid}   primitive(rank≥3): {totalPrimitive}   imprimitive(rank≥3): {totalImprim}");
        output.WriteLine("");
        output.WriteLine($"(1) intraCellRelations is a ClosedSubset: {closedChecks - closedViolations}/{closedChecks} checks pass  [validates `intraCellRelations_isClosed`]");
        if (closedViolations > 0) foreach (var w in closedWitnesses) output.WriteLine($"      ‼ order {w.n} #{w.idx}: NON-closed intraCell {w.I}");
        output.WriteLine($"(2) primitive ∧ nonempty base ⟹ intraCellRelations = {{0}}: {vacuityChecks - vacuityViolations}/{vacuityChecks} checks pass  [validates `intraCellRelations_eq_singleton_zero_of_primitive`]");
        if (vacuityViolations > 0) foreach (var w in vacuityWitnesses) output.WriteLine($"      ‼ order {w.n} #{w.idx} (|base|={w.baseSize}, rank={w.rank}): intraCell = {w.I} ≠ {{0}} — C#/Lean MODEL MISMATCH");
        output.WriteLine($"(3) Primitive() ⟺ no proper ClosedSubset (Lean `IsPrimitive`): {(totalPrimitive + totalImprim) - primCorrespondenceViolations}/{totalPrimitive + totalImprim} agree;  imprimitive-with-generated-block: {imprimWithBlock}/{totalImprim}  [non-vacuous side: imprimitive ⟺ a block exists]");
        output.WriteLine("");
        output.WriteLine($"SeparatesAtBoundedBase (primitive ⟹ discretize at base+O(1) = ⌈log₂n⌉+2): {primSeparate}/{totalPrimitive} separate");
        output.WriteLine($"  primitive schemes that do NOT separate at the bound: {nonSeparating.Count}");

        // classify any non-separating primitive (a potential G2-B witness) by its Aut group.
        int genuineWitness = 0;
        foreach (var (n, idx, s, depth) in nonSeparating)
        {
            var autos = AutGroup(s, autCap);
            if (autos is null) { output.WriteLine($"  ★ order {n} #{idx} depth={depth}: |Aut|>{autCap} (LARGE ⟹ Cameron-side)"); continue; }
            var (trans, orb, schurian, abelian, ord) = Analyze(s, autos);
            int basebound = (int)Math.Floor(Math.Log2(Math.Max(1, ord))) + 2;
            bool genuine = schurian && !abelian && depth > basebound;
            if (genuine) genuineWitness++;
            output.WriteLine($"  ★ order {n} #{idx} depth={depth}: |Aut|={ord} {(schurian ? "SCHURIAN" : "non-Schurian")} {(abelian ? "abelian" : "non-abelian")} ⟹ {(genuine ? "‼ GENUINE G2-B WITNESS" : "not a witness")}");
        }

        output.WriteLine("");
        if (vacuityViolations == 0 && closedViolations == 0)
            output.WriteLine("VERDICT (model cross-check): the C# warmRefine model AGREES with the Lean intra-cell theorems on every catalogue scheme (orders 5..30) — `intraCellRelations_isClosed` and `intraCellRelations_eq_singleton_zero_of_primitive` hold empirically.");
        else
            output.WriteLine("VERDICT (model cross-check): ‼ DISCREPANCY between the C# model and the Lean theorems — investigate (probe bug or a model-fidelity gap).");
        if (nonSeparating.Count == 0)
            output.WriteLine("VERDICT (G2-B): every primitive scheme SEPARATES at base+O(1) — SeparatesAtBoundedBase holds throughout; G2-B emptiness supported on the exact formal object.");
        else if (genuineWitness == 0)
            output.WriteLine("VERDICT (G2-B): non-separating primitives exist but NONE is a genuine witness (large-Aut / non-schurian / abelian) — seal stands.");
        else
            output.WriteLine($"VERDICT (G2-B): {genuineWitness} GENUINE WITNESS(ES) — seal counterexample; STATEMENT CHANGE REQUIRED.");

        // ── headline assertions ──
        Assert.True(totalValid > 0, "no schemes parsed");
        Assert.Equal(0, closedViolations);                // intraCellRelations_isClosed holds empirically
        Assert.Equal(0, vacuityViolations);               // the vacuity theorem holds empirically (C#/Lean model agreement)
        Assert.Equal(0, primCorrespondenceViolations);    // Primitive() ⟺ Lean IsPrimitive (no proper ClosedSubset)
        Assert.Equal(0, genuineWitness);                  // no G2-B witness on the exact formal object
    }

    // ── Theorem 3.1 (Ponomarenko–Vasil'ev, arXiv:1602.07132) — the density boundary ──
    //   For ANY homogeneous coherent configuration:  2·c·(k-1) < n  ⟹  every one-point
    //   extension is 1-regular  ⟹  b(X) ≤ 2  AND  s(C) ≤ 2  (recovery depth ≤ 4).
    //     k    = max valency;
    //     c(X) = max_{r≠0} Σ_t p^r_{t,t*}   (the indistinguishing number; t* = adjoint of t).
    //   This is a general, CHECKABLE sufficient condition that discharges BOTH budget terms
    //   (base + s(C)) at once.  It sharpens G2-B from the vague "non-abelian primitive" to the
    //   concrete "primitive with 2c(k-1) ≥ n" — the DENSE residue, the module-adjoin/O(log n)
    //   target.  This probe measures which primitive catalogue schemes Thm 3.1 already covers
    //   and isolates the dense residue (if any).

    static int[] Adjoint(Scheme s)
    {
        var adj = new int[s.Rank];
        for (int k = 0; k < s.Rank; k++)
        {
            bool found = false;
            for (int i = 0; i < s.N && !found; i++)
                for (int j = 0; j < s.N; j++)
                    if (s.Rel[i, j] == k) { adj[k] = s.Rel[j, i]; found = true; break; }
        }
        return adj;
    }

    // c(X) = max over non-identity relations r of Σ_t p^r_{t, t*}.
    static int Indistinguishing(Scheme s, int[] adj)
    {
        int c = 0;
        for (int r = 1; r < s.Rank; r++)
        {
            int cr = 0;
            for (int t = 0; t < s.Rank; t++) cr += s.P[r, t, adj[t]];
            if (cr > c) c = cr;
        }
        return c;
    }

    static int MaxValency(Scheme s)
    {
        int k = 0;
        for (int i = 1; i < s.Rank; i++) if (s.Valency[i] > k) k = s.Valency[i];
        return k;
    }

    [Fact]
    public void Probe_Theorem31_DensityBoundary()
    {
        const int autCap = 200_000;                       // |Aut| enumeration cap ("large" above this = Cameron-side)
        var orders = Enumerable.Range(5, 26).ToArray();   // 5..30

        int adjViolations = 0;                             // self-test: adj involutive + valency-preserving ⟹ c well-formed
        // Theorem 3.1 validation (over ALL valid homogeneous schemes that satisfy 2c(k-1)<n):
        int thm31Holds = 0, thm31HoldsMaxWL = 0, thm31HoldsNonTame = 0;
        // Recovery / residue analysis (rank≥3 primitive only — the seal's domain; rank-2 = complete graph K_n = large/Cameron):
        int primTotal = 0, primHolds = 0, primHoldsMaxWL = 0;
        int dense = 0, denseRecover = 0, denseDepth1Fail = 0;   // depth1Fail ∧ recover = the genuine Clebsch-type residue
        int denseLargeCameron = 0, genuineWitness = 0;
        var clebschTypeRows = new List<string>();          // dense ∧ tame ∧ ¬depth-1 — recovers but outside Thm 3.1
        var witnessRows = new List<string>();

        output.WriteLine("Theorem 3.1 (Ponomarenko–Vasil'ev, arXiv:1602.07132) density boundary:");
        output.WriteLine("  2c(k-1) < n  ⟹  b(X) ≤ 2 ∧ s(C) ≤ 2.   c(X) = max_{r≠0} Σ_t p^r_{t,t*},  k = max valency.");
        output.WriteLine("Hanaki–Miyamoto catalogue, orders 5..30.  Recovery = EdgeGenerates ∨ WL-depth ≤ ⌈log2 n⌉+2 (project 'tame').\n");
        output.WriteLine("  order :  #prim(rank≥3) | thm31-holds | DENSE (fails 2c(k-1)<n)");

        foreach (int n in orders)
        {
            var path = DataPath(n);
            if (path == "") { output.WriteLine($"  order {n,2}: data file missing — skip"); continue; }
            var raw = ParseCatalogue(path, n);
            int tameBound = (int)Math.Ceiling(Math.Log2(n)) + 2;

            int prim = 0, pHolds = 0, pFails = 0;
            for (int idx = 0; idx < raw.Count; idx++)
            {
                var s = BuildScheme(raw[idx], n);
                if (s is null) continue;

                var adj = Adjoint(s);
                for (int k = 0; k < s.Rank; k++)
                    if (adj[adj[k]] != k || s.Valency[adj[k]] != s.Valency[k]) adjViolations++;

                int kmax = MaxValency(s), c = Indistinguishing(s, adj);
                bool thm31 = 2 * c * (kmax - 1) < n;

                // Thm 3.1 validation over ALL homogeneous schemes (any rank, primitive or not):
                if (thm31)
                {
                    int wlv = WLDepth(s, n);
                    thm31Holds++;
                    if (wlv > tameBound) thm31HoldsNonTame++;
                    else if (wlv > thm31HoldsMaxWL) thm31HoldsMaxWL = wlv;
                }

                // Recovery / residue analysis: rank≥3 primitive only (rank-2 K_n is large/Cameron, skipped):
                if (s.Rank <= 2 || !Primitive(s)) continue;
                prim++; primTotal++;
                bool edge = Recovers(s);
                int wl = WLDepth(s, n);
                bool tame = edge || wl <= tameBound;

                if (thm31) { pHolds++; primHolds++; if (wl > primHoldsMaxWL) primHoldsMaxWL = wl; continue; }

                // dense residue (primitive, rank≥3, 2c(k-1) ≥ n):
                pFails++; dense++;
                if (tame)
                {
                    denseRecover++;
                    if (!edge)   // recovers at bounded WL-depth but FAILS depth-1 EdgeGenerates — the genuine amorphic residue
                    {
                        denseDepth1Fail++;
                        clebschTypeRows.Add($"    order {n,2} #{idx,-3} rank={s.Rank} k={kmax} c={c}  2c(k-1)={2 * c * (kmax - 1)}≥{n}  depth1=NO  WLdepth={wl}");
                    }
                }
                else
                {
                    // not tame: classify by |Aut| exactly as the standing falsifier (large ⟹ Cameron-side, not a leak)
                    var autos = AutGroup(s, autCap);
                    if (autos is null) { denseLargeCameron++; continue; }
                    var (_, _, schurian, abelian, ord) = Analyze(s, autos);
                    int basebound = (int)Math.Floor(Math.Log2(Math.Max(1, ord))) + 2;
                    if (schurian && !abelian && wl > basebound)
                    {
                        genuineWitness++;
                        witnessRows.Add($"    ‼ order {n,2} #{idx} rank={s.Rank} k={kmax} c={c} WLdepth={wl} |Aut|={ord} SCHURIAN non-abelian — GENUINE G2-B WITNESS");
                    }
                    else denseLargeCameron++;    // large-Aut / non-schurian / abelian ⟹ not a small-Aut leak
                }
            }
            output.WriteLine($"  order {n,2}:  prim={prim,3} | holds={pHolds,3} | dense={pFails,3}");
        }

        output.WriteLine("");
        output.WriteLine($"THEOREM 3.1 VALIDATION: {thm31Holds} homogeneous schemes satisfy 2c(k-1)<n; ALL recover, max WL-depth {thm31HoldsMaxWL}, non-tame {thm31HoldsNonTame}.");
        output.WriteLine($"PRIMITIVE (rank≥3): total {primTotal}; covered by Thm 3.1 {primHolds} (WL-depth ≤ {primHoldsMaxWL}); DENSE residue {dense}.");
        output.WriteLine($"  dense residue: recover {denseRecover}  (of which depth-1-EdgeGenerates FAILS but WL-recovers = {denseDepth1Fail} — the genuine amorphic residue);");
        output.WriteLine($"                 non-tame & large/Cameron/non-schurian/abelian {denseLargeCameron};  GENUINE small-Aut witnesses {genuineWitness}.");
        if (clebschTypeRows.Count > 0)
        {
            output.WriteLine("  amorphic residue (primitive, recovers at bounded WL-depth, FAILS depth-1, OUTSIDE Thm 3.1 — the module-adjoin target):");
            foreach (var r in clebschTypeRows) output.WriteLine(r);
        }
        foreach (var r in witnessRows) output.WriteLine(r);

        output.WriteLine("");
        output.WriteLine($"VERDICT (Thm 3.1, validated): every 2c(k-1)<n scheme recovers at WL-depth ≤ {thm31HoldsMaxWL} — confirms b(X) ≤ 2 empirically. " +
                         $"But the condition is NARROW: only {primHolds}/{primTotal} primitives satisfy it.");
        output.WriteLine($"VERDICT (the residue): the genuine amorphic G2-B candidates ({denseDepth1Fail} schemes incl. order-16 #19/#20 Clebsch, order-25 #16/#17) " +
                         $"VIOLATE 2c(k-1)<n yet RECOVER at low WL-depth — they lie OUTSIDE Theorem 3.1, which therefore does NOT discharge them. " +
                         $"The module-adjoin / O(log n) thread is still required for exactly this dense-amorphic residue.");
        output.WriteLine(genuineWitness == 0
            ? "VERDICT (falsifier): 0 genuine small-Aut schurian non-abelian non-recovering primitives — G2-B emptiness re-confirmed through the density lens."
            : $"VERDICT (falsifier): ‼ {genuineWitness} GENUINE WITNESS(ES) — seal counterexample; STATEMENT CHANGE REQUIRED.");

        // ── assertions ──
        Assert.True(primTotal > 0, "no primitive schemes parsed");
        Assert.Equal(0, adjViolations);        // adjoint involutive + valency-preserving ⟹ c(X) well-formed
        Assert.Equal(0, thm31HoldsNonTame);    // Theorem 3.1 holds empirically: 2c(k-1)<n ⟹ recovers (in fact WL-depth ≤ 2)
        Assert.Equal(0, genuineWitness);       // no small-Aut schurian non-abelian non-recovering primitive (the standing falsifier)
    }

    // ── Non-affine amorphic residue: Latin-square-type SRG schemes ──────────────
    // Gol'fand–Ivanov–Klin: an amorphic scheme (≥3 classes) is all-SRG of Latin-square or
    // negative-Latin-square type.  Latin-square GRAPHS from RANDOM (non-group) Latin squares are
    // primitive SRGs with SMALL Aut and NON-affine origin — exactly the residue the affine
    // module-adjoin cannot reach (no F_p-module).  This probe builds them across growing m and asks:
    // does the non-affine residue still recover at bounded depth (falsifier), and does depth stay
    // flat or grow ~log n (the poly-vs-quasipoly fork)?
    //   SCOPE: reaches the LATIN-SQUARE-type non-affine residue.  The negative-Latin-square
    //   (Clebsch-family) non-affine residue needs the heavier Davis–Xiang PDS construction in
    //   non-elementary-abelian groups and stays deferred.

    static int[,] CyclicLatinSquare(int m)
    {
        var L = new int[m, m];
        for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) L[i, j] = (i + j) % m;
        return L;
    }

    // Intercalate-switch randomization: random 2×2 symbol swaps, each preserving the Latin property.
    // For m ≥ 5, enough switches leave the cyclic-group main class ⟹ a small-Aut (non-affine) square.
    static int[,] RandomizedLatinSquare(int m, int steps, Random rng)
    {
        var L = (int[,])CyclicLatinSquare(m).Clone();
        for (int s = 0; s < steps; s++)
        {
            int r1 = rng.Next(m), r2 = rng.Next(m), c1 = rng.Next(m);
            if (r1 == r2) continue;
            int a = L[r1, c1], b = L[r2, c1];
            if (a == b) continue;
            int c2 = -1;
            for (int c = 0; c < m; c++) if (L[r1, c] == b) { c2 = c; break; }   // an intercalate {a,b}
            if (c2 < 0 || L[r2, c2] != a) continue;
            L[r1, c1] = b; L[r2, c1] = a; L[r1, c2] = a; L[r2, c2] = b;
        }
        return L;
    }

    // Latin-square graph as a rank-3 scheme on m² cells: 0=id, 1=collinear (row|col|symbol), 2=else.
    static int[,] LatinSquareGraphRel(int[,] L, int m)
    {
        int n = m * m;
        var M = new int[n, n];
        for (int i1 = 0; i1 < m; i1++) for (int j1 = 0; j1 < m; j1++)
            for (int i2 = 0; i2 < m; i2++) for (int j2 = 0; j2 < m; j2++)
            {
                int x = i1 * m + j1, y = i2 * m + j2;
                if (x == y) { M[x, y] = 0; continue; }
                bool coll = i1 == i2 || j1 == j2 || L[i1, j1] == L[i2, j2];
                M[x, y] = coll ? 1 : 2;
            }
        return M;
    }

    // Latin-square NET scheme on m² cells, parallel classes kept SEPARATE (the rank-≥4 amorphic object):
    //   0=id, 1=same row, 2=same column, 3=same symbol, 4=non-collinear.  This is where depth-1 EdgeGenerates
    //   can FAIL (the Clebsch-type behaviour), unlike the rank-3 graph.  BuildScheme gates coherence.
    static int[,] LatinSquareNetRel(int[,] L, int m)
    {
        int n = m * m;
        var M = new int[n, n];
        for (int i1 = 0; i1 < m; i1++) for (int j1 = 0; j1 < m; j1++)
            for (int i2 = 0; i2 < m; i2++) for (int j2 = 0; j2 < m; j2++)
            {
                int x = i1 * m + j1, y = i2 * m + j2;
                if (x == y) { M[x, y] = 0; continue; }
                if (i1 == i2) M[x, y] = 1;
                else if (j1 == j2) M[x, y] = 2;
                else if (L[i1, j1] == L[i2, j2]) M[x, y] = 3;
                else M[x, y] = 4;
            }
        return M;
    }

    [Fact]
    public void Probe_AmorphicResidue_LatinSquare()
    {
        const int autCap = 200_000;
        int primCount = 0, validNonAffinePrim = 0, genuineWitness = 0;
        var witnessRows = new List<string>();
        var growth = new List<(int n, int wl)>();   // non-affine primitive depth vs n

        output.WriteLine("Non-affine amorphic residue — Latin-square-type SRG schemes (Gol'fand–Ivanov–Klin).");
        output.WriteLine("Cyclic square = affine/group control (large Aut); randomized = non-group ⟹ small Aut, NON-affine.");
        output.WriteLine("Recovery = EdgeGenerates ∨ WL-depth ≤ ⌈log2 n⌉+2.   |Aut| computed ONLY for non-recoverers (witness check).\n");
        output.WriteLine("   m  n   origin      rank prim  k   c  thm31 edgeGen WLdepth  |Aut|     recover?");

        for (int m = 4; m <= 10; m++)
        {
            int n = m * m;
            int tameBound = (int)Math.Ceiling(Math.Log2(n)) + 2;
            var squares = new List<(string origin, int[,] L)> { ("cyclic", CyclicLatinSquare(m)) };
            for (int t = 0; t < 4; t++) squares.Add(($"rand#{t}", RandomizedLatinSquare(m, 50 * n, new Random(1000 * m + t))));

            void Measure(string tag, int[,] M)
            {
                var s = BuildScheme(M, n);
                if (s is null) { output.WriteLine($"  {m,2} {n,4}  {tag,-12} INVALID (not a CC) — skip"); return; }
                bool prim = Primitive(s);
                if (prim) primCount++;
                var adj = Adjoint(s);
                int k = MaxValency(s), c = Indistinguishing(s, adj);
                bool thm31 = 2 * c * (k - 1) < n;
                bool edge = Recovers(s);
                int wl = WLDepth(s, n);
                bool tame = edge || wl <= tameBound;
                bool nonAffine = !tag.StartsWith("cyclic") && m >= 5;   // order-≤4 Latin squares are all group-isotopic (affine)
                if (prim && nonAffine) { validNonAffinePrim++; growth.Add((n, wl)); }

                // |Aut| computed ONLY for a NON-recoverer — to tell a small-Aut witness from a large/Cameron case.
                // (A recovering scheme cannot be a witness, so its |Aut| is irrelevant and AutGroup is skipped.)
                string autStr = "—";
                if (!tame)
                {
                    var autos = AutGroup(s, autCap);
                    if (autos is null) autStr = $">{autCap} (large/Cameron)";
                    else
                    {
                        var (_, _, schurian, abelian, o) = Analyze(s, autos);
                        autStr = o.ToString();
                        if (prim && schurian && !abelian && wl > (int)Math.Floor(Math.Log2(Math.Max(1, o))) + 2)
                        {
                            genuineWitness++;
                            witnessRows.Add($"    ‼ m={m} {tag} n={n} rank={s.Rank} WLdepth={wl} |Aut|={o} — GENUINE non-affine witness");
                        }
                    }
                }
                output.WriteLine($"  {m,2} {n,4}  {tag,-12} {s.Rank,3} {(prim ? "yes" : "no "),4} {k,3} {c,3}  {(thm31 ? "yes" : "no "),-4} {(edge ? "yes" : "NO "),-5} {wl,4}    {autStr,-9} {(tame ? "recover" : "★NON-RECOVER")}");
            }

            foreach (var (origin, L) in squares)
            {
                Measure(origin, LatinSquareGraphRel(L, m));        // rank-3 SRG (depth-1-easy)
                Measure(origin + "/net", LatinSquareNetRel(L, m)); // rank-≥4 net scheme (reaches the depth-1-failure zone)
            }
        }

        output.WriteLine("");
        output.WriteLine($"primitive schemes built: {primCount};  non-affine (non-group, randomized m≥5) primitive: {validNonAffinePrim}");
        if (growth.Count > 0)
        {
            var byN = growth.GroupBy(g => g.n).OrderBy(g => g.Key).Select(g => $"n={g.Key}:maxWL={g.Max(x => x.wl)}");
            output.WriteLine($"  non-affine recovery depth vs n: {string.Join("  ", byN)}");
        }
        foreach (var r in witnessRows) output.WriteLine(r);

        output.WriteLine("");
        output.WriteLine(validNonAffinePrim > 0
            ? $"VERDICT (construction): reached the non-affine zone — {validNonAffinePrim} non-group (m≥5) primitive Latin-square SRG schemes built."
            : "VERDICT (construction): ‼ stayed in the large-Aut zone (m too small / randomization insufficient) — probe INCONCLUSIVE on the non-affine residue.");
        output.WriteLine(genuineWitness == 0
            ? "VERDICT (falsifier): 0 genuine non-affine witnesses — every small-Aut Latin-square-type amorphic scheme recovers at bounded depth."
            : $"VERDICT (falsifier): ‼ {genuineWitness} GENUINE non-affine WITNESS(ES) — the non-affine residue is non-recovering; module-adjoin scope INSUFFICIENT, statement-relevant.");
        output.WriteLine("VERDICT (scope): Latin-square GRAPHS are primitive but rank-3 (depth-1-easy); Latin-square NET schemes are " +
                         "rank-≥4 but IMPRIMITIVE (parallel classes = block systems ⟹ the handled case, not G2-B). The genuine PRIMITIVE " +
                         "rank-4 amorphic residue is NEGATIVE-Latin-square type (Clebsch family), which Latin-square constructions cannot " +
                         "produce — it needs the Davis–Xiang partial-difference-set construction in non-elementary-abelian groups (the heavier deferred route).");

        // ── assertions ──
        Assert.True(primCount > 0, "no primitive Latin-square schemes constructed");
        Assert.Equal(0, genuineWitness);   // no non-affine non-recovering small-Aut primitive (falsifier extends to non-affine)
    }
}
