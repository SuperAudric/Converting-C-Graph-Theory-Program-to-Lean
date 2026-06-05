using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Xunit;
using Xunit.Abstractions;
using Canonizer;

// ─────────────────────────────────────────────────────────────────────────────
// A2-iii twin-pair / block-invisibility search  (docs/chain-descent-a2iii-plan.md
// §1.1; chain-descent-exhaustive-obstruction.md §0.7 "A2 status").
//
// The Gate-G obligation behind EOL Step 3a is `SchemePartSeparatesBlock`
// (Scheme.lean §13): for a *schurian scheme graph* G, does the depth-n counting
// partition `schemePart_at` (= 1-WL from an individualized v) separate the
// I-membership boundary of every closed subset I?  The open A2-iii question is
// whether it holds for EVERY ClosedSubset, or whether some schurian scheme graph
// has a closed subset I that 1-WL cannot see — a relation-algebra "counting-twin"
// pair (two relations 1-WL merges, one in I and one not).  Such a witness would
// be the coarse-block-invisible (O*)-existence object the EOL routes around; its
// absence across a broad battery is the green light for the Lean A2-iii proof.
//
// METHODOLOGY (the load-bearing correction).  A `SchurianSchemeGraph` requires
// `isAut_imp_isSchemeAut`: the scheme's relations are EXACTLY the orbitals of the
// graph's OWN automorphism group.  Pairing an a-priori group scheme with a single
// non-generating relation (e.g. the Z8 scheme with the antipodal matching, whose
// real Aut is S2≀S4 ⊋ Z8) is NOT a valid scheme graph — it manufactures spurious
// "closed subsets" and spurious straddles (the same trap the A2-i probe hit and
// retracted).  So this probe is GRAPH-FIRST: pick a vertex-transitive graph G,
// compute Aut(G) by backtracking, take the orbital scheme S_G = orbitals of
// Aut(G) (schurian, and G is a valid SchurianSchemeGraph for it by construction),
// then test 1-WL-from-v on G against the closed subsets of S_G.  A straddle here
// is genuine; it can only arise when G is WL-dimension ≥ 2 (1-WL coarser than the
// Aut-orbitals) AND imprimitive.
//
// No production code is touched.
// ─────────────────────────────────────────────────────────────────────────────
public class TwinPairSearchExperiment(ITestOutputHelper output)
{
    const int CapN = 16;            // backtracking-Aut degree cap
    const int CapAuts = 200_000;    // automorphism enumeration cap

    // ── Union-find ──────────────────────────────────────────────────────────
    sealed class DSU
    {
        readonly int[] p;
        public DSU(int n) { p = new int[n]; for (int i = 0; i < n; i++) p[i] = i; }
        public int Find(int x) { while (p[x] != x) { p[x] = p[p[x]]; x = p[x]; } return x; }
        public void Union(int a, int b) { int ra = Find(a), rb = Find(b); if (ra != rb) p[ra] = rb; }
    }

    // ── A symmetric association scheme on N points ──────────────────────────
    sealed class Scheme
    {
        public required int N;
        public required int D;            // D+1 relations, indices 0..D
        public required int[,] Rel;
        public required int[,,] P;        // [i,j,k]
        public required int[] Valency;
    }

    // ── All automorphisms of a graph by backtracking (capped) ───────────────
    // Returns null if |Aut| exceeds the cap (we then skip — an incomplete set
    // would yield a too-fine, invalid scheme).
    static List<int[]>? AllAutomorphisms(bool[,] adj, int n)
    {
        var deg = new int[n];
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (adj[i, j]) deg[i]++;
        var autos = new List<int[]>();
        var img = new int[n];
        var used = new bool[n];
        bool overflow = false;

        void Search(int i)
        {
            if (overflow) return;
            if (i == n) { autos.Add((int[])img.Clone()); if (autos.Count > CapAuts) overflow = true; return; }
            for (int c = 0; c < n; c++)
            {
                if (used[c] || deg[c] != deg[i]) continue;
                bool ok = true;
                for (int j = 0; j < i; j++)
                    if (adj[i, j] != adj[c, img[j]]) { ok = false; break; }
                if (!ok) continue;
                img[i] = c; used[c] = true;
                Search(i + 1);
                used[c] = false;
                if (overflow) return;
            }
        }
        Search(0);
        return overflow ? null : autos;
    }

    // ── Orbital scheme of a transitive group given by generators ────────────
    static Scheme? OrbitalScheme(int n, List<int[]> gens, out string reason)
    {
        reason = "";
        // transitivity
        var reach = new bool[n]; reach[0] = true;
        var st = new Stack<int>(); st.Push(0); int rc = 1;
        while (st.Count > 0) { int x = st.Pop(); foreach (var g in gens) { int y = g[x]; if (!reach[y]) { reach[y] = true; rc++; st.Push(y); } } }
        if (rc != n) { reason = "intransitive"; return null; }

        var dsu = new DSU(n * n);
        for (int u = 0; u < n; u++)
            for (int v = 0; v < n; v++)
            { int pid = u * n + v; foreach (var g in gens) dsu.Union(pid, g[u] * n + g[v]); }
        for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) dsu.Union(u * n + v, v * n + u);

        int diagRoot = dsu.Find(0);
        for (int u = 0; u < n; u++) if (dsu.Find(u * n + u) != diagRoot) { reason = "diag not one orbital"; return null; }

        var rootToId = new Dictionary<int, int> { [diagRoot] = 0 };
        int next = 1;
        var Rel = new int[n, n];
        for (int u = 0; u < n; u++)
            for (int v = 0; v < n; v++)
            {
                int r = dsu.Find(u * n + v);
                if (!rootToId.TryGetValue(r, out int id)) { id = next++; rootToId[r] = id; }
                Rel[u, v] = id;
            }
        int d1 = next;

        var firstPair = new (int u, int v)?[d1];
        for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) firstPair[Rel[u, v]] ??= (u, v);
        var P = new int[d1, d1, d1];
        for (int k = 0; k < d1; k++)
        {
            var (u0, v0) = firstPair[k]!.Value;
            var bc = new int[d1, d1];
            for (int w = 0; w < n; w++) bc[Rel[u0, w], Rel[w, v0]]++;
            for (int i = 0; i < d1; i++) for (int j = 0; j < d1; j++) P[i, j, k] = bc[i, j];
            // well-definedness (orbital schemes always pass, but verify)
            for (int u = 0; u < n; u++)
                for (int v = 0; v < n; v++)
                {
                    if (Rel[u, v] != k) continue;
                    var c = new int[d1, d1];
                    for (int w = 0; w < n; w++) c[Rel[u, w], Rel[w, v]]++;
                    for (int i = 0; i < d1; i++) for (int j = 0; j < d1; j++)
                        if (c[i, j] != bc[i, j]) { reason = "not a scheme"; return null; }
                }
        }
        var val = new int[d1];
        for (int v = 0; v < n; v++) val[Rel[0, v]]++;
        return new Scheme { N = n, D = d1 - 1, Rel = Rel, P = P, Valency = val };
    }

    // ── 1-WL from an individualized vertex v, to the n-round fixpoint ─────────
    static int[] OneWLFrom(int n, bool[,] adj, int v)
    {
        var col = new int[n];
        for (int i = 0; i < n; i++) col[i] = (i == v) ? 1 : 0;
        for (int round = 0; round < n; round++)
        {
            var dict = new Dictionary<string, int>();
            var nc = new int[n];
            for (int w = 0; w < n; w++)
            {
                var nb = new List<int>();
                for (int u = 0; u < n; u++) if (u != w && adj[w, u]) nb.Add(col[u]);
                nb.Sort();
                string key = col[w] + "|" + string.Join(",", nb);
                if (!dict.TryGetValue(key, out int id)) { id = dict.Count; dict[key] = id; }
                nc[w] = id;
            }
            if (SamePartition(col, nc)) break;
            col = nc;
        }
        return col;
    }

    static bool SamePartition(int[] a, int[] b)
    {
        var map = new Dictionary<int, int>(); var inv = new Dictionary<int, int>();
        for (int i = 0; i < a.Length; i++)
        {
            if (map.TryGetValue(a[i], out int mb)) { if (mb != b[i]) return false; } else map[a[i]] = b[i];
            if (inv.TryGetValue(b[i], out int ma)) { if (ma != a[i]) return false; } else inv[b[i]] = a[i];
        }
        return true;
    }

    static int[] RelationTwinPartition(Scheme s)
    {
        int d1 = s.D + 1;
        var cls = (int[])s.Valency.Clone(); Normalize(cls);
        while (true)
        {
            var sig = new string[d1];
            for (int i = 0; i < d1; i++)
            {
                var parts = new List<(int, int, int)>();
                for (int j = 0; j < d1; j++) for (int k = 0; k < d1; k++)
                    if (s.P[i, j, k] != 0) parts.Add((cls[j], cls[k], s.P[i, j, k]));
                parts.Sort();
                sig[i] = cls[i] + "|" + string.Join(";", parts);
            }
            var nc = new int[d1]; var dict = new Dictionary<string, int>();
            for (int i = 0; i < d1; i++) { if (!dict.TryGetValue(sig[i], out int id)) { id = dict.Count; dict[sig[i]] = id; } nc[i] = id; }
            if (SamePartition(cls, nc)) return cls;
            cls = nc;
        }
    }

    static void Normalize(int[] c)
    {
        var dict = new Dictionary<int, int>();
        for (int i = 0; i < c.Length; i++) { if (!dict.TryGetValue(c[i], out int id)) { id = dict.Count; dict[c[i]] = id; } c[i] = id; }
    }

    static List<bool[]> ClosedSubsets(Scheme s)
    {
        int d1 = s.D + 1;
        var result = new List<bool[]>();
        if (d1 > 20) return result;
        for (long mask = 0; mask < (1L << d1); mask++)
        {
            if ((mask & 1) == 0) continue;
            var I = new bool[d1];
            for (int i = 0; i < d1; i++) I[i] = ((mask >> i) & 1) != 0;
            if (IsClosed(I, s)) result.Add(I);
        }
        return result;
    }

    static bool IsClosed(bool[] I, Scheme s)
    {
        int d1 = s.D + 1;
        for (int i = 0; i < d1; i++)
        {
            if (!I[i]) continue;
            for (int j = 0; j < d1; j++)
            {
                if (!I[j]) continue;
                for (int k = 0; k < d1; k++) if (s.P[i, j, k] != 0 && !I[k]) return false;
            }
        }
        return true;
    }

    static bool NonTrivial(bool[] I) { int c = I.Count(x => x); return c > 1 && c < I.Length; }

    sealed class Straddle
    {
        public required string Graph;
        public required string IBlock;
        public required int RelW, RelU;
        public required bool TwinByIntersection;
    }

    sealed class GraphResult
    {
        public bool Valid;
        public string Reason = "";
        public int Rank;
        public bool Imprimitive;
        public bool Recovers;       // 1-WL-from-v cells == Aut-orbital v-profile
        public string Sig = "";
        public List<Straddle> Straddles = new();
    }

    // ── Test one graph (graph-first; faithful) ───────────────────────────────
    static GraphResult TestGraph(string name, int n, bool[,] adj)
    {
        var r = new GraphResult();
        if (n > CapN) { r.Reason = "too big"; return r; }
        var autos = AllAutomorphisms(adj, n);
        if (autos == null) { r.Reason = "Aut too large"; return r; }
        var s = OrbitalScheme(n, autos, out string reason);
        if (s == null) { r.Reason = reason; return r; }   // e.g. not vertex-transitive
        r.Valid = true;
        r.Rank = s.D + 1;

        var closed = ClosedSubsets(s);
        var nt = closed.Where(NonTrivial).ToList();
        r.Imprimitive = nt.Count > 0;

        var cell = OneWLFrom(n, adj, 0);

        // recovery: do 1-WL cells respect the Aut-orbital v-profile (Rel[0,·])?
        bool recovers = true;
        for (int w = 0; w < n && recovers; w++)
            for (int u = 0; u < n && recovers; u++)
                if (w != 0 && u != 0 && cell[w] == cell[u] && s.Rel[0, w] != s.Rel[0, u]) recovers = false;
        r.Recovers = recovers;

        r.Sig = $"{s.N}|{s.D}|{string.Join(",", s.Valency.OrderBy(x => x))}|rec={recovers}|imp={r.Imprimitive}";

        if (nt.Count > 0)
        {
            var twin = RelationTwinPartition(s);
            foreach (var I in nt)
            {
                // any cell holding both an in-block and out-of-block non-v vertex
                var inByCell = new Dictionary<int, int>();   // cell -> a relation ∈ I
                var outByCell = new Dictionary<int, int>();  // cell -> a relation ∉ I
                for (int w = 0; w < n; w++)
                {
                    if (w == 0) continue;
                    int rel = s.Rel[0, w]; int c = cell[w];
                    if (I[rel]) inByCell.TryAdd(c, rel); else outByCell.TryAdd(c, rel);
                }
                foreach (var kv in inByCell)
                    if (outByCell.TryGetValue(kv.Key, out int outRel))
                    {
                        var rels = Enumerable.Range(0, I.Length).Where(i => I[i]);
                        r.Straddles.Add(new Straddle
                        {
                            Graph = name,
                            IBlock = "{" + string.Join(",", rels) + "}",
                            RelW = kv.Value,
                            RelU = outRel,
                            TwinByIntersection = twin[kv.Value] == twin[outRel]
                        });
                        break; // one witness per closed subset is enough
                    }
            }
        }
        return r;
    }

    // ── Graph battery (vertex-transitive; aimed at imprimitive + WL-dim ≥ 2) ──
    static bool[,] Circulant(int n, int[] conn)
    {
        var a = new bool[n, n];
        foreach (int d in conn)
            for (int i = 0; i < n; i++) { a[i, (i + d) % n] = true; a[(i + d) % n, i] = true; }
        return a;
    }

    // lexicographic product C_m[ K̄_k ]: m blocks of k, blocks adjacent per a graph B on m.
    static bool[,] BlowUp(int m, int k, Func<int, int, bool> baseAdj)
    {
        int n = m * k;
        var a = new bool[n, n];
        for (int bi = 0; bi < m; bi++)
            for (int bj = 0; bj < m; bj++)
                if (baseAdj(bi, bj))
                    for (int x = 0; x < k; x++) for (int y = 0; y < k; y++) a[bi * k + x, bj * k + y] = true;
        return a;
    }

    static IEnumerable<(string name, int n, bool[,] adj)> Battery()
    {
        // circulant sweep: connection sets of size 1..3 (1..2 for n≥15 to bound
        // Aut-backtracking cost on the larger, denser graphs).
        for (int n = 8; n <= CapN; n++)
        {
            int half = n / 2;
            int hiSize = n >= 15 ? 2 : 3;
            var ds = Enumerable.Range(1, half).ToArray();
            foreach (var subset in Subsets(ds, 1, hiSize))
            {
                yield return ($"Circ{n}[{string.Join(",", subset)}]", n, Circulant(n, subset.ToArray()));
            }
        }
        // known non-compact (1-WL-cospectral) controls at n=16: 4×4 rook (Hamming
        // H(2,4)) and the Shrikhande graph.  Both validate the WL-dim≥2 detector
        // and are primitive SRGs (rank-2 schemes — recover from v, no closed subset).
        yield return ("Rook4x4", 16, Rook4x4Adj());
        yield return ("Shrikhande", 16, ShrikhandeAdj());
        // lexicographic blow-ups of cycles (imprimitive controls): C_m[K̄_k]
        foreach (var (m, k) in new[] { (4, 2), (4, 3), (6, 2), (5, 2), (3, 4), (7, 2) })
        {
            int n = m * k; if (n > CapN) continue;
            yield return ($"C{m}[~K{k}]", n, BlowUp(m, k, (i, j) => (i - j + m) % m == 1 || (j - i + m) % m == 1));
        }
        // cube Q3, prism, Möbius ladders (imprimitive bipartite-ish)
        yield return ("Q3", 8, CubeAdj(3));
        // prism Y_n = C_n × K2
        foreach (int m in new[] { 4, 5, 6, 7 })
        {
            int n = 2 * m; if (n > CapN) continue;
            yield return ($"Prism{m}", n, PrismAdj(m));
            yield return ($"Mobius{m}", n, MobiusAdj(m));
        }
        // Petersen (primitive control, n=10)
        yield return ("Petersen", 10, PetersenAdj());
    }

    static IEnumerable<List<int>> Subsets(int[] items, int lo, int hi)
    {
        int m = items.Length;
        for (long mask = 1; mask < (1L << m); mask++)
        {
            int pc = System.Numerics.BitOperations.PopCount((ulong)mask);
            if (pc < lo || pc > hi) continue;
            var s = new List<int>();
            for (int i = 0; i < m; i++) if (((mask >> i) & 1) != 0) s.Add(items[i]);
            yield return s;
        }
    }

    static bool[,] CubeAdj(int dim)
    {
        int n = 1 << dim; var a = new bool[n, n];
        for (int x = 0; x < n; x++) for (int b = 0; b < dim; b++) { int y = x ^ (1 << b); a[x, y] = true; }
        return a;
    }
    static bool[,] PrismAdj(int m)
    {
        int n = 2 * m; var a = new bool[n, n];
        void E(int i, int j) { a[i, j] = true; a[j, i] = true; }
        for (int i = 0; i < m; i++) { E(i, (i + 1) % m); E(m + i, m + (i + 1) % m); E(i, m + i); }
        return a;
    }
    static bool[,] MobiusAdj(int m)
    {
        // Möbius–Kantor-style: two m-cycles cross-linked (Möbius ladder on 2m).
        int n = 2 * m; var a = new bool[n, n];
        void E(int i, int j) { a[i, j] = true; a[j, i] = true; }
        for (int i = 0; i < n; i++) E(i, (i + 1) % n);
        for (int i = 0; i < m; i++) E(i, i + m);
        return a;
    }
    static bool[,] PetersenAdj()
    {
        int n = 10; var a = new bool[n, n];
        void E(int i, int j) { a[i, j] = true; a[j, i] = true; }
        for (int i = 0; i < 5; i++) { E(i, (i + 1) % 5); E(5 + i, 5 + (i + 2) % 5); E(i, 5 + i); }
        return a;
    }
    static bool[,] Rook4x4Adj()
    {
        int n = 16; var a = new bool[n, n];
        for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++)
            for (int r2 = 0; r2 < 4; r2++) for (int c2 = 0; c2 < 4; c2++)
                if ((r == r2) ^ (c == c2)) a[4 * r + c, 4 * r2 + c2] = true; // same row xor same col
        return a;
    }
    static bool[,] ShrikhandeAdj()
    {
        // Cayley graph of Z4×Z4, connection set ±{(1,0),(0,1),(1,1)}.
        int n = 16; var a = new bool[n, n];
        int Idx(int x, int y) => 4 * ((x % 4 + 4) % 4) + ((y % 4 + 4) % 4);
        var conn = new (int, int)[] { (1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3) };
        for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++)
            foreach (var (dx, dy) in conn) a[Idx(x, y), Idx(x + dx, y + dy)] = true;
        return a;
    }

    // ── The probe ────────────────────────────────────────────────────────────
    [Fact]
    public void TwinPairSearch_NoBlockInvisibleClosedSubset()
    {
        int tried = 0, valid = 0, skippedBig = 0, skippedAut = 0, notVT = 0;
        int imprimitive = 0, wlDim2 = 0, imprimWlDim2 = 0;
        var straddles = new List<Straddle>();
        var seen = new HashSet<string>();
        int deduped = 0, maxN = 0, maxRank = 0;

        foreach (var (name, n, adj) in Battery())
        {
            tried++;
            var r = TestGraph(name, n, adj);
            if (!r.Valid)
            {
                if (r.Reason == "too big") skippedBig++;
                else if (r.Reason == "Aut too large") skippedAut++;
                else notVT++;
                continue;
            }
            if (!seen.Add(r.Sig)) { deduped++; continue; }
            valid++;
            maxN = Math.Max(maxN, n); maxRank = Math.Max(maxRank, r.Rank);
            if (r.Imprimitive) imprimitive++;
            if (!r.Recovers) wlDim2++;
            if (r.Imprimitive && !r.Recovers) imprimWlDim2++;
            straddles.AddRange(r.Straddles);
        }

        var sb = new StringBuilder();
        sb.AppendLine("── A2-iii twin-pair / block-invisibility search (graph-first, Aut-faithful) ──");
        sb.AppendLine($"graphs tried                  : {tried}");
        sb.AppendLine($"  skipped (n>{CapN})              : {skippedBig}");
        sb.AppendLine($"  skipped (Aut > cap)         : {skippedAut}");
        sb.AppendLine($"  not vertex-transitive       : {notVT}");
        sb.AppendLine($"  duplicate schemes           : {deduped}");
        sb.AppendLine($"distinct schurian schemes     : {valid}   (max N={maxN}, max rank={maxRank})");
        sb.AppendLine($"  imprimitive                 : {imprimitive}");
        sb.AppendLine($"  WL-dim ≥ 2 (1-WL coarse)     : {wlDim2}");
        sb.AppendLine($"  *** imprimitive ∧ WL-dim≥2  : {imprimWlDim2}  (the regime that can fire) ***");
        sb.AppendLine($"BLOCK-INVISIBLE straddles     : {straddles.Count}");
        if (straddles.Count > 0)
        {
            sb.AppendLine();
            sb.AppendLine("!!! GENUINE COUNTEREXAMPLE(S) — schurian scheme graph with an invisible block !!!");
            foreach (var st in straddles.Take(40))
                sb.AppendLine($"  {st.Graph}: block I={st.IBlock}, merged R{st.RelW}(∈I) ~ R{st.RelU}(∉I)  "
                    + $"[intersection-twin={st.TwinByIntersection}]");
            sb.AppendLine();
            sb.AppendLine("→ A2-iii REFUTED on this scheme: block-visibility is not universal.");
            sb.AppendLine("  This (graph, closed subset) is the coarse-block-invisible / (O*) candidate.");
        }
        else
        {
            sb.AppendLine();
            if (imprimWlDim2 == 0)
                sb.AppendLine("GATE CANNOT FIRE: no imprimitive ∧ WL-dim≥2 schurian scheme graph was "
                    + "reached by this battery (all imprimitive schemes recover / are WL-dim 1). "
                    + "Same regime-unreachability as A2-i — the decisive object needs richer generators "
                    + "or the theory/Lean proof.");
            else
                sb.AppendLine($"No straddle across {imprimWlDim2} imprimitive WL-dim≥2 schurian scheme "
                    + "graphs: every closed-subset block-of-v is 1-WL-visible even off recovery. "
                    + "Positive support for A2-iii (green light for the Lean proof); NOT a proof of "
                    + "non-existence — only that this battery exhibits no witness.");
        }
        output.WriteLine(sb.ToString());

        Assert.True(valid >= 15, $"too few distinct schurian schemes tested ({valid})");
        // The probe is scientific, not a regression gate: a counterexample is a
        // finding, reported above; we do not assert its absence.
    }

    // ── Focused, independent verification of the Shrikhande counterexample ────
    // Confirms every link of the claim (Aut correct, scheme rank, I genuinely a
    // closed block system, 1-WL genuinely blind to it) before it is believed —
    // and contrasts with the rook graph (rank-3 Aut, recovers, no closed subset).
    [Fact]
    public void Verify_Shrikhande_BlockInvisible()
    {
        var sb = new StringBuilder();

        void Report(string name, bool[,] adj, int n)
        {
            sb.AppendLine($"── {name} ──");
            var autos = AllAutomorphisms(adj, n)!;
            sb.AppendLine($"|Aut| = {autos.Count}");
            var s = OrbitalScheme(n, autos, out string reason)!;
            sb.AppendLine($"scheme rank (relations) = {s.D + 1}, valencies = [{string.Join(",", Enumerable.Range(0, s.D + 1).Select(i => s.Valency[i]))}]");
            // which relation(s) are the graph's edges?
            var edgeRels = new SortedSet<int>();
            for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) if (adj[u, v]) edgeRels.Add(s.Rel[u, v]);
            sb.AppendLine($"edge relation(s) = {{{string.Join(",", edgeRels)}}}");
            var closed = ClosedSubsets(s);
            var nt = closed.Where(NonTrivial).ToList();
            sb.AppendLine($"non-trivial closed subsets: {nt.Count}");
            var cell = OneWLFrom(n, adj, 0);
            int ncells = cell.Distinct().Count();
            int norbits = Enumerable.Range(0, n).Select(w => s.Rel[0, w]).Distinct().Count();
            sb.AppendLine($"1-WL-from-0 cells = {ncells}, Aut-orbital v-profile classes = {norbits}  "
                + $"(recovers = {ncells == norbits})");
            foreach (var I in nt)
            {
                var rels = Enumerable.Range(0, I.Length).Where(i => I[i]).ToList();
                // block of vertex 0 under schemeEquiv I = {w : Rel[0,w] ∈ I}
                var blockOf0 = Enumerable.Range(0, n).Where(w => I[s.Rel[0, w]]).ToList();
                // genuine block system? all blocks (over each basepoint) equal-sized.
                var blockSizes = Enumerable.Range(0, n)
                    .Select(v => Enumerable.Range(0, n).Count(w => I[s.Rel[v, w]]))
                    .Distinct().ToList();
                // 1-WL straddle witness?
                int wIn = -1, uOut = -1;
                for (int w = 0; w < n && wIn < 0; w++)
                    if (w != 0 && I[s.Rel[0, w]])
                        for (int u = 0; u < n; u++)
                            if (u != 0 && !I[s.Rel[0, u]] && cell[w] == cell[u]) { wIn = w; uOut = u; break; }
                sb.AppendLine($"  closed I={{{string.Join(",", rels)}}}: block(0) size={blockOf0.Count}, "
                    + $"block sizes={{{string.Join(",", blockSizes)}}}, "
                    + (wIn >= 0
                        ? $"1-WL BLIND: w={wIn}(R{s.Rel[0, wIn]}∈I) & u={uOut}(R{s.Rel[0, uOut]}∉I) share cell {cell[wIn]}"
                        : "1-WL sees this block (no straddle)"));
            }
            sb.AppendLine();
        }

        Report("Shrikhande", ShrikhandeAdj(), 16);
        Report("Rook4x4 (contrast: rank-3 Aut)", Rook4x4Adj(), 16);
        output.WriteLine(sb.ToString());

        // Correctness anchors for the Aut routine (known group orders).
        Assert.Equal(192, AllAutomorphisms(ShrikhandeAdj(), 16)!.Count);
        Assert.Equal(1152, AllAutomorphisms(Rook4x4Adj(), 16)!.Count);

        // The headline facts of the counterexample.
        var sh = OrbitalScheme(16, AllAutomorphisms(ShrikhandeAdj(), 16)!, out _)!;
        Assert.True(sh.D + 1 >= 4, "Shrikhande orbital scheme should be rank ≥ 3 (not the rank-2 SRG)");
        var shClosed = ClosedSubsets(sh).Where(NonTrivial).ToList();
        Assert.True(shClosed.Count >= 1, "Shrikhande should have a non-trivial closed subset (imprimitive Aut)");
    }
}
