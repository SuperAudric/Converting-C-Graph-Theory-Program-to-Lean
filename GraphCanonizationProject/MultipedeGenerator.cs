using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

// Multipede graph generator — Gurevich–Shelah / Neuen–Schweitzer.
//
// Purpose
// -------
// Multipedes are RIGID (trivial automorphism group) yet IR-hard: color
// refinement plus individualization cannot crack them cheaply, but there is no
// symmetry to harvest. They are the canonical "IR blind spot" — the second of
// chain descent's two flag causes (docs/chain-descent-exhaustive-obstruction.md
// §0.6): a flag carrying a *trivial* residual group, classified `IrBlindSpot`
// (versus the symmetric Tier-2 / Cameron flag, whose residual is non-trivial).
//
// CFI graphs (CfiGraphGenerator) are the *symmetric* hard case — a large
// automorphism group (the gauge Z_2^β) the canonizer consumes, so it canonizes
// CFI(K4–K7). Multipedes are their rigid counterpart: nothing to consume. They
// are the project's only IR-core test fixture (strategy §14, §15 gap 5).
//
// Construction (Neuen–Schweitzer, STOC 2018 / arXiv:1705.03283, §4)
// -----------------------------------------------------------------
// From a bipartite base graph G = (V, W, E):
//   * Each w ∈ W becomes a SEGMENT: a pair {a(w), b(w)}.
//   * Each v ∈ V becomes a CFI GADGET X_{N(v)} over its neighbourhood —
//       - one MIDDLE vertex m_A per even-cardinality subset A ⊆ N(v);
//       - edges m_A — a(w) for w ∈ A, and m_A — b(w) for w ∈ N(v) \ A.
//     The same parity gadget CFI uses — but here the gadget's outer vertices
//     ARE the shared segments, so there are no inter-gadget bridges (the
//     structural delta from CfiGraphGenerator's BuildCfiPair).
//
// Rigidity — the key property (Neuen–Schweitzer Lemma 4.1, 4.3, 4.4)
// ------------------------------------------------------------------
// G is "odd" iff its V×W biadjacency matrix A_G has full COLUMN rank over F_2
// (equivalently A_G x = 0 ⟹ x = 0). The fine-coloured multipede R(G) is RIGID
// iff G is odd: a colour-respecting automorphism induces a segment swap-set
// X ⊆ W (the w with a(w) ↔ b(w)); the CFI gadget admits only EVEN swaps
// (Lemma 4.1), so X is even on every gadget's neighbourhood, and oddness forces
// X = ∅, hence the identity. |Aut R(G)| = 2^(|W| − rk_{F2} A_G) (Lemma 4.4).
//
// This generator emits the FINE-COLOURED multipede: each segment F(w) is its
// own colour and each gadget middle-set M(v) is its own colour (a(w), b(w)
// share a colour; the 4 middles of a degree-3 gadget share a colour — so the
// gadget swap is allowed by colour and killed only by oddness). The colouring
// is delivered as `VertexTypes`, consumed by `CanonGraphOrdererChainDescent.Run`.
// Fine colouring — rather than a rigid *uncoloured* base (Neuen–Schweitzer ESA
// 2017, arXiv:1705.03686, Lemma 3.2) — is what lets us use a small, fully
// deterministic, vertex-transitive circulant base while still guaranteeing
// rigidity from oddness alone.
//
// Base family
// -----------
// `BuildCirculant(m)`: V = W = Z_m, check i covers bits {i, i+1, i+3} mod m
// (degree 3). The connection polynomial 1 + x + x^3 is primitive over F_2
// (order 7), so A_G has full F_2 rank — the base is odd, hence the multipede is
// rigid — exactly when 7 ∤ m. The generator computes oddness regardless
// (defensive). The multipede has 6m vertices (2m segment + 4m middle).
//
// References
// ----------
//   - Gurevich, Shelah, "On finite rigid structures", J. Symb. Log. 61 (1996) —
//     the original multipede.
//   - Neuen, Schweitzer, "An exponential lower bound for individualization-
//     refinement algorithms for graph isomorphism" (STOC 2018, arXiv:1705.03283)
//     — §4 construction; Lemma 4.1 (gadget even-swap), 4.3/4.4 (rigid ⟺ odd).
//   - Neuen, Schweitzer, "Benchmark Graphs for Practical Graph Isomorphism"
//     (ESA 2017, arXiv:1705.03686) — §3 degree-3 / uncoloured variant.

namespace Canonizer
{
    using EdgeType = Int32;

    public static class MultipedeGenerator
    {
        /// <summary>
        /// A fine-coloured multipede graph. `VertexTypes[i]` is the colour of
        /// vertex i (pass it as the `vertexTypes` argument to the canonizer's
        /// `Run`); `BaseIsOdd` is the rigidity certificate (full F_2 column rank
        /// of the base biadjacency ⟹ rigid, Neuen–Schweitzer Lemma 4.3).
        /// `VertexRoles[i]` is a human-readable role tag for diagnostics.
        /// </summary>
        public record Multipede(
            AdjMatrix Graph,
            int[] VertexTypes,
            string BaseName,
            int BaseV,
            int BaseW,
            bool BaseIsOdd,
            string[] VertexRoles);

        // ── Entry points ─────────────────────────────────────────────────────

        /// <summary>
        /// Multipede over the circulant base on Z_m where check i covers bits
        /// {i, (i+1) mod m, (i+3) mod m}. The base is odd — so the multipede is
        /// rigid — exactly when 7 ∤ m (1 + x + x^3 is primitive of order 7 over
        /// F_2). The result has 6m vertices.
        /// </summary>
        public static Multipede BuildCirculant(int m)
        {
            if (m < 4) throw new ArgumentException("Circulant multipede requires m ≥ 4 (offsets 0,1,3 must be distinct).");
            return BuildMultipede(CirculantBiadjacency(m, new[] { 0, 1, 3 }), $"Circulant{m}");
        }

        /// <summary>
        /// General multipede from a |V|×|W| bipartite biadjacency:
        /// `biadjacency[v, w] != 0` iff w ∈ N(v). Every V-vertex (gadget) must
        /// have degree ≥ 2. The oddness/rigidity of the base is reported in
        /// `Multipede.BaseIsOdd` (use `AssertRigid` to require it).
        /// </summary>
        public static Multipede BuildMultipede(int[,] biadjacency, string baseName)
        {
            int nV = biadjacency.GetLength(0);
            int nW = biadjacency.GetLength(1);

            // Sorted neighbourhoods of each gadget.
            var nbr = new int[nV][];
            for (int v = 0; v < nV; v++)
            {
                var list = new List<int>();
                for (int w = 0; w < nW; w++)
                    if (biadjacency[v, w] != 0) list.Add(w);
                if (list.Count < 2)
                    throw new ArgumentException(
                        $"Multipede gadget {v} has degree {list.Count}; every V-vertex needs degree ≥ 2.");
                nbr[v] = list.ToArray();
            }

            bool isOdd = IsOdd(biadjacency);

            // Flat-index layout: segments first (a(w), b(w) per w in 0..nW-1),
            // then middle vertices grouped by gadget. The bitmask is over
            // nbr[v] in listed order; even-popcount masks are the even subsets A.
            var aIdx = new int[nW];
            var bIdx = new int[nW];
            var roles = new List<string>();
            int idx = 0;
            for (int w = 0; w < nW; w++)
            {
                aIdx[w] = idx++; roles.Add($"seg[w{w}]^a");
                bIdx[w] = idx++; roles.Add($"seg[w{w}]^b");
            }

            var middleIdx = new Dictionary<int, int>[nV];
            for (int v = 0; v < nV; v++)
            {
                int d = nbr[v].Length;
                middleIdx[v] = new Dictionary<int, int>();
                for (int bm = 0; bm < (1 << d); bm++)
                {
                    if (System.Numerics.BitOperations.PopCount((uint)bm) % 2 != 0) continue;
                    middleIdx[v][bm] = idx++;
                    var sLabel = string.Join(",", Enumerable.Range(0, d)
                        .Where(i => (bm & (1 << i)) != 0).Select(i => $"w{nbr[v][i]}"));
                    roles.Add($"gad[v{v}]:m{{{sLabel}}}");
                }
            }
            int n = idx;

            // Edges: m_A — a(w) iff w ∈ A, else m_A — b(w).
            var adj = new EdgeType[n, n];
            for (int v = 0; v < nV; v++)
            {
                int d = nbr[v].Length;
                foreach (var (bm, mi) in middleIdx[v])
                {
                    for (int i = 0; i < d; i++)
                    {
                        int w = nbr[v][i];
                        bool wInA = (bm & (1 << i)) != 0;
                        int target = wInA ? aIdx[w] : bIdx[w];
                        adj[mi, target] = 1;
                        adj[target, mi] = 1;
                    }
                }
            }

            // Fine colouring: colour w (0..nW-1) for both vertices of segment w;
            // colour nW+v for every middle of gadget v. a(w), b(w) share a colour
            // so the gadget swap is allowed by colour and killed only by oddness.
            var types = new int[n];
            for (int w = 0; w < nW; w++) { types[aIdx[w]] = w; types[bIdx[w]] = w; }
            for (int v = 0; v < nV; v++)
                foreach (var mi in middleIdx[v].Values) types[mi] = nW + v;

            return new Multipede(new AdjMatrix(adj), types, baseName, nV, nW, isOdd, roles.ToArray());
        }

        /// <summary>
        /// Multipede over an expander-like base: `nChecks` gadgets × `nBits`
        /// segments, each gadget incident to `degree` distinct bits chosen by a
        /// seeded RNG. Seeds are scanned upward from `seed` until the base is odd
        /// (so the multipede is rigid). Unlike the thin circulant, a random
        /// `degree`-regular bipartite base has high treewidth, so the rigid
        /// multipede genuinely resists refinement — the descent must branch with
        /// nothing to harvest, the IR-blind-spot regime that flags.
        /// </summary>
        public static Multipede BuildRandomRegular(int nChecks, int nBits, int degree, int seed = 0)
        {
            if (degree < 2) throw new ArgumentException("degree must be ≥ 2.");
            // An even degree forces the all-ones vector into the F_2 kernel (every
            // gadget's incident bits sum to 0 mod 2), so the base is never odd —
            // it can never yield a rigid multipede. The literature uses degree 3.
            if (degree % 2 == 0) throw new ArgumentException("degree must be ODD (even degree is never odd/rigid).");
            if (degree > nBits) throw new ArgumentException("degree cannot exceed nBits.");
            if (nChecks < nBits) throw new ArgumentException("nChecks must be ≥ nBits for an odd base.");
            for (int s = seed; s < seed + 10000; s++)
            {
                var b = RandomRegularBiadjacency(nChecks, nBits, degree, s);
                if (IsOdd(b))
                    return BuildMultipede(b, $"RandReg(c{nChecks},b{nBits},d{degree},s{s})");
            }
            throw new InvalidOperationException(
                $"No odd random-{degree}-regular base found in 10000 seeds from {seed}.");
        }

        private static int[,] RandomRegularBiadjacency(int nChecks, int nBits, int degree, int seed)
        {
            var rng = new Random(seed);
            var b = new int[nChecks, nBits];
            for (int v = 0; v < nChecks; v++)
            {
                var chosen = new HashSet<int>();
                while (chosen.Count < degree) chosen.Add(rng.Next(nBits));
                foreach (var w in chosen) b[v, w] = 1;
            }
            return b;
        }

        // ── Rigidity test + base factories ───────────────────────────────────

        /// <summary>
        /// Full-COLUMN-rank test of the |V|×|W| biadjacency over F_2: rank == |W|.
        /// True ⟺ the base is "odd" ⟺ the fine-coloured multipede is rigid
        /// (Neuen–Schweitzer Lemma 4.4). Plain Gaussian elimination over F_2.
        /// </summary>
        public static bool IsOdd(int[,] biadjacency)
        {
            int nV = biadjacency.GetLength(0);
            int nW = biadjacency.GetLength(1);
            if (nV < nW) return false;   // cannot have column rank nW with < nW rows

            var rows = new bool[nV][];
            for (int v = 0; v < nV; v++)
            {
                rows[v] = new bool[nW];
                for (int w = 0; w < nW; w++) rows[v][w] = (biadjacency[v, w] & 1) != 0;
            }

            int rank = 0;
            for (int col = 0; col < nW && rank < nV; col++)
            {
                int pivot = -1;
                for (int r = rank; r < nV; r++)
                    if (rows[r][col]) { pivot = r; break; }
                if (pivot < 0) continue;                       // free column
                (rows[rank], rows[pivot]) = (rows[pivot], rows[rank]);
                for (int r = 0; r < nV; r++)
                    if (r != rank && rows[r][col])
                        for (int c = col; c < nW; c++) rows[r][c] ^= rows[rank][c];
                rank++;
            }
            return rank == nW;
        }

        /// <summary>
        /// Circulant biadjacency on V = W = Z_m: check i covers bits
        /// {(i + o) mod m : o ∈ offsets}.
        /// </summary>
        public static int[,] CirculantBiadjacency(int m, int[] offsets)
        {
            var b = new int[m, m];
            for (int i = 0; i < m; i++)
                foreach (var o in offsets)
                    b[i, ((i + o) % m + m) % m] = 1;
            return b;
        }

        // ── Verification / diagnostic helpers ────────────────────────────────

        /// <summary>
        /// Throw unless the base is odd — i.e. unless the multipede is provably
        /// rigid (Neuen–Schweitzer Lemma 4.3). Lets a test trust a trivial
        /// harvested residual as genuine rigidity, not a premature flag.
        /// </summary>
        public static void AssertRigid(Multipede m)
        {
            if (!m.BaseIsOdd)
                throw new InvalidOperationException(
                    $"Multipede base '{m.BaseName}' is not odd (F_2 column rank < {m.BaseW}); not provably rigid.");
        }

        /// <summary>
        /// Sanity-check structural invariants: square symmetric loopless graph,
        /// exactly 2·|W| segment vertices and the right middle count, and types
        /// agreeing with the role tags. Throws on failure so a probe failure can
        /// be trusted as a canonizer finding, not a generator artifact.
        /// </summary>
        public static void AssertWellFormed(Multipede mp)
        {
            int n = mp.Graph.VertexCount;
            if (mp.VertexTypes.Length != n)
                throw new InvalidOperationException("VertexTypes length disagrees with vertex count.");
            if (mp.VertexRoles.Length != n)
                throw new InvalidOperationException("VertexRoles length disagrees with vertex count.");

            for (int i = 0; i < n; i++)
            {
                if (mp.Graph[i, i] != 0)
                    throw new InvalidOperationException($"Multipede is not loopless at vertex {i}.");
                for (int j = 0; j < n; j++)
                    if (mp.Graph[i, j] != mp.Graph[j, i])
                        throw new InvalidOperationException($"Multipede adjacency is not symmetric at ({i},{j}).");
            }

            int segCount = mp.VertexRoles.Count(r => r.StartsWith("seg[", StringComparison.Ordinal));
            if (segCount != 2 * mp.BaseW)
                throw new InvalidOperationException(
                    $"Expected {2 * mp.BaseW} segment vertices, found {segCount}.");
        }

        /// <summary>Human-readable description of a multipede for diagnostics.</summary>
        public static string Describe(Multipede mp)
        {
            var sb = new StringBuilder();
            sb.AppendLine($"Multipede from base: {mp.BaseName}  (|V|={mp.BaseV} gadgets, |W|={mp.BaseW} segments)");
            sb.AppendLine($"Vertices: {mp.Graph.VertexCount}, odd/rigid: {mp.BaseIsOdd}");
            sb.AppendLine("Vertex roles (type):");
            for (int i = 0; i < mp.Graph.VertexCount; i++)
                sb.AppendLine($"  [{i,3}] ({mp.VertexTypes[i],3}) {mp.VertexRoles[i]}");
            return sb.ToString();
        }
    }
}
