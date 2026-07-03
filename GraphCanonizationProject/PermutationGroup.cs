using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

namespace Canonizer
{
    // ── Permutation utilities ───────────────────────────────────────────────
    //
    // A permutation of {0..n-1} is an int[] `p` of length n, with p[i] the
    // image of i. Composition applies the right operand first:
    // Compose(p, q)[i] = p[q[i]]  ("q then p").
    public static class Perm
    {
        public static int[] Identity(int n)
        {
            var p = new int[n];
            for (int i = 0; i < n; i++) p[i] = i;
            return p;
        }

        // (p ∘ q): apply q, then p.
        public static int[] Compose(int[] p, int[] q)
        {
            var r = new int[q.Length];
            for (int i = 0; i < q.Length; i++) r[i] = p[q[i]];
            return r;
        }

        public static int[] Inverse(int[] p)
        {
            var r = new int[p.Length];
            for (int i = 0; i < p.Length; i++) r[p[i]] = i;
            return r;
        }

        public static bool IsIdentity(int[] p)
        {
            for (int i = 0; i < p.Length; i++)
                if (p[i] != i) return false;
            return true;
        }

        public static bool IsPermutation(int[] p)
        {
            var seen = new bool[p.Length];
            foreach (int x in p)
            {
                if (x < 0 || x >= p.Length || seen[x]) return false;
                seen[x] = true;
            }
            return true;
        }

        // Build a permutation of {0..n-1} from disjoint cycles. Unlisted points
        // are fixed. Example: FromCycles(4, new[]{0,1,2,3}) is the 4-cycle.
        public static int[] FromCycles(int n, params int[][] cycles)
        {
            var p = Identity(n);
            foreach (var c in cycles)
                for (int i = 0; i < c.Length; i++)
                    p[c[i]] = c[(i + 1) % c.Length];
            return p;
        }

        // First point moved by p, or -1 if p is the identity.
        public static int FirstMoved(int[] p)
        {
            for (int i = 0; i < p.Length; i++)
                if (p[i] != i) return i;
            return -1;
        }

        // The order of `p` — the lcm of its cycle lengths.
        public static long Order(int[] p)
        {
            var seen = new bool[p.Length];
            long ord = 1;
            for (int i = 0; i < p.Length; i++)
                if (!seen[i])
                {
                    int len = 0, j = i;
                    while (!seen[j]) { seen[j] = true; j = p[j]; len++; }
                    ord = ord / Gcd(ord, len) * len;
                }
            return ord;
        }

        // p^e (e ≥ 0) by fast exponentiation.
        public static int[] Pow(int[] p, long e)
        {
            var r = Identity(p.Length);
            var b = (int[])p.Clone();
            while (e > 0) { if ((e & 1) == 1) r = Compose(r, b); b = Compose(b, b); e >>= 1; }
            return r;
        }

        static long Gcd(long a, long b) { while (b != 0) { (a, b) = (b, a % b); } return a; }
    }

    // ── Permutation group via a stabilizer chain ────────────────────────────
    //
    // The group-theoretic foundation of the route-2 calculator. Per
    // docs/chain-descent-calculator.md §2 ("The model: the calculator is a
    // stabilizer chain"), the calculator's object *is* a stabilizer chain;
    // this type provides it.
    //
    // A group on {0..N-1} is given by generators; a base and the basic
    // transversals (the stabilizer chain) are computed lazily by Schreier–Sims.
    // This is what makes calculator-doc theorems T-A and T-B "free": every
    // subgroup of S_N — whatever its order, up to N! — has a base of ≤ N
    // points and a polynomial-size chain. Group *elements* are never
    // enumerated; generators and transversals are.
    //
    // Implementation note: this uses textbook recursive Schreier–Sims without
    // sifting of Schreier generators. It is correct for any group and
    // efficient for the small/moderate groups Phase 1 targets (Tier 0/1/CFI —
    // e.g. D18, D9≀Z2). The sifting optimisation that keeps construction
    // polynomial for large groups is a deferred concern.
    public sealed class PermutationGroup
    {
        public int N { get; }

        private readonly List<int[]> _generators = new();
        private List<Level>? _chain;

        // One level of the stabilizer chain: the orbit of BasePoint under the
        // level's group, with one coset representative per orbit point.
        private sealed class Level
        {
            public required int BasePoint;
            // Transversal[pt] is a group element u with u[BasePoint] = pt,
            // or null when pt is not in the basic orbit.
            public required int[]?[] Transversal;
            public required int OrbitSize;
        }

        // The trivial group on {0..n-1}.
        public PermutationGroup(int n)
        {
            if (n < 0) throw new ArgumentOutOfRangeException(nameof(n));
            N = n;
        }

        public IReadOnlyList<int[]> Generators => _generators;

        // Add a generator. Identity generators are ignored; the chain is
        // invalidated and rebuilt lazily on the next query.
        public void AddGenerator(int[] perm)
        {
            if (perm.Length != N)
                throw new ArgumentException(
                    $"Permutation length {perm.Length} does not match group degree {N}.");
            if (!Perm.IsPermutation(perm))
                throw new ArgumentException("Argument is not a permutation of {0..N-1}.");
            if (Perm.IsIdentity(perm)) return;
            _generators.Add((int[])perm.Clone());
            _chain = null;
        }

        // |G|, the group order — the product of the basic orbit sizes.
        public BigInteger Order
        {
            get
            {
                EnsureChain();
                BigInteger order = BigInteger.One;
                foreach (var lvl in _chain!) order *= lvl.OrbitSize;
                return order;
            }
        }

        public bool IsTrivial => Order.IsOne;

        // Whether the group is abelian. A group is abelian iff its generators
        // pairwise commute, so this is a sound + complete test on `_generators`
        // (no chain needed). Used to tell a hidden-*abelian* residual (a CFI
        // gauge Z_2^d the linear/cross-branch harvest would consume — NOT a
        // Cameron section) apart from a genuinely non-abelian Tier-2 residual:
        // the "F2" distinction of docs/chain-descent-exhaustive-obstruction.md
        // §0.6, which an order-only flag signal cannot make.
        public bool IsAbelian
        {
            get
            {
                for (int i = 0; i < _generators.Count; i++)
                    for (int j = i + 1; j < _generators.Count; j++)
                        if (!Perm.IsIdentity(
                                Perm.Compose(Perm.Inverse(Perm.Compose(_generators[i], _generators[j])),
                                             Perm.Compose(_generators[j], _generators[i]))))
                            return false;
                return true;
            }
        }

        // Whether the group is elementary abelian of exponent 2 (a Z_2^d) —
        // abelian with every generator an involution (for an abelian group,
        // g^2 = 1 on the generators forces exponent 2 on the whole group). This
        // is exactly the CFI gauge group's signature; it pins the
        // `AbelianUnconsumed` flag cause to the structure the project's harvest
        // is built to absorb.
        public bool IsElementaryAbelian
        {
            get
            {
                if (!IsAbelian) return false;
                foreach (var g in _generators)
                    if (!Perm.IsIdentity(Perm.Compose(g, g))) return false;
                return true;
            }
        }

        // The base of the computed stabilizer chain.
        public int[] BasePoints
        {
            get
            {
                EnsureChain();
                return _chain!.Select(l => l.BasePoint).ToArray();
            }
        }

        // Membership test: sift `perm` through the chain; it is in the group
        // iff the residue is the identity.
        public bool Contains(int[] perm)
        {
            if (perm.Length != N || !Perm.IsPermutation(perm)) return false;
            EnsureChain();
            var cur = perm;
            foreach (var lvl in _chain!)
            {
                int img = cur[lvl.BasePoint];
                var rep = lvl.Transversal[img];
                if (rep == null) return false;
                cur = Perm.Compose(Perm.Inverse(rep), cur);
            }
            return Perm.IsIdentity(cur);
        }

        // The orbit of `point` under the whole group, sorted ascending.
        public int[] Orbit(int point)
        {
            var inOrbit = new bool[N];
            var orbit = new List<int> { point };
            inOrbit[point] = true;
            var queue = new Queue<int>();
            queue.Enqueue(point);
            while (queue.Count > 0)
            {
                int o = queue.Dequeue();
                foreach (var g in _generators)
                {
                    int img = g[o];
                    if (!inOrbit[img])
                    {
                        inOrbit[img] = true;
                        orbit.Add(img);
                        queue.Enqueue(img);
                    }
                }
            }
            orbit.Sort();
            return orbit.ToArray();
        }

        // ── Route-C F1 substrate: normal closure + the regular normal p-subgroup (socle) ──
        //
        // F1 (docs/chain-descent-route-c-plan.md §6) recovers the additive (F_p)^d
        // structure from an abstract affine-polar graph as the SOCLE of its automorphism
        // group. These are the general group-theoretic operations that recovery needs.

        // Enumerate all elements of the group (BFS closure of the generators). |result|
        // = Order. Use only when the group is small enough to materialise (F1 calls this
        // on the translation group T, whose order is the graph's vertex count).
        public IEnumerable<int[]> Elements()
        {
            var set = new HashSet<int[]>(PermComparer.Instance) { Perm.Identity(N) };
            var queue = new Queue<int[]>();
            queue.Enqueue(Perm.Identity(N));
            while (queue.Count > 0)
            {
                var x = queue.Dequeue();
                foreach (var g in _generators)
                {
                    var y = Perm.Compose(g, x);
                    if (set.Add(y)) queue.Enqueue(y);
                }
            }
            return set;
        }

        // The normal closure ⟨g^G⟩ — the smallest normal subgroup of G containing `g`.
        // Standard fixed-point algorithm: close `g` under conjugation by the group's
        // generators until the subgroup stops growing (membership via the chain).
        public PermutationGroup NormalClosure(int[] g)
        {
            if (g.Length != N) throw new ArgumentException("degree mismatch", nameof(g));
            var nc = new PermutationGroup(N);
            nc.AddGenerator(g);
            bool changed = true;
            while (changed)
            {
                changed = false;
                foreach (var x in nc.Generators.ToArray())
                    foreach (var s in _generators)
                    {
                        var c = Perm.Compose(s, Perm.Compose(x, Perm.Inverse(s)));  // s x s⁻¹
                        if (!nc.Contains(c)) { nc.AddGenerator(c); changed = true; }
                    }
            }
            return nc;
        }

        // Whether every generator's order divides `p`. For an ABELIAN group this
        // certifies exponent dividing `p` on the whole group — the general-`p`
        // counterpart of the exponent-2 test baked into `IsElementaryAbelian`.
        public bool HasExponentDividing(int p)
        {
            foreach (var g in _generators)
                if (!Perm.IsIdentity(Perm.Pow(g, p))) return false;
            return true;
        }

        // The unique regular normal elementary-abelian p-subgroup, if one exists, else
        // null. For an affine-primitive permutation group this is the SOCLE = the
        // regular translation group T ≅ (F_p)^d — the additive structure Route-C's F1
        // recovers. Found as the normal closure of a p-element whose closure is a
        // regular elementary-abelian p-group of order = the degree (unique by socle
        // minimality). 'Regular' = order equal to the degree AND transitive (⟹ the
        // point stabiliser is trivial). Seeds: p-parts of generators, then of pairwise
        // products (lazy — generators alone suffice for the harvested affine Aut).
        public PermutationGroup? RegularNormalPSubgroup(int p)
        {
            if (N == 0) return null;
            bool IsTarget(PermutationGroup nc) =>
                nc.Order == N && nc.IsAbelian && nc.HasExponentDividing(p) && nc.Orbit(0).Length == N;

            foreach (var c in PElementSeeds(p))
            {
                if (Perm.IsIdentity(c)) continue;
                var nc = NormalClosure(c);
                if (IsTarget(nc)) return nc;
            }
            return null;
        }

        // p-parts (g^{p'-part of order}) of generators, then of pairwise products — the
        // lazy seed stream for `RegularNormalPSubgroup`.
        private IEnumerable<int[]> PElementSeeds(int p)
        {
            static int[] PPart(int[] g, int p)
            {
                long m = Perm.Order(g);
                while (m % p == 0) m /= p;   // m := p'-part of the order
                return Perm.Pow(g, m);
            }
            var gens = _generators;
            foreach (var g in gens) yield return PPart(g, p);
            for (int i = 0; i < gens.Count; i++)
                for (int j = 0; j < gens.Count; j++)
                    if (i != j) yield return PPart(Perm.Compose(gens[i], gens[j]), p);
        }

        // ── Schreier–Sims ────────────────────────────────────────────────────

        private void EnsureChain()
        {
            _chain ??= BuildChain();
        }

        private List<Level> BuildChain()
        {
            var chain = new List<Level>();
            IReadOnlyList<int[]> curGens = _generators;

            while (true)
            {
                // Pick a base point: any point moved by some current generator.
                int b = -1;
                foreach (var g in curGens)
                {
                    int m = Perm.FirstMoved(g);
                    if (m >= 0) { b = m; break; }
                }
                if (b < 0) break; // residual group is trivial — chain complete

                // Orbit of b under curGens, with a coset representative per
                // orbit point: u_img = g ∘ u_o satisfies u_img[b] = img.
                int[]?[] transversal = new int[N][];
                transversal[b] = Perm.Identity(N);
                var orbit = new List<int> { b };
                var queue = new Queue<int>();
                queue.Enqueue(b);
                while (queue.Count > 0)
                {
                    int o = queue.Dequeue();
                    var uo = transversal[o]!;
                    foreach (var g in curGens)
                    {
                        int img = g[o];
                        if (transversal[img] == null)
                        {
                            transversal[img] = Perm.Compose(g, uo);
                            orbit.Add(img);
                            queue.Enqueue(img);
                        }
                    }
                }

                // Schreier generators for the stabilizer of b:
                // sg = u_{g[o]}^{-1} ∘ g ∘ u_o  (each fixes b and all earlier
                // base points). By Schreier's lemma they generate the
                // stabilizer; recurse on them.
                var schreier = new HashSet<int[]>(PermComparer.Instance);
                foreach (int o in orbit)
                {
                    var uo = transversal[o]!;
                    foreach (var g in curGens)
                    {
                        var uimg = transversal[g[o]]!;
                        var sg = Perm.Compose(Perm.Inverse(uimg), Perm.Compose(g, uo));
                        if (!Perm.IsIdentity(sg)) schreier.Add(sg);
                    }
                }

                chain.Add(new Level
                {
                    BasePoint = b,
                    Transversal = transversal,
                    OrbitSize = orbit.Count,
                });
                curGens = schreier.ToList();
            }

            return chain;
        }

        private sealed class PermComparer : IEqualityComparer<int[]>
        {
            public static readonly PermComparer Instance = new();

            public bool Equals(int[]? a, int[]? b)
            {
                if (ReferenceEquals(a, b)) return true;
                if (a == null || b == null || a.Length != b.Length) return false;
                for (int i = 0; i < a.Length; i++)
                    if (a[i] != b[i]) return false;
                return true;
            }

            public int GetHashCode(int[] a)
            {
                var h = new HashCode();
                foreach (int x in a) h.Add(x);
                return h.ToHashCode();
            }
        }
    }
}
