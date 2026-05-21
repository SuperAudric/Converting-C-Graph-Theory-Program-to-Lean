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
    }

    // ── Permutation group via a stabilizer chain ────────────────────────────
    //
    // The group-theoretic foundation of the route-2 calculator. Per
    // docs/flip-validation-calculator.md ("The current model: the calculator
    // is a stabilizer chain"), the calculator's object *is* a stabilizer
    // chain; this type provides it.
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
