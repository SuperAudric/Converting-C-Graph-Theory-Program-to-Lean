#!/usr/bin/env python3
# Probe v2 — the SHARP test: does the aggregate reader separate >2-vertex RIGID
# colour cells (the gadget MIDDLES), which is exactly where the single-bit step-5
# reader FAILED (<=2 classes/cell)? And still TIE gauge-equivalent middles?
#
# Full multipede (Neuen-Schweitzer): gadget v with neighbourhood N(v); middles
# m_A for every EVEN A subset of N(v); all middles of v share one colour (cell of
# size 2^(d-1)). A gauge swap-set X in ker(A_G) acts:  a(w)<->b(w) for w in X, and
#   m_A  |->  m_{A xor (X cap N(v))}.
# So two middles m_A, m_A' of gadget v are AUTOMORPHIC iff A xor A' in
#   projK(v) = { X cap N(v) : X in ker(A_G) }  (the kernel projected to N(v)).
# RIGID gadget (projK = {0}) => all 2^(d-1) middles are distinct orbits => the
# reader MUST give them 2^(d-1) distinct labels: the >2-cell separation test.
#
# Recovered-code read (gauge-invariant, order-free): for pinning p forcing the
# segment-orientation vector o^p on a forced set F^p, a middle m_A reads the
# partial vector  { w -> A_w xor o^p_w : w in N(v) cap F^p }.  This is
# gauge-invariant (a gauge X flips both A_w and o_w on X, leaving A_w xor o_w
# fixed) and, aggregated over pins, recovers A up to projK(v).

from itertools import product, combinations
from collections import Counter

def reduce_vec(basis, v):
    v = v[:]
    for lead, b in basis:
        if v[lead]:
            v = [x ^ y for x, y in zip(v, b)]
    return v

def build_basis(rows, n):
    basis = []
    for r in rows:
        v = reduce_vec(basis, r)
        leads = [i for i in range(n) if v[i]]
        if leads:
            basis.append((leads[0], v))
    return basis

def in_span(basis, target):
    return not any(reduce_vec(basis, target))

def kernel(rows, n):
    return [list(x) for x in product([0, 1], repeat=n)
            if all(sum(r[j] * x[j] for j in range(n)) % 2 == 0 for r in rows)]

def solve_forced(rows, n):
    """Return (forced_set, forced_values o): coords w with e_w in rowspace, and
    the unique value of coord w across all solutions of `rows . x = 0` shifted by
    a fixed particular solution. We use the all-zero RHS + a canonical particular
    solution 0, so forced value o_w = 0 for the homogeneous system; to get a
    nontrivial witness we solve rows . x = b for a fixed b (below)."""
    basis = build_basis([r[:] for r in rows], n)
    forced = [w for w in range(n) if in_span(basis, [1 if j == w else 0 for j in range(n)])]
    return set(forced), basis

MIXED_BASE = [
    [1, 1, 0, 0, 0], [1, 1, 1, 0, 0], [0, 0, 1, 1, 0],
    [0, 0, 0, 1, 1], [0, 0, 1, 0, 1], [1, 1, 0, 1, 1],
]
def circulant(m, offs=(0, 1, 3)):
    return [[1 if any((i + o) % m == w for o in offs) else 0 for w in range(m)] for i in range(m)]

def analyse(name, A, W, base_witness):
    print(f"\n===== {name} =====")
    ker = kernel([r[:] for r in A], W)
    ker_nt = [x for x in ker if any(x)]
    support = set(w for x in ker_nt for w in range(W) if x[w])
    rigid = [w for w in range(W) if w not in support]
    print(f"W={W} |gauge|={len(ker)} ker-support(gauge segs)={sorted(support)} rigid={rigid}")

    # neighbourhoods of each gadget
    V = len(A)
    Nb = [[w for w in range(W) if A[v][w]] for v in range(V)]

    # projected kernel per gadget: {X cap N(v)} as frozensets
    def projK(v):
        nv = Nb[v]
        s = set()
        for X in ker:
            s.add(frozenset(w for w in nv if X[w]))
        return s

    # forced orientation o^p under pinning p (= extra pinned coords with values).
    # witness o = base_witness on rigid coords (a genuine forced solution), 0 on gauge.
    # A pin (w0,c) forces additional coords; their forced value = value in the unique
    # solution of (A_G with s_{w0}=c). We compute forced set; forced value o_w:
    #   solve A_G x = 0 with x_{w0}=c is affine; for the READ we only need o_w for
    #   forced w, and gauge-invariance makes the read use A_w xor o_w. We take o = the
    #   canonical particular solution: o_w = base_witness[w] on the ORIGINAL rigid set,
    #   and for coords newly forced by the pin, o_w = the pin-propagated value.
    def forced_under(pin):
        rows = [r[:] for r in A]
        if pin is not None:
            w0, c = pin
            rows.append([1 if j == w0 else 0 for j in range(W)])
        basis = build_basis(rows, W)
        forced = set(w for w in range(W) if in_span(basis, [1 if j == w else 0 for j in range(W)]))
        # forced value: solve rows . x = rhs where rhs picks up the pin value.
        # Build augmented and back-substitute a particular solution.
        aug_rows = [r[:] for r in A] + ([[1 if j == w0 else 0 for j in range(W)]] if pin else [])
        rhs = [0] * len(A) + ([c] if pin else [])
        o = solve_particular(aug_rows, rhs, W)
        return forced, o

    def middle_read(pin, v, A_set):
        forced, o = forced_under(pin)
        nv = Nb[v]
        # partial vector over forced neighbourhood coords: w -> (w in A_set) xor o[w]
        return frozenset((w, (1 if w in A_set else 0) ^ o[w]) for w in nv if w in forced)

    # pinning family: empty + single-seg pins (gauge-closed, poly)
    pins = [None] + [(w, c) for w in range(W) for c in (0, 1)]

    def agg(v, A_set):
        return frozenset(middle_read(p, v, A_set) for p in pins)

    print("\nGADGET middle-cell separation (the >2-vertex test):")
    all_ok = True
    for v in range(V):
        nv = Nb[v]
        d = len(nv)
        evenA = [frozenset(c) for k in range(0, d + 1, 2) for c in combinations(nv, k)]
        pk = projK(v)
        # true orbits: m_A ~ m_A'  iff  A xor A' in projK(v)
        def orbit_key(Aset):
            # canonical rep of coset Aset + projK
            reps = set()
            for X in pk:
                reps.add(frozenset(Aset ^ X))
            return min(sorted(tuple(sorted(r)) for r in reps))
        true_orbit = {Aset: orbit_key(Aset) for Aset in evenA}
        read_sig = {Aset: agg(v, Aset) for Aset in evenA}
        # check: read_sig equal  <=>  same true orbit
        ok = True
        items = list(evenA)
        for i in range(len(items)):
            for j in range(i + 1, len(items)):
                Ai, Aj = items[i], items[j]
                same_read = read_sig[Ai] == read_sig[Aj]
                same_orbit = true_orbit[Ai] == true_orbit[Aj]
                if same_read != same_orbit:
                    ok = False
        n_orbits = len(set(true_orbit.values()))
        n_readclasses = len(set(read_sig.values()))
        tag = "RIGID-gad" if len(pk) == 1 else "gauge-gad"
        all_ok &= ok
        print(f"  gad {v} N={nv} [{tag}] middles={len(evenA)} "
              f"true-orbits={n_orbits} read-classes={n_readclasses} "
              f"{'OK' if ok and n_orbits == n_readclasses else 'XX'}")
    print(f"ALL gadget middle cells recovered exactly: {all_ok}")
    return all_ok

def solve_particular(rows, rhs, n):
    # Gaussian elimination to find ONE solution x with rows . x = rhs (mod 2).
    # rows may be inconsistent-> returns best effort (won't happen for our systems).
    M = [rows[i][:] + [rhs[i]] for i in range(len(rows))]
    piv_col = {}
    r = 0
    for c in range(n):
        pr = next((i for i in range(r, len(M)) if M[i][c]), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        for i in range(len(M)):
            if i != r and M[i][c]:
                M[i] = [a ^ b for a, b in zip(M[i], M[r])]
        piv_col[c] = r
        r += 1
    x = [0] * n
    for c, rr in piv_col.items():
        x[c] = M[rr][n]
    return x

if __name__ == "__main__":
    # witness: forced value 0 everywhere (homogeneous); reads use A xor o.
    analyse("MIXED (segs 0&1 coupled, rest rigid)", MIXED_BASE, 5, [0]*5)
    analyse("RIGID m=5 (odd base -> all gadgets rigid, all middles must split)", circulant(5), 5, [0]*5)
    analyse("PURE-GAUGE m=7 (Fano)", circulant(7), 7, [0]*7)
