#!/usr/bin/env python3
# Probe for AggFaithfulB (step 9F de-classed reader): does aggregating the
# forced-value read `baseReadPin` over an EQUIVARIANT, gauge-FIXED pinning family
#   (a) TIE gauge-coupled co-cellular vertices, and
#   (b) SEPARATE rigid (non-automorphic) co-cellular vertices,
# on a genuinely MIXED multipede (partial F2 kernel)?
#
# Multipede (Neuen-Schweitzer): base biadjacency A_G (V gadgets x W segments).
#   gauge = ker_{F2}(A_G) as segment-swap-sets X; a colour-aut flips a(w)<->b(w) for w in X.
#   e_w in rowspace(A_G) <=> e_w _|_ ker(A_G) <=> w NOT in support(ker) <=> w RIGID.
# So at the SEGMENT level forcedVal already splits rigid vs gauge. The question is
# whether the aggregate over pinnings separates the two FEET of a rigid segment
# (distinct canonical labels) while tying the two feet of a gauge segment.
#
# Extraction model = the recovered linear code = A_G over segment coords, lifted
# to feet: foot (w,side). Gauge-invariant witness x0 (forced by RefExtractEquivariant):
# x0 constant on gauge orbits. Read = encOpt(forcedVal(A_G u pin, x0, .)).

from itertools import product, combinations

# ---------- F2 linear algebra ----------
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
    # right null space of the matrix whose ROWS are `rows` (each len n): {x : rows . x = 0}
    ker = []
    for x in product([0, 1], repeat=n):
        if all(sum(r[j] * x[j] for j in range(n)) % 2 == 0 for r in rows):
            ker.append(list(x))
    return ker

# ---------- bases ----------
def circulant_biadj(m, offsets=(0, 1, 3)):
    return [[1 if ((i + o) % m) == w else 0 for w in range(m)]
            for i in range(m) for o in [None]  # placeholder, rebuild below
            ] if False else \
           [[1 if any(((i + o) % m) == w for o in offsets) else 0 for w in range(m)]
            for i in range(m)]

# A genuinely MIXED base: col0 == col1 (segments 0,1 gauge-coupled), cols 2,3,4 rigid.
# gadgets (rows) over segments 0..4:
MIXED_BASE = [
    [1, 1, 0, 0, 0],  # g0: {0,1}
    [1, 1, 1, 0, 0],  # g1: {0,1,2}
    [0, 0, 1, 1, 0],  # g2: {2,3}
    [0, 0, 0, 1, 1],  # g3: {3,4}
    [0, 0, 1, 0, 1],  # g4: {2,4}
    [1, 1, 0, 1, 1],  # g5: {0,1,3,4}
]

def analyse(name, A, W):
    print(f"\n===== {name}  (W={W} segments, V={len(A)} gadgets) =====")
    rows = [r[:] for r in A]
    basis = build_basis(rows, W)
    rank = len(basis)
    ker = kernel(rows, W)
    ker_nontriv = [x for x in ker if any(x)]
    support = set(w for x in ker_nontriv for w in range(W) if x[w])
    print(f"rank_F2(A_G) = {rank}, ker dim = {W - rank}, |gauge| = {len(ker)}")
    print(f"kernel support (gauge segments) = {sorted(support)}")
    rigid = [w for w in range(W) if w not in support]
    print(f"rigid segments = {rigid}")
    # forcedness at segment level: e_w in rowspace(A_G)?
    seg_forced = {w: in_span(basis, [1 if j == w else 0 for j in range(W)]) for w in range(W)}
    print("seg forced (e_w in rowspace, no pin):",
          {w: seg_forced[w] for w in range(W)})
    assert all(seg_forced[w] == (w in rigid) for w in range(W)), "forcedness != rigidity!"

    # ---------- feet + gauge-invariant witness ----------
    # feet: (w, side) side in {0,1}. Gauge X flips side for w in X.
    # A gauge-invariant witness x0 must satisfy x0(w,0)=x0(w,1) for gauge w (forced by
    # RefExtractEquivariant), and MAY differ for rigid w. Pick x0(w,side)= side for rigid w
    # (distinguishes the two feet), and x0(w,side)=0 for gauge w (equal => ties).
    def x0(w, side):
        return side if w in rigid else 0

    feet = [(w, s) for w in range(W) for s in (0, 1)]

    # ---------- pinning family (equivariant, gauge-CLOSED, poly) ----------
    # single-segment pins: "pin seg w to value c" adds row e_w to the system, witness
    # unaffected (forcedVal reads x0). Family {pin(w,c)} is closed under the gauge
    # (gauge maps pin(w,0)<->pin(w,1) for gauge w) and under base perms.
    pins = [("pin", w, c) for w in range(W) for c in (0, 1)]
    # also the empty pin (base system alone)
    pins = [("empty",)] + pins

    def pinned_basis(pin):
        r = [row[:] for row in A]
        if pin[0] == "pin":
            _, w, c = pin
            r.append([1 if j == w else 0 for j in range(W)])   # e_w  (value c irrelevant to forcedness)
        return build_basis(r, W)

    def forced_seg(pin, w):
        b = pinned_basis(pin)
        return in_span(b, [1 if j == w else 0 for j in range(W)])

    def encOpt_none(): return 0
    def encOpt_some(v): return 1 + v

    def base_read(pin, foot):
        w, side = foot
        if forced_seg(pin, w):
            return encOpt_some(x0(w, side))
        return encOpt_none()

    # ---------- aggregate (SET and MULTISET) ----------
    def agg_set(foot):
        return frozenset(base_read(p, foot) for p in pins)
    def agg_multiset(foot):
        from collections import Counter
        return tuple(sorted(Counter(base_read(p, foot) for p in pins).items()))

    # ---------- true co-cellular tie/separate target ----------
    # co-cellular pairs = the two feet of the same segment (fine colouring).
    # tie iff w in gauge support (automorphic); separate iff rigid.
    print("\nper-segment  |  feet aggSET equal? | aggMSET equal? | want(tie iff gauge)")
    ok_set = ok_mset = True
    for w in range(W):
        f0, f1 = (w, 0), (w, 1)
        set_eq = agg_set(f0) == agg_set(f1)
        mset_eq = agg_multiset(f0) == agg_multiset(f1)
        want_tie = (w in support)              # gauge => should tie
        tag = "gauge" if want_tie else "RIGID"
        set_good = (set_eq == want_tie)
        mset_good = (mset_eq == want_tie)
        ok_set &= set_good
        ok_mset &= mset_good
        print(f"  seg {w} [{tag:5}] |  SET {str(set_eq):5} {'OK' if set_good else 'XX'} "
              f"|  MSET {str(mset_eq):5} {'OK' if mset_good else 'XX'} | want tie={want_tie}")
    print(f"SET aggregate recovers tie/separate:   {ok_set}")
    print(f"MSET aggregate recovers tie/separate:  {ok_mset}")
    return ok_set, ok_mset

if __name__ == "__main__":
    analyse("MIXED (partial kernel, segs 0&1 coupled)", MIXED_BASE, 5)
    analyse("PURE-GAUGE m=7 (Fano/simplex, all coupled)", circulant_biadj(7), 7)
    analyse("RIGID m=5 (odd base, trivial gauge)", circulant_biadj(5), 5)
