"""Is INTERIOR REPEAT-DETECTION recoverable from the condensed key, under CAO?

The condensation P_n = P_{n-1} o P_1 loses only one thing: appending mid->b cannot see
whether b already occurs in the prefix.  2-WL's DiagSep makes repeats AT THE ENDPOINTS
free (c(x,y) reveals x==y), so the only loss is an INTERIOR repeat x_i = x_j, 0<i<j<L.
Shortest such walk has L=4 (x_1 = x_3).

Test: give the condenser the MOST GENEROUS key 2-WL could possibly carry along a walk --
for every position, the pair colours to BOTH endpoints, plus every consecutive edge colour:

    K(w) = ( (c(a,x_i), c(x_i,b))_i , (c(x_i,x_{i+1}))_i )

If "is this walk simple" is CONSTANT on each K-class, repeat-detection is recoverable and
the condensation can be repaired.  If some K-class is MIXED, it is not -- and the two
walks in that class are an explicit witness.

Run at a CAO root (cells = Aut-orbits) and at the post-individualization CAO residue,
which is the state the propagation argument actually operates on.
"""
import sys
from probe_pathcondense import (shrikhande, rook44, net_z4, rank_partition, same,
                                wl2_pair_closure)
from probe_cao_cleanroom import cfi, all_isos, orbits


def wl2_indiv(n, adj, v):
    """2-WL pair closure after individualizing v (v=None -> plain root closure)."""
    c = rank_partition({(a, b): (adj[a][b], a == b, a == v, b == v)
                        for a in range(n) for b in range(n)})
    for _ in range(3 * n + 5):
        nxt = rank_partition({(a, b): (c[(a, b)],
                                       tuple(sorted((c[(a, x)], c[(x, b)])
                                                    for x in range(n))))
                              for a in range(n) for b in range(n)})
        if same(nxt, c):
            return c
        c = nxt
    return c


def walks_from(n, adj, a, L):
    cur = [(a,)]
    for _ in range(L):
        cur = [w + (y,) for w in cur for y in range(n) if adj[w[-1]][y]]
    return cur


def condensed_key(w, c):
    """Most generous key the condenser could carry: for every position, the pair colours to
    BOTH endpoints, the FIBRE colour c(x,x) (= that vertex's whole closed-walk / loop profile,
    a coherent-algebra diagonal entry), and every consecutive edge colour."""
    a, b = w[0], w[-1]
    return (tuple((c[(a, x)], c[(x, b)], c[(x, x)]) for x in w),
            tuple(c[(w[i], w[i + 1])] for i in range(len(w) - 1)))


def repeat_pattern(w):
    """Canonical equality pattern of the walk's positions (the truth the key must match)."""
    first = {}
    out = []
    for i, x in enumerate(w):
        out.append(first.setdefault(x, i))
    return tuple(out)


def purity(n, adj, c, L, starts=None):
    """Are 'is simple' / the full repeat pattern constant on each condensed class?"""
    starts = range(n) if starts is None else starts
    cls_simple, cls_pat = {}, {}
    total = 0
    for a in starts:
        for w in walks_from(n, adj, a, L):
            total += 1
            k = condensed_key(w, c)
            cls_simple.setdefault(k, set()).add(len(set(w)) == len(w))
            cls_pat.setdefault(k, {}).setdefault(repeat_pattern(w), w)
    mixed_s = [k for k, v in cls_simple.items() if len(v) > 1]
    mixed_p = [k for k, v in cls_pat.items() if len(v) > 1]
    n_in_mixed = sum(1 for k in mixed_s for _ in [0])
    return total, len(cls_simple), mixed_s, mixed_p, cls_pat


def sep_purity(n, adj, c, L, starts=None):
    """Per separation s: is 'this walk repeats at separation s' determined by the key?

    Separation s means x_i = x_{i+s}.  Repeats touching position 0 or L are free (DiagSep),
    so only INTERIOR ones (0 < i, i+s < L) are counted.
    """
    starts = range(n) if starts is None else starts
    cls = {}
    for a in starts:
        for w in walks_from(n, adj, a, L):
            k = condensed_key(w, c)
            d = cls.setdefault(k, {})
            for s in range(2, L):
                hit = any(w[i] == w[i + s] for i in range(1, L - s))
                d.setdefault(s, set()).add(hit)
    out = {}
    for s in range(2, L):
        positions = len(range(1, L - s))          # is the separation even expressible?
        witnessed = sum(1 for d in cls.values() if True in d.get(s, ()))
        mixed = sum(1 for d in cls.values() if len(d.get(s, ())) > 1)
        out[s] = (positions, witnessed, mixed)
    return out, len(cls)


def report(label, n, adj, v, lengths=(4, 5), starts=None):
    auts = all_isos(n, adj, [0] * n, [0] * n)
    orb = orbits(n, auts)
    root_cells = len(set(orb))
    print(f'=== {label}   n={n} |Aut|={len(auts)}')
    for tag, vv in (('ROOT (no individualization)', None), (f'RESIDUE after indiv v={v}', v)):
        c = wl2_indiv(n, adj, vv)
        fib = sorted({c[(x, x)] for x in range(n)})
        if vv is None:
            tgt = root_cells
            cao = len(fib) == tgt
        else:
            stab = [g for g in auts if g[vv] == vv]
            korb = orbits(n, stab)
            tgt = len(set(korb))
            cao = all((c[(x, x)] == c[(y, y)]) == (korb[x] == korb[y])
                      for x in range(n) for y in range(n))
        print(f'  --- {tag}:  2-WL fibres {len(fib)} vs orbits {tgt}   CAO holds? {cao}')
        for L in lengths:
            total, ncls, mixed_s, mixed_p, cls_pat = purity(n, adj, c, L, starts)
            print(f'      L={L}: {total:8d} walks -> {ncls:6d} condensed classes   '
                  f'MIXED on is-simple: {len(mixed_s):5d}   MIXED on repeat-pattern: {len(mixed_p):5d}')
            if mixed_s:
                k = mixed_s[0]
                ws = list(cls_pat[k].values())
                simple = [w for w in ws if len(set(w)) == len(w)]
                looped = [w for w in ws if len(set(w)) != len(w)]
                if simple and looped:
                    print(f'         WITNESS same condensed key: simple {simple[0]}  '
                          f'vs looped {looped[0]}')
        Lmax = max(lengths)
        sp, ncls = sep_purity(n, adj, c, Lmax, starts)
        parts = []
        for s, (pos, wit, m) in sp.items():
            if pos == 0:
                parts.append(f's={s}: n/a (no position)')
            elif wit == 0:
                parts.append(f's={s}: VACUOUS (never occurs)')
            else:
                parts.append(f's={s}: {"RECOVERABLE" if m == 0 else f"LOST ({m} mixed)"}')
        print(f'      interior-repeat detection at L={Lmax} ({ncls} classes): '
              + '  '.join(parts))
        sys.stdout.flush()
    print()


if __name__ == '__main__':
    n, adj = shrikhande(); report('Shrikhande (CAO root, 2-WL misses orbitals)', n, adj, 0)
    n, adj = rook44();     report('rook 4x4 (CAO root)', n, adj, 0)
    n, adj = net_z4();     report('net(Z4) = CFI[K4]-twisted', n, adj, 0, lengths=(4, 5, 6, 7))
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    n, adj, _, _ = cfi(K4, 4)
    report('CFI[K4] plain', n, adj, 0, lengths=(4, 5, 6, 7))
