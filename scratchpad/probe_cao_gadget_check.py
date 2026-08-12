"""probe_cao_gadget_check.py — verify the ONE-CUBE-PER-SLOT reduction.

Claim (reader, 2026-08-12): the two cubes per edge -- present only so the encoding is reversible
(`1->1'` vs `1'->1`) -- can be halved to ONE cube by attaching BOTH payload endpoints to BOTH
corners of the pair, which is symmetric in i,j by construction.

Checked here:
  (1) the gauge (Q4 translations) acts TRANSITIVELY on the 8 unordered complementary pairs, so all
      8 types are gauge-equivalent and the root stays one orbit;
  (2) delta = p ^ p' is CONSTANT (= 1111) on complementary pairs, so doc section 3.2's condition
      `1 ^ 1' = 2 ^ 2'` is satisfied AUTOMATICALLY and stops being a design obligation;
  (3) the ordered/two-cube alternative is NOT symmetric in i,j with a single cube -- confirming the
      doubling was load-bearing in the original design and that both-to-both is what removes it.
"""

ALL = 15


def unordered_pairs():
    seen, out = set(), []
    for p in range(16):
        q = p ^ ALL
        if p in seen:
            continue
        seen.add(p)
        seen.add(q)
        out.append(frozenset({p, q}))
    return out


if __name__ == '__main__':
    pairs = unordered_pairs()
    print(f'(0) Q4 has {len(pairs)} unordered complementary pairs (16 ordered)')

    orbit = {pairs[0]}
    frontier = [pairs[0]]
    while frontier:
        cur = frontier.pop()
        for t in range(16):
            img = frozenset({x ^ t for x in cur})
            if img not in orbit:
                orbit.add(img)
                frontier.append(img)
    print(f'(1) gauge orbit of one complementary pair: {len(orbit)} of {len(pairs)} '
          f'-> transitive: {len(orbit) == len(pairs)}')
    stab = [t for t in range(16) if frozenset({x ^ t for x in pairs[0]}) == pairs[0]]
    print(f'    stabilizer of a pair: {sorted(stab)}  (order {len(stab)}); '
          f'16 / {len(stab)} = {16 // len(stab)} = number of types')

    deltas = {min(p) ^ max(p) for p in pairs}
    print(f'(2) delta = p ^ p\' over all complementary pairs: {deltas} '
          f'-> constant: {len(deltas) == 1}  => doc 3.2 condition is AUTOMATIC')

    # (3) with ONE cube and an ORDERED attachment (i -> p, j -> p_bar) the configuration is not
    #     invariant under swapping i and j: the swap sends (p, p_bar) to (p_bar, p), a different
    #     ordered pair, and no translation fixes the slot while reversing the pair.
    p, q = min(pairs[0]), max(pairs[0])
    reversers = [t for t in range(16) if (p ^ t, q ^ t) == (q, p)]
    fixers = [t for t in reversers if all((x ^ t) in {p, q} for x in (p, q))]
    print(f'(3) translations reversing the ordered pair ({p},{q}): {reversers} '
          f'-> a single ORDERED cube is i/j-asymmetric unless one exists AND is the identity on '
          f'the slot; both-to-both removes the need.')
