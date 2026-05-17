# Polynomial canonization strategy (forward greedy + backward flip-validation)

A candidate **polynomial-time** graph canonizer whose only persistent state is a
partial-order matrix `P`. The design is an extension of
[`CanonGraphOrdererPartialOrderSinglePair`](../GraphCanonizationProject/CanonGraphOrdererPartialOrderSinglePair.cs)
that replaces exponential branching with a two-pass discipline:

1. **Forward pass** — greedily build a guess stack with a single-pair guess per
   non-singleton cell, propagating after each.
2. **Backward pass** — from the deepest guess outward, decide whether it is a
   true symmetry tie-break (lock) or a wrong-direction choice (flip and
   lex-min). Each guess is touched at most once per pass.

Total work `O(n · poly(n))` *if* the invariants in §4 hold. That would resolve
GI ∈ P, so the burden of proof is high; this document records the precise
claims the implementation depends on so they can be validated or broken.

---

## 1. State

The **only persistent state** is

```
P : n×n matrix over {Less, Unknown, Greater}
```

held antisymmetric and transitively closed at all times. `P` begins all
`Unknown` apart from order forced by vertex types. The vertex partition into
"cells" (suspected automorphism orbits) is re-derived from `(A, P)` at every
step — never stored.

The algorithm additionally maintains a **transient guess record** for the
backward pass:

```
guesses : stack of GuessRecord
GuessRecord = {
    a, b          : the two vertices
    direction     : LESS (a<b) or GREATER (a>b)
    kind          : PRIMARY (forward-pass choice) | DERIVED (closure)
    driver        : index of the PRIMARY guess that forced this one
                    (DERIVED only; null for PRIMARY)
    cell_snapshot : the cell-tree position the guess split
}
```

The guess record is not state in the canonization sense — it's a transcript of
how `P` was built, used only by the backward pass.

---

## 2. Operations

### Refine (free, reads `P`, never writes it)

1-WL colour refinement on the coloured graph
`(A, edge_label = (adj[u,v], P[u,v]))`. Each vertex's colour is the sorted
multiset of `(neighbour_colour, edge, Prel)` tuples, iterated to a fixpoint.
**Split-only**: refinement can never order two cells. Cells are numbered in
canonical signature order, so any "lex-min cell / pair" rule is
isomorphism-invariant.

### Primary guess (the only writer of `P` from a choice)

Pick one non-singleton cell `C` (lex-min by canonical id). Pick two of its
members `a, b` (lex-min by index — they are 1-WL-equivalent at this point, so
index-based selection is invariant up to the orbit-equivalent choice the
backward pass will reconcile). Write `P[a,b] = LESS`, push a `PRIMARY` record.

### Transitive closure (treated as a series of `DERIVED` guesses — §4.4)

For each `(i,j,k)` with `P[i,k] = LESS` and `P[k,j] = LESS` and
`P[i,j] = UNKNOWN`: set `P[i,j] = LESS`, push a `DERIVED` record with
`driver` = the most-recent `PRIMARY` that completed the chain. If at any
point a derivation would set `P[v,v] = LESS` or contradict an existing
`P[i,j] = GREATER`, the branch is **dead** (no canonical form along this
path; the lex-min in the backward pass will pick the surviving direction).

### Local orbit test (polynomial)

Given a primary guess `(a, b)` made in cell `C` that split into `A ∋ a` and
`B ∋ b`, the test asks: *does the pairing of `A` to `B` induced by deeper
guesses extend to an automorphism that fixes everything outside `C`?* It is
a row/column permutation check: build the permutation `σ` that maps each
`A`-vertex to its `B`-partner (and vice versa) and is the identity
elsewhere, then verify `σ·A·σᵀ = A` and that every locked `P` relation is
σ-stable. `O(n²)`. Sound (a passing test really witnesses an automorphism);
sound-but-incomplete is acceptable because a false `no` only triggers a
lex-min recompute that gives the same canonical result.

---

## 3. The two passes

### Forward pass

```
refine to fixpoint
while some cell |C| > 1:
    a, b := lex-min pair within C
    push PRIMARY(a, b, LESS)
    P[a,b] := LESS;  P[b,a] := GREATER
    transitive-close P (pushing DERIVED records)
    refine to fixpoint
```

Termination: every primary guess strictly increases the number of `P`-resolved
pairs, bounded by `n²`. In practice the cell count strictly decreases per
guess, so termination is in `O(n)` primaries.

### Backward pass

```
for i = len(guesses) − 1 down to 0:
    g := guesses[i]
    if g.kind == DERIVED: continue        # decided by g.driver
    if transposition_test(g.a, g.b, P_at_position(i)):
        g.locked := VALID                 # the swap is genuinely an Aut
        continue
    if local_orbit_test(g.a, g.b, g.cell_snapshot):
        g.locked := VALID
        continue
    # Flip and lex-min:
    re-propagate from position i with direction reversed
    if lex(M_reverse) < lex(M_current):
        rewrite g and its DERIVED descendants
        adopt the reversed permuted matrix
    g.locked := RESOLVED
```

Each `PRIMARY` is visited once; each visit is `O(poly(n))`; there are `O(n)`
primaries; total `O(n · poly(n))` provided the invariants in §4 hold.

---

## 4. The invariants the polynomial claim depends on

These are the load-bearing claims. The algorithm is correct iff (4.1) and
(4.4) hold; it is polynomial iff (4.2) and (4.3) additionally hold.

### 4.1  Iso-invariance of the guess set (correctness)

At every node the set of candidate guesses is a function of `(A, P)` only.
Cell ids come from canonical signature order; the in-cell pair `(a, b)` is
lex-min by index, which selects an automorphism-equivalent representative.
This is the standard IR correctness argument and is shared with
`PartialOrderIR` / `SinglePair`.

### 4.2  Weakened symmetry of propagation (polynomial)

> For every pair `(v, w)`, `v` and `w` are in the same cell after propagating
> `a<b` iff they are in the same cell after propagating `b<a`.

I.e. *the partition coarseness is direction-independent*; only labels and the
roles of `a`, `b` themselves swap. This is what permits a backward flip to
reuse the deeper cell structure verbatim instead of re-discovering it.

**Why it holds for 1-WL.** The equivalence relation 1-WL computes is the
coarsest equitable refinement of the initial colouring. Swapping one `Less`
for one `Greater` is a *relabelling* of signature symbols, not a change in
their structural information content. Empirically verified on `C4` with
`(0 1)` non-Aut, on the 6-vertex asymmetric graph
`{0-1, 0-2, 0-3, 1-4, 2-5}` with `(1 2)` non-Aut, and on `K3`. No
counterexample is known to the authors.

**Why it holds across closure.** Within a cell, all vertices have identical
Prel profiles, so closure produces *the same* new derivations for every
cell-mate (either everyone in the cell gains `Less` to some target, or no
one does). The within-cell symmetry is preserved by closure exactly when it
was preserved beforehand. Therefore closure-derived asymmetries only affect
vertices that were already distinguished, and partition coarseness survives.

**Status.** Empirical, not proven. The first place to look for a
counterexample is a CFI graph where 1-WL fails — see §6.

### 4.3  Deeper-guess locks survive shallow flips (polynomial)

> A `VALID` lock on a deeper primary guess remains correct after flipping a
> shallower primary, provided weakened symmetry holds.

This is what permits the backward pass to be linear in the guess count. The
argument: by 4.2 the cell that the deeper guess split is the same set of
vertices in both shallow directions, and the local orbit test is a function
of (cell members, A restricted to them, P restricted to them with deeper
constraints) — all of which transport unchanged.

**Status.** This is the single most fragile claim and the one most worth
falsifying first. A failure here means the backward pass cascades and the
polynomial bound is lost. See §6 for the diagnostic that detects it.

### 4.4  Closure as guess (correctness + polynomial)

A naive transitive closure can derive a chain of `n!` orderings that all
trace back to a single primary guess; if the primary is later flipped, the
chain must unravel. To bound this:

- Every relation written by closure is recorded as a `DERIVED` guess with a
  `driver` pointer to the most-recent `PRIMARY` whose addition completed the
  chain. (If multiple primaries could have completed it, the lex-earliest
  one wins — this is iso-invariant given canonical guess ordering.)
- The backward pass skips `DERIVED` records; they ride along with their
  driver. Flipping a primary automatically flips its `DERIVED` descendants
  (the new direction re-runs closure from scratch under the flipped
  primary).
- There are at most `n(n−1)` `DERIVED` records total (one per directed cell
  pair), so the bookkeeping stays polynomial.

**Why no transitive-closure issue arises between non-automorphic pairs.**
A non-automorphic pair `(u, v)` is, by definition, in different cells. The
direction `u<v` vs `u>v` is *forced* by structure (transitive closure of
relations already on `P`), not chosen — so the comparison function would
give the same verdict from either side. Closure asymmetries are confined to
pairs whose ordering descends from a primary guess; flipping the primary
flips the chain.

---

## 5. Why this is potentially polynomial (and why that's suspicious)

If all four invariants hold:

- Forward pass: `O(n)` primaries × `O(n³)` per propagation = `O(n⁴)`.
- Backward pass: `O(n)` primaries × `O(n²)` per local orbit test +
  `O(n⁴)` worst-case re-propagation on a flip = `O(n⁵)`.
- `DERIVED` records: `O(n²)` rewrite cost amortised over the backward pass.

Total `O(n⁵)`. Polynomial.

This would resolve **Graph Isomorphism ∈ P**, currently quasi-polynomial
(Babai). That is not a refutation, but it is a very strong reason to demand
proof of 4.2 and 4.3 rather than empirical evidence on small cases — the
known GI-hard families are explicitly constructed to defeat 1-WL-style
arguments, and a polynomial canonizer must handle them.

---

## 6. Validation strategy

The cheapest move is implementation plus targeted testing. Run on:

- **CFI(K_m)** for `m = 3, 4, 5, 6`, using
  [`CfiGraphGenerator`](../GraphCanonizationProject/CfiGraphGenerator.cs).
- **Miyazaki graphs** at growing sizes (need a generator; standard
  constructions in the literature).
- The existing scramble-invariance test bed at sizes 4–7 to confirm no
  regression.

For each run, record:

| Metric | What a failure looks like |
|---|---|
| Primary guess count | Super-linear in `n` ⇒ forward pass not bounded as claimed |
| `DERIVED` count | Super-quadratic in `n` ⇒ closure-as-guess bookkeeping leaks |
| Backward-pass flips | Should be `O(n)` |
| **Locked-then-invalidated guesses** | **Any non-zero count falsifies 4.3 directly** |
| Wall-clock scaling | Super-polynomial trend on the CFI/Miyazaki series |
| Canonical-form stability across scramblings | Disagreement falsifies 4.1 |

The locked-then-invalidated counter is the most diagnostic: if a deeper
guess that was marked `VALID` ever turns out to have the wrong direction
when re-checked after a shallow flip, the polynomial argument has collapsed
and the failure pinpoints the structural fact that needs replacement.

---

## 7. Implementation notes

Build on `CanonGraphOrdererPartialOrderSinglePair`:

- Reuse: `Refine`, `TransitiveClose`, `SeedFromTypes`, `IsTotal`,
  `ReadPermutation`, `ApplyBetween`/`ApplyIndividualize` helpers.
- Replace: `Search` (exhaustive recursion) with `ForwardPass` (greedy stack
  build) followed by `BackwardPass` (single sweep).
- Add: guess stack with `PRIMARY`/`DERIVED` distinction; per-guess
  `cell_snapshot` (just the member list of the split cell — `O(n)` per
  guess, `O(n²)` total); `LocalOrbitTest(a, b, cell)`; `TranspositionTest`
  as a fast pre-check.

A useful intermediate milestone: implement only the **forward pass + final
read-off**, with no backward pass. This is already a complete canonizer if
weakened symmetry plus iso-invariant cell selection are enough — it's the
"trust the first direction" version. Comparing its outputs against
`PartialOrderIR` on the size-4/5/6/7 known-graphs corpus tests whether the
forward direction alone is correct; if it is, the backward pass is purely
about correcting wrong choices and the polynomial claim narrows to "are
wrong choices rare enough that the backward pass terminates quickly."

Test scaffolding analogous to
[`GraphCanonTests.PartialOrderIR.cs`](../GraphCanonizationProject.Tests/GraphCanonTests.PartialOrderIR.cs)
should be added with the diagnostic counters from §6 exposed.

---

## 8. Open questions

1. **Prove or disprove 4.2 across closure.** A proof would discharge the
   correctness concern entirely; a counterexample would point at a
   replacement for the cell-tracking model.
2. **Prove or disprove 4.3.** Even if 4.2 holds, the deeper-guess lock
   survival is a separate claim and the load-bearing one for polynomial
   bound.
3. **Closure-as-guess assignment of `driver`.** The "lex-earliest primary
   that completes the chain" rule is iso-invariant under canonical guess
   ordering, but a multi-primary chain needs the assignment to be
   *deterministic* in the face of order-of-derivation ambiguity. Specify
   precisely.
4. **Behaviour when both forward directions of a primary lead to a closure
   contradiction.** Section 2 calls this branch dead, but the algorithm
   must pick the surviving canonical form somehow. If neither survives,
   that's a propagation-soundness bug, not an algorithm bug — but a clean
   error mode needs to be defined.
5. **Higher-`k`-WL as the propagation engine.** Stronger refinement reduces
   the primary guess count and shrinks the work the backward pass has to
   do. The complexity arithmetic of §5 changes; the invariants 4.2–4.4
   should still hold (refinement strength is orthogonal to the
   directional-symmetry argument).
