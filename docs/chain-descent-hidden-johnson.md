# Chain descent — the hidden-Johnson question

Companion to [`chain-descent-calculator.md`](./chain-descent-calculator.md) §7,
which states as a one-line "near-theorem" that a Johnson group cannot be hidden
as the full automorphism group of a graph. This doc makes that rigorous as far
as it currently goes.

- **Pieces A and B — proved here (§3, §4).** A Johnson group that is *visibly*
  realised as graph symmetries forces the graph's edge set to be a union of just
  `k+1` "overlap classes" — a small, completely explicit structure.
- **Piece C — scoped here, not yet proved (§5).** Turning "small, explicit
  structure" into "chain descent canonises it in polynomial time". Classical and
  in reach; §5 is the work plan.
- **The limitation — §6.** All of this addresses only the *visible* Johnson
  (the vertices literally are the k-subsets). The *encoded*, CFI-style hidden
  Johnson — the genuine Tier-2 threat — is out of scope, and §6 says exactly why.

**Bottom line.** The near-theorem rigorously kills the *naive* hidden Johnson
(including the "blow each vertex up into a chunk" construction). It does not
close Tier 2; it *sharpens* it — any real hidden Johnson must be encoded.

---

## 1. Definitions

Fix integers `m, k` with `1 ≤ k` and `m ≥ 2k + 1`.

- **The label set** `[m] = {1, …, m}`.
- **k-subsets**: `V` is the set of all size-`k` subsets of `[m]`. There are
  `C(m,k)` ("m choose k") of them.
- **The Johnson graph** `J(m,k)`: vertex set `V`; two k-subsets are joined by an
  edge exactly when they overlap in `k-1` elements.
- **A label permutation** `σ` (a bijection `[m] → [m]`) acts on a k-subset by
  relabelling its elements: `σ · A = {σ(x) : x ∈ A}`. This sends k-subsets to
  k-subsets, so it is a permutation of `V`.
- **The Johnson group** is the set of all permutations of `V` that arise this
  way — one for each label permutation `σ`. (For `1 ≤ k ≤ m-1` distinct `σ`
  give distinct permutations of `V`, so the Johnson group is a faithful copy of
  the symmetric group `S_m`.) It is the symmetry group of `J(m,k)`.
- **Overlap classes.** For `j = 0, 1, …, k`, let
  `O_j = { (A, B) ∈ V × V : |A ∩ B| = j }` —
  the set of *ordered* pairs of k-subsets overlapping in exactly `j` elements.
  `O_k` is the diagonal (`A = B`); `O_{k-1}` is the edge set of `J(m,k)`. The
  `O_j` partition all ordered pairs into `k+1` blocks. Each `O_j` is a symmetric
  relation, since `|A ∩ B| = |B ∩ A|`.
- **A Johnson scheme graph** is a graph on vertex set `V` whose edge set is a
  union of overlap classes.

---

## 2. The near-theorem

> **Near-Theorem.** Let `G` be a graph whose vertices are identified with the
> k-subsets `V` (`m ≥ 2k+1`), and suppose the Johnson group is contained in
> `Aut(G)`. Then:
>
> - **(A + B)** `E(G)` is a union of overlap classes — `G` is a Johnson scheme
>   graph. *Proved, §3–§4.*
> - **(C)** `G` is canonised by chain descent in polynomial time: the Johnson
>   structure in `G` cascades, so it is Tier 1, not the Tier-2 wall. *Scoped,
>   §5.*

Two notes on the hypothesis.

- It says the Johnson group is *contained in* `Aut(G)`, not *equal to* it. This
  is the weaker, more natural hypothesis (the calculator doc §7 says "is"); a
  graph with *extra* symmetry beyond the Johnson group only cascades more
  easily, so containment is all that is used.
- It assumes the vertices *are* the k-subsets and the Johnson group acts on them
  the standard way (relabelling the `m` labels). This is the load-bearing
  assumption — §6 is about what happens when it fails.

---

## 3. Piece A — symmetry constrains the edges

**Lemma A.** Let `G` be any graph and `H` any group of automorphisms of `G`
(`H ≤ Aut(G)`). Then `E(G)` is a union of `H`-orbits on ordered vertex pairs.

(An *`H`-orbit on ordered pairs* — the technical name is an *orbital* — is a
maximal set of pairs that `H` shuffles among themselves: `(u,v)` and `(u',v')`
are in the same orbit when some `h ∈ H` sends `u ↦ u'` and `v ↦ v'`.)

*Proof.* By definition, `h ∈ Aut(G)` means `h` preserves edges: `(u,v) ∈ E(G)`
iff `(h·u, h·v) ∈ E(G)`. So every `h ∈ H` maps `E(G)` onto `E(G)`. A set mapped
onto itself by every element of `H` contains, with any pair `(u,v)`, the entire
`H`-orbit of `(u,v)`. Hence `E(G)` is a union of `H`-orbits. ∎

**This lemma, on its own, is empty.** It holds for *every* graph and *every*
group of its symmetries — it is just the definition of "automorphism" restated.
"Symmetry forces a scheme" is true universally and says nothing on its own. All
the content of the near-theorem is in Piece B: it is specifically the *Johnson*
group whose orbits are simple.

---

## 4. Piece B — the Johnson group's pair-classes are overlap-size

**Lemma B.** The orbits of the Johnson group on ordered pairs of k-subsets are
*exactly* the `k+1` overlap classes `O_0, O_1, …, O_k`.

In words: two pairs of k-subsets can be carried one to the other by a label
permutation **if and only if** they have the same overlap size. The Johnson
group cannot tell two pairs apart by anything finer than overlap.

*Proof.* Two things to show: (i) each `O_j` is *preserved* by the Johnson group,
and (ii) the Johnson group acts *transitively* on each `O_j` (so `O_j` is a
single orbit, not several smaller ones).

*(i) Preserved.* A label permutation `σ` is a bijection of `[m]`, so it
preserves intersection sizes: `|σ·A ∩ σ·B| = |A ∩ B|`. So `σ` maps `O_j` into
`O_j`. Hence each `O_j` is a union of orbits.

*(ii) Transitive on each `O_j`.* Take two pairs `(A,B)` and `(A',B')`, both with
overlap exactly `j`. Each pair carves the label set `[m]` into four regions:

| region             | `(A,B)` size  | `(A',B')` size |
|--------------------|---------------|----------------|
| in both            | `j`           | `j`            |
| in the first only  | `k - j`       | `k - j`        |
| in the second only | `k - j`       | `k - j`        |
| in neither         | `m - 2k + j`  | `m - 2k + j`   |

The region sizes depend only on `m, k, j` — so the two pairs carve `[m]` into
regions of *matching sizes* (all four sizes are `≥ 0` because `m ≥ 2k+1` and
`0 ≤ j ≤ k`). Pick any label permutation `σ` that maps each region of `(A,B)`
onto the same-size region of `(A',B')`. Then `σ` carries the "in both" and "in
first only" regions of `(A,B)` onto those of `(A',B')`, whose union is `A'`; so
`σ·A = A'`. Likewise `σ·B = B'`. So one pair maps to the other — the action is
transitive on `O_j`.

By (i) and (ii) each `O_j` is exactly one orbit; there are `k+1` of them. ∎

**Corollary (A + B).** If the Johnson group is contained in `Aut(G)`, then
`E(G)` is a union of overlap classes — and, since `E(G)` has no self-loops, a
union of `O_0, …, O_{k-1}`. `G` is a Johnson scheme graph.

*Proof.* Lemma A: `E(G)` is a union of Johnson-group orbits. Lemma B: those
orbits are the `O_j`. The diagonal `O_k` is excluded as `E(G)` has no loops. ∎

**Why this has teeth.** There are only `k+1` overlap classes, and they are
described by a single number — the overlap size. The moment a Johnson group is
*visibly* the symmetry of a graph, the graph's entire edge structure is pinned
to one of a *tiny, totally explicit* menu. This is the exact opposite of
"refinement-resistant": there is nothing for refinement to fail to see. Piece C
turns this into the polynomial-time bound.

---

## 5. Piece C — scope and work plan  *(not yet proved)*

**Goal.** Promote the Corollary to: *a Johnson scheme graph is canonised by
chain descent in polynomial time* — equivalently, the Johnson structure
cascades, so it is Tier 1.

The work splits into four sub-pieces. None is open-problem-hard; the difficulty
ratings are relative.

**C1 — Orbit / transversal structure (the backbone). *[in reach — standard]***
At any descent node, some set of k-subsets `A_1, …, A_t` has been
individualised. The leftover Johnson symmetry is the set of label permutations
fixing every `A_j` setwise. Claim: this is a *Young subgroup* — the `A_j`
together cut `[m]` into "atoms", and the leftover group is exactly "permute each
atom freely, no mixing across atoms". Its orbits on the remaining vertices are
the *profile classes*: two k-subsets are interchangeable iff they have the same
intersection size with every atom. Pure finite-group theory (Young subgroups
acting on k-subsets); a handful of lemmas; independent of *which* overlap
classes happen to be edges (it depends only on the group).

**C2 — Transversal discovery, i.e. T-C for this class. *[the crux]***
The chain-descent cost model (`chain-descent-calculator.md` §4) is polynomial
once each stabiliser-chain level's transversal can be *discovered* cheaply
(theorem T-C). By C1 each transversal is a profile class, and a profile class is
computable directly in polynomial time — for each vertex, compute its
intersection sizes against the individualised k-subsets. So T-C holds for
Johnson scheme graphs.

- *Subtlety.* This routes T-C through *direct computation of profiles*, not
  through 1-WL refinement. For the Johnson graph itself (`E(G) = O_{k-1}`), 1-WL
  from one individualised vertex already recovers the overlap partition
  (standard: the Johnson graph is distance-regular). For a *general* union of
  overlap classes it is not immediate that 1-WL alone recovers the full profile
  partition — it may land on a coarser one.
- *Routing decision.* Prove C2 via direct profile computation (call it option
  b): it is elementary and fully general. Treat "1-WL alone also recovers the
  profiles" (option a) as an *optional* strengthening — clean for the Johnson
  graph, a small separate question for general unions. Option (b) already
  delivers the near-theorem's conclusion ("a visible Johnson is not a wall"): it
  exhibits a cheap oracle, which is the point.

**C3 — Depth bound. *[in reach — easy]***
Each genuine individualisation splits an atom in two, and there are at most `m`
atoms, so the chain has at most `m-1` genuine levels (and `≤ C(m,k)` levels
total). Polynomial.

**C4 — Assembly. *[in reach — bookkeeping]***
C1 + C2 + C3, together with theorems T-A and T-B (free, from computational
group theory — `chain-descent-calculator.md` §4), give: the descent is a single
lex-leader path of polynomially many levels, each costing polynomial work.
Hence polynomial total. A Johnson scheme graph is Tier 1.

**Main risk.** Only C2's optional strengthening (option a) is genuinely
uncertain — and it is optional. Everything load-bearing — C1, C2 option (b),
C3, C4 — is classical finite-group theory and combinatorics.

**Effort.** Paper-rigorous: a bounded task, roughly a dozen lemmas, all
standard; clearly doable. Lean: C1 needs Young subgroups acting on k-subsets
built up (mathlib has the permutation/subgroup groundwork but not this action
packaged); C2–C4 are lighter. A real but finite formalisation project —
recommend paper-first, then assess Lean separately.

**Connection to orbit-recovery work (2026-05-26).** Tier 2 of the
orbit-recovery program
([`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md) §10)
sketches a theorem that **subsumes Piece C** — orbit recovery for
association schemes (Johnson, Hamming, distance-regular) at depth 1.
The proof routes through scheme intersection-matrix theory rather than
through Young subgroup combinatorics directly, which may give a
cleaner path than the C1–C4 plan above. Worth comparing the two routes
once Tier-1 orbit-recovery is settled.

---

## 6. What the near-theorem does and does not rule out

The hypothesis is precise: the vertices *are* the k-subsets, and the Johnson
group acts on them *the standard way* — relabelling the `m` labels. Under that
hypothesis, Pieces A and B force the simple overlap structure and Piece C
(scoped) makes it polynomial.

**What this rules out — the naive hidden Johnson.** Any attempt to build a hard
instance by taking a Johnson graph and dressing it up *while keeping the
k-subsets as the vertices* is dead. In particular the "blow each vertex up into
a chunk" idea: a uniform blow-up is undone by refinement (the chunks become
cells and collapse back to points), and the result still satisfies the
hypothesis — so A, B, C apply and it cascades. There is no hiding here.

**What this does *not* rule out — the encoded hidden Johnson.** A genuine hidden
Johnson, of the kind discussed in `chain-descent-calculator.md` §7, does *not*
satisfy the hypothesis. The Johnson group is still inside `Aut(G)`, but it acts
on a *gadget* vertex set through a CFI-style encoding — the vertices are not the
k-subsets, and the symmetries are not visible label-relabellings.

Against such a graph:

- Lemma A still holds — `E(G)` is a union of the orbits of *whatever* action the
  encoding produces.
- Lemma B **fails** — those orbits are not the overlap classes `O_j`. They are
  whatever the encoding produces, and an encoding can make them a large,
  refinement-resistant family (exactly what CFI does to a `Z₂`).

So the near-theorem's method — Piece B — is specifically a statement about the
standard k-subset action. It has nothing to say about an encoded action. Proving
A, B, C does not shrink the real Tier-2 question; it *sharpens* it: any genuine
hidden Johnson **must** be encoded, never naive. Ruling out the encoded case is
the open construction question of `chain-descent-calculator.md` §7 — and it is
Babai-hard.
