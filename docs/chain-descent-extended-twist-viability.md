# Extended twist construction — viability proof plan

> **Status: paper-proof plan (paper-first).** A plan for deciding whether
> the *extended* (non-singleton sub-cell) twist construction of the linear
> oracle is **provably valid** — so we can use it freely — or **provably
> fails** on some configuration — which narrows the construction's scope.
> Not a proof; a route to one. Companion to
> [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md) §4.2–§4.4.

---

## 0. The question, framed precisely

The linear oracle constructs a candidate twist `t : V → V` carrying an
explored representative `r_1` onto an unexplored `r_j`, by matching the
refinement footprint (coupled-component sub-cells) of `r_1` to that of
`r_j` and matching vertices within paired sub-cells
([linear-oracle.md §4.2](./chain-descent-linear-oracle.md)).

- **All-singletons case:** every sub-cell is a singleton ⇒ the matching
  is **forced**. This is the clean, provable case (the Phase-1 Lean
  target, [linear-oracle.md §8.2](./chain-descent-linear-oracle.md)).
- **Extended (non-singleton) case:** some sub-cell `C` has `|C| ≥ 2`.
  The within-`C` vertex matching is *not* forced. The "attempt any size,
  verify gates" stance ([build brief §3](./chain-descent-linear-oracle-build-brief.md))
  says to attempt it anyway and let the edge-check filter. Empirically
  (CFI K4, 2026-05-28) this case is common: 13/29 size-2 decision
  footprints and *all* size-3+ footprints have a non-singleton sub-cell.

**Three distinct properties — keep them separate.**

1. **Soundness** — never harvest a non-automorphism. This is **free**:
   the §4.5 edge-by-edge `IsAutomorphism` gate rejects any bad candidate.
   Soundness is *not* the question.
2. **Iso-invariance of the verdict** — the descent's flag/canonical
   output must be a function of iso-invariant cell ids, not the input
   labelling ([strategy §15 gap 2](./chain-descent-strategy.md)). With
   the oracle *online*, twist *discovery* must be iso-invariant too. This
   is a **hard requirement**, and it is where the extended case is at
   risk.
3. **Effectiveness** — does the construction actually produce the twist
   when one exists (so the descent collapses)?

So the viability question is: **is there an iso-invariant construction
rule that is effective for non-singleton sub-cells — or is there a
configuration where no such rule exists?**

---

## 1. The central obstruction (the likely-decisive observation)

> **Within a non-singleton sub-cell, there is no iso-invariant order.**

A sub-cell `C` is a *cell*: every vertex in `C` has the **same refined
colour** — they are refinement-indistinguishable by construction. So any
rule that matches vertex `a ∈ C` (in `r_1`'s footprint) to a specific
vertex `a' ∈ C'` (in `r_j`'s) must break the tie *using information
1-WL cannot see* — i.e. the vertex index. That makes the discovered
twist a function of the labelling, violating requirement (2).

This splits the non-singleton case into two structurally different
sub-cases, and **neither admits a direct iso-invariant match:**

- **(a) Symmetric residual.** The residual stabilizer (automorphisms
  fixing the path, preserving `P`) acts non-trivially on `C` — say it
  contains a swap `(a b)` with `a, b ∈ C`. Then *both* `a ↦ a'` and
  `a ↦ b'` extend to valid twists (they differ by the stabilizer). The
  only iso-invariant object is the **whole coset** of valid matchings,
  not a single one. An iso-invariant rule would have to be
  stabilizer-equivariant, which cannot single out one vertex's image.
- **(b) Rigid residual (IR blind spot).** `C` is non-singleton yet the
  residual stabilizer is *trivial* on it — refinement-resistant but
  asymmetric (the Neuen–Schweitzer multipede regime,
  [strategy §15 gap 5](./chain-descent-strategy.md)). There **is** a
  unique correct matching, but refinement cannot expose it, so no
  bounded rule finds it; there is also no symmetry to harvest.

**Consequence.** The "extended construction" *read as a direct canonical
match within non-singleton sub-cells* is **not viable** — case (a) is
forbidden by iso-invariance, case (b) has no twist to find. The
all-singletons case is special precisely because a singleton sub-cell
gives a forced, iso-invariant match (one vertex, no tie to break).

This reframes the real question (next section): the viable extension is
not "match within `C`" but **"individualize within `C` and recurse"** —
whose termination is exactly *orbit recovery*.

---

## 2. The reframe: the viable extension is recursion = orbit recovery

Refinement leaves `C` non-singleton ⇒ it cannot, *at this depth*,
separate `C`'s vertices. The principled, iso-invariant move is to
**individualize a representative of `C` and re-refine** — pushing the
decision one level deeper ([linear-oracle.md §4.4](./chain-descent-linear-oracle.md)
option 2). The extended construction then *reduces to the all-singletons
case at greater depth* **iff `C` cascades to singletons in bounded
depth**.

That "iff" is the **orbit-recovery property**, already a theorem for the
relevant classes:

- `OrbitPartition adj P S` ⊆ warm-refine partition **always** (orbits ⊆
  cells; [orbit-recovery §3](./chain-descent-orbit-recovery.md)). A
  non-singleton sub-cell is a cell that may be *coarser* than its orbits.
- **`theorem_1_HOR_at_depth` / `theorem_1_HOR_cfi_oddDeg`** (proved,
  axiom-free for OddDegree CFI): for CFI(H), bounded individualization
  (`≤ tw(H)`) makes warm refinement **discrete**, so cells = orbits —
  every sub-cell becomes a singleton at the cascade depth.
- **`theorem_2_HOR_concrete_rank_two_J_singleton`** (proved, axiom-clean):
  for schurian scheme graphs of rank ≤ 2, `|J| = 1` (Petersen / Kneser /
  Johnson `J(5,2)`), 1-WL at depth 1 already equals the `Aut_v`-orbit
  partition.

So **for the cascade class the recursion provably terminates**, and the
extended construction *is* viable — but its content is entirely carried
by the orbit-recovery theorems, not by a new "matching" idea.

---

## 3. The expected verdict (hypothesis to confirm or refute)

> The extended construction is viable **exactly up to the
> cascade / abelian boundary**, and that boundary **coincides with the
> global tractable/wall split** — because it is the same orbit-recovery
> (T-C) question localized to a sub-cell.

Concretely, partition non-singleton sub-cells by their residual:

| Sub-cell residual | Viable? | Mechanism | Status |
|---|---|---|---|
| (none — all-singletons) | **Yes** | forced match | provable now (warm_6_2) |
| Abelian, cascades (`Z₂` gauge) | **Yes, recursively** | individualize + recurse to singletons | inherits `theorem_1_HOR` |
| Schurian-scheme residual | **Yes, recursively** | depth-1 (or depth-`k`) recovery | inherits `theorem_2_HOR` |
| Rigid / IR blind spot | **No** | no symmetry to harvest | flag (gap 5) |
| Non-abelian wall (hidden Johnson, `A_k`) | **No (conjectured)** | no bounded cascade | the open wall |

So the answer to *"can we use it freely?"* is: **freely within the
cascade class** (which the orbit-recovery theorems certify), **not at the
wall** — and the wall is *detectable* (a non-singleton sub-cell that
fails to cascade after the orbit-recovery depth bound). The
direct-index-matching version is never used: it is unsound for the
*verdict's* iso-invariance even though the edge-check keeps the *answer*
sound.

This is exactly the "narrows our options" outcome: the construction is
**all-singletons-direct, else recurse-to-cascade, else flag** — not
"attempt an arbitrary match at any size."

---

## 4. Proof obligations (ordered lemma chain)

A1–A2 are the positive Phase-1 result; B1 is the new obstruction lemma;
B2 is assembly of existing theorems; B3 is the known-hard wall.

- **A1 — forced match is iso-invariant and unique (all-singletons).**
  When every coupled sub-cell is a singleton, the `r_1 ↔ r_j` matching is
  the unique partition-respecting bijection. *Tools:* `warm_6_2` /
  `warmRefine_agree_off'` (the two branches share the partition),
  `samePartition_chain` (the residual is exactly the `DirAssignment`
  choice), `rankPerm` (the canonical relabelling).
- **A2 — the forced twist is an automorphism for the abelian gauge.**
  For the `Z₂^β` CFI gauge, `t` is a product of `flipPair`s; it preserves
  adjacency. *Tools:* `flipPair`, `flipPair_comm` (abelian),
  `flipPair_partition_invariant`; discharge `LeafTwistSpec`
  (`relabelMatrix t (canonAdj σ) = canonAdj σ'`). **This is the Phase-1
  Lean deliverable.**
- **B1 — iso-invariance obstruction (new, the linchpin).** If a coupled
  sub-cell `C` has `|C| ≥ 2` and a non-trivial residual stabilizer, then
  no iso-invariant (stabilizer-equivariant) rule selects a single
  within-`C` bijection; the iso-invariant object is the coset. *Route:*
  formalize "iso-invariant discovery = equivariant under the residual
  stabilizer", then show equivariance + single-valued ⇒ trivial
  stabilizer on `C`. Pairs with the rigid sub-case (B1'): a rigid
  non-singleton `C` has no automorphism to harvest at all
  (`aut_trivial_of_discrete_warmRefine` contrapositive at non-discrete
  depth). Together: **non-singleton ⇒ no direct iso-invariant twist.**
- **B2 — recursive resolution = orbit recovery.** Individualizing a rep
  of `C` and re-refining strictly refines the footprint; iterating
  reaches all-singletons within the orbit-recovery depth. *Tools:*
  `CascadesAt`, `theorem_1_HOR_at_depth`, `theorem_2_HOR_concrete`. The
  extended construction *inherits* their depth bounds (`≤ tw(H)` for CFI,
  `1` for rank-≤2 schemes).
- **B3 — the wall (failure case).** Exhibit / characterize a non-singleton
  sub-cell whose residual is a non-abelian action that does **not**
  cascade in bounded depth (the encoded-Johnson case). Proving the
  failure = confirming the boundary. *Connection:* hidden-Johnson
  [Piece C](./chain-descent-hidden-johnson.md) (the cascade half) is the
  same obligation, localized to a sub-cell.

---

## 5. What this determines for the C# build

- **Implement A1/A2:** all-singletons direct matching — provably valid,
  iso-invariant. (M3, the clean case.)
- **Do *not* implement direct index-matching for non-singletons.** It is
  sound (verification) but its *success is labelling-dependent*, which
  would break the iso-invariance of the flag/canonical **verdict** (gap
  2) even though the returned matrix is correct. This is the precise
  sense in which "attempt any size" must be qualified: attempt
  *recursion*, not *index-matching*.
- **For non-singletons: recurse** (individualize within `C`, re-refine,
  retry the now-finer footprint), bounded by the orbit-recovery depth;
  **flag** if it has not cascaded by then (rigid or wall). This is M4/M5,
  and it is literally the cascade oracle applied to a sub-cell.

---

## 6. Tractability and effort

- **A1/A2:** tractable; the Phase-1 Lean target already scoped in
  [linear-oracle.md §8.2](./chain-descent-linear-oracle.md). ~as planned.
- **B1 (obstruction):** new but small — an equivariance argument about
  refinement-indistinguishable cells; should be paper-tractable and
  Lean-feasible (it is a *negative* statement, often easier).
- **B2 (recursion = orbit recovery):** **largely already done** —
  `theorem_1_HOR_cfi_oddDeg` (axiom-free) and
  `theorem_2_HOR_concrete_rank_two_J_singleton` (axiom-clean) supply the
  termination. The extended construction *assembles* them; little new.
- **B3 (wall):** the open hard content (hidden-Johnson Piece C). Proving
  the failure is a research result, not a checklist item — but the build
  does not need it: flagging is sound, and B1+B2 already tell the build
  what to do.

**Bottom line for the decision.** The honest expected outcome is **not**
"the extended direct construction is universally valid" and **not** "it
is universally invalid" — it is a **characterization**: direct matching
is valid only for all-singletons; the genuine extension is *recursive*
and is viable exactly on the cascade class (certified by the
orbit-recovery theorems), failing at the rigid and non-abelian-wall
residuals. That both **lets us use the recursive extension freely within
the cascade class** and **pins the precise configurations where it must
flag**.

---

## 7. Cross-references

- [`chain-descent-linear-oracle.md`](./chain-descent-linear-oracle.md)
  §4.2 (construction), §4.3 (boundary, conjectural), §4.4 (recursion
  option), §8.2 (Phase-1 Lean target).
- [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md)
  — `theorem_1_HOR` (CFI cascade depth ≤ tw(H)), the orbit ⊆ cell
  framing; B2 inherits these.
- [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)
  — Piece C (the cascade half) is the same obligation as B3.
- [`chain-descent-strategy.md`](./chain-descent-strategy.md) §15 gap 2
  (flag iso-invariance — the requirement B1 is about), gap 5 (IR blind
  spots — the rigid sub-case).
- `ChainDescent.lean` — `warm_6_2`, `warmRefine_agree_off'`,
  `samePartition_chain`, `flipPair*`, `LeafTwistSpec`, `OrbitPartition`,
  `theorem_1_HOR_at_depth`, `aut_trivial_of_discrete_warmRefine`;
  `ChainDescent/CFI.lean` `theorem_1_HOR_cfi_oddDeg`;
  `ChainDescent/Scheme.lean` `theorem_2_HOR_concrete_rank_two_J_singleton`.
