import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Function.Iterate

/-!
# Direction invariance of warm 1-WL refinement (chain descent §6.2)

This file states, and partially proves, the load-bearing direction-symmetry
invariant ("invariant 6.2") for the **chain-descent** canonizer — see
`docs/chain-descent-strategy.md` §6.2 and `docs/chain-descent-overview.md`
§7.2. ("Flip validation" was the earlier name of the chain-descent design;
the file has been renamed accordingly.)

## Informal claim

Let `P₀` be a partial-order matrix and `χ₀` a 1-WL-stable colouring of
`(adj, P₀)`. For any "guess" pair `(a, b)` with `P₀ a b = unknown`,
running warm refinement after applying `(a, b, less)` + TC produces the
same partition as warm refinement after applying `(a, b, greater)` + TC,
starting from `χ₀`.

## Key insight (and where the original sketch broke)

Warm refinement is **split-only**: it can only further partition the cells
of its starting colouring, never merge them (`warmRefine_refines`). That
much holds.

The original sketch went further: it claimed the guess + TC leaves
cell-mates with *equal signatures*, so a cell does not split at all. That
is **false** — a guess applied to an individual vertex genuinely splits a
cell (`cell_split_uniform_false`). The honest, weaker claim is that a cell
*does* split, but **into the same sub-cells under either guess direction**;
only the order labels differ. Proving that direction-symmetric-split
statement is the genuine open content of §6.2.

## Proof status

- Definitions are concrete (one `axiom`, `refineStep`/`refineStep_iff`, to
  abstract over the colour-encoding question).
- `warmRefine_refines` — **proved** (`Nat.iterate` induction).
- `transitiveClose_swap` — the unconditionally-stated lemma is **FALSE**;
  `closeStep`'s `less`-first tie-break is not σ-symmetric. Replaced by the
  machine-checked refutations `closeStep_swap_false` / `transitiveClose_swap_false`
  (witness: `conflictMatrix`). A consistency-restricted version is future work.
- `cell_split_uniform` — the lemma as stated is **FALSE**; refuted by the
  machine-checked `cell_split_uniform_false` (witness: `witnessP0`). A
  singleton-`(a,b)`-restricted version is future work.
- `warm_6_2` — still `sorry`. Believed true, but its original proof route
  (via `cell_split_uniform`) is invalid; see the note on the theorem.
-/

namespace ChainDescent

/-! ## Partial-order entries -/

inductive POE
  | less
  | unknown
  | greater
deriving DecidableEq, Repr

namespace POE

/-- Antisymmetric reverse on one entry: `P(i, j) = neg (P(j, i))`. -/
def neg : POE → POE
  | .less    => .greater
  | .unknown => .unknown
  | .greater => .less

@[simp] theorem neg_neg (e : POE) : neg (neg e) = e := by
  cases e <;> rfl

/-- σ-swap: the matrix-wide relabelling used in the direction-symmetry
argument. Coincides with `neg` on a single entry, but spelled separately
to keep the semantic distinction clear (antisymmetry vs. relabelling). -/
def swap : POE → POE := neg

@[simp] theorem swap_swap (e : POE) : swap (swap e) = e := neg_neg e

@[simp] theorem swap_less    : swap .less    = .greater := rfl
@[simp] theorem swap_greater : swap .greater = .less    := rfl
@[simp] theorem swap_unknown : swap .unknown = .unknown := rfl

end POE

/-! ## P-matrix definitions -/

/-- The partial-order matrix: `(Fin n) × (Fin n) → POE`. -/
def PMatrix (n : Nat) := Fin n → Fin n → POE

namespace PMatrix

variable {n : Nat}

/-- Apply σ-swap pointwise: swap every `less` with `greater` throughout. -/
def swap (P : PMatrix n) : PMatrix n := fun i j => POE.swap (P i j)

@[simp] theorem swap_swap (P : PMatrix n) : swap (swap P) = P := by
  funext i j; exact POE.swap_swap _

/-- Antisymmetric matrix: `P i j = neg (P j i)`. -/
def Antisymmetric (P : PMatrix n) : Prop :=
  ∀ i j : Fin n, P i j = POE.neg (P j i)

end PMatrix

/-! ## Adjacency

A minimal locally-defined adjacency matrix to keep this file self-
contained (independent of `Graph.AdjMatrix` from `LeanGraphCanonizerV4`). -/

structure AdjMatrix (n : Nat) where
  adj : Fin n → Fin n → Nat

/-! ## Guess application -/

/-- Apply a single guess `(a, b, dir)`: set `P(a, b) := dir` and
`P(b, a) := neg dir`, leaving everything else unchanged. Does not
transitively close. -/
def applyGuess {n : Nat} (P : PMatrix n) (a b : Fin n) (dir : POE) : PMatrix n :=
  fun i j =>
    if i = a ∧ j = b then dir
    else if i = b ∧ j = a then POE.neg dir
    else P i j

/-- Applying `(a, b, swap dir)` to the σ-swapped matrix equals swapping
after applying `(a, b, dir)` to the original. The key structural fact
linking the two guess directions through σ. Requires `a ≠ b` so the two
guess-position branches don't collide on the diagonal. -/
theorem applyGuess_swap {n : Nat} (P : PMatrix n) (a b : Fin n) (hab : a ≠ b)
    (dir : POE) :
    PMatrix.swap (applyGuess P a b dir) =
      applyGuess (PMatrix.swap P) a b (POE.swap dir) := by
  funext i j
  unfold applyGuess PMatrix.swap
  by_cases h1 : i = a ∧ j = b
  · -- (i, j) = (a, b). The (b, a) inner branch would require a = b.
    have h2_neg : ¬ (i = b ∧ j = a) := fun ⟨hib, _⟩ =>
      hab (h1.1.symm.trans hib)
    simp only [if_pos h1, if_neg h2_neg]
  · by_cases h2 : i = b ∧ j = a
    · -- (i, j) = (b, a). Reduce the ifs, then case on `dir` so the
      -- swap/neg compositions compute concretely.
      simp only [if_neg h1, if_pos h2]
      cases dir <;> rfl
    · -- (i, j) hits neither branch; both sides reduce to swap (P i j).
      simp only [if_neg h1, if_neg h2]

/-! ## Transitive closure -/

/-- Single-step closure: derive `(i, j)` from a chain `i → k → j` of one
direction. Uses `List.finRange` for decidable enumeration. -/
def closeStep {n : Nat} (P : PMatrix n) : PMatrix n := fun i j =>
  match P i j with
  | .less    => .less
  | .greater => .greater
  | .unknown =>
      if (List.finRange n).any
            (fun k => decide (P i k = .less) && decide (P k j = .less))
      then .less
      else if (List.finRange n).any
            (fun k => decide (P i k = .greater) && decide (P k j = .greater))
      then .greater
      else .unknown

/-- Transitive closure: iterate `closeStep` `n * n` times. Each round can
introduce at most one new entry per `(i, j)` pair, so `n²` rounds suffice
to reach fixpoint. -/
def transitiveClose {n : Nat} (P : PMatrix n) : PMatrix n :=
  (closeStep^[n * n]) P

/-!
### The σ-swap commutation lemma is FALSE as originally stated

The original file asserted, unconditionally,

```
transitiveClose (swap P) = swap (transitiveClose P)
```

with a proof sketch appealing to "symmetry of the chain rule under
`less ↔ greater`". That sketch is wrong. `closeStep` resolves a pair that
has *both* a `less`-chain and a `greater`-chain running through it by the
**first `if`** — it unconditionally picks `less`. That tie-break is not
σ-symmetric: on the σ-swapped matrix the (now-swapped) chains hit the same
first `if` and `less` is picked *again*, where σ-symmetry would demand
`greater`. So the two sides disagree on any matrix with a conflicted pair.

`conflictMatrix` below is a concrete 4-vertex witness; `closeStep_swap_false`
and `transitiveClose_swap_false` are machine-checked refutations.

A *correct* version needs a consistency hypothesis — no pair may carry
both a `less`-chain and a `greater`-chain (automatic for any `P` that
extends to a genuine partial order). Stating and proving that conditional
lemma is left as follow-up; it is **not** on the critical path for
`warm_6_2`, whose proof route is a direct within-cell argument, not the
σ-relabel argument (which swapping the guess direction would break anyway,
since it swaps the whole pre-guess matrix).
-/

/-- A concrete 4-vertex `PMatrix` with a conflicted pair: entry `(0,1)` is
`unknown`, yet it carries a `less`-chain `0 → 2 → 1` and a `greater`-chain
`0 → 3 → 1` simultaneously. -/
def conflictMatrix : PMatrix 4 := fun i j =>
  match i.val, j.val with
  | 0, 2 => .less
  | 2, 0 => .greater
  | 2, 1 => .less
  | 1, 2 => .greater
  | 0, 3 => .greater
  | 3, 0 => .less
  | 3, 1 => .greater
  | 1, 3 => .less
  | _, _ => .unknown

/-- `closeStep` never demotes a decided `less` entry. -/
theorem closeStep_keeps_less {n : Nat} (Q : PMatrix n) {i j : Fin n}
    (h : Q i j = .less) : closeStep Q i j = .less := by
  simp only [closeStep, h]

/-- Iterating `closeStep` preserves a `less` entry — once decided, frozen. -/
theorem iterate_closeStep_keeps_less {n : Nat} (i j : Fin n) :
    ∀ (k : Nat) (Q : PMatrix n), Q i j = .less →
      ((closeStep^[k]) Q) i j = .less := by
  intro k
  induction k with
  | zero => intro Q h; exact h
  | succ k ih =>
    intro Q h
    rw [Function.iterate_succ, Function.comp_apply]
    exact ih (closeStep Q) (closeStep_keeps_less Q h)

/-- Single-step σ-swap commutation already fails on `conflictMatrix`:
`closeStep` decides `(0,1)` as `less` for both the matrix and its σ-swap,
where σ-symmetry would force the swapped run to pick `greater`. -/
theorem closeStep_swap_false :
    ¬ ∀ (m : Nat) (P : PMatrix m),
        closeStep (PMatrix.swap P) = PMatrix.swap (closeStep P) := by
  intro h
  have hbad := congrFun (congrFun (h 4 conflictMatrix) 0) 1
  revert hbad
  decide

/-- `transitiveClose conflictMatrix` decides the conflicted pair `(0,1)`
as `less` (the `less`-chain wins the first `if`). -/
theorem transitiveClose_conflict_less :
    transitiveClose conflictMatrix 0 1 = .less := by
  have h1 : closeStep conflictMatrix 0 1 = POE.less := by decide
  show (closeStep^[4 * 4]) conflictMatrix 0 1 = .less
  rw [show 4 * 4 = 15 + 1 from rfl, Function.iterate_succ, Function.comp_apply]
  exact iterate_closeStep_keeps_less 0 1 15 (closeStep conflictMatrix) h1

/-- `transitiveClose (swap conflictMatrix)` *also* decides `(0,1)` as
`less` — the σ-swap did not flip the tie-break. -/
theorem transitiveClose_swap_conflict_less :
    transitiveClose (PMatrix.swap conflictMatrix) 0 1 = .less := by
  have h1 : closeStep (PMatrix.swap conflictMatrix) 0 1 = POE.less := by decide
  show (closeStep^[4 * 4]) (PMatrix.swap conflictMatrix) 0 1 = .less
  rw [show 4 * 4 = 15 + 1 from rfl, Function.iterate_succ, Function.comp_apply]
  exact iterate_closeStep_keeps_less 0 1 15
    (closeStep (PMatrix.swap conflictMatrix)) h1

/--
**Refutation: `transitiveClose` does NOT commute with σ-swap.**

`transitiveClose (swap conflictMatrix) (0,1) = less`, whereas
`swap (transitiveClose conflictMatrix) (0,1) = swap less = greater`. The
unconditional commutation lemma is therefore false.
-/
theorem transitiveClose_swap_false :
    ¬ ∀ (m : Nat) (P : PMatrix m),
        transitiveClose (PMatrix.swap P) = PMatrix.swap (transitiveClose P) := by
  intro h
  have hbad := congrFun (congrFun (h 4 conflictMatrix) 0) 1
  rw [transitiveClose_swap_conflict_less] at hbad
  simp only [PMatrix.swap, transitiveClose_conflict_less, POE.swap_less] at hbad
  exact absurd hbad (by decide)

/-! ## Colourings, signatures, and 1-WL refinement -/

/-- A colouring assigns each vertex a natural-number colour. -/
def Colouring (n : Nat) := Fin n → Nat

/-- The signature of vertex `v` under colouring `χ` and graph `(adj, P)`:
the multiset of `(neighbour-colour, adjacency-value, P-relation)` tuples
over all `u ≠ v`. -/
def signature {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (χ : Colouring n) (v : Fin n) : Multiset (Nat × Nat × POE) :=
  ((Finset.univ : Finset (Fin n)).filter (· ≠ v)).val.map fun u =>
    (χ u, adj.adj v u, P v u)

/-- One round of 1-WL refinement: assign each vertex a new colour
encoding `(old colour, signature)`.

We abstract over the encoding via the axiom `refineStep_iff` below.
Concretely the canonical implementation would pair `(χ v, sortedSig v)`
and inject into `Nat` via a fixed `(Nat × Multiset _) ↪ Nat`; we don't
fix one because the partition-level reasoning that downstream proofs use
doesn't depend on the encoding. -/
axiom refineStep {n : Nat} : AdjMatrix n → PMatrix n → Colouring n → Colouring n

/-- Partition-level characterisation of `refineStep`: two vertices get
the same refined colour iff they had the same old colour AND the same
signature. -/
axiom refineStep_iff {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (χ : Colouring n) (v w : Fin n) :
    refineStep adj P χ v = refineStep adj P χ w ↔
      χ v = χ w ∧ signature adj P χ v = signature adj P χ w

/-- Warm refinement: iterate `refineStep` `n` times starting from
`initial`. `n` iterations always suffice because each round either
strictly refines the partition (one fewer cell-mate pair stays equivalent)
or reaches fixpoint, and there are at most `n` non-trivial rounds.

Marked `noncomputable` because `refineStep` is axiomatised (only its
partition behaviour, via `refineStep_iff`, is specified). -/
noncomputable def warmRefine {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (initial : Colouring n) : Colouring n :=
  ((refineStep adj P)^[n]) initial

/-! ## Partition equivalence -/

/-- Two colourings induce the same partition iff their equivalence
classes coincide. -/
def samePartition {n : Nat} (χ₁ χ₂ : Colouring n) : Prop :=
  ∀ i j : Fin n, χ₁ i = χ₁ j ↔ χ₂ i = χ₂ j

namespace samePartition

variable {n : Nat}

theorem refl (χ : Colouring n) : samePartition χ χ := fun _ _ => Iff.rfl

theorem symm {χ₁ χ₂ : Colouring n} (h : samePartition χ₁ χ₂) :
    samePartition χ₂ χ₁ := fun i j => (h i j).symm

theorem trans {χ₁ χ₂ χ₃ : Colouring n}
    (h₁₂ : samePartition χ₁ χ₂) (h₂₃ : samePartition χ₂ χ₃) :
    samePartition χ₁ χ₃ := fun i j => Iff.trans (h₁₂ i j) (h₂₃ i j)

end samePartition

/-! ## Key lemmas -/

/-- **Refinement is split-only (one round).** Equal new colour implies
equal old colour. Immediate from `refineStep_iff`. -/
theorem refineStep_refines {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (χ : Colouring n) {v w : Fin n}
    (h : refineStep adj P χ v = refineStep adj P χ w) : χ v = χ w :=
  ((refineStep_iff adj P χ v w).mp h).1

/--
**Lemma (warm refinement is split-only).**

```
warmRefine adj P initial v = warmRefine adj P initial w → initial v = initial w
```

Proof sketch: induction on the iteration count in `Nat.iterate`. The base
case (zero iterations) is `initial v = initial w → initial v = initial w`.
The inductive step uses `refineStep_refines` to peel off one round.
-/
theorem warmRefine_refines {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (initial : Colouring n) {v w : Fin n}
    (h : warmRefine adj P initial v = warmRefine adj P initial w) :
    initial v = initial w := by
  -- Generalised over the iteration count and the starting colouring so the
  -- induction hypothesis can peel a round off the *front*.
  have key : ∀ k (χ : Colouring n),
      ((refineStep adj P)^[k]) χ v = ((refineStep adj P)^[k]) χ w → χ v = χ w := by
    intro k
    induction k with
    | zero => intro χ hk; exact hk
    | succ k ih =>
      intro χ hk
      rw [Function.iterate_succ, Function.comp_apply] at hk
      exact refineStep_refines adj P χ (ih (refineStep adj P χ) hk)
  exact key n initial h

/-!
### The cell-uniform signature lemma is FALSE as originally stated

The original `cell_split_uniform` claimed: if `v` and `w` lie in the same
`χ₀`-cell and neither is `a` nor `b`, their post-guess + TC signatures
*coincide*. Its proof sketch argued that cell-coherence forces "the set of
TC chains from `v`" to match "the set from `w` cell-by-cell".

That argument has a real gap. Cell-coherence is a **multiset** property:
cell-mates relate identically to every *cell*. But a guess `(a, b)` is
applied to two *individual vertices*, and TC chains run through individual
vertices. Two cell-mates `v, w` can relate symmetrically to the *cell*
containing `a` while relating asymmetrically to `a` *itself* — so the
`a → b` edge propagates to one of them and not the other.

`witnessP0` below is a concrete 5-vertex witness. Cells are `{0,1}`,
`{2,3}`, `{4}`; `χ₀` is 1-WL-stable; `0 < 2` and `1 < 3` hold. Guessing
`(a, b) = (2, 4)` gives `0 < 2 < 4` so TC adds `0 < 4`, but `1` has no
chain to `4` — so `0` gains a `less` to `4` that `1` does not, and the
signatures of the cell-mates `0` and `1` *differ*. `cell_split_uniform_false`
is the machine-checked refutation.

A *correct* version needs `a` and `b` to be **singleton `χ₀`-cells** (so
"relates to `a`'s cell" coincides with "relates to `a`"). That holds for
the individualised vertex in chain descent, but not for the unindividualised
partner in a `k ≥ 2` target cell — which is exactly the regime §7's linear
oracle must handle. Stating and proving the singleton-restricted lemma is
left as follow-up.
-/

/-- Iterating `closeStep` from one of its fixpoints stays at that fixpoint. -/
theorem iterate_closeStep_fix {n : Nat} (M : PMatrix n)
    (hM : closeStep M = M) : ∀ k, (closeStep^[k]) M = M := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ', Function.comp_apply, ih]; exact hM

/-- Witness adjacency: the empty graph on 5 vertices (adjacency plays no
role in the refutation; the discrepancy is entirely in `P`). -/
private def witnessAdj : AdjMatrix 5 := ⟨fun _ _ => 0⟩

/-- Witness pre-guess matrix: `0 < 2` and `1 < 3`. With cells `{0,1}`,
`{2,3}`, `{4}` the cell-mates `0, 1` relate symmetrically to the *cell*
`{2,3}` but asymmetrically to the *vertices* `2` and `3`. -/
private def witnessP0 : PMatrix 5 := fun i j =>
  match i.val, j.val with
  | 0, 2 => .less
  | 2, 0 => .greater
  | 1, 3 => .less
  | 3, 1 => .greater
  | _, _ => .unknown

/-- Witness colouring: cells `{0,1}`, `{2,3}`, `{4}`. -/
private def witnessChi : Colouring 5 := fun i =>
  match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | _ => 2

/-- The explicit `closeStep`-fixpoint of `applyGuess witnessP0 2 4 less`:
`witnessP0` plus the guess `2 < 4` plus the one closure entry `0 < 4`. -/
private def witnessTC : PMatrix 5 := fun i j =>
  match i.val, j.val with
  | 0, 2 => .less
  | 2, 0 => .greater
  | 1, 3 => .less
  | 3, 1 => .greater
  | 2, 4 => .less
  | 4, 2 => .greater
  | 0, 4 => .less
  | 4, 0 => .greater
  | _, _ => .unknown

/-- `transitiveClose (applyGuess witnessP0 2 4 less) = witnessTC`, proved
without unfolding the 25-fold iterate: one `closeStep` already reaches the
fixpoint `witnessTC`, and `iterate_closeStep_fix` carries it the rest. -/
private theorem witnessTC_eq :
    transitiveClose (applyGuess witnessP0 2 4 .less) = witnessTC := by
  have hstep : closeStep (applyGuess witnessP0 2 4 .less) = witnessTC := by
    funext i j; revert i j; decide
  have hfix : closeStep witnessTC = witnessTC := by
    funext i j; revert i j; decide
  show (closeStep^[5 * 5]) (applyGuess witnessP0 2 4 .less) = witnessTC
  rw [show 5 * 5 = 24 + 1 from rfl, Function.iterate_succ, Function.comp_apply,
    hstep]
  exact iterate_closeStep_fix witnessTC hfix 24

/-- `witnessChi` is 1-WL-stable for `(witnessAdj, witnessP0)`: cell-mates
have equal signatures, which via `refineStep_iff` is exactly stability. -/
private theorem witnessChi_stable :
    samePartition witnessChi (refineStep witnessAdj witnessP0 witnessChi) := by
  have hsig : ∀ i j : Fin 5, witnessChi i = witnessChi j →
      signature witnessAdj witnessP0 witnessChi i
        = signature witnessAdj witnessP0 witnessChi j := by decide
  intro i j
  rw [refineStep_iff]
  exact ⟨fun hij => ⟨hij, hsig i j hij⟩, fun h => h.1⟩

/--
**Refutation: cell-mates do NOT keep equal signatures after a guess + TC.**

For the witness above, `0` and `1` are `χ₀`-cell-mates, `(2, 4)` is a
guessable pair, and `0, 1 ∉ {2, 4}` — every hypothesis of the original
`cell_split_uniform` holds — yet under `transitiveClose (applyGuess
witnessP0 2 4 less)` vertex `0` carries a `less` to `4` that vertex `1`
lacks, so the two signatures differ. The `less` conjunct of the claimed
conclusion is false, hence the lemma is false.
-/
theorem cell_split_uniform_false :
    ¬ ∀ {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n) (χ₀ : Colouring n),
        samePartition χ₀ (refineStep adj P₀ χ₀) →
        ∀ (a b : Fin n), a ≠ b → P₀ a b = .unknown →
        ∀ (v w : Fin n), χ₀ v = χ₀ w →
          (v ≠ a ∧ v ≠ b ∧ w ≠ a ∧ w ≠ b) →
            signature adj (transitiveClose (applyGuess P₀ a b .less)) χ₀ v
              = signature adj (transitiveClose (applyGuess P₀ a b .less)) χ₀ w
            ∧
            signature adj (transitiveClose (applyGuess P₀ a b .greater)) χ₀ v
              = signature adj (transitiveClose (applyGuess P₀ a b .greater)) χ₀ w := by
  intro h
  have hconj := h witnessAdj witnessP0 witnessChi witnessChi_stable
    2 4 (by decide) (by decide) 0 1 (by decide) (by decide)
  rw [witnessTC_eq] at hconj
  exact absurd hconj.1 (by decide)

/-! ## Main theorem -/

/--
**Direction invariance of warm refinement (algorithm §6.2).** — OPEN (`sorry`).

For any pre-guess matrix `P₀` with stable colouring `χ₀`, and any
guessable pair `(a, b)`, warm refinement under
`TC (applyGuess P₀ a b less)` and `TC (applyGuess P₀ a b greater)`,
starting from `χ₀`, induce the same *partition*.

**The theorem is still believed true** — it is the partition-level
("weak") form of invariant 6.2, empirically checked on `C4`, `K3`, and
the 6-vertex asymmetric graph (see `docs/chain-descent-strategy.md` §6.2).
What changed is the **proof route**.

The original sketch reduced it to `cell_split_uniform`: cell-mates `v, w`
(neither `a` nor `b`) keep *equal signatures* after the guess, so cells
do not split at all. `cell_split_uniform_false` above shows that is wrong
— a guess on an individual vertex *does* split a cell. The honest picture
is weaker and is what must now be proved:

> after the guess, a `χ₀`-cell may split, **but it splits into the same
> sub-cells regardless of guess direction** — only the order labels on
> the split differ.

So the surviving ingredient is `warmRefine_refines` (warm refinement only
splits `χ₀`, never merges it — handles the `χ₀ v ≠ χ₀ w` case), and the
missing ingredient is a *direction-symmetric split* lemma replacing the
(false) *no-split* lemma `cell_split_uniform`. That lemma is the real
content of §6.2 and the genuine open obligation; note the σ-relabel route
is also unavailable, since `transitiveClose_swap` is false (see above) and
in any case swapping the guess direction swaps the whole pre-guess matrix.
-/
theorem warm_6_2 {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χ₀ : Colouring n)
    (h_stable : samePartition χ₀ (refineStep adj P₀ χ₀))
    (a b : Fin n) (hab : a ≠ b) (h_unknown : P₀ a b = .unknown) :
    samePartition
      (warmRefine adj (transitiveClose (applyGuess P₀ a b .less))    χ₀)
      (warmRefine adj (transitiveClose (applyGuess P₀ a b .greater)) χ₀) := by
  sorry

end ChainDescent
