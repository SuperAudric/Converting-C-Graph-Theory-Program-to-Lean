import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Function.Iterate

/-!
# Direction invariance of warm 1-WL refinement (algorithm §6.2)

This file states and partially proves the load-bearing direction-symmetry
invariant for the flip-validation canonizer
(see `docs/flip-validation-strategy.md` §6.2).

## Informal claim

Let `P₀` be a partial-order matrix and `χ₀` a 1-WL-stable colouring of
`(adj, P₀)`. For any "guess" pair `(a, b)` with `P₀ a b = unknown`,
running warm refinement after applying `(a, b, less)` + TC produces the
same partition as warm refinement after applying `(a, b, greater)` + TC,
starting from `χ₀`.

## Key insight

Warm refinement is **split-only**: it can only further partition the cells
of its starting colouring, never merge them. Combined with cell-coherence
of `χ₀` (all members of a cell have identical out-relations to every
other cell), the splits induced by the new guess + TC are uniform within
each cell of `χ₀` — every member of a cell sees the same structural
change regardless of guess direction.

This sidesteps the freshly-1-WL counterexample in which between-cell
guesses can produce different partitions under `<` vs `>` via asymmetric
TC chains: warm refinement starting from the pre-guess partition cannot
merge cells, so the post-guess freshly-1-WL coarsening simply doesn't
materialise.

## Proof status

- Definitions are concrete (one `axiom` to abstract over the colour-
  encoding question; see `refineStep_iff`).
- Trivial structural lemmas are proven.
- `transitiveClose_swap`, `warmRefine_refines`, `cell_split_uniform`,
  and `warm_6_2` are `sorry` with prose sketches above each. These are
  the next-iteration work items.
-/

namespace FlipValidation

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

/--
**Lemma (transitive closure commutes with σ-swap).**

```
transitiveClose (swap P) = swap (transitiveClose P)
```

Proof sketch: induction on iteration count. The base case (zero iterations)
is `swap (swap P) = P`. The inductive step needs `closeStep ∘ swap =
swap ∘ closeStep`, which follows from the symmetry of the chain rule
under `less ↔ greater`: the rule "`P i k = less ∧ P k j = less ⇒ P i j =
less`" swaps with "`P i k = greater ∧ P k j = greater ⇒ P i j = greater`"
under the σ-relabel, and `List.any` over the universal index set respects
this swap.
-/
theorem transitiveClose_swap {n : Nat} (P : PMatrix n) :
    transitiveClose (PMatrix.swap P) = PMatrix.swap (transitiveClose P) := by
  sorry

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
  sorry

/--
**Lemma (cell-uniform signature change under guess + TC).**

If `v` and `w` are in the same cell of `χ₀` (a 1-WL-stable colouring of
`(adj, P₀)`) and neither `v` nor `w` is the guessed pair `(a, b)`, then
their post-guess signatures coincide regardless of guess direction.

Proof sketch:
1. By stability of `χ₀` and `refineStep_iff`, members of a cell of
   `χ₀` have equal signatures under `(adj, P₀, χ₀)`. So `signature adj
   P₀ χ₀ v = signature adj P₀ χ₀ w`.
2. The transitive closure under `applyGuess P₀ a b dir` adds entries
   only along chains involving the new `(a, b)` edge. For `v` and `w`
   in the same `χ₀`-cell, cell-coherence gives that their out-relations
   to every other `χ₀`-cell are identical. Hence the set of TC chains
   from `v` matches the set from `w` cell-by-cell, and the new entries
   added to `v`'s row equal (as a multiset of `(cell, A, P)` triples)
   the new entries added to `w`'s row.
3. The post-TC signatures of `v` and `w` therefore remain equal, for
   each of the two directions independently.

The key observation is that this argument is symmetric in `less` vs
`greater` — the cell-coherence and chain-matching are direction-agnostic,
so both conjuncts of the conclusion hold by the same reasoning.
-/
theorem cell_split_uniform {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χ₀ : Colouring n)
    (h_stable : samePartition χ₀ (refineStep adj P₀ χ₀))
    (a b : Fin n) (hab : a ≠ b) (h_unknown : P₀ a b = .unknown)
    (v w : Fin n) (h_same_cell : χ₀ v = χ₀ w)
    (h_neither : v ≠ a ∧ v ≠ b ∧ w ≠ a ∧ w ≠ b) :
    signature adj (transitiveClose (applyGuess P₀ a b .less))    χ₀ v
      = signature adj (transitiveClose (applyGuess P₀ a b .less))    χ₀ w
    ∧
    signature adj (transitiveClose (applyGuess P₀ a b .greater)) χ₀ v
      = signature adj (transitiveClose (applyGuess P₀ a b .greater)) χ₀ w := by
  sorry

/-! ## Main theorem -/

/--
**Direction invariance of warm refinement (algorithm §6.2).**

For any pre-guess matrix `P₀` with stable colouring `χ₀`, and any
guessable pair `(a, b)`, warm refinement under
`TC (applyGuess P₀ a b less)` and `TC (applyGuess P₀ a b greater)`,
starting from `χ₀`, induce the same partition.

Proof sketch (combines the lemmas above):

For any `v, w : Fin n` we show the two-sided implication
`warmRefine ... .less v = warmRefine ... .less w ↔
 warmRefine ... .greater v = warmRefine ... .greater w`.

- If `v, w` are not in the same `χ₀`-cell (i.e., `χ₀ v ≠ χ₀ w`), then
  by `warmRefine_refines` they cannot be in the same cell of either
  warm-refined colouring. Both sides of the iff are False.
- If `v, w` are in the same `χ₀`-cell and neither is `a` nor `b`,
  `cell_split_uniform` gives equal signatures under both directions.
  Iterating `refineStep_iff`, the warm-refined colours of `v` and `w`
  remain equal in both directions; both sides of the iff are True.
- If one of `v, w` is `a` (or `b`), individualisation in the first
  round splits that vertex into its own singleton sub-cell in both
  directions — the splits are direction-symmetric because the only
  thing that differs between the two `refineStep` runs at that vertex
  is the `(b, less)` vs `(b, greater)` entry in its signature, which
  doesn't affect equality with any non-`a, b` vertex (their signatures
  don't contain such an entry on their side).
-/
theorem warm_6_2 {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χ₀ : Colouring n)
    (h_stable : samePartition χ₀ (refineStep adj P₀ χ₀))
    (a b : Fin n) (hab : a ≠ b) (h_unknown : P₀ a b = .unknown) :
    samePartition
      (warmRefine adj (transitiveClose (applyGuess P₀ a b .less))    χ₀)
      (warmRefine adj (transitiveClose (applyGuess P₀ a b .greater)) χ₀) := by
  sorry

end FlipValidation
