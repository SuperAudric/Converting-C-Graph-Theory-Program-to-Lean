import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Order.PiLex
import Mathlib.Logic.Function.Iterate

/-!
# Direction invariance of warm 1-WL refinement (chain descent §6.2)

This file states and proves the load-bearing direction-symmetry invariant
("invariant 6.2") for the **chain-descent** canonizer.

**Companion: [`ChainDescent.md`](./ChainDescent.md)** — the self-contained
proving guide: the C# implementation modelled, the Lean ↔ C# correspondence,
the TC-relegation equivalence, the modelling axiom, the proof state, the
hardness map, the gaps and the future work. Read that plus this file; the
`docs/` design files are not needed.

## Informal claim

For a guessed pair `(a, b)` and a starting colouring `χι` in which `a` and
`b` are singletons, warm refinement after the guess `a < b` and after the
guess `b < a` induce the **same partition** — the two runs differ only in
the order labels on the splits. This is `warm_6_2`, proved below.

## Model (settled in design discussion)

- **Transitive closure is relegated.** A guess writes a single `P` entry;
  consistency is a lex-min ranking criterion, not a propagation step. So the
  post-guess matrix is `applyGuess P₀ a b dir` — `transitiveClose` does not
  sit in the refinement loop, and `P⁻`/`P⁺` differ only at `(a,b)`/`(b,a)`.
- **Individualisation assigns a fresh colour**, making the guessed vertices
  singletons by construction — the property the canonizer's oracle relies
  on, rather than left to a refinement hand-wave (see `ChainDescent.md` §5).

The earlier route (`cell_split_uniform`: cell-mates keep *equal signatures*,
no split) is false — `cell_split_uniform_false` refutes it. The route that
works: a guess *does* split a cell, but **into the same sub-cells under
either direction**, because off `{a,b}` the refinement signature cannot even
see the guess.

## Proof status

- Definitions are concrete (one `axiom`, `refineStep`/`refineStep_iff`, to
  abstract over the colour-encoding question).
- `warmRefine_refines` — **proved** (`Nat.iterate` induction).
- `warm_6_2` — **proved**. The four supporting lemmas
  (`refineStep_preserves_singleton`, `iterate_refineStep_preserves_singleton`,
  `signature_applyGuess_off`, `signature_eq_of_samePartition`) are proved;
  `warm_6_2` itself is an induction on the refinement round.
- `transitiveClose_swap` — the unconditionally-stated lemma is **FALSE**;
  `closeStep`'s `less`-first tie-break is not σ-symmetric. Machine-checked
  refutations `closeStep_swap_false` / `transitiveClose_swap_false` (witness:
  `conflictMatrix`). Moot under TC relegation — kept as a record, since the
  σ-relabel route to 6.2 is not the one taken.
- `cell_split_uniform` — the lemma as stated is **FALSE**; refuted by the
  machine-checked `cell_split_uniform_false` (witness: `witnessP0`).
-/

namespace ChainDescent

/-! ## Partial-order entries -/

inductive POE
  | less
  | unknown
  | greater
deriving DecidableEq, Repr

namespace POE

/-- Manual `Fintype` instance for `POE` (only three values). Needed
downstream for `Fintype (PMatrix n)` → `Fintype (DirAssignment P₀ D)`. -/
instance : Fintype POE :=
  ⟨{POE.less, POE.unknown, POE.greater}, fun x => by cases x <;> decide⟩

end POE

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
contained (independent of `Graph.AdjMatrix` from the archived `LeanGraphCanonizerV4` lean module). -/

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
partner in a `k ≥ 2` target cell — which is exactly the regime the linear
oracle must handle (`ChainDescent.md` §10). Stating and proving the
singleton-restricted lemma is left as follow-up.
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

/-! ## §6.2 — direction invariance of warm refinement

The model here is the one settled in design discussion:

* **Transitive closure is relegated.** A guess writes a single `P` entry and
  nothing else (consistency becomes a lex-min ranking criterion, not a
  propagation step). So the post-guess matrix is `applyGuess P₀ a b dir`,
  which differs from `P₀` at *only* the `(a,b)` / `(b,a)` entries — and
  `closeStep` / `transitiveClose` are absent from the refinement loop.
* **Individualisation assigns a fresh colour.** Warm refinement starts from a
  colouring `χι` in which the guessed vertices `a` and `b` are *singletons*
  (their own cells). This is the "`A`, `B` are always singletons" property
  the canonizer's oracle relies on (`ChainDescent.md` §5); modelling it
  directly makes it true by construction rather than by a refinement hand-wave.

Under this model 6.2 is provable: `P⁻` and `P⁺` differ only inside `{a,b}`,
so the only vertices whose refinement signature can depend on the guess
direction are `a` and `b` — and those are quarantined as singletons.
-/

/-- One refinement round preserves a singleton: if no vertex shares `a`'s
colour, none shares it after `refineStep` either — refinement only splits. -/
theorem refineStep_preserves_singleton {n : Nat} (adj : AdjMatrix n)
    (P : PMatrix n) (χ : Colouring n) (a : Fin n)
    (hsing : ∀ u, u ≠ a → χ u ≠ χ a) :
    ∀ u, u ≠ a → refineStep adj P χ u ≠ refineStep adj P χ a := by
  intro u hu h
  exact hsing u hu (refineStep_refines adj P χ h)

/-- Iterating refinement preserves a singleton, for any number of rounds. -/
theorem iterate_refineStep_preserves_singleton {n : Nat} (adj : AdjMatrix n)
    (P : PMatrix n) (a : Fin n) :
    ∀ (k : Nat) (χ : Colouring n), (∀ u, u ≠ a → χ u ≠ χ a) →
      ∀ u, u ≠ a →
        ((refineStep adj P)^[k]) χ u ≠ ((refineStep adj P)^[k]) χ a := by
  intro k
  induction k with
  | zero => intro χ hsing u hu; exact hsing u hu
  | succ k ih =>
    intro χ hsing u hu
    simp only [Function.iterate_succ, Function.comp_apply]
    exact ih (refineStep adj P χ)
      (refineStep_preserves_singleton adj P χ a hsing) u hu

/-- Off the guessed pair, the guess is invisible: for `x ∉ {a,b}` the
signature under `applyGuess P₀ a b dir` equals the signature under `P₀` —
`applyGuess` only touches the `(a,b)` / `(b,a)` entries, none of which sits
in `x`'s row. -/
theorem signature_applyGuess_off {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (a b : Fin n) (d : POE) (χ : Colouring n) (x : Fin n)
    (hxa : x ≠ a) (hxb : x ≠ b) :
    signature adj (applyGuess P₀ a b d) χ x = signature adj P₀ χ x := by
  unfold signature
  apply Multiset.map_congr rfl
  intro u _
  have hP : applyGuess P₀ a b d x u = P₀ x u := by
    unfold applyGuess
    rw [if_neg (fun h => hxa h.1), if_neg (fun h => hxb h.1)]
  rw [hP]

/-- **Signature equality is a partition invariant of the colouring.** If `χ`
and `χ'` induce the same partition, two vertices have equal signatures under
`χ` iff they do under `χ'`: the colour *values* differ, but only by a
relabelling `g`, and `Multiset.map` carries that relabelling through. -/
theorem signature_eq_of_samePartition {n : Nat} (adj : AdjMatrix n)
    (P : PMatrix n) {χ χ' : Colouring n} (h : samePartition χ χ') (i j : Fin n) :
    (signature adj P χ i = signature adj P χ j)
      ↔ (signature adj P χ' i = signature adj P χ' j) := by
  have key : ∀ (μ ν : Colouring n), samePartition μ ν →
      signature adj P μ i = signature adj P μ j →
      signature adj P ν i = signature adj P ν j := by
    intro μ ν hμν hsig
    classical
    obtain ⟨g, hg⟩ : ∃ g : Nat → Nat, ∀ v, ν v = g (μ v) := by
      refine ⟨fun c => if hc : ∃ v, μ v = c then ν hc.choose else c, fun v => ?_⟩
      have hex : ∃ v', μ v' = μ v := ⟨v, rfl⟩
      simp only [dif_pos hex]
      exact ((hμν hex.choose v).mp hex.choose_spec).symm
    have hmap : ∀ v, signature adj P ν v
        = (signature adj P μ v).map (fun t => (g t.1, t.2.1, t.2.2)) := by
      intro v
      unfold signature
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro u _
      simp only [Function.comp_apply, hg]
    rw [hmap i, hmap j, hsig]
  exact ⟨key χ χ' h, key χ' χ h.symm⟩

/--
**Direction invariance of warm refinement (chain descent §6.2).**

For any pre-guess matrix `P₀`, guessed pair `(a, b)`, and starting colouring
`χι` in which `a` and `b` are singletons (the fresh-colour individualisation),
warm refinement after the guess `a < b` and after the guess `b < a` induce
the **same partition**. The two runs differ only in the order labels on the
splits — the partition itself is direction-independent.

This is the partition-level ("weak") form of invariant 6.2 (see
[`ChainDescent.md`](./ChainDescent.md)), empirically checked on `C4`, `K3`,
and the 6-vertex asymmetric graph.

Proof. `applyGuess P₀ a b less` and `applyGuess P₀ a b greater` differ at only
the `(a,b)`/`(b,a)` entries, so for any vertex `x ∉ {a,b}` the refinement
signature is identical under the two directions (`signature_applyGuess_off`).
By induction on the refinement round, the two colourings stay partition-equal:
vertices in `{a,b}` are singletons throughout
(`iterate_refineStep_preserves_singleton`), so they never satisfy a
`samePartition` equality test with a distinct vertex; every other pair is
governed by `refineStep_iff`, the off-pair signature equality, and
`signature_eq_of_samePartition` against the inductive hypothesis.
-/
theorem warm_6_2 {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (a b : Fin n) (χι : Colouring n)
    (ha : ∀ u, u ≠ a → χι u ≠ χι a)
    (hb : ∀ u, u ≠ b → χι u ≠ χι b) :
    samePartition
      (warmRefine adj (applyGuess P₀ a b .less)    χι)
      (warmRefine adj (applyGuess P₀ a b .greater) χι) := by
  suffices key : ∀ k, samePartition
      (((refineStep adj (applyGuess P₀ a b .less)))^[k] χι)
      (((refineStep adj (applyGuess P₀ a b .greater)))^[k] χι) from key n
  intro k
  induction k with
  | zero => exact samePartition.refl χι
  | succ k ih =>
    intro i j
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [refineStep_iff, refineStep_iff]
    set Xl := (refineStep adj (applyGuess P₀ a b .less))^[k] χι
    set Xg := (refineStep adj (applyGuess P₀ a b .greater))^[k] χι
    have saL : ∀ u, u ≠ a → Xl u ≠ Xl a :=
      iterate_refineStep_preserves_singleton adj (applyGuess P₀ a b .less) a k χι ha
    have sbL : ∀ u, u ≠ b → Xl u ≠ Xl b :=
      iterate_refineStep_preserves_singleton adj (applyGuess P₀ a b .less) b k χι hb
    have saG : ∀ u, u ≠ a → Xg u ≠ Xg a :=
      iterate_refineStep_preserves_singleton adj (applyGuess P₀ a b .greater) a k χι ha
    have sbG : ∀ u, u ≠ b → Xg u ≠ Xg b :=
      iterate_refineStep_preserves_singleton adj (applyGuess P₀ a b .greater) b k χι hb
    by_cases hij : i = j
    · subst hij; simp
    · -- a vertex of {a,b} meeting a distinct vertex: colours differ both ways
      have split : ∀ x y : Fin n, x ≠ y → (x = a ∨ x = b) →
          Xl x ≠ Xl y ∧ Xg x ≠ Xg y := by
        intro x y hxy hx
        rcases hx with hx | hx <;> subst hx
        · exact ⟨fun e => saL y (Ne.symm hxy) e.symm,
                 fun e => saG y (Ne.symm hxy) e.symm⟩
        · exact ⟨fun e => sbL y (Ne.symm hxy) e.symm,
                 fun e => sbG y (Ne.symm hxy) e.symm⟩
      by_cases hi : i = a ∨ i = b
      · obtain ⟨hm, hp⟩ := split i j hij hi
        exact ⟨fun e => absurd e.1 hm, fun e => absurd e.1 hp⟩
      · by_cases hj : j = a ∨ j = b
        · obtain ⟨hm, hp⟩ := split j i (Ne.symm hij) hj
          exact ⟨fun e => absurd e.1 (Ne.symm hm),
                 fun e => absurd e.1 (Ne.symm hp)⟩
        · -- i, j ∉ {a,b}: the guess is invisible to both rows
          have hia : i ≠ a := fun e => hi (Or.inl e)
          have hib : i ≠ b := fun e => hi (Or.inr e)
          have hja : j ≠ a := fun e => hj (Or.inl e)
          have hjb : j ≠ b := fun e => hj (Or.inr e)
          rw [signature_applyGuess_off adj P₀ a b .less Xl i hia hib,
              signature_applyGuess_off adj P₀ a b .less Xl j hja hjb,
              signature_applyGuess_off adj P₀ a b .greater Xg i hia hib,
              signature_applyGuess_off adj P₀ a b .greater Xg j hja hjb,
              ih i j, signature_eq_of_samePartition adj P₀ ih i j]

/-! ## §6.2 corollaries — direction-blindness (Q1) and guess commutativity (Q2) -/

/-- σ-swapping `P` relabels each signature's `POE` component by the involution
`POE.swap`; the colour and adjacency components are untouched. -/
theorem signature_swap {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (χ : Colouring n) (v : Fin n) :
    signature adj (PMatrix.swap P) χ v
      = (signature adj P χ v).map (fun t : Nat × Nat × POE => (t.1, t.2.1, POE.swap t.2.2)) := by
  unfold signature
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro u _
  simp [PMatrix.swap, Function.comp]

/--
**Direction-blindness (Q1).** Warm refinement on `P` and on its σ-swap induce
the *same partition*: the `< ↔ >` mirror of a refinement world is
partition-identical to the original.

`transitiveClose_swap` failed to give this — but only because `closeStep`'s
`less`-first tie-break broke σ-symmetry. With TC relegated there is no
`closeStep` in the loop; `signature` under `PMatrix.swap P` is just a
*bijective* relabelling of `signature` under `P` (`signature_swap`), so the
partition is preserved.

Caveat — this is a symmetry that **co-swaps the base matrix**. Applied to a
guess (`warmRefine_applyGuess_swap`) it relates `(P₀, less)` to
`(swap P₀, greater)`, not `(P₀, less)` to `(P₀, greater)`. The two coincide
only when `swap P₀ = P₀` — an all-`unknown` `P₀`, i.e. the descent root —
where it re-proves `warm_6_2`. Deeper, `P₀` carries structure and the
symmetry genuinely co-swaps it; so there is **no** `<`/`>` antisymmetry for a
fixed `P₀` beyond `warm_6_2` itself.
-/
theorem warmRefine_swap {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (χ : Colouring n) :
    samePartition (warmRefine adj P χ) (warmRefine adj (PMatrix.swap P) χ) := by
  have hpoe : Function.Injective POE.swap :=
    Function.Involutive.injective POE.swap_swap
  have hGinj : Function.Injective
      (fun t : Nat × Nat × POE => (t.1, t.2.1, POE.swap t.2.2)) := by
    rintro ⟨c1, e1, p1⟩ ⟨c2, e2, p2⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1, h.2.1, hpoe h.2.2⟩
  suffices key : ∀ k, samePartition ((refineStep adj P)^[k] χ)
      ((refineStep adj (PMatrix.swap P))^[k] χ) from key n
  intro k
  induction k with
  | zero => exact samePartition.refl χ
  | succ k ih =>
    intro i j
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [refineStep_iff, refineStep_iff]
    set X := (refineStep adj P)^[k] χ
    set Y := (refineStep adj (PMatrix.swap P))^[k] χ
    rw [ih i j, signature_swap adj P Y i, signature_swap adj P Y j,
        (Multiset.map_injective hGinj).eq_iff,
        ← signature_eq_of_samePartition adj P ih i j]

/-- The guess and its `< ↔ >` mirror made explicit: warm refinement after
`a < b` on `P₀` and after `b < a` on the σ-swapped `P₀` induce the same
partition (`applyGuess_swap` + `warmRefine_swap`). -/
theorem warmRefine_applyGuess_swap {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (a b : Fin n) (hab : a ≠ b) (χ : Colouring n) :
    samePartition
      (warmRefine adj (applyGuess P₀ a b .less) χ)
      (warmRefine adj (applyGuess (PMatrix.swap P₀) a b .greater) χ) := by
  have h := warmRefine_swap adj (applyGuess P₀ a b .less) χ
  rw [applyGuess_swap P₀ a b hab .less, POE.swap_less] at h
  exact h

/--
**Guesses commute (Q2).** Guessing on `{a, b}` and on `{b, c}` — distinct
pairs sharing the vertex `b` — touches four distinct matrix entries, so the
two `applyGuess` writes commute. Hence the descent state reached by a *fixed*
pair of guesses does not depend on the order they were issued: making `{a,b}`
then `{b,c}` yields exactly the same `(adj, P)` — and therefore the same
refinement, partition, and boundary — as `{b,c}` then `{a,b}`.

(TC relegation is what makes this clean: a guess is now a single entry write,
and writes to disjoint entries commute. With TC in the loop one would also
need closure confluence.)
-/
theorem applyGuess_comm {n : Nat} (P : PMatrix n) (a b c : Fin n)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (d₁ d₂ : POE) :
    applyGuess (applyGuess P a b d₁) b c d₂
      = applyGuess (applyGuess P b c d₂) a b d₁ := by
  funext i j
  unfold applyGuess
  split_ifs <;> simp_all

/-! ## §6.2 generalised — the partition is shared across all guess directions

`warm_6_2` flips *one* decision. The generalisation below flips *any set* of
them at once, and is the precise cross-branch-sharing statement: see
`warmRefine_agree_off`. -/

/-- If `P` and `Q` agree on every entry with an endpoint outside `D`, then off
`D` they give the same signature — a signature row of `x ∉ D` only reads
`x`'s entries, all of which agree. -/
theorem signature_agree_off {n : Nat} (adj : AdjMatrix n) (P Q : PMatrix n)
    (χ : Colouring n) {D : Finset (Fin n)}
    (hPQ : ∀ x y : Fin n, (x ∉ D ∨ y ∉ D) → P x y = Q x y)
    (x : Fin n) (hx : x ∉ D) :
    signature adj P χ x = signature adj Q χ x := by
  unfold signature
  apply Multiset.map_congr rfl
  intro u _
  rw [hPQ x u (Or.inl hx)]

/--
**Composable cross-branch sharing.** The cross-level strengthening of
`warmRefine_agree_off`: the two starting colourings need only induce the
*same partition*, not be literally equal.

This is what lets the cross-branch-sharing argument **chain across descent
levels**. At descent level `k` the `a<b` and `b<a` sub-branches carry
colourings that are `samePartition`-equal (by the level-`k` instance of this
lemma) but have *diverged in raw colour value*; feeding them into level `k+1`
still yields equal partitions. With a literal-equality hypothesis the argument
would stall after the first level. `warmRefine_agree_off` is the special case
`χ = χ'`.
-/
theorem warmRefine_agree_off' {n : Nat} (adj : AdjMatrix n) (P Q : PMatrix n)
    (χ χ' : Colouring n) (D : Finset (Fin n))
    (hχ : samePartition χ χ')
    (hPQ : ∀ x y : Fin n, (x ∉ D ∨ y ∉ D) → P x y = Q x y)
    (hsing : ∀ x ∈ D, ∀ u, u ≠ x → χ u ≠ χ x) :
    samePartition (warmRefine adj P χ) (warmRefine adj Q χ') := by
  -- The singleton hypothesis transports across the partition to `χ'`.
  have hsing' : ∀ x ∈ D, ∀ u, u ≠ x → χ' u ≠ χ' x := by
    intro x hx u hu e; exact hsing x hx u hu ((hχ u x).mpr e)
  suffices key : ∀ k, samePartition ((refineStep adj P)^[k] χ)
      ((refineStep adj Q)^[k] χ') from key n
  intro k
  induction k with
  | zero => exact hχ
  | succ k ih =>
    intro i j
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [refineStep_iff, refineStep_iff]
    set Xp := (refineStep adj P)^[k] χ
    set Xq := (refineStep adj Q)^[k] χ'
    by_cases hij : i = j
    · subst hij; simp
    · by_cases hi : i ∈ D
      · have hsp := iterate_refineStep_preserves_singleton adj P i k χ (hsing i hi)
        have hsq := iterate_refineStep_preserves_singleton adj Q i k χ' (hsing' i hi)
        exact ⟨fun h => absurd h.1 (fun e => hsp j (Ne.symm hij) e.symm),
               fun h => absurd h.1 (fun e => hsq j (Ne.symm hij) e.symm)⟩
      · by_cases hj : j ∈ D
        · have hsp := iterate_refineStep_preserves_singleton adj P j k χ (hsing j hj)
          have hsq := iterate_refineStep_preserves_singleton adj Q j k χ' (hsing' j hj)
          exact ⟨fun h => absurd h.1 (hsp i hij), fun h => absurd h.1 (hsq i hij)⟩
        · rw [ih i j,
              signature_agree_off adj P Q Xp hPQ i hi,
              signature_agree_off adj P Q Xp hPQ j hj,
              signature_eq_of_samePartition adj Q ih i j]

/--
**The cell partition depends only on the matrix off the decision set.**

Let `D` be a set of vertices, each a singleton of the starting colouring `χι`
(the fresh-colour individualisation), and let `P`, `Q` be any two matrices
that **agree on every entry with an endpoint outside `D`**. Then warm
refinement from `χι` induces the *same partition* under `P` and under `Q`.

This is `warm_6_2` generalised from one decision to a whole set, and it is the
precise **cross-branch work-sharing** statement. Take `D` to be the decision
vertices of a node and `P`, `Q` two descendant states reached by *any*
guesses on `D`-pairs in *any* directions and *any* order: every guess writes
only `D×D` entries, so `P` and `Q` agree off `D` automatically, and the
hypothesis holds. Consequences:

* The `2^d` leaves of a `d`-genuine-decision subtree **all carry one and the
  same cell partition**. The partition is computed once, not `2^d` times.
* The branch that guessed `A < B` and the branch that guessed `A < C` (with
  `A, B, C` all individualised, so `D ⊇ {A,B,C}`) reach states agreeing off
  `D` — hence the *same* partition. That is the "share the first guess of
  `A<C` with the `A<B` branch" you were after: the shared object is the
  partition, and it transports verbatim.
* What is **not** shared, and what the residual exponential now lives in
  entirely: the *order labels* — which `D`-singleton is "less". The descent is
  thereby reduced from "explore `2^d` partitions" to "one fixed partition,
  optimise the labelling over `Z₂^d`". Closing *that* `Z₂^d` optimisation
  cheaply is exactly the linear oracle (`ChainDescent.md` §10); this theorem
  is the reduction that hands it a well-posed problem.
-/
theorem warmRefine_agree_off {n : Nat} (adj : AdjMatrix n) (P Q : PMatrix n)
    (χι : Colouring n) (D : Finset (Fin n))
    (hPQ : ∀ x y : Fin n, (x ∉ D ∨ y ∉ D) → P x y = Q x y)
    (hsing : ∀ x ∈ D, ∀ u, u ≠ x → χι u ≠ χι x) :
    samePartition (warmRefine adj P χι) (warmRefine adj Q χι) :=
  warmRefine_agree_off' adj P Q χι χι D (samePartition.refl χι) hPQ hsing

/-! ## §6.2 spine — the descent's target-cell sequence is branch-independent

`warm_6_2` and `warmRefine_agree_off` share the *partition* across guess
directions. The canonizer's next move is *target-cell selection* — from the
refined partition it picks the cell to branch on next. If that selection reads
only the partition (not raw refined colour ids) it is direction-blind too, and
the descent's whole sequence of target cells is a fixed **spine** shared by
every branch. See `ChainDescent.md` §11 for the full argument and consequences.

The selection **must** be partition-invariant: across the `a<b` and `b<a`
branches the refined colour *values* genuinely diverge (a non-`D` vertex's
signature is lex-ranked among all vertices, including the `D`-vertices whose
colours differ by direction), so a "lowest raw colour id" rule can pick
different cells in the two branches even when the partition is identical. -/

/-- A target-cell selector is **partition-invariant** when it depends only on
the partition a colouring induces, not on raw colour values. Cross-branch
sharing of the descent spine is sound exactly for such selectors. -/
def PartitionInvariant {n : Nat} (sel : Colouring n → Finset (Fin n)) : Prop :=
  ∀ χ χ' : Colouring n, samePartition χ χ' → sel χ = sel χ'

/-- **The next branch target is direction-blind.** For a partition-invariant
selector, the target cell chosen after the guess `a < b` is the *same* cell as
after `b < a`. The base case of the descent-spine induction. -/
theorem target_direction_blind {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (a b : Fin n) (χι : Colouring n)
    (ha : ∀ u, u ≠ a → χι u ≠ χι a) (hb : ∀ u, u ≠ b → χι u ≠ χι b)
    {sel : Colouring n → Finset (Fin n)} (hsel : PartitionInvariant sel) :
    sel (warmRefine adj (applyGuess P₀ a b .less) χι)
      = sel (warmRefine adj (applyGuess P₀ a b .greater) χι) :=
  hsel _ _ (warm_6_2 adj P₀ a b χι ha hb)

/-- **The next branch target composes across descent levels.** For a
partition-invariant selector and matrices `P`, `Q` agreeing off an
all-singleton decision set `D`, the target cell is the same — even when the
two starting colourings only agree up to partition. This is the inductive step
of the descent-spine argument (`ChainDescent.md` §11): it composes because
`warmRefine_agree_off'` accepts `samePartition` starting colourings. -/
theorem target_agree_off {n : Nat} (adj : AdjMatrix n) (P Q : PMatrix n)
    (χ χ' : Colouring n) (D : Finset (Fin n))
    (hχ : samePartition χ χ')
    (hPQ : ∀ x y : Fin n, (x ∉ D ∨ y ∉ D) → P x y = Q x y)
    (hsing : ∀ x ∈ D, ∀ u, u ≠ x → χ u ≠ χ x)
    {sel : Colouring n → Finset (Fin n)} (hsel : PartitionInvariant sel) :
    sel (warmRefine adj P χ) = sel (warmRefine adj Q χ') :=
  hsel _ _ (warmRefine_agree_off' adj P Q χ χ' D hχ hPQ hsing)

/-! ## §13 — propagation closure as a candidate matroid

Working development per [`docs/chain-descent-matroid.md`](../docs/chain-descent-matroid.md).
The goal is to model the propagation behaviour of warm refinement as a *matroid*
(or a slightly-weaker threshold structure) on the set of pair-guesses, then use
binary/non-binary classification as a polynomial Tier-2 detection scheme.

**The ground set `Egnd n`.** Canonical ordered pairs `(i, j)` with `i < j` —
equivalent to unordered pairs of distinct vertices, but with a fixed
orientation that makes the P-write antisymmetric. A "pair-guess" is an element
of `Egnd n`.

**The closure `cl S`.** Pairs whose endpoints are separated by warm refinement
after committing `S`'s pair-orderings.

**The four matroid axioms:**

* **M0 monotone** — `S ⊆ T → cl S ⊆ cl T` (more commits → finer partition)
* **M1 extensive** — `S ⊆ cl S` (a committed pair separates its endpoints)
* **M2 idempotent** — `cl (cl S) = cl S` (cross-cell commits don't refine further)
* **M3 exchange** — `y ∈ cl (S ∪ {x}) ∖ cl S → x ∈ cl (S ∪ {y}) ∖ cl S`

M0, M1, M2 are expected to be reachable from existing theorems plus moderate
helper lemmas; M3 is the load-bearing open claim. This section sets up the
definitions and statements; proofs in progress.
-/

/-- The canonical ground set: ordered pairs `(i, j)` with `i < j`. -/
def Egnd (n : Nat) : Set (Fin n × Fin n) := { p | p.1 < p.2 }

theorem mem_Egnd {n : Nat} {p : Fin n × Fin n} : p ∈ Egnd n ↔ p.1 < p.2 :=
  Iff.rfl

theorem Egnd_ne {n : Nat} {p : Fin n × Fin n} (hp : p ∈ Egnd n) : p.1 ≠ p.2 :=
  Fin.ne_of_lt hp

/-- Commit a set `S ⊆ Egnd n` of pair-guesses to a P-matrix: for each
`(u, v) ∈ S` write `P u v := less` and `P v u := greater`; leave other entries
unchanged.

If `S` is *not* canonical and contains both `(i, j)` and `(j, i)`, the
`less`-branch wins for `(i, j)` and is *also* picked for `(j, i)` — breaking
antisymmetry. Stick to `S ⊆ Egnd n` to avoid this. -/
noncomputable def Pof {n : Nat} (P₀ : PMatrix n) (S : Set (Fin n × Fin n)) :
    PMatrix n := fun i j =>
  haveI : Decidable ((i, j) ∈ S) := Classical.propDecidable _
  haveI : Decidable ((j, i) ∈ S) := Classical.propDecidable _
  if (i, j) ∈ S then .less
  else if (j, i) ∈ S then .greater
  else P₀ i j

/-- The propagation closure: pairs in the canonical ground set whose endpoints
are separated by warm refinement after committing `S`. -/
noncomputable def cl {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι : Colouring n) (S : Set (Fin n × Fin n)) : Set (Fin n × Fin n) :=
  { p | p ∈ Egnd n ∧
    warmRefine adj (Pof P₀ S) χι p.1 ≠ warmRefine adj (Pof P₀ S) χι p.2 }

/-! ### M1 — extensiveness

A pair-guess committed under fresh-colour individualisation has its endpoints
in distinct singleton cells, which warm refinement preserves. So the pair is
in `cl`. The fresh-colour hypothesis is the matroid-friendly individualisation
model already used by `warm_6_2` and `warmRefine_agree_off'`.
-/

/-- The fresh-colour hypothesis at a pair: both endpoints are `χι`-singletons. -/
def SingletonAt {n : Nat} (χι : Colouring n) (p : Fin n × Fin n) : Prop :=
  (∀ u, u ≠ p.1 → χι u ≠ χι p.1) ∧ (∀ u, u ≠ p.2 → χι u ≠ χι p.2)

/-- **M1 — extensiveness of `cl`.** For canonical `S` whose vertices are all
`χι`-singletons, every pair in `S` lies in `cl S`. -/
theorem cl_extensive {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι : Colouring n) (S : Set (Fin n × Fin n))
    (hScanon : S ⊆ Egnd n)
    (hsing : ∀ p ∈ S, SingletonAt χι p) :
    S ⊆ cl adj P₀ χι S := by
  intro p hp
  refine ⟨hScanon hp, ?_⟩
  have hne : p.1 ≠ p.2 := Egnd_ne (hScanon hp)
  -- p.1 is a χι-singleton, so it stays a singleton under warm refinement.
  have h1 := (hsing p hp).1
  have hkeep := iterate_refineStep_preserves_singleton adj (Pof P₀ S) p.1 n χι h1
  -- warmRefine = iterate^[n]; hkeep p.2 (hne.symm) gives the inequality.
  intro heq
  exact hkeep p.2 hne.symm heq.symm

/-! ### M0 — monotonicity (the unhypothesised form is FALSE)

The naive M0 — `S ⊆ T → cl S ⊆ cl T`, for arbitrary `χι` — does **not** hold.

**Counterexample.** `n = 4`, `adj ≡ 0`, `χι ≡ 0`, `S = {(0,1)}`,
`T = {(0,1), (2,3)}`. Under `S`'s `P`-matrix the signatures at round 1 split
`0` from `2` (vertex 0 has a `.less` entry, vertex 2 has all `.unknown`).
Under `T`'s `P`-matrix the involution `(0 2)(1 3)` is an automorphism of
`(adj, P)`, so refineStep keeps `{0,2}` and `{1,3}` co-classed. So
`(0,2) ∈ cl S \ cl T` — adding `(2,3)` to `S` *destroys* the separation of `0`
and `2` by introducing a new symmetry.

**Diagnosis.** The closure operator on pair-guesses is not monotone in `S`
because more commits can introduce new automorphisms of `(adj, Pof S)`. A
single asymmetric commit (only `(0,1)`) breaks more symmetry than two
symmetric commits (`(0,1)` *and* `(2,3)`, jointly invariant under swap).

**Fresh-colour fix.** Individualising the endpoints of `T` to distinct
`χι`-singletons breaks the swap symmetry mechanically: vertices `0,1,2,3`
have distinct `χι` colours and stay singletons under iteration
(`iterate_refineStep_preserves_singleton`), so they cannot be merged by
refinement regardless of `Pof`. With that hypothesis, M0 is the natural
target.

We do not state a refuted `cl_monotone_unknown` in Lean (the unhypothesised
version is false, recorded here and in `docs/chain-descent-matroid.md`).
-/

/-- **Pof is entry-wise monotone in `S` when `P₀` decides nothing.** For the
all-unknown starting `P₀`, `S ⊆ T` (with `T` canonical) gives
`Pof P₀ S i j = .unknown ∨ Pof P₀ S i j = Pof P₀ T i j` at every entry. Pure
fact about `Pof` — does *not* extend to a `cl` monotonicity result, since the
warm refinement step is not monotone in `P` without the fresh-colour
hypothesis above. -/
theorem Pof_mono_entry_of_unknown {n : Nat}
    {S T : Set (Fin n × Fin n)} (hST : S ⊆ T) (hTcanon : T ⊆ Egnd n)
    (i j : Fin n) :
    Pof (fun _ _ => POE.unknown) S i j = .unknown ∨
      Pof (fun _ _ => POE.unknown) S i j =
        Pof (fun _ _ => POE.unknown) T i j := by
  classical
  by_cases h1 : (i, j) ∈ S
  · right
    have h1T : (i, j) ∈ T := hST h1
    simp [Pof, h1, h1T]
  · by_cases h2 : (j, i) ∈ S
    · right
      have h2T : (j, i) ∈ T := hST h2
      have hji : j < i := hTcanon h2T
      have hijT : (i, j) ∉ T := fun h => absurd (hTcanon h) (lt_asymm hji)
      simp [Pof, h1, h2, hijT, h2T]
    · left
      simp [Pof, h1, h2]

/-! ### M0 (hypothesised) — attempt 1: every vertex individualised

The strongest reasonable hypothesis: `χι` makes *every* vertex of `Fin n` a
singleton (fully discrete starting partition). Under this, the warm-refined
partition is also fully discrete (singletons stay singletons), so `cl S` is
*all* canonical pairs for every `S`. Monotonicity is then vacuous: every `cl`
equals every other. The theorem holds but conveys no information about the
matroid structure.
-/

/-- A colouring is fully discrete: every vertex is a `χι`-singleton. -/
def FullyDiscrete {n : Nat} (χι : Colouring n) : Prop :=
  ∀ v u, u ≠ v → χι u ≠ χι v

/-- **M0 under the discrete hypothesis (trivial).** When `χι` is fully discrete,
every canonical pair lies in every `cl S` — so `cl S = Egnd n` for every `S` and
monotonicity is vacuous. Recorded for the record; provides no structural info. -/
theorem cl_monotone_discrete {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι : Colouring n) (hχι : FullyDiscrete χι)
    {S T : Set (Fin n × Fin n)} (_hST : S ⊆ T) :
    cl adj P₀ χι S ⊆ cl adj P₀ χι T := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  -- Under FullyDiscrete, p.1 and p.2 are χι-singletons; warm refinement
  -- preserves singletons, so their warm-refined colours stay distinct
  -- regardless of which P-matrix is used.
  have hne : p.1 ≠ p.2 := Egnd_ne hp.1
  have hsing : ∀ u, u ≠ p.1 → χι u ≠ χι p.1 := fun u hu => hχι p.1 u hu
  have hkeep :=
    iterate_refineStep_preserves_singleton adj (Pof P₀ T) p.1 n χι hsing
  intro heq
  exact hkeep p.2 hne.symm heq.symm

/-! ### M0 (hypothesised) — attempt 2: T-individualised

The real target: `χι` makes the vertices of `T` (the larger set) singletons,
but leaves vertices not in any `T`-pair unconstrained. Under this hypothesis
the M0 counterexample is killed (the swap symmetry across `T`'s pairs is broken
by distinct `χι`-colours on the `T`-vertices), but the closure is not vacuous —
non-`T` vertices can still merge into multi-vertex cells.

This is *not yet proved*; see the matroid doc for the proof obligation.
-/

/-- `χι`-singletons for every endpoint of every pair in `T`. -/
def TVerticesSingletons {n : Nat} (χι : Colouring n) (T : Set (Fin n × Fin n)) :
    Prop := ∀ p ∈ T, SingletonAt χι p

/-- **Strong form of M0 under T-individualised.** The partitions induced by
`Pof P₀ S` and `Pof P₀ T` warm-refinements *coincide* (`samePartition`) when
`S ⊆ T` and `χι` makes every endpoint of every `T`-pair a singleton.

Mechanism in three pieces:
1. `T`-endpoints are `χι`-singletons (hypothesis) and stay singletons under
   either refinement (`iterate_refineStep_preserves_singleton`), so any pair
   `(i, j)` with `i` or `j` a `T`-endpoint is vacuously `samePartition`-equal
   on both sides (both False ↔ both False).
2. For `(i, j)` with neither endpoint in any `T`-pair, `Pof P₀ S` and
   `Pof P₀ T` agree on rows `i` and `j` (no commit in `S ⊆ T` touches a
   non-`T`-endpoint), so the signatures at `i` and `j` are literally equal
   when computed against the same colouring.
3. `signature_eq_of_samePartition` plus the inductive hypothesis transports
   the signature-equality between `χ_S^k` and `χ_T^k`.

Stronger than monotonicity: `cl S = cl T` under this hypothesis. -/
theorem warmRefine_samePartition_T_individualised {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χι : Colouring n)
    {S T : Set (Fin n × Fin n)} (hST : S ⊆ T)
    (hsing : TVerticesSingletons χι T) :
    samePartition (warmRefine adj (Pof P₀ S) χι)
                  (warmRefine adj (Pof P₀ T) χι) := by
  suffices key : ∀ k, samePartition
      ((refineStep adj (Pof P₀ S))^[k] χι)
      ((refineStep adj (Pof P₀ T))^[k] χι) from key n
  intro k
  induction k with
  | zero => exact samePartition.refl χι
  | succ k ih =>
    intro i j
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [refineStep_iff, refineStep_iff]
    set χ_S := (refineStep adj (Pof P₀ S))^[k] χι
    set χ_T := (refineStep adj (Pof P₀ T))^[k] χι
    by_cases hij : i = j
    · subst hij; simp
    · -- Helper: vertex v in some T-pair is a χι-singleton; iterate preserves.
      have h_singleton : ∀ v : Fin n, (∃ p ∈ T, p.1 = v ∨ p.2 = v) →
          (∀ u, u ≠ v → χ_S u ≠ χ_S v) ∧ (∀ u, u ≠ v → χ_T u ≠ χ_T v) := by
        rintro v ⟨p, hpT, hv⟩
        have hv_χι : ∀ u, u ≠ v → χι u ≠ χι v := by
          rcases hv with rfl | rfl
          · exact (hsing p hpT).1
          · exact (hsing p hpT).2
        exact ⟨iterate_refineStep_preserves_singleton adj (Pof P₀ S) v k χι hv_χι,
               iterate_refineStep_preserves_singleton adj (Pof P₀ T) v k χι hv_χι⟩
      -- Helper: for v not in any T-pair, Pof S and Pof T agree on v's row.
      have h_Pof_eq : ∀ v : Fin n, (¬ ∃ p ∈ T, p.1 = v ∨ p.2 = v) →
          ∀ u, Pof P₀ S v u = Pof P₀ T v u := by
        intro v hv u
        classical
        simp only [Pof]
        have h1T : (v, u) ∉ T := fun h => hv ⟨(v, u), h, Or.inl rfl⟩
        have h2T : (u, v) ∉ T := fun h => hv ⟨(u, v), h, Or.inr rfl⟩
        have h1S : (v, u) ∉ S := fun h => h1T (hST h)
        have h2S : (u, v) ∉ S := fun h => h2T (hST h)
        simp [h1S, h1T, h2S, h2T]
      -- Case analysis: i in T-pair / j in T-pair / neither.
      by_cases hi_T : ∃ p ∈ T, p.1 = i ∨ p.2 = i
      · obtain ⟨hSi, hTi⟩ := h_singleton i hi_T
        refine ⟨fun h => ?_, fun h => ?_⟩
        · exact absurd h.1 (fun e => hSi j (Ne.symm hij) e.symm)
        · exact absurd h.1 (fun e => hTi j (Ne.symm hij) e.symm)
      · by_cases hj_T : ∃ p ∈ T, p.1 = j ∨ p.2 = j
        · obtain ⟨hSj, hTj⟩ := h_singleton j hj_T
          refine ⟨fun h => ?_, fun h => ?_⟩
          · exact absurd h.1 (fun e => hSj i hij e)
          · exact absurd h.1 (fun e => hTj i hij e)
        · -- Main case: i, j not in any T-pair.
          have hPi := h_Pof_eq i hi_T
          have hPj := h_Pof_eq j hj_T
          have hSigi : signature adj (Pof P₀ S) χ_T i
              = signature adj (Pof P₀ T) χ_T i := by
            unfold signature
            apply Multiset.map_congr rfl
            intro u _
            rw [hPi u]
          have hSigj : signature adj (Pof P₀ S) χ_T j
              = signature adj (Pof P₀ T) χ_T j := by
            unfold signature
            apply Multiset.map_congr rfl
            intro u _
            rw [hPj u]
          rw [ih i j, signature_eq_of_samePartition adj (Pof P₀ S) ih i j,
              hSigi, hSigj]

/-- **M0 under the T-individualised hypothesis.** The genuine M0 target,
provable. Follows immediately from the stronger `samePartition` result. -/
theorem cl_monotone_T_individualised {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χι : Colouring n)
    {S T : Set (Fin n × Fin n)} (hST : S ⊆ T)
    (hsing : TVerticesSingletons χι T) :
    cl adj P₀ χι S ⊆ cl adj P₀ χι T := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  intro heq
  exact hp.2 ((warmRefine_samePartition_T_individualised adj P₀ χι hST hsing
    p.1 p.2).mpr heq)

/-! ### M2 — idempotence

`cl (cl S) = cl S`, under fresh-colour individualisation of *both* `S`'s
pairs and `cl S`'s pairs.

The proof reduces to the M0 strong form: applying
`warmRefine_samePartition_T_individualised` with `T = cl S` (the larger set)
gives `samePartition (warmRefine_S) (warmRefine_{cl S})`, hence the sets of
separated pairs literally coincide. The two-direction set equality is then
just unfolding the `samePartition`.

The hypothesis `∀ p ∈ S ∪ cl S, SingletonAt χι p` packages both the M1
hypothesis (for `S`) and the M0-strong hypothesis (for `cl S`).

**Note on the original M2 attempt.** An earlier formulation conjectured that
`cl_idempotent` holds without any individualisation hypothesis, via a per-
cell-symmetry argument (within-cell multisets stay equal after committing
cross-cell pairs). That argument is correct *under fresh colours* (which break
the would-be symmetries that wreck M0) but cannot be true unhypothesised —
the M0 counterexample (§13 above) is itself a witness that committing
cross-cell pairs *can* coarsen the partition when those cells contain
non-individualised vertices that can pair-swap.
-/

/-- **M2 — idempotence of `cl` under fresh-colour individualisation.** -/
theorem cl_idempotent {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι : Colouring n) (S : Set (Fin n × Fin n))
    (hScanon : S ⊆ Egnd n)
    (hsing : ∀ p ∈ S ∪ cl adj P₀ χι S, SingletonAt χι p) :
    cl adj P₀ χι (cl adj P₀ χι S) = cl adj P₀ χι S := by
  have hsing_S : ∀ p ∈ S, SingletonAt χι p := fun p hp => hsing p (Or.inl hp)
  have hsing_cl : TVerticesSingletons χι (cl adj P₀ χι S) :=
    fun p hp => hsing p (Or.inr hp)
  have hSsubcl : S ⊆ cl adj P₀ χι S := cl_extensive adj P₀ χι S hScanon hsing_S
  have hsame := warmRefine_samePartition_T_individualised adj P₀ χι hSsubcl hsing_cl
  apply Set.ext
  intro p
  refine ⟨fun hp => ⟨hp.1, fun heq => hp.2 ((hsame p.1 p.2).mp heq)⟩,
          fun hp => ⟨hp.1, fun heq => hp.2 ((hsame p.1 p.2).mpr heq)⟩⟩

/-! ### Closure-system status of `cl` (negative result, 2026-05-23)

After investigating M0, M1, M2, M3 and additional standard closure axioms, the
finding is that **`cl` as defined here satisfies essentially no standard
closure-system axiom unhypothesised** — only extensiveness survives. Each
failure has an explicit witness (see
[`docs/chain-descent-matroid.md`](../docs/chain-descent-matroid.md) §6).

| Axiom | Unhypothesised | Witness against |
|-------|----------------|------------------|
| CL0 `cl(∅) = ∅` | ✓ under all-same χι | — |
| CL1 extensive `S ⊆ cl S` | ✓ for canonical `S` (conjectured, used as M1) | — |
| CL2 idempotent | ✗ | `S = {(0,1),(2,3)}` (4-vertex empty graph) |
| CL3 monotone | ✗ | `S = {(0,1)}, T = {(0,1),(2,3)}` |
| Matroid M3 exchange | ✗ | `S = {(0,1)}, x = (0,2), y = (2,3)` |
| Anti-exchange | ✗ | `S = ∅, x = (0,1), y = (0,2)` |
| Additivity `cl(S∪T) = cl S ∪ cl T` | ✗ | follows from monotone failure |
| **Subadditivity** `cl(S∪T) ⊆ cl S ∪ cl T` | ✗ | `S = {(0,2),(1,3)}, T = {(0,2),(1,4)}` |

So `cl` is in **no** standard closure-system family (topological closure,
matroid, convex geometry, polymatroid, Moore family, …). The matroid framing
is dead in its current form — see `docs/chain-descent-matroid.md` for the
full story and the proposed pivot to provenance-tracking closure.

**What survives, under fresh-colour:** when `χι` makes every endpoint of every
pair in the relevant set a singleton, M0–M2 hold (M0 and M2 actually hold as
*equalities*, not just `⊆`). M3 is vacuously true because the closure becomes
constant under that hypothesis. This is captured by `cl_extensive`,
`cl_monotone_T_individualised`, `cl_idempotent` (above). The closure is then
structurally degenerate — a rank-0 matroid where every element is a loop —
which is *trivially binary*, so it can't distinguish Tier-1 from Tier-2.
Documented for completeness; no Tier-2-detection power.

**M3 unhypothesised — concrete counterexample (kept as record).** With
`n = 4`, `adj ≡ 0`, `χι ≡ 0`, `S = {(0,1)}`, `x = (0,2)`, `y = (2,3)`: the
M3 premise holds (`y ∈ cl(S ∪ {x}) ∖ cl S`) but the conclusion's `x ∉ cl S`
clause fails — `(0,2) ∈ cl({(0,1)})`. Not encoded as a Lean refutation
because `warmRefine` is noncomputable (the refutation would need invariance-
based equality arguments for the surviving direction). Manual verification
in `docs/chain-descent-matroid.md` §6.

**If matroid-like-structure work is revived in the future**, the natural
next object to study is `cl_prov` — closure tracking the *provenance* of
each forced relation back to a driving commit, in the style of strategy
doc §10's `DERIVED` records. That object likely satisfies the matroid
axioms (the binary case literally being `F_2`-linear-algebra on derived
relations), and is the right level for Tier-2 detection via binary-matroid
classification. §14 below tests the simplest such candidate.
-/

/-! ## §14 — Provenance closure (TC-based) — `cl_prov`

After §13's negative result on warm-refinement `cl`, the natural next layer
to test is **provenance closure** via transitive closure of the partial
order. This uses only TC propagation — no 1-WL cascade — so it captures
the "what does S transitively imply as an ordering?" question.

**Result** (this section): cl_prov is a **topological closure** (Kuratowski
CL0–CL3 hold) but **NOT a matroid** (M3 exchange fails — concrete
machine-checked counterexample `cl_prov_M3_false`).

**Implication.** Standard TC-based provenance gives a clean topological
closure structure but is insufficient for binary-matroid representability
(which would be needed for Tier-2 detection). Richer provenance — tracking
the `F_2`-linear-algebraic dependencies between commits and derived
relations, à la strategy doc §10 `DERIVED` records — would be needed, and
is significantly more modelling work. That extension is out of scope here.
-/

/-- A computable, Finset-based version of `Pof` (the Set-based one in §13
is `noncomputable`, blocking `decide`-checkable refutations). -/
def Pof_fs {n : Nat} (P₀ : PMatrix n) (S : Finset (Fin n × Fin n)) :
    PMatrix n := fun i j =>
  if (i, j) ∈ S then .less
  else if (j, i) ∈ S then .greater
  else P₀ i j

/-- All-unknown commits-to-matrix: shortcut for `Pof_fs (·,· ↦ .unknown) S`. -/
def commitsToP {n : Nat} (S : Finset (Fin n × Fin n)) : PMatrix n :=
  Pof_fs (fun _ _ => .unknown) S

/-- Provenance closure (TC-based). `cl_prov S` = canonical pair-guesses
whose direction is decided by transitive closure of `S`'s commits. -/
def cl_prov {n : Nat} (S : Finset (Fin n × Fin n)) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter fun p =>
    p.1.val < p.2.val ∧
      transitiveClose (commitsToP S) p.1 p.2 ≠ .unknown

/-! ### Helper lemmas for the closure axioms -/

/-- `closeStep` returns `.unknown` on the all-unknown matrix at every entry. -/
theorem closeStep_unknown {n : Nat} (i j : Fin n) :
    closeStep (fun _ _ : Fin n => POE.unknown) i j = POE.unknown := by
  unfold closeStep
  simp

/-- The all-unknown matrix is a fixpoint of `closeStep`. -/
theorem closeStep_unknown_fixpoint {n : Nat} :
    closeStep (fun _ _ : Fin n => POE.unknown) = fun _ _ => POE.unknown := by
  funext i j; exact closeStep_unknown i j

/-- `transitiveClose` of the all-unknown matrix is the all-unknown matrix. -/
theorem transitiveClose_unknown {n : Nat} :
    transitiveClose (fun _ _ : Fin n => POE.unknown) = fun _ _ => POE.unknown := by
  unfold transitiveClose
  -- iterate^[n*n] of identity-on-unknown = identity-on-unknown
  have key : ∀ k, (closeStep^[k]) (fun _ _ : Fin n => POE.unknown)
      = fun _ _ => POE.unknown := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ', Function.comp_apply, ih,
                       closeStep_unknown_fixpoint]
  exact key (n * n)

/-! ### CL0–CL3 for `cl_prov` -/

/-- **CL0 — empty closure.** `cl_prov ∅ = ∅`. -/
theorem cl_prov_empty {n : Nat} : cl_prov (∅ : Finset (Fin n × Fin n)) = ∅ := by
  ext p
  refine ⟨fun hp => ?_, fun hp => absurd hp (by simp)⟩
  simp only [cl_prov, Finset.mem_filter] at hp
  have hP : commitsToP (∅ : Finset (Fin n × Fin n)) = fun _ _ => POE.unknown := by
    funext i j
    simp [commitsToP, Pof_fs]
  rw [hP, transitiveClose_unknown] at hp
  exact absurd rfl hp.2.2

/-- **CL1 — extensiveness.** For canonical `S`, every commit is decided
by TC (its direct `.less` write survives). -/
theorem cl_prov_extensive {n : Nat} (S : Finset (Fin n × Fin n))
    (hScanon : ∀ p ∈ S, p.1.val < p.2.val) :
    S ⊆ cl_prov S := by
  intro p hpS
  simp only [cl_prov, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hScanon p hpS, ?_⟩
  -- Pof_fs S p.1 p.2 = .less since p ∈ S
  have hPof : commitsToP S p.1 p.2 = .less := by
    simp [commitsToP, Pof_fs, hpS]
  -- transitiveClose preserves .less by iterate_closeStep_keeps_less
  unfold transitiveClose
  rw [iterate_closeStep_keeps_less p.1 p.2 (n * n) (commitsToP S) hPof]
  decide

/-! ### M3 (matroid exchange) — REFUTED

The exchange axiom of matroid theory:
> `y ∈ cl(S ∪ {x}) ∖ cl(S) → x ∈ cl(S ∪ {y}) ∖ cl(S)`.

**Refuted.** With `n = 5`, `S = {(1,2), (3,4)}`, `x = (2,3)`, `y = (1,4)`:

- `y ∈ cl_prov(S ∪ {x})`: the chain `1 → 2 → 3 → 4` derives `(1,4)`. ✓
- `y ∉ cl_prov(S)`: `(1,2)` and `(3,4)` share no vertex, no chain. ✓
- `x ∉ cl_prov(S ∪ {y})`: `{(1,2), (3,4), (1,4)}` has no chain reaching
  `(2,3)` — none of `(2,?)` or `(?,3)` is decided. ✗

So cl_prov_TC is not a matroid. Machine-checked via `decide` on the
concrete 5-vertex instance.
-/

/-- Concrete counterexample: with `n=5`, `S = {(1,2), (3,4)}`,
`x = (2,3)`, `y = (1,4)`, the matroid exchange premise holds but the
conclusion's `x ∈ cl_prov(S ∪ {y})` clause fails. -/
theorem cl_prov_M3_false :
    let S : Finset (Fin 5 × Fin 5) := {(1, 2), (3, 4)}
    let x : Fin 5 × Fin 5 := (2, 3)
    let y : Fin 5 × Fin 5 := (1, 4)
    y ∈ cl_prov (S ∪ {x}) ∧
    y ∉ cl_prov S ∧
    x ∉ cl_prov (S ∪ {y}) := by
  decide

/-! ### Direction-monotonicity infrastructure for CL3 / CL2

Both CL3 and CL2 reduce to a "less-direction entry-mono" argument lifted
through `transitiveClose`. The naive "decidedness-only" mono fails because
`closeStep`'s `.less`-first tie-break can shift direction between two
related matrices. The fix is to carry **canonical-consistency** as a joint
invariant — under it, no pair can host both a `.less`-chain and a
`.greater`-chain, killing the bad case.

Both CL3 and CL2 filter to canonical pairs `i.val < j.val`, so we only
need the `.less` direction of mono throughout. -/

/-- A `.less`-chain in `P` from `i` to `j`: some intermediate `k` with
both edges `.less`. -/
def hasLessChain {n : Nat} (P : PMatrix n) (i j : Fin n) : Prop :=
  ∃ k : Fin n, P i k = .less ∧ P k j = .less

/-- A `.greater`-chain in `P` from `i` to `j`. -/
def hasGreaterChain {n : Nat} (P : PMatrix n) (i j : Fin n) : Prop :=
  ∃ k : Fin n, P i k = .greater ∧ P k j = .greater

/-- A `PMatrix` is **canonical-consistent** if every `.less` entry sits at
`i.val < j.val` and every `.greater` entry at `i.val > j.val`. -/
def CanConsistent {n : Nat} (P : PMatrix n) : Prop :=
  (∀ i j : Fin n, P i j = .less → i.val < j.val) ∧
  (∀ i j : Fin n, P i j = .greater → i.val > j.val)

/-- One-sided (`.less`) entry-wise mono. Sufficient for CL3 and CL2 since
both filter to canonical pairs. -/
def LessMono {n : Nat} (P Q : PMatrix n) : Prop :=
  ∀ i j : Fin n, P i j = .less → Q i j = .less

/-- Under canonical-consistency, no pair has both a `.less`-chain and a
`.greater`-chain (the chain endpoints' canonical ordering constraints
conflict). -/
theorem canConsistent_no_conflict {n : Nat} {P : PMatrix n}
    (hP : CanConsistent P) (i j : Fin n)
    (hL : hasLessChain P i j) (hG : hasGreaterChain P i j) : False := by
  obtain ⟨k, hik, hkj⟩ := hL
  obtain ⟨m, him, hmj⟩ := hG
  have h1 : i.val < j.val := Nat.lt_trans (hP.1 i k hik) (hP.1 k j hkj)
  have h2 : j.val < i.val := Nat.lt_trans (hP.2 m j hmj) (hP.2 i m him)
  exact Nat.lt_irrefl _ (Nat.lt_trans h1 h2)

/-- **Classification of `commitsToP S i j`** based on `S`-membership.
Three mutually exclusive cases under canonical `S`. -/
theorem commitsToP_classify {n : Nat} (S : Finset (Fin n × Fin n))
    (i j : Fin n) :
    (commitsToP S i j = .less ∧ (i, j) ∈ S) ∨
    (commitsToP S i j = .greater ∧ (i, j) ∉ S ∧ (j, i) ∈ S) ∨
    (commitsToP S i j = .unknown ∧ (i, j) ∉ S ∧ (j, i) ∉ S) := by
  by_cases h1 : (i, j) ∈ S
  · left
    refine ⟨?_, h1⟩
    simp [commitsToP, Pof_fs, h1]
  · by_cases h2 : (j, i) ∈ S
    · right; left
      refine ⟨?_, h1, h2⟩
      simp [commitsToP, Pof_fs, h1, h2]
    · right; right
      refine ⟨?_, h1, h2⟩
      simp [commitsToP, Pof_fs, h1, h2]

/-- `commitsToP` of a canonical `S` is canonical-consistent. -/
theorem commitsToP_canConsistent {n : Nat} (S : Finset (Fin n × Fin n))
    (hScanon : ∀ p ∈ S, p.1.val < p.2.val) :
    CanConsistent (commitsToP S) := by
  refine ⟨?_, ?_⟩
  · intro i j h
    rcases commitsToP_classify S i j with ⟨_, hmem⟩ | ⟨heq, _⟩ | ⟨heq, _⟩
    · exact hScanon (i, j) hmem
    · rw [heq] at h; cases h
    · rw [heq] at h; cases h
  · intro i j h
    rcases commitsToP_classify S i j with ⟨heq, _⟩ | ⟨_, _, hmem⟩ | ⟨heq, _⟩
    · rw [heq] at h; cases h
    · exact hScanon (j, i) hmem
    · rw [heq] at h; cases h

/-! ### closeStep helpers -/

/-- `closeStep` never demotes a decided `.greater` entry. -/
theorem closeStep_keeps_greater {n : Nat} (Q : PMatrix n) {i j : Fin n}
    (h : Q i j = .greater) : closeStep Q i j = .greater := by
  simp only [closeStep, h]

/-- Iterating `closeStep` preserves a `.greater` entry — once decided, frozen. -/
theorem iterate_closeStep_keeps_greater {n : Nat} (i j : Fin n) :
    ∀ (k : Nat) (Q : PMatrix n), Q i j = .greater →
      ((closeStep^[k]) Q) i j = .greater := by
  intro k
  induction k with
  | zero => intro Q h; exact h
  | succ k ih =>
    intro Q h
    rw [Function.iterate_succ, Function.comp_apply]
    exact ih (closeStep Q) (closeStep_keeps_greater Q h)

/-- `closeStep` preserves any decided entry. -/
theorem closeStep_decided {n : Nat} (P : PMatrix n) (i j : Fin n)
    (hP : P i j ≠ .unknown) : closeStep P i j = P i j := by
  cases hPij : P i j with
  | less    => exact closeStep_keeps_less P hPij
  | greater => exact closeStep_keeps_greater P hPij
  | unknown => exact absurd hPij hP

/-- `closeStep` at an `.unknown` entry, expanded. -/
theorem closeStep_unknown_eq {n : Nat} (P : PMatrix n) (i j : Fin n)
    (hP : P i j = .unknown) :
    closeStep P i j =
      (if (List.finRange n).any
            (fun k => decide (P i k = .less) && decide (P k j = .less))
        then .less
        else if (List.finRange n).any
              (fun k => decide (P i k = .greater) && decide (P k j = .greater))
          then .greater
          else .unknown) := by
  unfold closeStep
  rw [hP]

/-- **Classification of `closeStep P i j`'s output for `.less` case.** -/
theorem closeStep_eq_less_iff {n : Nat} (P : PMatrix n) (i j : Fin n) :
    closeStep P i j = .less ↔
      P i j = .less ∨ (P i j = .unknown ∧ hasLessChain P i j) := by
  constructor
  · intro h
    cases hPij : P i j with
    | less => left; rfl
    | greater =>
      rw [closeStep_keeps_greater P hPij] at h; cases h
    | unknown =>
      right
      refine ⟨rfl, ?_⟩
      rw [closeStep_unknown_eq P i j hPij] at h
      by_cases h1 : (List.finRange n).any
            (fun k => decide (P i k = .less) && decide (P k j = .less))
      · rw [List.any_eq_true] at h1
        obtain ⟨k, _, hk⟩ := h1
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hk
        exact ⟨k, hk.1, hk.2⟩
      · -- No .less-chain: closeStep outputs .greater or .unknown, not .less
        rw [if_neg h1] at h
        by_cases h2 : (List.finRange n).any
              (fun k => decide (P i k = .greater) && decide (P k j = .greater))
        · rw [if_pos h2] at h; cases h
        · rw [if_neg h2] at h; cases h
  · rintro (hP | ⟨hP, k, hik, hkj⟩)
    · exact closeStep_keeps_less P hP
    · rw [closeStep_unknown_eq P i j hP]
      have : (List.finRange n).any
            (fun k' => decide (P i k' = .less) && decide (P k' j = .less)) = true := by
        rw [List.any_eq_true]
        refine ⟨k, List.mem_finRange _, ?_⟩
        simp [hik, hkj]
      rw [if_pos this]

/-- A direction for `closeStep` outputs: if it's `.less` (or `.greater`),
the `.less`-chain (or `.greater`-chain) plus underlying `.less`/`.greater`
entries determine it. The `.greater` case below mirrors. -/
theorem closeStep_eq_greater_iff {n : Nat} (P : PMatrix n) (i j : Fin n) :
    closeStep P i j = .greater ↔
      P i j = .greater ∨
        (P i j = .unknown ∧ ¬ hasLessChain P i j ∧ hasGreaterChain P i j) := by
  constructor
  · intro h
    cases hPij : P i j with
    | less => rw [closeStep_keeps_less P hPij] at h; cases h
    | greater => left; rfl
    | unknown =>
      right
      refine ⟨rfl, ?_, ?_⟩
      · -- No .less-chain
        intro ⟨k, hik, hkj⟩
        rw [closeStep_unknown_eq P i j hPij] at h
        have : (List.finRange n).any
              (fun k' => decide (P i k' = .less) && decide (P k' j = .less)) = true := by
          rw [List.any_eq_true]
          refine ⟨k, List.mem_finRange _, ?_⟩
          simp [hik, hkj]
        rw [if_pos this] at h; cases h
      · -- .greater-chain
        rw [closeStep_unknown_eq P i j hPij] at h
        by_cases h1 : (List.finRange n).any
              (fun k => decide (P i k = .less) && decide (P k j = .less))
        · rw [if_pos h1] at h; cases h
        · rw [if_neg h1] at h
          by_cases h2 : (List.finRange n).any
                (fun k => decide (P i k = .greater) && decide (P k j = .greater))
          · rw [List.any_eq_true] at h2
            obtain ⟨k, _, hk⟩ := h2
            rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hk
            exact ⟨k, hk.1, hk.2⟩
          · rw [if_neg h2] at h; cases h
  · rintro (hP | ⟨hP, hNoLess, k, hik, hkj⟩)
    · exact closeStep_keeps_greater P hP
    · rw [closeStep_unknown_eq P i j hP]
      have h_no_less : (List.finRange n).any
          (fun k' => decide (P i k' = .less) && decide (P k' j = .less)) = false := by
        rw [List.any_eq_false]
        intro k' _ hbad
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hbad
        exact hNoLess ⟨k', hbad.1, hbad.2⟩
      rw [if_neg (by rw [h_no_less]; decide)]
      have h_greater : (List.finRange n).any
          (fun k' => decide (P i k' = .greater) && decide (P k' j = .greater)) = true := by
        rw [List.any_eq_true]
        refine ⟨k, List.mem_finRange _, ?_⟩
        simp [hik, hkj]
      rw [if_pos h_greater]

/-- `closeStep` preserves canonical-consistency. -/
theorem closeStep_canConsistent {n : Nat} {P : PMatrix n}
    (hP : CanConsistent P) : CanConsistent (closeStep P) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    rcases (closeStep_eq_less_iff P i j).mp hij with hLess | ⟨_, k, hik, hkj⟩
    · exact hP.1 i j hLess
    · exact Nat.lt_trans (hP.1 i k hik) (hP.1 k j hkj)
  · intro i j hij
    rcases (closeStep_eq_greater_iff P i j).mp hij with hGreat | ⟨_, _, k, hik, hkj⟩
    · exact hP.2 i j hGreat
    · exact Nat.lt_trans (hP.2 k j hkj) (hP.2 i k hik)

/-- Iterating `closeStep` preserves canonical-consistency. -/
theorem iterate_closeStep_canConsistent {n : Nat} (P : PMatrix n)
    (hP : CanConsistent P) : ∀ k, CanConsistent ((closeStep^[k]) P) := by
  intro k
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact closeStep_canConsistent ih

/-- `transitiveClose` preserves canonical-consistency. -/
theorem transitiveClose_canConsistent {n : Nat} (P : PMatrix n)
    (hP : CanConsistent P) : CanConsistent (transitiveClose P) :=
  iterate_closeStep_canConsistent P hP (n * n)

/-- **Joint inductive step for `LessMono`.** Under canonical-consistency of
both matrices and `.less`-mono between them, `closeStep` preserves
`.less`-mono.

Threats to the `.less`-chain case: `Q i j = .greater` (ruled out by chain
+ canonical-consistency of `Q`) or a `Q .greater`-chain pre-empting the
tie-break (irrelevant — the if-chain prioritizes `.less`). -/
theorem closeStep_lessMono {n : Nat} {P Q : PMatrix n}
    (hQ : CanConsistent Q) (hPQ : LessMono P Q) :
    LessMono (closeStep P) (closeStep Q) := by
  intro i j hLess
  rcases (closeStep_eq_less_iff P i j).mp hLess with hP | ⟨_, k, hik, hkj⟩
  · -- P i j = .less; transport to Q
    exact closeStep_keeps_less Q (hPQ i j hP)
  · -- P i j = .unknown with .less-chain through k
    have hQik : Q i k = .less := hPQ i k hik
    have hQkj : Q k j = .less := hPQ k j hkj
    -- Show closeStep Q i j = .less
    cases hQij : Q i j with
    | less    => exact closeStep_keeps_less Q hQij
    | greater =>
      exfalso
      have h_lt : i.val < j.val := Nat.lt_trans (hQ.1 i k hQik) (hQ.1 k j hQkj)
      have h_gt : j.val < i.val := hQ.2 i j hQij
      exact Nat.lt_irrefl _ (Nat.lt_trans h_lt h_gt)
    | unknown =>
      exact (closeStep_eq_less_iff Q i j).mpr (Or.inr ⟨hQij, k, hQik, hQkj⟩)

/-- Iterating `closeStep` preserves `.less`-mono. -/
theorem iterate_closeStep_lessMono {n : Nat} {P Q : PMatrix n}
    (_ : CanConsistent P) (hQ : CanConsistent Q) (hPQ : LessMono P Q) :
    ∀ k, LessMono ((closeStep^[k]) P) ((closeStep^[k]) Q) := by
  intro k
  induction k with
  | zero => exact hPQ
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    exact closeStep_lessMono (iterate_closeStep_canConsistent Q hQ k) ih

/-- `transitiveClose` preserves `.less`-mono. -/
theorem transitiveClose_lessMono {n : Nat} {P Q : PMatrix n}
    (hP : CanConsistent P) (hQ : CanConsistent Q) (hPQ : LessMono P Q) :
    LessMono (transitiveClose P) (transitiveClose Q) :=
  iterate_closeStep_lessMono hP hQ hPQ (n * n)

/-- Base case for CL3: under `S ⊆ T` both canonical,
`commitsToP S → commitsToP T` is `.less`-mono. -/
theorem commitsToP_lessMono {n : Nat} {S T : Finset (Fin n × Fin n)}
    (hST : S ⊆ T) :
    LessMono (commitsToP S) (commitsToP T) := by
  intro i j h
  rcases commitsToP_classify S i j with ⟨_, hmem⟩ | ⟨heq, _⟩ | ⟨heq, _⟩
  · -- (i,j) ∈ S ⊆ T, so commitsToP T i j = .less
    rcases commitsToP_classify T i j with ⟨heqT, _⟩ | ⟨_, hnot, _⟩ | ⟨_, hnot, _⟩
    · exact heqT
    · exact absurd (hST hmem) hnot
    · exact absurd (hST hmem) hnot
  · rw [heq] at h; cases h
  · rw [heq] at h; cases h

/-! ### CL3 — monotonicity (proved) -/

/-- **CL3 — monotonicity.** For canonical `S ⊆ T`, `cl_prov S ⊆ cl_prov T`. -/
theorem cl_prov_monotone {n : Nat} {S T : Finset (Fin n × Fin n)}
    (hST : S ⊆ T) (hScanon : ∀ p ∈ S, p.1.val < p.2.val)
    (hTcanon : ∀ p ∈ T, p.1.val < p.2.val) :
    cl_prov S ⊆ cl_prov T := by
  intro p hp
  simp only [cl_prov, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  obtain ⟨hlt, hdec⟩ := hp
  refine ⟨hlt, ?_⟩
  have hCanS : CanConsistent (commitsToP S) := commitsToP_canConsistent S hScanon
  have hCanT : CanConsistent (commitsToP T) := commitsToP_canConsistent T hTcanon
  have hCanTCS : CanConsistent (transitiveClose (commitsToP S)) :=
    transitiveClose_canConsistent _ hCanS
  -- Under canonical-consistency, TC decided + p.1 < p.2 ⟹ TC value = .less
  have hLess : transitiveClose (commitsToP S) p.1 p.2 = .less := by
    cases h : transitiveClose (commitsToP S) p.1 p.2 with
    | less    => rfl
    | unknown => exact absurd h hdec
    | greater => exact absurd hlt (Nat.not_lt_of_lt (hCanTCS.2 p.1 p.2 h))
  -- Lift through LessMono
  have hLifted : LessMono (transitiveClose (commitsToP S))
                          (transitiveClose (commitsToP T)) :=
    transitiveClose_lessMono hCanS hCanT (commitsToP_lessMono hST)
  have hLessT : transitiveClose (commitsToP T) p.1 p.2 = .less :=
    hLifted p.1 p.2 hLess
  rw [hLessT]; decide

/-! ### TC idempotence (for CL2)

`closeStep` is monotone on decidedness: each entry transitions
`.unknown → .less/.greater` at most once. So after `n*n` rounds the iterate
has saturated. Argument via the strictly-decreasing potential
`numUnknown`. -/

/-- Number of `.unknown` entries in a `PMatrix`. -/
def numUnknown {n : Nat} (P : PMatrix n) : Nat :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => P p.1 p.2 = .unknown)).card

/-- `numUnknown ≤ n * n`. -/
theorem numUnknown_le {n : Nat} (P : PMatrix n) : numUnknown P ≤ n * n := by
  unfold numUnknown
  calc _ ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
            Finset.card_filter_le _ _
    _ = n * n := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

/-- The unknown set of `closeStep P` is contained in the unknown set of `P`. -/
theorem closeStep_unknown_subset {n : Nat} (P : PMatrix n) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun p => closeStep P p.1 p.2 = .unknown)) ⊆
    ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun p => P p.1 p.2 = .unknown)) := by
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  by_contra hPp
  exact hPp (by rw [← closeStep_decided P p.1 p.2 hPp]; exact hp)

/-- If `closeStep P ≠ P`, then `numUnknown` strictly drops. -/
theorem closeStep_numUnknown_lt {n : Nat} {P : PMatrix n}
    (hne : closeStep P ≠ P) : numUnknown (closeStep P) < numUnknown P := by
  -- Some pair where closeStep P differs from P
  have hExists : ∃ (p : Fin n × Fin n), closeStep P p.1 p.2 ≠ P p.1 p.2 := by
    by_contra hAll
    apply hne
    funext i j
    by_contra hne'
    exact hAll ⟨(i, j), hne'⟩
  obtain ⟨p, hpne⟩ := hExists
  have hPunk : P p.1 p.2 = .unknown := by
    by_contra hdec
    exact hpne (closeStep_decided P p.1 p.2 hdec)
  have hCSdec : closeStep P p.1 p.2 ≠ .unknown := by
    intro hUnk; apply hpne; rw [hUnk, hPunk]
  unfold numUnknown
  refine Finset.card_lt_card ?_
  refine ⟨closeStep_unknown_subset P, ?_⟩
  intro hSub
  have hp_in : p ∈ ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun p => P p.1 p.2 = .unknown)) := by
    simp [hPunk]
  have := hSub hp_in
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact hCSdec this

/-- After `k` iterations of `closeStep`, either a fixed point has been
reached at some step `≤ k`, or `numUnknown` has dropped by at least `k`. -/
theorem iterate_closeStep_progress {n : Nat} (P : PMatrix n) :
    ∀ k, (∃ j ≤ k, (closeStep^[j+1]) P = (closeStep^[j]) P) ∨
         numUnknown ((closeStep^[k]) P) + k ≤ numUnknown P := by
  intro k
  induction k with
  | zero => right; simp
  | succ k ih =>
    rcases ih with ⟨j, hj_le, hFix⟩ | hDrop
    · -- Already at fixed point at step j ≤ k → still at fixed point
      left; exact ⟨j, Nat.le_succ_of_le hj_le, hFix⟩
    · -- numUnknown drop ≥ k at step k. Either step k+1 reaches fixed point or strict drop.
      by_cases hFixAtK : (closeStep^[k+1]) P = (closeStep^[k]) P
      · left; exact ⟨k, Nat.le_succ k, hFixAtK⟩
      · right
        -- closeStep^[k+1] P = closeStep (closeStep^[k] P); the step from k to k+1 differs
        have hkStep : (closeStep^[k+1]) P = closeStep ((closeStep^[k]) P) := by
          rw [Function.iterate_succ' closeStep k, Function.comp_apply]
        have hStepNe : closeStep ((closeStep^[k]) P) ≠ (closeStep^[k]) P := by
          intro hAbs
          apply hFixAtK
          rw [hkStep, hAbs]
        have hLt : numUnknown (closeStep ((closeStep^[k]) P)) <
                    numUnknown ((closeStep^[k]) P) :=
          closeStep_numUnknown_lt hStepNe
        rw [hkStep]
        omega

/-- After `n*n` iterations, `closeStep` has reached a fixed point. -/
theorem transitiveClose_is_fixpoint {n : Nat} (P : PMatrix n) :
    closeStep (transitiveClose P) = transitiveClose P := by
  unfold transitiveClose
  rcases iterate_closeStep_progress P (n * n) with ⟨j, hj_le, hFix⟩ | hDrop
  · -- fixed point at step j ≤ n*n; iterate it forward
    have hExt : ∀ m, (closeStep^[j+m]) P = (closeStep^[j]) P := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [show j + (m + 1) = (j + m) + 1 from by omega,
            Function.iterate_succ' closeStep (j+m), Function.comp_apply, ih]
        -- now goal: closeStep ((closeStep^[j]) P) = (closeStep^[j]) P
        rw [← Function.comp_apply (f := closeStep), ← Function.iterate_succ' closeStep,
            hFix]
    have h1 : (closeStep^[n*n + 1]) P = (closeStep^[j]) P := by
      have := hExt (n * n + 1 - j)
      rw [show j + (n * n + 1 - j) = n * n + 1 from by omega] at this
      exact this
    have h2 : (closeStep^[n*n]) P = (closeStep^[j]) P := by
      have := hExt (n * n - j)
      rw [show j + (n * n - j) = n * n from by omega] at this
      exact this
    rw [show closeStep ((closeStep^[n*n]) P) = (closeStep^[n*n + 1]) P from by
        rw [Function.iterate_succ' closeStep (n*n), Function.comp_apply]]
    rw [h1, h2]
  · -- numUnknown ((closeStep^[n*n]) P) + n*n ≤ numUnknown P ≤ n*n
    --  ⟹ numUnknown ((closeStep^[n*n]) P) ≤ 0; but then... actually this branch
    -- still needs argument. The drop tells us many transitions happened; we
    -- still need that the NEXT step is a fixed point.
    -- Alternative: numUnknown P ≤ n*n, hDrop: numUnknown ((closeStep^[n*n]) P) + n*n ≤ numUnknown P
    -- So numUnknown ((closeStep^[n*n]) P) = 0 and numUnknown P = n*n.
    -- If numUnknown ((closeStep^[n*n]) P) = 0, no entry is .unknown, so closeStep is identity
    -- (closeStep on all-decided is identity).
    have hUnkZero : numUnknown ((closeStep^[n*n]) P) = 0 := by
      have hPle := numUnknown_le P
      omega
    -- closeStep on a matrix with no .unknown entries is identity
    apply funext; intro i
    apply funext; intro j
    by_cases hP : (closeStep^[n*n]) P i j = .unknown
    · -- Contradiction: numUnknown should include (i,j) but is 0
      exfalso
      have : (i, j) ∈ ((Finset.univ : Finset (Fin n × Fin n)).filter
          (fun p => (closeStep^[n*n]) P p.1 p.2 = .unknown)) := by simp [hP]
      have hCard : ((Finset.univ : Finset (Fin n × Fin n)).filter
          (fun p => (closeStep^[n*n]) P p.1 p.2 = .unknown)).card ≠ 0 :=
        Finset.card_ne_zero.mpr ⟨(i, j), this⟩
      exact hCard hUnkZero
    · exact closeStep_decided _ i j hP

/-- **TC idempotence.** -/
theorem transitiveClose_idempotent {n : Nat} (M : PMatrix n) :
    transitiveClose (transitiveClose M) = transitiveClose M := by
  have hFix : closeStep (transitiveClose M) = transitiveClose M :=
    transitiveClose_is_fixpoint M
  unfold transitiveClose at hFix ⊢
  exact iterate_closeStep_fix ((closeStep^[n*n]) M) hFix (n * n)

/-! ### CL2 — idempotence (proved) -/

/-- `cl_prov S` is canonical. -/
theorem cl_prov_canonical {n : Nat} (S : Finset (Fin n × Fin n)) :
    ∀ p ∈ cl_prov S, p.1.val < p.2.val := by
  intro p hp
  simp only [cl_prov, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  exact hp.1

/-- `commitsToP (cl_prov S)` is `.less`-bounded by `transitiveClose
(commitsToP S)`. -/
theorem commitsToP_cl_prov_lessMono {n : Nat} (S : Finset (Fin n × Fin n))
    (hScanon : ∀ p ∈ S, p.1.val < p.2.val) :
    LessMono (commitsToP (cl_prov S)) (transitiveClose (commitsToP S)) := by
  have hCanS : CanConsistent (commitsToP S) := commitsToP_canConsistent S hScanon
  have hCanTCS : CanConsistent (transitiveClose (commitsToP S)) :=
    transitiveClose_canConsistent _ hCanS
  intro i j h
  rcases commitsToP_classify (cl_prov S) i j with ⟨_, hmem⟩ | ⟨heq, _⟩ | ⟨heq, _⟩
  · -- (i,j) ∈ cl_prov S: extract hlt and hdec
    simp only [cl_prov, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨hlt, hdec⟩ := hmem
    cases hTC : transitiveClose (commitsToP S) i j with
    | less    => rfl
    | unknown => exact absurd hTC hdec
    | greater => exact absurd hlt (Nat.not_lt_of_lt (hCanTCS.2 i j hTC))
  · rw [heq] at h; cases h
  · rw [heq] at h; cases h

/-- **CL2 — idempotence.** `cl_prov (cl_prov S) = cl_prov S`. -/
theorem cl_prov_idempotent {n : Nat} (S : Finset (Fin n × Fin n))
    (hScanon : ∀ p ∈ S, p.1.val < p.2.val) :
    cl_prov (cl_prov S) = cl_prov S := by
  apply Finset.Subset.antisymm
  · intro p hp
    simp only [cl_prov, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hlt, hdec⟩ := hp
    refine ⟨hlt, ?_⟩
    have hCanCl : CanConsistent (commitsToP (cl_prov S)) :=
      commitsToP_canConsistent (cl_prov S) (cl_prov_canonical S)
    have hCanS : CanConsistent (commitsToP S) := commitsToP_canConsistent S hScanon
    have hCanTCS : CanConsistent (transitiveClose (commitsToP S)) :=
      transitiveClose_canConsistent _ hCanS
    have hLess : LessMono (commitsToP (cl_prov S)) (transitiveClose (commitsToP S)) :=
      commitsToP_cl_prov_lessMono S hScanon
    have hLifted : LessMono (transitiveClose (commitsToP (cl_prov S)))
                            (transitiveClose (transitiveClose (commitsToP S))) :=
      transitiveClose_lessMono hCanCl hCanTCS hLess
    rw [transitiveClose_idempotent] at hLifted
    have hCanTCcl : CanConsistent (transitiveClose (commitsToP (cl_prov S))) :=
      transitiveClose_canConsistent _ hCanCl
    have hLessCl : transitiveClose (commitsToP (cl_prov S)) p.1 p.2 = .less := by
      cases h : transitiveClose (commitsToP (cl_prov S)) p.1 p.2 with
      | less    => rfl
      | unknown => exact absurd h hdec
      | greater => exact absurd hlt (Nat.not_lt_of_lt (hCanTCcl.2 p.1 p.2 h))
    have : transitiveClose (commitsToP S) p.1 p.2 = .less :=
      hLifted p.1 p.2 hLessCl
    rw [this]; decide
  · exact cl_prov_extensive (cl_prov S) (cl_prov_canonical S)

/-! ### Status summary

`cl_prov` (TC-based provenance closure):

| axiom | status |
|-------|--------|
| CL0 `cl_prov ∅ = ∅` | **proved** (`cl_prov_empty`) |
| CL1 extensive `S ⊆ cl_prov S` | **proved** for canonical S (`cl_prov_extensive`) |
| CL2 idempotent `cl_prov (cl_prov S) = cl_prov S` | **proved** (`cl_prov_idempotent`) |
| CL3 monotone `S ⊆ T → cl_prov S ⊆ cl_prov T` | **proved** (`cl_prov_monotone`) |
| **M3 exchange** | **REFUTED** by decide (`cl_prov_M3_false`) on `n=5`, `S={(1,2),(3,4)}`, `x=(2,3)`, `y=(1,4)` |

CL2/CL3 proved via direction-monotonicity (`LessMono`) lifted through
`transitiveClose` under joint canonical-consistency (`CanConsistent`).
The `closeStep` `.less`-first tie-break would shift direction in general,
but `canConsistent_no_conflict` rules out the bad case (a pair carrying
both a `.less`-chain and a `.greater`-chain) under canonical-consistency.
TC idempotence (`transitiveClose_idempotent`) is via a `numUnknown`
potential argument: each round strictly decreases the unknown count if not
at a fixed point, bounded by `n*n`.

M3's failure remains the decisive structural finding: **`cl_prov` is a
topological closure but not a matroid**, so it doesn't support binary-
matroid representability and the intended Tier-2 detection scheme. See
`docs/chain-descent-matroid.md` §8 for the closed-framework verdict.
-/

/-! ## §15 — the descent spine

Formalisation of `ChainDescent.md` §11. The headline (spine) theorem is

> *With a partition-invariant target selector, the descent's per-level
> state `(D_k, π_k, T_k)` — individualised vertex set, refined partition,
> target cell — is identical for every branch. The tree of partitions is
> therefore a path of length ≤ n; the `2^d` order branchings overlay a
> single fixed partition.*

This is the **reduction** the linear oracle needs: it hands the oracle
one fixed partition and a clean `Z₂^d` residual label-optimisation
problem instead of `2^d` distinct refinement worlds.

**Per-level lemmas, all proved (§§9–11):**
* `warmRefine_agree_off'` — partition composes across descent levels
  (accepts `samePartition` start colourings; this is the workhorse).
* `target_direction_blind` / `target_agree_off` — partition-invariant
  target selection composes across the level.
* `iterate_refineStep_preserves_singleton` — `D`-singletons stay
  singletons under refinement.

**What this section adds.** The recursion stringing the per-level lemmas
across the whole descent. Specifically:

1. `IndivStep χ D T` — *existential* witness of an individualisation step
   (the descent's "fresh-colour the target cell"); not a function — see
   the modelling discussion below.
2. `DescentTrace adj P₀ χι₀ sel k D P χι` — inductive predicate "this
   `(D, P, χι)` state is reachable by `k` descent steps."
3. `SpineChain ... k` — a record bundling a trace with its derived data.
4. `spine_partition_branch_independent` — the spine theorem proper: any
   two `SpineChain`s at level `k` share both `D` and partition.

**Modelling — existential individualisation.** The descent has to
"fresh-colour" a target cell to individualise it; modelling that as a
function (`individualise : Colouring → Finset → Colouring`) forces a
concrete encoding fight (offsets, collision-freeness). The existential
route bundles the witness into the inductive trace instead — at every
descent step, a `IndivStep` is *provided* (rather than computed) as part
of the step's data. The spine theorem then says: *however* the witnesses
were chosen, the resulting partition is the same.

Producing concrete witnesses (proving they exist) is a separate concern
— polynomial, but not part of the spine reduction. A concrete
`individualise` instance can be added as a follow-on if the C# side ever
needs it.

**Scope.** Spine theorem only (the headline branch-independence statement).
Out of scope for this section:
* the "all-`less` descent computes the whole spine" corollary;
* leaf / order-label theory;
* the linear oracle's `Z₂^d` reduction (the spine sets up its precondition,
  but the reduction itself lives in a future section).

See `ChainDescent.md` §11 for the full informal argument and §10 item 1
for context. -/

/-- A *witness* of one descent-step's individualisation: from a starting
colouring `χ` and a target cell `T`, produce a new colouring `χ'` that
singletons every vertex in `T` and refines `χ` outside `T`.

We model this **existentially** (per modelling decision recorded in §15
docstring): `IndivStep` is data, not a function. The descent's trace
carries one such witness at each step, and the spine theorem then says
the resulting partition is the same *however* the witnesses were chosen.

**Axioms.**
* `singletons_T` — every `v ∈ T` is a `χ'`-singleton (against every other
  vertex, in or out of `T`). This covers all the "`x ∈ T` or `y ∈ T`"
  inequality cases the spine induction needs.
* `refines_off_T` — for `x, y ∉ T`, `χ'` collapses `x ≡ y` iff `χ` does.
  Equivalently, `χ'` restricted to `Tᶜ` is partition-equal to `χ`
  restricted to `Tᶜ`.

A concrete witness function (e.g. `fun v => if v ∈ T then 2·χ v + v.val +
offset else 2·χ v`) satisfies both axioms; we do not commit to one,
because the spine theorem is conditional on whichever witness the trace
carries. -/
structure IndivStep {n : Nat} (χ : Colouring n) (T : Finset (Fin n)) where
  χ' : Colouring n
  singletons_T : ∀ v ∈ T, ∀ u, u ≠ v → χ' u ≠ χ' v
  refines_off_T : ∀ x y, x ∉ T → y ∉ T → (χ' x = χ' y ↔ χ x = χ y)

namespace IndivStep

/-- **D-singletons are preserved.** If `χ` already singletons every vertex
in `D`, then `χ'` singletons every vertex in `D ∪ T`. (D-vertices already
χ-singletons stay singletons via `refines_off_T`; T-vertices are
χ'-singletons by `singletons_T`.) Used in the trace's successor step. -/
theorem singletons_union {n : Nat} {χ : Colouring n} {D T : Finset (Fin n)}
    (step : IndivStep χ T)
    (hD : ∀ v ∈ D, ∀ u, u ≠ v → χ u ≠ χ v) :
    ∀ v ∈ D ∪ T, ∀ u, u ≠ v → step.χ' u ≠ step.χ' v := by
  intro v hv u huv
  rcases Finset.mem_union.mp hv with hvD | hvT
  · -- v ∈ D.  Split on whether v ∈ T (use singletons_T) or not (use refines_off_T + hD).
    by_cases hvT : v ∈ T
    · exact step.singletons_T v hvT u huv
    · by_cases huT : u ∈ T
      · -- u ∈ T, v ∉ T.  singletons_T at u (∈ T) with v ≠ u gives χ' v ≠ χ' u.
        exact fun e => step.singletons_T u huT v (Ne.symm huv) e.symm
      · -- both u, v ∉ T.  refines_off_T plus hD.
        intro e
        have hχ : χ u = χ v := (step.refines_off_T u v huT hvT).mp e
        exact hD v hvD u huv hχ
  · -- v ∈ T: directly singletons_T.
    exact step.singletons_T v hvT u huv

/-- **The χι-samePartition step.** Two `IndivStep`s applied to
`samePartition`-equal starting colourings, with the *same target* `T`,
produce `samePartition`-equal results.

This is the inductive engine for level `k → k+1` of the spine theorem:
given the IH `samePartition π_k¹ π_k²` and two individualisation
witnesses at level `k+1`, the level-`k+1` colourings still induce the
same partition, so `warmRefine_agree_off'` (which only needs
`samePartition` start colourings) chains. -/
theorem samePartition_of_samePartition {n : Nat}
    {χ₁ χ₂ : Colouring n} {T : Finset (Fin n)}
    (hpart : samePartition χ₁ χ₂)
    (step₁ : IndivStep χ₁ T) (step₂ : IndivStep χ₂ T) :
    samePartition step₁.χ' step₂.χ' := by
  intro x y
  by_cases hxy : x = y
  · subst hxy; simp
  · by_cases hxT : x ∈ T
    · -- x ∈ T: both sides False (χ' singletons x).
      refine ⟨fun e => ?_, fun e => ?_⟩
      · exact absurd e.symm (step₁.singletons_T x hxT y (Ne.symm hxy))
      · exact absurd e.symm (step₂.singletons_T x hxT y (Ne.symm hxy))
    · by_cases hyT : y ∈ T
      · -- y ∈ T: both sides False.
        refine ⟨fun e => ?_, fun e => ?_⟩
        · exact absurd e (step₁.singletons_T y hyT x hxy)
        · exact absurd e (step₂.singletons_T y hyT x hxy)
      · -- both off T: chain refines_off_T through samePartition.
        rw [step₁.refines_off_T x y hxT hyT,
            hpart x y,
            (step₂.refines_off_T x y hxT hyT).symm]

/-- **Concrete `IndivStep` witness.** A constructive realisation of one
individualisation step, used to prove that traces exist at every level
(otherwise `DescentTrace` could be vacuous and the spine theorem
trivially true).

**Encoding.** `χ' v := if v ∈ T then 2 * (χ v * n + v.val) + 1 else 2 * χ v`.

The parity bit marks T-membership (T-vertices get odd values, non-T
vertices get even ones); the `χ v * n + v.val` factor is a base-`n`
encoding of `(χ v, v.val)` and is injective because `v.val < n`. Both
`IndivStep` axioms follow from these properties and `omega`. -/
def default {n : Nat} (χ : Colouring n) (T : Finset (Fin n)) :
    IndivStep χ T where
  χ' := fun v => if v ∈ T then 2 * (χ v * n + v.val) + 1 else 2 * χ v
  singletons_T := by
    intro v hv u hu
    show (if u ∈ T then 2 * (χ u * n + u.val) + 1 else 2 * χ u)
       ≠ (if v ∈ T then 2 * (χ v * n + v.val) + 1 else 2 * χ v)
    rw [if_pos hv]
    by_cases huT : u ∈ T
    · rw [if_pos huT]
      intro heq
      have huv : u.val < n := u.isLt
      have hvv : v.val < n := v.isLt
      have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) huv
      -- Extract base-`n` equality from the encoding.
      have hadd : χ u * n + u.val = χ v * n + v.val := by omega
      -- Base-`n` injectivity: high digits give χ values; low digits
      -- give `.val`s.  Use Nat division.
      have huval : (χ u * n + u.val) / n = χ u := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn,
            Nat.div_eq_of_lt huv, Nat.zero_add]
      have hvval : (χ v * n + v.val) / n = χ v := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn,
            Nat.div_eq_of_lt hvv, Nat.zero_add]
      have hχ_eq : χ u = χ v := by rw [← huval, hadd, hvval]
      rw [hχ_eq] at hadd
      have hval_eq : u.val = v.val := by omega
      exact hu (Fin.ext hval_eq)
    · rw [if_neg huT]
      -- Parity mismatch: `2 * χ u` is even; `2 * (…) + 1` is odd.
      intro h
      omega
  refines_off_T := by
    intro x y hx hy
    show ((if x ∈ T then 2 * (χ x * n + x.val) + 1 else 2 * χ x)
        = (if y ∈ T then 2 * (χ y * n + y.val) + 1 else 2 * χ y))
        ↔ χ x = χ y
    rw [if_neg hx, if_neg hy]
    constructor
    · intro h; omega
    · intro h; rw [h]

end IndivStep

/-- Convenience: every `(χ, T)` admits an `IndivStep` (the `default` one).
Ensures `DescentTrace` is non-vacuous at every level. -/
instance {n : Nat} (χ : Colouring n) (T : Finset (Fin n)) :
    Nonempty (IndivStep χ T) := ⟨IndivStep.default χ T⟩

/-- A `DescentTrace adj P₀ χι₀ sel k D P χι` records "the state `(D, P, χι)`
is reachable by `k` descent steps from root `(P₀, χι₀)` using selector
`sel`."

* **zero**: at level 0 the state is the root — `D = ∅`, `P = P₀`,
  `χι = χι₀`.
* **succ**: at level `k+1` you have a sub-trace at level `k`, an
  `IndivStep` witness individualising the target cell `sel (warmRefine
  adj P χι)`, and a new matrix `P'` that agrees with `P₀` off the
  enlarged decision set. The new state is `(D ∪ sel(…), P', step.χ')`.

`P'` is any matrix obtained by writing arbitrary `POE` entries inside
the new `D ∪ T` — i.e. any choice of guess directions. The trace is
*existential* in the guess directions: it doesn't track which `POE`s
were written, only that `P'` lives in the agree-off-`D ∪ T` equivalence
class. This is exactly the hypothesis `warmRefine_agree_off'` needs. -/
inductive DescentTrace {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) :
    Nat → Finset (Fin n) → PMatrix n → Colouring n → Type where
  | zero : DescentTrace adj P₀ χι₀ sel 0 ∅ P₀ χι₀
  | succ {k : Nat} {D : Finset (Fin n)} {P : PMatrix n} {χι : Colouring n}
      (prev : DescentTrace adj P₀ χι₀ sel k D P χι)
      -- Individualisation operates on the **refined** partition `warmRefine
      -- adj P χι = π_k`, not on the raw `χι`. The target cell `sel π_k` is
      -- a function of the refined partition; individualising fresh-colours
      -- those vertices on top of `π_k`. This matches the descent's
      -- operational order (refine → pick target → individualise) and is
      -- what makes the spine's `samePartition` chain (the IH gives shared
      -- *refined* partition, which is exactly the IndivStep input).
      (step : IndivStep (warmRefine adj P χι) (sel (warmRefine adj P χι)))
      (P' : PMatrix n)
      (hP' : ∀ x y,
              (x ∉ D ∪ sel (warmRefine adj P χι) ∨
               y ∉ D ∪ sel (warmRefine adj P χι))
              → P' x y = P₀ x y) :
      DescentTrace adj P₀ χι₀ sel (k+1)
        (D ∪ sel (warmRefine adj P χι))
        P'
        step.χ'

namespace DescentTrace

/-- **The trace's colouring singletons `D`.** Inductive invariant: zero
gives `D = ∅` (vacuous); succ enlarges `D ↦ D ∪ T` and `χι ↦ step.χ'`
which singletons `D ∪ T` by `IndivStep.singletons_union` applied to the
inductive hypothesis. -/
theorem singletons {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {k : Nat} {D : Finset (Fin n)} {P : PMatrix n} {χι : Colouring n}
    (trace : DescentTrace adj P₀ χι₀ sel k D P χι) :
    ∀ v ∈ D, ∀ u, u ≠ v → χι u ≠ χι v := by
  induction trace with
  | zero => intro v hv; exact absurd hv (by simp)
  | succ _ step _ _ ih =>
    -- step's input is the *refined* partition `warmRefine adj P χι`. To
    -- apply `step.singletons_union`, we lift the IH's `χ` singleton
    -- property to `warmRefine` via singleton preservation.
    refine step.singletons_union ?_
    intro v hv u hu
    exact iterate_refineStep_preserves_singleton _ _ v _ _ (ih v hv) u hu

/-- **The trace's matrix agrees with `P₀` off `D`.** Inductive invariant:
zero gives `P = P₀` (so the agreement is trivial); succ records the
agreement explicitly in the `hP'` field. -/
theorem P_agrees {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {k : Nat} {D : Finset (Fin n)} {P : PMatrix n} {χι : Colouring n}
    (trace : DescentTrace adj P₀ χι₀ sel k D P χι) :
    ∀ x y, (x ∉ D ∨ y ∉ D) → P x y = P₀ x y := by
  induction trace with
  | zero => intro _ _ _; rfl
  | succ _ _ _ hP' _ => exact hP'

end DescentTrace

/-- A `SpineChain ... k` bundles a `DescentTrace` together with its derived
state `(D, P, χι)`. The spine theorem is stated as branch-independence
of two such chains. -/
structure SpineChain {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) (k : Nat) where
  D : Finset (Fin n)
  P : PMatrix n
  χι : Colouring n
  trace : DescentTrace adj P₀ χι₀ sel k D P χι

namespace SpineChain

variable {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
  {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)} {k : Nat}

/-- The chain's level-`k` partition: warm refinement applied to the
chain's accumulated `(P, χι)`. -/
noncomputable def partition (chain : SpineChain adj P₀ χι₀ sel k) :
    Colouring n :=
  warmRefine adj chain.P chain.χι

end SpineChain

/-! ### The spine theorem -/

/-- Heterogeneous variant of `IndivStep.samePartition_of_samePartition` that
accepts the targets `T₁`, `T₂` as separate parameters with an equality
hypothesis. Used by the inductive step of the spine theorem, where the
two targets are `sel (warmRefine adj P_prev₁ χι_prev₁)` and
`sel (warmRefine adj P_prev₂ χι_prev₂)` — equal by partition-invariance
of `sel` against the inductive hypothesis, but not literally equal.
The `subst` discharges the dependency. -/
theorem IndivStep.samePartition_het {n : Nat}
    {χ₁ χ₂ : Colouring n} {T₁ T₂ : Finset (Fin n)}
    (hpart : samePartition χ₁ χ₂) (hT : T₁ = T₂)
    (step₁ : IndivStep χ₁ T₁) (step₂ : IndivStep χ₂ T₂) :
    samePartition step₁.χ' step₂.χ' := by
  subst hT
  exact step₁.samePartition_of_samePartition hpart step₂

/-- **The descent spine theorem (branch independence).**

Any two `DescentTrace`s through `k` levels — with potentially different
guess-direction choices and individualisation witnesses — agree on:

* the accumulated decision set `D` (literal equality), and
* the level-`k` partition (`samePartition` equality).

Proof: induction on `k`. Base case `k = 0` is `samePartition.refl` after
forced agreement of `D = ∅`, `P = P₀`, `χι = χι₀`. Inductive step `k+1`
destructures both traces; the IH at level `k` gives partition agreement,
which `hsel`-partition-invariance lifts to target-cell agreement; that in
turn gives `D_{k+1}` agreement and `IndivStep.samePartition_het` lifts
the colouring to level `k+1`; the two level-`k+1` matrices both agree
with `P₀` off the new `D`, so they agree with each other; finally
`warmRefine_agree_off'` discharges the inductive step.

The `D = ∅`-singletoning hypothesis is the trace's first invariant
(`DescentTrace.singletons`); the matrix agreement is the second
(`DescentTrace.P_agrees`); both are used at level `k+1`. -/
theorem spine_branch_independent {n : Nat} {adj : AdjMatrix n}
    {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} (hsel : PartitionInvariant sel) :
    ∀ {k : Nat} {D₁ D₂ : Finset (Fin n)} {P₁ P₂ : PMatrix n}
      {χι₁ χι₂ : Colouring n},
      DescentTrace adj P₀ χι₀ sel k D₁ P₁ χι₁ →
      DescentTrace adj P₀ χι₀ sel k D₂ P₂ χι₂ →
      D₁ = D₂ ∧ samePartition (warmRefine adj P₁ χι₁) (warmRefine adj P₂ χι₂) := by
  intro k
  induction k with
  | zero =>
    intro D₁ D₂ P₁ P₂ χι₁ χι₂ t₁ t₂
    cases t₁
    cases t₂
    exact ⟨rfl, samePartition.refl _⟩
  | succ k ih =>
    intro D₁ D₂ P₁ P₂ χι₁ χι₂ t₁ t₂
    cases t₁ with
    | succ prev₁ step₁ _ hP₁' =>
      rename_i Dp₁ Pp₁ χιp₁
      cases t₂ with
      | succ prev₂ step₂ _ hP₂' =>
        rename_i Dp₂ Pp₂ χιp₂
        obtain ⟨hD_prev, hπ_prev⟩ := ih prev₁ prev₂
        -- Targets agree by partition-invariance of `sel`.
        have hT : sel (warmRefine adj Pp₁ χιp₁) = sel (warmRefine adj Pp₂ χιp₂) :=
          hsel _ _ hπ_prev
        -- New D's are equal (congruence: D_prev's agree, targets agree).
        refine ⟨by rw [hD_prev, hT], ?_⟩
        -- step.χ's induce equal partitions.
        have hχ_sing : samePartition step₁.χ' step₂.χ' :=
          IndivStep.samePartition_het hπ_prev hT step₁ step₂
        -- Name the new decision set for clarity.
        set Dnew := Dp₁ ∪ sel (warmRefine adj Pp₁ χιp₁) with hDnew
        -- The two level-(k+1) matrices both agree with P₀ off Dnew, hence
        -- with each other.
        have hPQ : ∀ x y, (x ∉ Dnew ∨ y ∉ Dnew) → P₁ x y = P₂ x y := by
          intro x y h
          have h₂ : x ∉ Dp₂ ∪ sel (warmRefine adj Pp₂ χιp₂) ∨
                    y ∉ Dp₂ ∪ sel (warmRefine adj Pp₂ χιp₂) := by
            rcases h with hx | hy
            · exact Or.inl (by rw [hDnew, hD_prev, hT] at hx; exact hx)
            · exact Or.inr (by rw [hDnew, hD_prev, hT] at hy; exact hy)
          calc P₁ x y = P₀ x y := hP₁' x y h
            _ = P₂ x y := (hP₂' x y h₂).symm
        -- Dnew vertices are step₁.χ'-singletons. `singletons_union` needs the
        -- prev D singletoned in step's *input*, which is `warmRefine` of prev's
        -- (P, χι) — lifted from `prev₁.singletons` via singleton preservation.
        have hsing : ∀ v ∈ Dnew, ∀ u, u ≠ v → step₁.χ' u ≠ step₁.χ' v := by
          refine step₁.singletons_union ?_
          intro v hv u hu
          exact iterate_refineStep_preserves_singleton _ _ v _ _
            (prev₁.singletons v hv) u hu
        exact warmRefine_agree_off' adj P₁ P₂ step₁.χ' step₂.χ' Dnew
          hχ_sing hPQ hsing

/-- **The spine theorem, `SpineChain` wrapper.** Convenience form of
`spine_branch_independent` against the chain bundle: any two
`SpineChain`s at level `k` agree on `D` and on their level-`k`
partition. -/
theorem SpineChain.branch_independent {n : Nat} {adj : AdjMatrix n}
    {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} (hsel : PartitionInvariant sel)
    {k : Nat} (chain₁ chain₂ : SpineChain adj P₀ χι₀ sel k) :
    chain₁.D = chain₂.D ∧ samePartition chain₁.partition chain₂.partition :=
  spine_branch_independent hsel chain₁.trace chain₂.trace

/-! ### Constructive existence — a concrete reference chain

The spine theorem above is conditional on the existence of `IndivStep`
witnesses (bundled in `DescentTrace`). To prove the theorem isn't vacuous
— and to give the C# side a *reference* level-`k` partition every chain
must match — we construct a concrete `defaultSpineChain` using
`IndivStep.default` at every level and `P = P₀` throughout (which
trivially agrees with `P₀` off any `D`, satisfying the trace's `hP'`
clause).

This is the "all-`less` corollary" in its honest form: with the
existential `IndivStep` model and arbitrary `P'`-agrees-off-`D`, the
cleanest reference is "no guesses written, default individualisation."
By `spine_branch_independent`, any other chain at level `k` shares this
reference's partition.

Producing an actually-all-`.less` matrix `P` would just be a different
choice inside the same equivalence class — same partition by spine. -/

/-- The level-`k` colouring of the default chain: iterate "refine then
individualise via `IndivStep.default`," starting from `χι₀`. The
matrix is held fixed at `P₀` throughout. -/
noncomputable def defaultColouring {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) : Nat → Colouring n
  | 0 => χι₀
  | k+1 =>
    let χι := defaultColouring adj P₀ χι₀ sel k
    let π := warmRefine adj P₀ χι
    (IndivStep.default π (sel π)).χ'

/-- The level-`k` decision set of the default chain: accumulate
`sel (warmRefine adj P₀ (defaultColouring k))` across all levels. -/
noncomputable def defaultD {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) : Nat → Finset (Fin n)
  | 0 => ∅
  | k+1 =>
    let χι := defaultColouring adj P₀ χι₀ sel k
    let π := warmRefine adj P₀ χι
    defaultD adj P₀ χι₀ sel k ∪ sel π

/-- The concrete `DescentTrace` for the default construction. -/
noncomputable def defaultTrace {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) :
    (k : Nat) → DescentTrace adj P₀ χι₀ sel k
                  (defaultD adj P₀ χι₀ sel k)
                  P₀
                  (defaultColouring adj P₀ χι₀ sel k)
  | 0 => DescentTrace.zero
  | k+1 =>
    let prev := defaultTrace adj P₀ χι₀ sel k
    let π := warmRefine adj P₀ (defaultColouring adj P₀ χι₀ sel k)
    DescentTrace.succ prev (IndivStep.default π (sel π)) P₀
      (fun _ _ _ => rfl)

/-- The concrete reference `SpineChain` at every level. -/
noncomputable def defaultSpineChain {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) (k : Nat) :
    SpineChain adj P₀ χι₀ sel k where
  D := defaultD adj P₀ χι₀ sel k
  P := P₀
  χι := defaultColouring adj P₀ χι₀ sel k
  trace := defaultTrace adj P₀ χι₀ sel k

/-- **Reference corollary (formerly "all-`less` corollary").** Every
`SpineChain` at level `k` has the same `D` and the same partition as
`defaultSpineChain`. This is the load-bearing existence statement:
*there is a canonical level-`k` partition, computable by one
deterministic descent.* -/
theorem SpineChain.eq_default {n : Nat} {adj : AdjMatrix n}
    {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} (hsel : PartitionInvariant sel)
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) :
    chain.D = defaultD adj P₀ χι₀ sel k ∧
    samePartition chain.partition (defaultSpineChain adj P₀ χι₀ sel k).partition :=
  SpineChain.branch_independent hsel chain (defaultSpineChain adj P₀ χι₀ sel k)

/-! ### §15.1 — Leaf characterisation

The descent terminates at a **leaf** — a state where the partition is
*discrete*, i.e. every cell is a singleton.  At that point the labelling
is fully determined modulo *order labels*: which `D`-singleton sorts
before which.  The order-label layer is the linear oracle's domain
(§15.2 — `DirAssignment` theory).

This sub-section:
1. Defines `Discrete` and `SpineChain.IsLeaf`.
2. Proves `IsLeaf` is `samePartition`-invariant and therefore
   spine-invariant (a corollary of `spine_branch_independent`).
3. Proves `defaultSpineChain_reaches_leaf` — termination within `n`
   levels, under two hypotheses on `sel`:
   * `TargetsNonsingletonCell` — `sel χ` only picks vertices in
     non-singleton cells of `χ` (otherwise nothing to break).
   * `NonemptyOnNonDiscrete` — `sel χ` is non-empty whenever `χ` is not
     already discrete (otherwise descent stalls).

Together these say *the selector keeps making progress until forced to
stop*. Reasonable assumptions on any concrete `sel`. -/

/-- A colouring is **discrete** when every cell is a singleton — equivalently,
the function `χ : Fin n → Nat` is injective. -/
def Discrete {n : Nat} (χ : Colouring n) : Prop :=
  ∀ i j : Fin n, χ i = χ j → i = j

namespace Discrete

/-- `Discrete` is `samePartition`-invariant. -/
theorem of_samePartition {n : Nat} {χ₁ χ₂ : Colouring n}
    (h : samePartition χ₁ χ₂) (hd : Discrete χ₁) : Discrete χ₂ := by
  intro i j hij
  exact hd i j ((h i j).mpr hij)

/-- Warm refinement preserves discreteness: if `χ` is injective, so is
`warmRefine adj P χ`. Lifted from per-vertex singleton preservation
(`iterate_refineStep_preserves_singleton`). -/
theorem warmRefine_preserves {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    {χ : Colouring n} (hd : Discrete χ) :
    Discrete (warmRefine adj P χ) := by
  intro i j hij
  by_contra hne
  exact iterate_refineStep_preserves_singleton adj P j n χ
    (fun u hu hχ => hu (hd u j hχ)) i hne hij

end Discrete

/-- A `SpineChain` reaches a *leaf* when its level-`k` partition is
discrete. At a leaf every vertex is a singleton, so the warm-refined
colouring uniquely identifies each vertex. -/
def SpineChain.IsLeaf {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)} {k : Nat}
    (chain : SpineChain adj P₀ χι₀ sel k) : Prop :=
  Discrete chain.partition

/-- `IsLeaf` is *spine-invariant*: a chain is a leaf iff the canonical
`defaultSpineChain` at the same level is. Direct corollary of
`spine_branch_independent` via `Discrete.of_samePartition`. -/
theorem SpineChain.isLeaf_iff_default {n : Nat} {adj : AdjMatrix n}
    {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} (hsel : PartitionInvariant sel)
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) :
    chain.IsLeaf ↔ (defaultSpineChain adj P₀ χι₀ sel k).IsLeaf := by
  obtain ⟨_, hπ⟩ := SpineChain.eq_default hsel chain
  exact ⟨Discrete.of_samePartition hπ, Discrete.of_samePartition hπ.symm⟩

/-! #### Termination hypotheses on `sel` -/

/-- The selector only picks vertices from **non-singleton** cells of the
colouring it inspects: every returned vertex has a same-colour partner.
Without this, the selector could pick a vertex already-individualised
and the descent would stall. -/
def TargetsNonsingletonCell {n : Nat}
    (sel : Colouring n → Finset (Fin n)) : Prop :=
  ∀ χ : Colouring n, ∀ v ∈ sel χ, ∃ u : Fin n, u ≠ v ∧ χ u = χ v

/-- The selector is non-empty when the colouring is not yet discrete.
Without this, the selector could return ∅ early and the descent would
freeze before reaching a leaf. -/
def NonemptyOnNonDiscrete {n : Nat}
    (sel : Colouring n → Finset (Fin n)) : Prop :=
  ∀ χ : Colouring n, ¬ Discrete χ → sel χ ≠ ∅

/-- **`D` covers all vertices ⇒ leaf.** When the descent's accumulated
decision set is the full vertex set, every vertex is a singleton of the
trace's colouring (by `DescentTrace.singletons`), the colouring is
therefore injective (`Discrete`), and warm refinement preserves
discreteness — so the spine partition is discrete. -/
theorem defaultD_univ_isLeaf {n : Nat} {adj : AdjMatrix n}
    {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} {k : Nat}
    (hD : defaultD adj P₀ χι₀ sel k = Finset.univ) :
    (defaultSpineChain adj P₀ χι₀ sel k).IsLeaf := by
  have hsing := (defaultTrace adj P₀ χι₀ sel k).singletons
  have hdisc : Discrete (defaultColouring adj P₀ χι₀ sel k) := by
    intro i j hij
    by_contra hne
    exact hsing j (by rw [hD]; exact Finset.mem_univ _) i hne hij
  exact Discrete.warmRefine_preserves adj P₀ hdisc

/-- **`D` strictly grows on every non-leaf step.** If the chain at level
`k` is not yet a leaf, then `sel π_k` is non-empty (by
`NonemptyOnNonDiscrete`), and its elements are *not* in
`defaultD k` (because `defaultD k` vertices are `π_k`-singletons while
`sel π_k` vertices are in non-singleton cells of `π_k` by
`TargetsNonsingletonCell`). So `defaultD (k+1) ⊋ defaultD k`. -/
theorem defaultD_grows_if_not_leaf {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χι₀ : Colouring n)
    {sel : Colouring n → Finset (Fin n)}
    (hcell : TargetsNonsingletonCell sel)
    (hne : NonemptyOnNonDiscrete sel)
    {k : Nat}
    (hnotleaf : ¬ (defaultSpineChain adj P₀ χι₀ sel k).IsLeaf) :
    (defaultD adj P₀ χι₀ sel k).card < (defaultD adj P₀ χι₀ sel (k+1)).card := by
  set π := warmRefine adj P₀ (defaultColouring adj P₀ χι₀ sel k) with hπ_def
  -- `sel π` is non-empty (chain not yet a leaf).
  have h_sel_ne : sel π ≠ ∅ := hne π hnotleaf
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr h_sel_ne
  -- `v` has a same-`π` partner — so `v` is not a `π`-singleton.
  obtain ⟨u, hu_ne, hu_eq⟩ := hcell π v hv
  -- `v ∉ defaultD k`: any `defaultD k` vertex is a `π`-singleton (warm
  -- refinement preserves singletons), contradicting the partner above.
  have hv_notin : v ∉ defaultD adj P₀ χι₀ sel k := by
    intro hv_in
    have hsing_χι : ∀ w, w ≠ v →
        defaultColouring adj P₀ χι₀ sel k w
        ≠ defaultColouring adj P₀ χι₀ sel k v :=
      (defaultTrace adj P₀ χι₀ sel k).singletons v hv_in
    have hsing_π : ∀ w, w ≠ v → π w ≠ π v := by
      intro w hw
      exact iterate_refineStep_preserves_singleton adj P₀ v n
        (defaultColouring adj P₀ χι₀ sel k) hsing_χι w hw
    exact hsing_π u hu_ne hu_eq
  -- `defaultD (k+1) = defaultD k ∪ sel π` strictly contains `defaultD k`.
  have h_subset : defaultD adj P₀ χι₀ sel k ⊆ defaultD adj P₀ χι₀ sel (k+1) :=
    fun w hw => Finset.mem_union_left _ hw
  have hv_in_next : v ∈ defaultD adj P₀ χι₀ sel (k+1) :=
    Finset.mem_union_right _ hv
  apply Finset.card_lt_card
  exact ⟨h_subset, fun h_rev => hv_notin (h_rev hv_in_next)⟩

/-- **Leaf existence.** Under the two `sel` hypotheses, the default
descent reaches a leaf within `n` levels.

Proof: by contradiction. If no leaf is reached in `[0, n]`, then by
`defaultD_grows_if_not_leaf` and induction `|defaultD i| ≥ i` for every
`i ≤ n`. At `i = n` we get `|defaultD n| ≥ n = |Finset.univ|`, hence
`defaultD n = Finset.univ`, hence — by `defaultD_univ_isLeaf` — the
level-`n` chain *is* a leaf. Contradicting our assumption that no leaf
exists in `[0, n]`. -/
theorem defaultSpineChain_reaches_leaf {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χι₀ : Colouring n)
    {sel : Colouring n → Finset (Fin n)}
    (hcell : TargetsNonsingletonCell sel)
    (hne : NonemptyOnNonDiscrete sel) :
    ∃ k ≤ n, (defaultSpineChain adj P₀ χι₀ sel k).IsLeaf := by
  by_contra h
  push Not at h
  -- `h : ∀ k ≤ n, ¬ IsLeaf`. Establish growth.
  have growth : ∀ i, i ≤ n → i ≤ (defaultD adj P₀ χι₀ sel i).card := by
    intro i hi
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hi' : i ≤ n := Nat.le_of_succ_le hi
      have ih' := ih hi'
      have h_notleaf : ¬ (defaultSpineChain adj P₀ χι₀ sel i).IsLeaf := h i hi'
      have h_grow := defaultD_grows_if_not_leaf adj P₀ χι₀ hcell hne h_notleaf
      omega
  -- At `i = n`, `|defaultD n| ≥ n`; combined with `defaultD n ⊆ univ` of
  -- cardinality `n`, we get `defaultD n = univ`, hence a leaf at `n`.
  have hn_card : n ≤ (defaultD adj P₀ χι₀ sel n).card := growth n (le_refl n)
  have h_univ_card : (Finset.univ : Finset (Fin n)).card = n := by
    rw [Finset.card_univ, Fintype.card_fin]
  have h_le_univ : (defaultD adj P₀ χι₀ sel n).card
      ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  have hD_univ : defaultD adj P₀ χι₀ sel n = Finset.univ :=
    Finset.eq_univ_of_card _ (by
      rw [Fintype.card_fin]; omega)
  exact h n (le_refl n) (defaultD_univ_isLeaf hD_univ)

/-! ### §15.2 — Order-label space (`DirAssignment`)

The spine theorem says the level-`k` *partition* is direction-independent.
What lives in the residual exponential are the **order labels** —
which `D`-singleton is "less than" which. This sub-section formalises
that residual layer.

A `DirAssignment P₀ D` is any `PMatrix` that:
* is antisymmetric (an honest partial-order matrix), and
* agrees with `P₀` on every entry with at least one endpoint outside `D`
  (only `D × D` entries are "free" — the rest are inherited from `P₀`).

These are exactly the matrices a descent through `D` could produce by
any combination of guesses. By the spine theorem, every `DirAssignment`
refined against a `D`-singletoning colouring induces the *same*
partition.

This is the linear oracle's input shape: a `DirAssignment` is a *point*
in the order-label space; the linear oracle's job (Phase C/D, future)
is to optimise over it. -/

/-- An **order assignment** relative to a base matrix `P₀` and a
decision set `D`: an antisymmetric matrix agreeing with `P₀` outside
`D × D`. -/
structure DirAssignment {n : Nat} (P₀ : PMatrix n) (D : Finset (Fin n)) where
  σ : PMatrix n
  antisym : PMatrix.Antisymmetric σ
  agrees_off : ∀ x y : Fin n, (x ∉ D ∨ y ∉ D) → σ x y = P₀ x y

namespace DirAssignment

variable {n : Nat} {P₀ : PMatrix n} {D : Finset (Fin n)}

/-- **Trivial DirAssignment.** When `P₀` is antisymmetric, `P₀` itself is
a valid order assignment for *any* `D` (no guesses made — every entry
agrees with `P₀` vacuously). Witnesses non-emptiness of
`DirAssignment P₀ D`. -/
def default (hP₀ : PMatrix.Antisymmetric P₀) : DirAssignment P₀ D where
  σ := P₀
  antisym := hP₀
  agrees_off := fun _ _ _ => rfl

/-- Any two `DirAssignment`s over the same `(P₀, D)`, refined against a
`D`-singletoning colouring `χι`, induce the *same* partition. Direct
application of `warmRefine_agree_off'`: both matrices agree with `P₀`
off `D`, hence with each other. -/
theorem samePartition_pair {n : Nat} (adj : AdjMatrix n)
    {P₀ : PMatrix n} {D : Finset (Fin n)} {χι : Colouring n}
    (hsing : ∀ v ∈ D, ∀ u, u ≠ v → χι u ≠ χι v)
    (σ₁ σ₂ : DirAssignment P₀ D) :
    samePartition (warmRefine adj σ₁.σ χι) (warmRefine adj σ₂.σ χι) := by
  refine warmRefine_agree_off' adj σ₁.σ σ₂.σ χι χι D
    (samePartition.refl χι) ?_ hsing
  intro x y h
  rw [σ₁.agrees_off x y h, σ₂.agrees_off x y h]

/-- **Spine equivalence.** A `DirAssignment` over a chain's decision set,
refined against the chain's colouring, induces the chain's partition.
The order-label residual is therefore *exactly* the choice of
`DirAssignment` — the partition is fixed; only the order labels vary. -/
theorem samePartition_chain {n : Nat} {adj : AdjMatrix n}
    {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} {k : Nat}
    (chain : SpineChain adj P₀ χι₀ sel k)
    (σ : DirAssignment P₀ chain.D) :
    samePartition (warmRefine adj σ.σ chain.χι) chain.partition := by
  refine warmRefine_agree_off' adj σ.σ chain.P chain.χι chain.χι chain.D
    (samePartition.refl _) ?_ chain.trace.singletons
  intro x y h
  exact (σ.agrees_off x y h).trans (chain.trace.P_agrees x y h).symm

/-! #### §15.2.1 — Single-pair `Z₂` flip action -/

/-- **Single-pair direction flip.** Flip the `(a, b)` and `(b, a)` entries
of a `DirAssignment` via `POE.neg`. Antisymmetry is preserved (negating
both sides of the antisymmetry equation consistently); `agrees_off` is
preserved (we only touch `D × D` entries, which the `agrees_off`
condition is vacuous on).

This is the **generator of the `Z₂` group** acting on direction
choices: one flip per unordered pair in `D`. -/
def flipPair {n : Nat} {P₀ : PMatrix n} {D : Finset (Fin n)}
    (σ : DirAssignment P₀ D) (a b : Fin n) (ha : a ∈ D) (hb : b ∈ D) :
    DirAssignment P₀ D where
  σ := fun i j =>
    if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then POE.neg (σ.σ i j) else σ.σ i j
  antisym := by
    intro i j
    by_cases h : (i = a ∧ j = b) ∨ (i = b ∧ j = a)
    · -- (i,j) is the flipped pair. Then (j,i) is too (swap branches).
      have h' : (j = a ∧ i = b) ∨ (j = b ∧ i = a) := by
        rcases h with ⟨hia, hjb⟩ | ⟨hib, hja⟩
        · exact Or.inr ⟨hjb, hia⟩
        · exact Or.inl ⟨hja, hib⟩
      simp only [if_pos h, if_pos h']
      -- Goal: POE.neg (σ.σ i j) = POE.neg (POE.neg (σ.σ j i)).
      -- Rewriting σ.antisym i j on the LHS gives both sides equal.
      rw [σ.antisym i j]
    · -- (i,j) not flipped. Then (j,i) isn't either.
      have h' : ¬ ((j = a ∧ i = b) ∨ (j = b ∧ i = a)) := by
        rintro (⟨hja, hib⟩ | ⟨hjb, hia⟩)
        · exact h (Or.inr ⟨hib, hja⟩)
        · exact h (Or.inl ⟨hia, hjb⟩)
      simp only [if_neg h, if_neg h']
      exact σ.antisym i j
  agrees_off := by
    intro x y h
    -- If `(x,y) = (a,b)` or `(b,a)`, both endpoints are in D — contradicting `h`.
    have h' : ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) := by
      rintro (⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
      · rcases h with hx | hy
        · exact hx (hxa ▸ ha)
        · exact hy (hyb ▸ hb)
      · rcases h with hx | hy
        · exact hx (hxb ▸ hb)
        · exact hy (hya ▸ ha)
    simp only [if_neg h']
    exact σ.agrees_off x y h

/-- DirAssignment equality is determined by the matrix field — `antisym`
and `agrees_off` are propositional and so subsumed by proof
irrelevance. Stated in per-entry form so `ext i j` chains into the
function-level equality directly. -/
@[ext]
theorem eq_of_σ_eq {σ₁ σ₂ : DirAssignment P₀ D}
    (h : ∀ i j, σ₁.σ i j = σ₂.σ i j) : σ₁ = σ₂ := by
  cases σ₁; cases σ₂
  congr 1
  funext i j
  exact h i j

/-- **Flip is an involution.** Two applications of `flipPair` to the same
pair return the original `DirAssignment`. The Z₂ generator squares to
the identity. -/
theorem flipPair_idempotent {n : Nat} {P₀ : PMatrix n} {D : Finset (Fin n)}
    (σ : DirAssignment P₀ D) (a b : Fin n) (ha : a ∈ D) (hb : b ∈ D) :
    (σ.flipPair a b ha hb).flipPair a b ha hb = σ := by
  ext i j
  by_cases h : (i = a ∧ j = b) ∨ (i = b ∧ j = a)
  · simp only [flipPair, if_pos h, POE.neg_neg]
  · simp only [flipPair, if_neg h]

/-- **Flipping preserves the partition.** A direct corollary of
`samePartition_pair`: both `σ` and `σ.flipPair a b _ _` are
`DirAssignment`s over the same `(P₀, D)`, so they share the spine
partition. The order labels move; the partition doesn't. -/
theorem flipPair_partition_invariant {n : Nat} (adj : AdjMatrix n)
    {P₀ : PMatrix n} {D : Finset (Fin n)} {χι : Colouring n}
    (hsing : ∀ v ∈ D, ∀ u, u ≠ v → χι u ≠ χι v)
    (σ : DirAssignment P₀ D) (a b : Fin n) (ha : a ∈ D) (hb : b ∈ D) :
    samePartition (warmRefine adj (σ.flipPair a b ha hb).σ χι)
                  (warmRefine adj σ.σ χι) :=
  samePartition_pair adj hsing (σ.flipPair a b ha hb) σ

/-- **Flips on different pairs commute.** When `{a, b} ∩ {c, d} = ∅`, the
two flip operations commute. This is the abelian-ness of the Z₂^d
action: distinct decisions don't interfere. -/
theorem flipPair_comm {n : Nat} {P₀ : PMatrix n} {D : Finset (Fin n)}
    (σ : DirAssignment P₀ D) (a b c d : Fin n)
    (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hd : d ∈ D)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (σ.flipPair a b ha hb).flipPair c d hc hd
      = (σ.flipPair c d hc hd).flipPair a b ha hb := by
  ext i j
  -- Each pair (a,b), (c,d) is independent — the if-then-else conditions
  -- never both fire on the same (i,j), so the two flips commute.
  by_cases hab : (i = a ∧ j = b) ∨ (i = b ∧ j = a)
  · -- Hits the (a,b) pair: c,d branch doesn't fire because {a,b} ∩ {c,d} = ∅.
    have hcd : ¬ ((i = c ∧ j = d) ∨ (i = d ∧ j = c)) := by
      rintro (⟨hic, hjd⟩ | ⟨hid, hjc⟩) <;>
        rcases hab with ⟨hia, hjb⟩ | ⟨hib, hja⟩
      · exact hac (hia ▸ hic)
      · exact hbc (hib ▸ hic)
      · exact had (hia ▸ hid)
      · exact hbd (hib ▸ hid)
    simp only [flipPair, if_pos hab, if_neg hcd]
  · by_cases hcd : (i = c ∧ j = d) ∨ (i = d ∧ j = c)
    · simp only [flipPair, if_pos hcd, if_neg hab]
    · simp only [flipPair, if_neg hab, if_neg hcd]

end DirAssignment

/-! ### §15.3 — Graph automorphisms and labelled adjacency (Phase D foundations)

Toward the leaf canonical form and the linear oracle's interface, this
sub-section defines:
* `IsAut π adj` — predicate that a `Fin n`-permutation preserves
  adjacency edge-by-edge.
* `IsAut.id` / `IsAut.comp` / `IsAut.symm` — the group structure
  (identity, composition, inverse).
* `labelledAdj π adj` — the adjacency matrix relabelled by `π`
  (entry `[i][j] = adj.adj (π⁻¹ i) (π⁻¹ j)`).
* `labelledAdj_eq_of_isAut` — automorphisms preserve the labelled
  adjacency (i.e. `labelledAdj π adj = adj.adj`).

**Out of scope this round (deferred to a future Phase D'):**
* `colourRank` (the rank-by-colour bijection on a `Discrete` colouring)
  — needs Finset.sort machinery.
* `SpineChain.canonAdj` (the leaf canonical labelled matrix) — needs
  `colourRank` plus the IsLeaf machinery.
* `canonForm` (lex-min over `DirAssignment`s).
* `LinearOracle` interface (twist discovery from a single branch's
  propagation pattern).

These foundations are what those future pieces will build on. -/

/-- A *graph automorphism* of `adj`: a `Fin n` permutation `π` preserving
adjacency on every edge. -/
def IsAut {n : Nat} (π : Equiv.Perm (Fin n)) (adj : AdjMatrix n) : Prop :=
  ∀ v w, adj.adj (π v) (π w) = adj.adj v w

namespace IsAut

variable {n : Nat} {adj : AdjMatrix n}

/-- The identity permutation is always an automorphism. -/
theorem refl : IsAut (Equiv.refl (Fin n)) adj := fun _ _ => rfl

/-- Composition of automorphisms is an automorphism. -/
theorem trans {π σ : Equiv.Perm (Fin n)}
    (hπ : IsAut π adj) (hσ : IsAut σ adj) : IsAut (π.trans σ) adj := by
  intro v w
  show adj.adj (σ (π v)) (σ (π w)) = adj.adj v w
  rw [hσ, hπ]

/-- The inverse of an automorphism is an automorphism. -/
theorem symm {π : Equiv.Perm (Fin n)}
    (hπ : IsAut π adj) : IsAut π.symm adj := by
  intro v w
  have h := hπ (π.symm v) (π.symm w)
  simp only [Equiv.apply_symm_apply] at h
  exact h.symm

end IsAut

/-- **Labelled adjacency**: relabel the adjacency matrix `adj` by a
permutation `π`. The new `(i, j)` entry is the original adjacency
between `π⁻¹ i` and `π⁻¹ j` — i.e. "vertex at canonical label `i`"
becomes whatever vertex `π⁻¹` maps `i` to. -/
def labelledAdj {n : Nat} (π : Equiv.Perm (Fin n)) (adj : AdjMatrix n) :
    Fin n → Fin n → Nat :=
  fun i j => adj.adj (π.symm i) (π.symm j)

/-- **Automorphisms fix the labelled adjacency.** When `π` is an
automorphism of `adj`, relabelling by `π` produces the same adjacency
matrix back. Equivalently: an automorphism is invisible at the labelled
level. The contrapositive — `labelledAdj π adj ≠ adj.adj → ¬ IsAut π
adj` — is how the descent's verifier rejects non-automorphism candidate
twists. -/
theorem labelledAdj_eq_of_isAut {n : Nat} {adj : AdjMatrix n}
    {π : Equiv.Perm (Fin n)} (h : IsAut π adj) :
    labelledAdj π adj = adj.adj := by
  funext i j
  show adj.adj (π.symm i) (π.symm j) = adj.adj i j
  have key := h (π.symm i) (π.symm j)
  simp only [Equiv.apply_symm_apply] at key
  exact key.symm

/-- **Converse: labelledAdj-equality implies IsAut.** A π that preserves
the labelled adjacency is an automorphism. The two characterisations
match. -/
theorem isAut_of_labelledAdj_eq {n : Nat} {adj : AdjMatrix n}
    {π : Equiv.Perm (Fin n)} (h : labelledAdj π adj = adj.adj) :
    IsAut π adj := by
  intro v w
  have := congrFun (congrFun h (π v)) (π w)
  show adj.adj (π v) (π w) = adj.adj v w
  simp only [labelledAdj, Equiv.symm_apply_apply] at this
  exact this.symm

/-! ### §15.4 — Rank bijection on a Discrete colouring (Phase D' part 1)

For a `Discrete` colouring (every cell singleton), define a canonical
bijection `Fin n → Fin n` that maps each vertex to its rank by colour
value. This is the bridge from "abstract leaf partition" to "concrete
labelling" needed to define the leaf canonical adjacency matrix. -/

namespace Colouring

variable {n : Nat}

/-- Strict rank of vertex `v`: number of vertices `u` with `χ u < χ v`. -/
def vertexRankNat (χ : Colouring n) (v : Fin n) : Nat :=
  (Finset.univ.filter (fun u => χ u < χ v)).card

theorem vertexRankNat_lt_n (χ : Colouring n) (v : Fin n) :
    vertexRankNat χ v < n := by
  show (Finset.univ.filter (fun u => χ u < χ v)).card < n
  have hlt : (Finset.univ.filter (fun u => χ u < χ v)).card
      < (Finset.univ : Finset (Fin n)).card := by
    apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hsub
    have hv : v ∈ Finset.univ.filter (fun u => χ u < χ v) :=
      hsub (Finset.mem_univ v)
    rw [Finset.mem_filter] at hv
    exact lt_irrefl _ hv.2
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by
    rw [Finset.card_univ, Fintype.card_fin]
  omega

/-- Vertex rank as `Fin n`. -/
def vertexRank (χ : Colouring n) (v : Fin n) : Fin n :=
  ⟨vertexRankNat χ v, vertexRankNat_lt_n χ v⟩

/-- Vertex rank is strictly monotonic in the colour value: `χ v < χ w`
implies `vertexRank χ v < vertexRank χ w`. -/
theorem vertexRank_strict_mono (χ : Colouring n) {v w : Fin n}
    (hvw : χ v < χ w) : vertexRank χ v < vertexRank χ w := by
  show vertexRankNat χ v < vertexRankNat χ w
  unfold vertexRankNat
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro u hu
    rw [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, lt_trans hu.2 hvw⟩
  · intro hsub
    have hvf : v ∈ Finset.univ.filter (fun u => χ u < χ w) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hvw⟩
    have hnotv : v ∉ Finset.univ.filter (fun u => χ u < χ v) := by
      rw [Finset.mem_filter]
      intro hh
      exact lt_irrefl _ hh.2
    exact hnotv (hsub hvf)

/-- On a `Discrete` colouring, `vertexRank` is injective. Equal ranks
force equal colour values (via strict monotonicity in both directions),
which forces equal vertices (by `Discrete`). -/
theorem vertexRank_injective (χ : Colouring n) (h : Discrete χ) :
    Function.Injective (vertexRank χ) := by
  intro v w hvw
  by_contra hne
  have hχne : χ v ≠ χ w := fun e => hne (h v w e)
  rcases lt_or_gt_of_ne hχne with hlt | hgt
  · exact absurd hvw (ne_of_lt (vertexRank_strict_mono χ hlt))
  · exact absurd hvw (ne_of_gt (vertexRank_strict_mono χ hgt))

/-- Injective ⇒ bijective on `Fin n → Fin n` (pigeonhole). -/
theorem vertexRank_bijective (χ : Colouring n) (h : Discrete χ) :
    Function.Bijective (vertexRank χ) :=
  Finite.injective_iff_bijective.mp (vertexRank_injective χ h)

/-- **The rank permutation.** Bijection `Fin n ≃ Fin n` mapping each
vertex to its colour-rank. -/
noncomputable def rankPerm (χ : Colouring n) (h : Discrete χ) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective (vertexRank χ) (vertexRank_bijective χ h)

@[simp] theorem rankPerm_apply (χ : Colouring n) (h : Discrete χ) (v : Fin n) :
    rankPerm χ h v = vertexRank χ v := rfl

end Colouring

/-! ### §15.5 — Leaf canonical adjacency (Phase D' part 2)

Bringing together the rank bijection (§15.4) with the spine theorem and
labelled adjacency (§15.3): every chain reaching a leaf, together with
a `DirAssignment`, produces a canonical labelled adjacency matrix.

The leaf's discrete partition is well-defined from `samePartition_chain`
+ `IsLeaf` (any `DirAssignment` refined against the chain's `χι` lands
on a `samePartition`-equal partition, which is `Discrete` iff the chain
is a leaf). The rank bijection on that discrete partition then
canonically labels each vertex by its position in the sorted-by-colour
order; relabelling `adj` by this permutation gives the leaf's
canonical adjacency. -/

/-- **Leaf canonical adjacency.** Given a `SpineChain` reaching a leaf
and a `DirAssignment σ` over the chain's `D`, produce the canonical
labelled adjacency matrix at this leaf.

The procedure:
1. Compute the warm-refined partition `π = warmRefine adj σ.σ chain.χι`.
2. Discharge `Discrete π` via `samePartition_chain` (its partition
   equals the chain's, which is Discrete by `isLeaf`).
3. The rank permutation `rankPerm π _` labels each vertex by its
   colour-rank.
4. `labelledAdj` gives the relabelled adjacency.

Different `DirAssignment`s give different canonical adjacency matrices
in general (the order labels on `D` affect the rank assignment); the
lex-min over `DirAssignment`s is the *canonical form* (`canonForm`,
§15.7 — currently a placeholder). -/
noncomputable def SpineChain.canonAdj {n : Nat} {adj : AdjMatrix n}
    {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} {k : Nat}
    (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D) :
    Fin n → Fin n → Nat :=
  let π := warmRefine adj σ.σ chain.χι
  let hDisc : Discrete π :=
    Discrete.of_samePartition
      (samePartition.symm (DirAssignment.samePartition_chain chain σ)) isLeaf
  labelledAdj (Colouring.rankPerm π hDisc) adj

/-! ### §15.6 — Lex order on matrices (Phase D' part 3) -/

/-- **Row-major lex strict less-than on `n × n` matrices.** `M₁ < M₂`
means: there is a first cell `(i, j)` (lex-ordered by row then column)
where the matrices disagree, and at that cell `M₁ i j < M₂ i j`. -/
def matrixLT {n : Nat} (M₁ M₂ : Fin n → Fin n → Nat) : Prop :=
  ∃ i : Fin n, ∃ j : Fin n,
    (∀ i' : Fin n, i' < i → ∀ j' : Fin n, M₁ i' j' = M₂ i' j') ∧
    (∀ j' : Fin n, j' < j → M₁ i j' = M₂ i j') ∧
    M₁ i j < M₂ i j

/-- `matrixLT` is irreflexive: no matrix is `<` itself. -/
theorem matrixLT_irrefl {n : Nat} (M : Fin n → Fin n → Nat) : ¬ matrixLT M M := by
  rintro ⟨_, _, _, _, hlt⟩
  exact lt_irrefl _ hlt

/-- `matrixLT` is asymmetric: `M₁ < M₂ → ¬ M₂ < M₁`. (Strict order.) -/
theorem matrixLT_asymm {n : Nat} {M₁ M₂ : Fin n → Fin n → Nat}
    (h₁ : matrixLT M₁ M₂) : ¬ matrixLT M₂ M₁ := by
  rintro h₂
  obtain ⟨i₁, j₁, hpre_i₁, hpre_j₁, hlt₁⟩ := h₁
  obtain ⟨i₂, j₂, hpre_i₂, hpre_j₂, hlt₂⟩ := h₂
  -- Two cases: i₁ < i₂, i₁ = i₂, i₁ > i₂.
  rcases lt_trichotomy i₁ i₂ with hi | hi | hi
  · -- i₁ < i₂: at (i₁, j₁), M₂ should equal M₁ (by hpre_i₂), contradicting hlt₁.
    have := hpre_i₂ i₁ hi j₁
    omega
  · -- i₁ = i₂: case on j₁ vs j₂.
    subst hi
    rcases lt_trichotomy j₁ j₂ with hj | hj | hj
    · have := hpre_j₂ j₁ hj
      omega
    · subst hj; omega
    · have := hpre_j₁ j₂ hj
      omega
  · -- i₁ > i₂: at (i₂, j₂), M₁ should equal M₂ (by hpre_i₁), contradicting hlt₂.
    have := hpre_i₁ i₂ hi j₂
    omega

/-! ### §15.7 — Fintype on DirAssignment + canonForm (Phase D' part 4) -/

/-- `PMatrix n = Fin n → Fin n → POE` is `Fintype` because both `Fin n`
and `POE` are. Stated explicitly because `PMatrix` is a `def` (not
`abbrev`), so the instance doesn't transparently inherit from `Pi`. -/
instance PMatrix.fintype {n : Nat} : Fintype (PMatrix n) := by
  unfold PMatrix
  infer_instance

namespace DirAssignment

variable {n : Nat} {P₀ : PMatrix n} {D : Finset (Fin n)}

/-- **`Fintype` instance on `DirAssignment P₀ D`.** The underlying
`PMatrix n = Fin n → Fin n → POE` is `Fintype` (since `POE` is); the
σ-field injection then makes `DirAssignment` itself `Fintype`. The
predicate fields (`antisym`, `agrees_off`) are Props and so add no
inhabitants on top of distinct σ. -/
noncomputable instance fintype : Fintype (DirAssignment P₀ D) :=
  Fintype.ofInjective (fun σ : DirAssignment P₀ D => σ.σ) (by
    intro x y hxy
    apply DirAssignment.eq_of_σ_eq
    intro i j
    exact congrFun (congrFun hxy i) j)

end DirAssignment

/-- **Relabel a matrix** by a permutation: same shape as `labelledAdj`
but works on bare `Fin n → Fin n → Nat` matrices (e.g. the output of
`SpineChain.canonAdj`). Used in `LinearOracleSpec.LeafTwistSpec` to
state the leaf-relabelling property without re-wrapping as an
`AdjMatrix`. -/
def relabelMatrix {n : Nat} (π : Equiv.Perm (Fin n))
    (M : Fin n → Fin n → Nat) : Fin n → Fin n → Nat :=
  fun i j => M (π.symm i) (π.symm j)

/-- **Lex-ordered matrix type.** `Lex (Fin n → Lex (Fin n → Nat))` is
`Fin n → Fin n → Nat` viewed under the row-major lex order. The
`LinearOrder` instance comes automatically from `Pi.Lex.linearOrder`
applied twice (inner: rows are sequences of `Nat`s; outer: matrix is
a sequence of rows). -/
abbrev MatrixLex (n : Nat) := Lex (Fin n → Lex (Fin n → Nat))

/-- Wrap a matrix into its Lex'd form. Identity at runtime (Lex is a
type synonym). -/
def toMatrixLex {n : Nat} (M : Fin n → Fin n → Nat) : MatrixLex n :=
  toLex (fun i => toLex (M i))

/-- Unwrap a Lex'd matrix back to a plain `Fin n → Fin n → Nat`. -/
def ofMatrixLex {n : Nat} (M : MatrixLex n) : Fin n → Fin n → Nat :=
  fun i j => ofLex ((ofLex M) i) j

@[simp] theorem ofMatrixLex_toMatrixLex {n : Nat} (M : Fin n → Fin n → Nat) :
    ofMatrixLex (toMatrixLex M) = M := rfl

@[simp] theorem toMatrixLex_ofMatrixLex {n : Nat} (M : MatrixLex n) :
    toMatrixLex (ofMatrixLex M) = M := rfl

theorem toMatrixLex_injective {n : Nat} :
    Function.Injective (@toMatrixLex n) := by
  intro M₁ M₂ h
  have := congrArg ofMatrixLex h
  simpa using this

/-- The Finset of Lex-wrapped `canonAdj` images over all
`DirAssignment`s. Extracted as a separate def so the spec proofs can
manipulate it cleanly (avoiding `let`-in-body unfolding pain). -/
noncomputable def canonFormImages {n : Nat} {adj : AdjMatrix n}
    {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} {k : Nat}
    (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf) :
    Finset (MatrixLex n) :=
  (Finset.univ : Finset (DirAssignment P₀ chain.D)).image (fun σ =>
    toMatrixLex (chain.canonAdj isLeaf σ))

theorem canonFormImages_nonempty {n : Nat} {adj : AdjMatrix n}
    {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} {k : Nat}
    (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    [hNE : Nonempty (DirAssignment P₀ chain.D)] :
    (canonFormImages chain isLeaf).Nonempty :=
  Finset.image_nonempty.mpr ⟨Classical.choice hNE, Finset.mem_univ _⟩

/-- **`canonForm`**: the canonical leaf adjacency matrix.

This is the **lex-min `canonAdj`** over all `DirAssignment`s. The lex
order is row-major (rows compared first, then columns within a row),
realised via `MatrixLex` and `Finset.min'`. Replaces the earlier
placeholder.

Requires `Nonempty (DirAssignment P₀ chain.D)` so the image is
non-empty. The default instance — `P₀` itself when `P₀` is
antisymmetric — gives this via `DirAssignment.default`.

Spec: `canonForm_mem_image` shows it's `canonAdj σ` for some `σ`;
`canonForm_le_canonAdj` shows it's `≤` every other `canonAdj`. -/
noncomputable def canonForm {n : Nat} {adj : AdjMatrix n}
    {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} {k : Nat}
    (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    [Nonempty (DirAssignment P₀ chain.D)] :
    Fin n → Fin n → Nat :=
  ofMatrixLex ((canonFormImages chain isLeaf).min'
    (canonFormImages_nonempty chain isLeaf))

/-- **`canonForm` comes from some `DirAssignment`.** The lex-min picks
an element of the image, so it equals `canonAdj` of some `σ`. -/
theorem canonForm_mem_image {n : Nat} {adj : AdjMatrix n}
    {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} {k : Nat}
    (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    [Nonempty (DirAssignment P₀ chain.D)] :
    ∃ σ : DirAssignment P₀ chain.D,
      canonForm chain isLeaf = chain.canonAdj isLeaf σ := by
  have h_ne := canonFormImages_nonempty chain isLeaf
  have h_mem := (canonFormImages chain isLeaf).min'_mem h_ne
  obtain ⟨σ, _, hσ⟩ := Finset.mem_image.mp h_mem
  refine ⟨σ, ?_⟩
  unfold canonForm
  rw [← hσ]
  rfl

/-- **`canonForm` is the lex-minimum.** For any `DirAssignment σ`, the
canonical form (in Lex form) is `≤` `canonAdj σ` (in Lex form). The
statement uses `MatrixLex`'s order (= row-major lex). -/
theorem canonForm_le_canonAdj {n : Nat} {adj : AdjMatrix n}
    {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)} {k : Nat}
    (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    [Nonempty (DirAssignment P₀ chain.D)]
    (σ : DirAssignment P₀ chain.D) :
    toMatrixLex (canonForm chain isLeaf) ≤ toMatrixLex (chain.canonAdj isLeaf σ) := by
  have h_σ_mem : toMatrixLex (chain.canonAdj isLeaf σ)
      ∈ canonFormImages chain isLeaf :=
    Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
  have h_min_le := (canonFormImages chain isLeaf).min'_le _ h_σ_mem
  unfold canonForm
  rw [toMatrixLex_ofMatrixLex]
  exact h_min_le

/-! ### §15.8 — Linear oracle interface (Phase D' part 5) -/

/-- **Linear oracle interface type.** Given a chain reaching a leaf and
a `DirAssignment` (the current branch), the linear oracle returns
either `None` (no twist discovered) or `Some` verified automorphism
`π` of `adj`.

The actual implementation — twist discovery from a single branch's
propagation pattern — lives in the C# side (see
`docs/chain-descent-calculator.md` §6). The Lean side just supplies the
interface and the spec.

This type is `Type` rather than `Sort` so the option's `Some` payload
can carry the proof component of the bundled subtype. -/
def LinearOracleSpec {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) : Type :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k), chain.IsLeaf →
    DirAssignment P₀ chain.D →
    Option { π : Equiv.Perm (Fin n) // IsAut π adj }

namespace LinearOracleSpec

variable {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
  {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}

/-- **Soundness (subtype-level).** When the oracle returns `some
result`, the returned permutation is an automorphism. This is
*automatic* from the bundled subtype — recorded as a theorem for
clarity. The stronger validity (that the returned `π` actually relates
the branch's leaf to another leaf, justifying pruning) is captured
by `LeafTwistSpec` below. -/
theorem some_isAut (oracle : LinearOracleSpec adj P₀ χι₀ sel)
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D)
    {result : { π : Equiv.Perm (Fin n) // IsAut π adj }}
    (_ : oracle chain isLeaf σ = some result) :
    IsAut result.val adj :=
  result.property

/-- **Leaf-twist validity.** When the oracle returns `some result`, the
returned `π` relates the input branch `σ`'s canonical adjacency to
*some other* `DirAssignment σ'`'s canonical adjacency via the
labelled-relabelling action. Concretely: `labelledAdj π (canonAdj σ) =
canonAdj σ'`. This is the property that justifies *pruning*: the two
branches give the same canonical form modulo a known automorphism.

The existence of `σ'` is the existential content; the oracle's actual
implementation should produce it constructively, but the Lean spec
quantifies existentially because the discovery algorithm is out of
scope. -/
def LeafTwistSpec (oracle : LinearOracleSpec adj P₀ χι₀ sel) : Prop :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (isLeaf : chain.IsLeaf)
    (σ : DirAssignment P₀ chain.D)
    (result : { π : Equiv.Perm (Fin n) // IsAut π adj }),
    oracle chain isLeaf σ = some result →
    ∃ σ' : DirAssignment P₀ chain.D,
      relabelMatrix result.val (chain.canonAdj isLeaf σ) = chain.canonAdj isLeaf σ'

end LinearOracleSpec

/-! ## §16 — Orbit recovery: shared infrastructure

The orbit-recovery program ([`docs/chain-descent-orbit-recovery.md`](../docs/chain-descent-orbit-recovery.md))
states that for "nice enough" graphs, 1-WL refinement after sufficient
fresh-colour individualization recovers `Aut_S`-orbits. This section
develops the **tier-agnostic** machinery the program rests on:

- Fresh-colour individualization and the pointwise stabilizer predicate
  (§16.1).
- Automorphisms preserve refinement (§16.2). The key lifting lemma.
- The orbit partition predicate `OrbitPartition` and the **trivial
  direction** `orbits ⊆ 1-WL cells` (§16.3). Always true; the
  load-bearing half of the squeeze used by both tiers.

Tier-specific assemblies live downstream:
- §17 — Tier 1 (CFI graphs): squeeze via "warmRefine is discrete at the
  cascade depth" + Fact B (`aut_trivial_of_discrete_warmRefine`).
- §18 — Tier 2 (schurian scheme graphs): squeeze via "warmRefine equals
  the scheme profile partition at depth 1" + "profile partition equals
  Aut_v orbits".

The squeeze framing common to both tiers:
```
OrbitPartition ⊆ samePartition (warmRefine adj P χ_S) ⊆ TargetPartition
```
- §16.3 gives the left inclusion (always true).
- The right inclusion is tier-specific: discrete (Tier 1), or scheme
  profile partition (Tier 2). Combined with `OrbitPartition ⊇
  TargetPartition` (Fact B / Step 1 in the paper proofs), the squeeze
  yields equality.
-/

/-! ### §16.1 — Fresh-colour individualization and pointwise stabilizer -/

/-- **Fresh-colour individualization** of a vertex set `S`. Each `v ∈ S`
gets a unique colour `v.val + 1`; vertices outside `S` share colour `0`.
The `+1` keeps `0` reserved for the non-individualized cell. -/
def individualizedColouring (n : Nat) (S : Finset (Fin n)) : Colouring n :=
  fun v => if v ∈ S then v.val + 1 else 0

/-- A permutation `π` *fixes `S` pointwise* iff `π v = v` for every `v ∈ S`. -/
def FixesPointwise {n : Nat} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    Prop :=
  ∀ v ∈ S, π v = v

namespace FixesPointwise

variable {n : Nat} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)}

/-- A permutation fixing `S` pointwise also stabilizes the complement setwise.
For `v ∉ S`, we have `π v ∉ S` — otherwise `π (π v) = π v` (by pointwise
fix) forces `π v = v` by injectivity, contradicting `v ∉ S`. -/
theorem complement (hπ : FixesPointwise π S) {v : Fin n} (hv : v ∉ S) :
    π v ∉ S := by
  intro hπv
  have hfix : π (π v) = π v := hπ (π v) hπv
  have heq : π v = v := π.injective hfix
  exact hv (heq ▸ hπv)

end FixesPointwise

/-- An automorphism fixing `S` pointwise preserves the individualized
colouring `χ_S`: `χ_S (π v) = χ_S v` for every `v`. -/
theorem individualizedColouring_invariant {n : Nat} {S : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπS : FixesPointwise π S) (v : Fin n) :
    individualizedColouring n S (π v) = individualizedColouring n S v := by
  unfold individualizedColouring
  by_cases hv : v ∈ S
  · rw [hπS v hv]
  · have hπv : π v ∉ S := hπS.complement hv
    simp [hv, hπv]

/-! ### §16.2 — Automorphisms preserve refinement -/

/-- An automorphism that preserves `(adj, P, χ)` pointwise preserves the
signature multiset for every vertex.

The proof reindexes the signature's underlying multiset along `π`: the
multiset over `u ≠ π v` of `(χ u, adj (π v) u, P (π v) u)` equals the
multiset over `u' ≠ v` of `(χ (π u'), adj (π v) (π u'), P (π v) (π u'))`,
which by the three invariance hypotheses equals the multiset over
`u' ≠ v` of `(χ u', adj v u', P v u')` = `signature adj P χ v`. -/
theorem signature_invariant_of_isAut {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {χ : Colouring n} {π : Equiv.Perm (Fin n)}
    (hπ : IsAut π adj) (hP : ∀ v u, P (π v) (π u) = P v u)
    (hχ : ∀ v, χ (π v) = χ v) (v : Fin n) :
    signature adj P χ (π v) = signature adj P χ v := by
  unfold signature
  -- Reindex the filtered multiset along π: u ranges over `univ.filter (· ≠ π v)`
  -- iff `u = π u'` for u' ranging over `univ.filter (· ≠ v)`.
  have key : (Finset.univ : Finset (Fin n)).filter (· ≠ π v) =
      ((Finset.univ : Finset (Fin n)).filter (· ≠ v)).map π.toEmbedding := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
               Equiv.coe_toEmbedding]
    constructor
    · intro hu
      refine ⟨π.symm u, ?_, π.apply_symm_apply u⟩
      intro h
      apply hu
      rw [← h, π.apply_symm_apply]
    · rintro ⟨u', hu', rfl⟩
      intro h
      exact hu' (π.injective h)
  rw [key, Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro u' _
  simp only [Function.comp_apply, Equiv.coe_toEmbedding]
  -- Show pointwise equality of the tuple `(χ (π u'), adj (π v) (π u'), P (π v) (π u'))`
  -- with `(χ u', adj v u', P v u')` via the three invariance hypotheses.
  refine Prod.mk.injEq .. |>.mpr ⟨hχ u', ?_⟩
  refine Prod.mk.injEq .. |>.mpr ⟨hπ v u', hP v u'⟩

/-- An automorphism that preserves `(adj, P, χ)` pointwise preserves
`refineStep`. Follows from signature invariance via `refineStep_iff`. -/
theorem refineStep_invariant_of_isAut {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {χ : Colouring n} {π : Equiv.Perm (Fin n)}
    (hπ : IsAut π adj) (hP : ∀ v u, P (π v) (π u) = P v u)
    (hχ : ∀ v, χ (π v) = χ v) (v : Fin n) :
    refineStep adj P χ (π v) = refineStep adj P χ v := by
  -- Two vertices have the same refined colour iff (same old colour, same
  -- signature). For π v and v: old colours equal by hχ; signatures equal
  -- by signature_invariant_of_isAut. Hence refined colours equal.
  have hχπ : χ (π v) = χ v := hχ v
  have hσ : signature adj P χ (π v) = signature adj P χ v :=
    signature_invariant_of_isAut hπ hP hχ v
  exact ((refineStep_iff adj P χ (π v) v).mpr ⟨hχπ, hσ⟩)

/-- Iterating refinement preserves the invariance: `(refineStep)^[k] χ` is
also `π`-invariant when the inputs are. -/
theorem iterate_refineStep_invariant_of_isAut {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {π : Equiv.Perm (Fin n)}
    (hπ : IsAut π adj) (hP : ∀ v u, P (π v) (π u) = P v u) :
    ∀ (k : Nat) {χ : Colouring n}, (∀ v, χ (π v) = χ v) →
      ∀ v, ((refineStep adj P)^[k]) χ (π v) = ((refineStep adj P)^[k]) χ v := by
  intro k
  induction k with
  | zero => intro χ hχ v; exact hχ v
  | succ k ih =>
    intro χ hχ v
    simp only [Function.iterate_succ, Function.comp_apply]
    -- Need to show invariance after one refineStep, then iterate ih on it.
    have hχ' : ∀ v, refineStep adj P χ (π v) = refineStep adj P χ v :=
      refineStep_invariant_of_isAut hπ hP hχ
    exact ih hχ' v

/-- Warm refinement preserves the invariance: if `(adj, P, χ_init)` are all
`π`-invariant (with `π` an automorphism), then `warmRefine adj P χ_init` is
also `π`-invariant. -/
theorem warmRefine_invariant_of_isAut {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {χ : Colouring n} {π : Equiv.Perm (Fin n)}
    (hπ : IsAut π adj) (hP : ∀ v u, P (π v) (π u) = P v u)
    (hχ : ∀ v, χ (π v) = χ v) (v : Fin n) :
    warmRefine adj P χ (π v) = warmRefine adj P χ v := by
  unfold warmRefine
  exact iterate_refineStep_invariant_of_isAut hπ hP n hχ v

/-! ### §16.3 — Orbit partition and the trivial direction

`OrbitPartition adj P S` is the equivalence relation on `Fin n` defined
by "some automorphism of `adj` preserving `P` and fixing `S` pointwise
maps `v` to `w`." It is the partition-level expression of "1-WL cells
contain Aut_S orbits."

The **trivial direction** (`OrbitPartition.subset_warmRefine`) says
this relation refines the 1-WL fixpoint partition: every Aut_S-orbit
lies inside a single 1-WL cell. This is always true and follows
directly from `warmRefine_invariant_of_isAut`. It is the load-bearing
half of the squeeze that both Tier 1 and Tier 2 use to conclude
"cells = orbits." -/

/-- **Aut_S orbit relation.** `v ~ w` iff some automorphism of `adj`
preserving `P` and fixing `S` pointwise maps `v` to `w`. -/
def OrbitPartition {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (S : Finset (Fin n)) (v w : Fin n) : Prop :=
  ∃ π : Equiv.Perm (Fin n),
    IsAut π adj ∧ (∀ x u, P (π x) (π u) = P x u) ∧
    FixesPointwise π S ∧ π v = w

namespace OrbitPartition

variable {n : Nat} {adj : AdjMatrix n} {P : PMatrix n} {S : Finset (Fin n)}

/-- Reflexivity: every vertex is in its own orbit (via the identity
permutation). -/
theorem refl (v : Fin n) : OrbitPartition adj P S v v :=
  ⟨Equiv.refl _, IsAut.refl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

/-- Symmetry: orbit equivalence is symmetric (via permutation inverse). -/
theorem symm {v w : Fin n} (h : OrbitPartition adj P S v w) :
    OrbitPartition adj P S w v := by
  obtain ⟨π, hπ, hP, hπS, hvw⟩ := h
  refine ⟨π.symm, hπ.symm, ?_, ?_, ?_⟩
  · intro x u
    have h := hP (π.symm x) (π.symm u)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm
  · intro v' hv'
    have hfix := hπS v' hv'
    -- π v' = v', so π.symm v' = v'.
    have := congrArg π.symm hfix
    simpa using this.symm
  · have := congrArg π.symm hvw
    simpa using this.symm

/-- Transitivity: orbit equivalence composes (via permutation composition). -/
theorem trans {v w u : Fin n}
    (h₁ : OrbitPartition adj P S v w) (h₂ : OrbitPartition adj P S w u) :
    OrbitPartition adj P S v u := by
  obtain ⟨π₁, hπ₁, hP₁, hπS₁, hvw⟩ := h₁
  obtain ⟨π₂, hπ₂, hP₂, hπS₂, hwu⟩ := h₂
  refine ⟨π₁.trans π₂, hπ₁.trans hπ₂, ?_, ?_, ?_⟩
  · intro x u'
    -- (π₁.trans π₂) x = π₂ (π₁ x)
    show P (π₂ (π₁ x)) (π₂ (π₁ u')) = P x u'
    rw [hP₂, hP₁]
  · intro v' hv'
    show π₂ (π₁ v') = v'
    rw [hπS₁ v' hv', hπS₂ v' hv']
  · show π₂ (π₁ v) = u
    rw [hvw]; exact hwu

/-- **The trivial direction: orbits refine 1-WL cells.** If `v` and `w` are
in the same Aut_S orbit, they share a cell in `warmRefine adj P χ_S`.

This is the always-true half of the squeeze. Both Tier 1 (CFI) and
Tier 2 (scheme graphs) combine this with a tier-specific bound on the
1-WL cells to conclude `OrbitPartition = warmRefine partition`. -/
theorem subset_warmRefine {v w : Fin n} (h : OrbitPartition adj P S v w) :
    warmRefine adj P (individualizedColouring n S) v =
      warmRefine adj P (individualizedColouring n S) w := by
  obtain ⟨π, hπ, hP, hπS, hvw⟩ := h
  have hχ : ∀ x, individualizedColouring n S (π x) = individualizedColouring n S x :=
    individualizedColouring_invariant hπS
  have hwarm := warmRefine_invariant_of_isAut hπ hP hχ v
  -- warmRefine ... (π v) = warmRefine ... v, and π v = w.
  rw [hvw] at hwarm
  exact hwarm.symm

end OrbitPartition

/-! ## §17 — Tier 1: orbit recovery for CFI graphs

Formalisation of Theorem 1 of [`docs/chain-descent-orbit-recovery.md`](../docs/chain-descent-orbit-recovery.md):
for connected `CFI(H)`, 1-WL refinement after `≤ tw(H)` fresh-colour
individualizations recovers the `Aut(CFI(H))_S`-orbit partition.

**Proof structure** (orbit-recovery doc §5):
- **Fact A** — CFI cascade depth ≤ tw(H). Classical Cai-Fürer-Immerman
  1992. Requires CFI construction in Lean (a multi-week infrastructure
  project); stated here as an `axiom` placeholder so the assembly can
  proceed.
- **Fact B** — discrete partition ⟹ `Aut_S` is trivial ⟹ cells = orbits.
  Provable from §16's shared infrastructure.
- **Assembly** — at the cascade depth, partition is discrete (Fact A),
  so cells = orbits (Fact B + §16.3 trivial direction).

Sub-sections:
- §17.1 — Fact B (discrete ⟹ trivial Aut_S; cells = orbits)
- §17.2 — Fact A placeholder + Theorem 1 assembly
-/

/-! ### §17.1 — Fact B: discrete partition ⟹ trivial Aut_S -/

/-- **Fact B (pointwise version).** If a `π`-invariant colouring `χ` is
discrete (every cell singleton), then `π` is the identity. -/
theorem id_of_discrete_invariant {n : Nat} {χ : Colouring n}
    {π : Equiv.Perm (Fin n)} (hd : Discrete χ)
    (hχ : ∀ v, χ (π v) = χ v) :
    π = Equiv.refl (Fin n) := by
  apply Equiv.ext
  intro v
  -- χ (π v) = χ v, so by discreteness π v = v.
  exact hd (π v) v (hχ v)

/-- **Fact B (CFI version).** Let `adj`, `P` be a graph state and `S` an
individualized vertex set. If `warmRefine adj P χ_S` is discrete, then every
automorphism of `adj` that preserves `P` and fixes `S` pointwise is the
identity. -/
theorem aut_trivial_of_discrete_warmRefine {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {S : Finset (Fin n)}
    (hd : Discrete (warmRefine adj P (individualizedColouring n S)))
    {π : Equiv.Perm (Fin n)}
    (hπ : IsAut π adj) (hP : ∀ v u, P (π v) (π u) = P v u)
    (hπS : FixesPointwise π S) :
    π = Equiv.refl (Fin n) := by
  have hχ : ∀ v, individualizedColouring n S (π v) = individualizedColouring n S v :=
    individualizedColouring_invariant hπS
  have hwarm : ∀ v, warmRefine adj P (individualizedColouring n S) (π v) =
      warmRefine adj P (individualizedColouring n S) v :=
    warmRefine_invariant_of_isAut hπ hP hχ
  exact id_of_discrete_invariant hd hwarm

/-- **Fact B (partition version).** At discrete depth, the orbit partition
collapses to equality of vertices — the reverse direction of the squeeze.

If `warmRefine adj P χ_S` is discrete, then `OrbitPartition v w ↔ v = w`.
Combined with §16.3's trivial direction, this gives `OrbitPartition v w ↔
warmRefine ... v = warmRefine ... w` for the Tier 1 cascade-discrete case. -/
theorem orbit_iff_eq_of_discrete_warmRefine {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {S : Finset (Fin n)}
    (hd : Discrete (warmRefine adj P (individualizedColouring n S)))
    (v w : Fin n) :
    OrbitPartition adj P S v w ↔ v = w := by
  constructor
  · intro h
    obtain ⟨π, hπ, hP, hπS, hvw⟩ := h
    have hπ_id := aut_trivial_of_discrete_warmRefine hd hπ hP hπS
    rw [← hvw, hπ_id]
    rfl
  · rintro rfl
    exact OrbitPartition.refl v

/-! ### §17.2 — The `CascadesAt` predicate

The orbit-recovery program's Tier-1 hypothesis "warmRefine becomes
discrete after some `S`" is, on its own, **trivially true for every
graph** — take `S = univ`, every vertex gets a unique fresh colour, and
warm refinement preserves discreteness. So the existential statement
carries no CFI-specific content.

The interesting content is the **depth at which discreteness is
reached**. We make depth explicit as a parameter `k`:

> `CascadesAt adj P k` iff some `S` with `|S| ≤ k` yields a discrete
> warmRefine.

The orbit-recovery doc notes that **any polynomial bound on `|S|`
preserves polynomial runtime** for chain descent (Corollary 1) — so
the chain-descent polynomial argument only needs `CascadesAt adj P (p
n)` for some polynomial `p`. The classical CFI cascade content is
`|S| ≤ tw(H)`; we capture that abstractly in §17.4 below. -/

/-- **Cascade at depth `k`**: some `S` with `|S| ≤ k` makes `warmRefine`
discrete. Every graph satisfies `CascadesAt adj P n` trivially
(`cascadesAt_univ`); the interesting case is `k` polynomial in `n` and
strictly less than `n` for special families (CFI: `k ≤ tw(H)`). -/
def CascadesAt {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) (k : Nat) : Prop :=
  ∃ S : Finset (Fin n),
    S.card ≤ k ∧
    Discrete (warmRefine adj P (individualizedColouring n S))

/-- **Trivial cascade at depth `n`.** Take `S = univ`: each vertex gets
a unique fresh colour `v.val + 1`, the initial colouring is discrete,
and warm refinement preserves discreteness. This is the "every-graph
fallback" — non-content in itself; the polynomial-depth claim is
non-trivial only when `k < n`. -/
theorem cascadesAt_univ {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) :
    CascadesAt adj P n := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · rw [Finset.card_univ, Fintype.card_fin]
  · apply Discrete.warmRefine_preserves
    intro i j hij
    -- individualizedColouring n univ assigns each v the colour v.val + 1.
    have hi : (i : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
    have hj : (j : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
    have hci : individualizedColouring n Finset.univ i = i.val + 1 := by
      simp [individualizedColouring, hi]
    have hcj : individualizedColouring n Finset.univ j = j.val + 1 := by
      simp [individualizedColouring, hj]
    rw [hci, hcj] at hij
    exact Fin.ext (Nat.succ_injective hij)

/-- Monotonicity: a cascade at depth `k` is a cascade at every depth `≥ k`. -/
theorem CascadesAt.mono {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {k₁ k₂ : Nat} (hle : k₁ ≤ k₂) (h : CascadesAt adj P k₁) :
    CascadesAt adj P k₂ := by
  obtain ⟨S, hcard, hd⟩ := h
  exact ⟨S, Nat.le_trans hcard hle, hd⟩

/-! ### §17.3 — Theorem 1 (depth-parameterised, unconditional)

Given a cascade hypothesis at depth `k`, the squeeze argument
(§16.3 trivial direction + §17.1 Fact B) gives orbit recovery at
`|S| ≤ k`. No axioms beyond the standard `refineStep` basis — all
CFI specificity has been pushed into the `CascadesAt` hypothesis.

This is the structural Theorem 1. Tier-1 specialisations
(`theorem_1_HOR_at_n`, `theorem_1_HOR_cfi`) instantiate the cascade
hypothesis from different sources (trivial bound vs. CFI axiom). -/

/-- **Theorem 1 (depth-parametrised, unconditional).** If `adj`
cascades at depth `k`, the 1-WL fixpoint partition equals the Aut_S
orbit partition at some `S` with `|S| ≤ k`.

This is the load-bearing theorem of Tier 1. The CFI-specific
content lives in the cascade hypothesis. -/
theorem theorem_1_HOR_at_depth {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {k : Nat} (h : CascadesAt adj P k) :
    ∃ S : Finset (Fin n),
      S.card ≤ k ∧
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      ∀ v w,
        OrbitPartition adj P S v w ↔
        warmRefine adj P (individualizedColouring n S) v =
          warmRefine adj P (individualizedColouring n S) w := by
  obtain ⟨S, hcard, hd⟩ := h
  refine ⟨S, hcard, hd, ?_⟩
  intro v w
  constructor
  · exact OrbitPartition.subset_warmRefine
  · intro hχ
    have hvw : v = w := hd v w hχ
    rw [hvw]
    exact OrbitPartition.refl w

/-! ### §17.4 — Specialisations and the CFI placeholder axioms

The Tier-1 theorem in three forms:
- **Trivial-bound form** (`theorem_1_HOR_at_n`): every graph admits
  orbit recovery at depth `n`. Axiom-free; not informative on its
  own but useful as a smoke-test.
- **Legacy form** (`theorem_1_HOR`): existential, no depth bound.
  Axiom-free corollary of `theorem_1_HOR_at_n`.
- **CFI polynomial-depth form** (`theorem_1_HOR_cfi`): conditional
  on the CFI placeholder axioms. The actual deliverable for
  Corollary 1 of the orbit-recovery doc.

The CFI axioms mirror the Tier 2 (§18) structure: an abstract Prop
predicate `IsCFI` (placeholder until CFI infrastructure lands) plus a
single Fact-A-shaped existence axiom relating `IsCFI` to a polynomial
cascade depth. -/

/-- **Theorem 1, trivial-bound corollary.** Every graph admits orbit
recovery at depth `n`. Axiom-free; specialises
`theorem_1_HOR_at_depth` to the universal `cascadesAt_univ`. -/
theorem theorem_1_HOR_at_n {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) :
    ∃ S : Finset (Fin n),
      S.card ≤ n ∧
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      ∀ v w,
        OrbitPartition adj P S v w ↔
        warmRefine adj P (individualizedColouring n S) v =
          warmRefine adj P (individualizedColouring n S) w :=
  theorem_1_HOR_at_depth (cascadesAt_univ adj P)

/-- **Theorem 1 (legacy existential form).** No depth bound; some `S`
makes `warmRefine` discrete and orbits = cells. Axiom-free corollary
of `theorem_1_HOR_at_n`; kept for downstream use. -/
theorem theorem_1_HOR {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) :
    ∃ S : Finset (Fin n),
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      ∀ v w,
        OrbitPartition adj P S v w ↔
        warmRefine adj P (individualizedColouring n S) v =
          warmRefine adj P (individualizedColouring n S) w := by
  obtain ⟨S, _, hd, hpart⟩ := theorem_1_HOR_at_n adj P
  exact ⟨S, hd, hpart⟩

/-- **Theorem 1, pointwise corollary.** Aut_S is trivial at the cascade
depth. Axiom-free corollary of `theorem_1_HOR_at_n` +
`aut_trivial_of_discrete_warmRefine`. -/
theorem theorem_1_HOR_pointwise {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) :
    ∃ S : Finset (Fin n),
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      ∀ (π : Equiv.Perm (Fin n)),
        IsAut π adj → (∀ v u, P (π v) (π u) = P v u) →
        FixesPointwise π S → π = Equiv.refl (Fin n) := by
  obtain ⟨S, _, hd, _⟩ := theorem_1_HOR_at_n adj P
  refine ⟨S, hd, ?_⟩
  intro π hπ hP hπS
  exact aut_trivial_of_discrete_warmRefine hd hπ hP hπS

/-! #### CFI placeholder axioms — polynomial-depth Fact A

Three axioms, mirroring §18's Tier 2 structure:

- `IsCFI adj` — abstract Prop placeholder for "the graph is a CFI
  graph." No introduction rule until CFI infrastructure lands.
- `cfi_depth_bound : Nat → Nat` + `cfi_depth_bound_le` — abstract
  polynomial cascade-depth function for CFI, asserting `cfi_depth_bound
  n ≤ n` as the (placeholder) polynomial relation. Classical content:
  `cfi_depth_bound n = tw(H)` for `adj = CFI(H)`, often much smaller
  than `n`.
- `cfi_cascades_polynomially` — the Tier-1 Fact A. Asserts a CFI
  graph cascades at depth `cfi_depth_bound n`. Becomes a theorem once
  CFI infrastructure lands.

Concrete (non-placeholder) realisations would tighten
`cfi_depth_bound n ≤ n` to a meaningful polynomial relation (e.g.,
`cfi_depth_bound n = tw H` where `n = |V(CFI(H))|` and the polynomial
relation comes from `tw H ≤ n_H ≤ n`). -/

/-- **Abstract Prop: the graph `adj` is a CFI graph.** Placeholder
until CFI construction lands in Lean (~200-400 lines; G5 of
orbit-recovery doc). Mirrors `IsSchurianSchemeGraph` in §18. -/
axiom IsCFI {n : Nat} (adj : AdjMatrix n) : Prop

/-- **Abstract polynomial cascade-depth function for CFI graphs.** A
function `Nat → Nat` representing the classical bound `tw(H) ≤ n_H ≤ n`
for `adj = CFI(H)`. Concrete realisation requires CFI infrastructure. -/
axiom cfi_depth_bound : Nat → Nat

/-- **The CFI depth bound is `≤ n`** — the placeholder polynomial
relation. The classical content `tw H ≤ n` (where `H` is the CFI base
graph) gives this trivially. -/
axiom cfi_depth_bound_le : ∀ n, cfi_depth_bound n ≤ n

/-- **Fact A (polynomial-depth form, placeholder).** A CFI graph
cascades at depth `cfi_depth_bound n`. Becomes a theorem once
`cfi_depth_bound` is given a concrete realisation (`tw H`) and CFI
infrastructure makes the cascade lemma provable. -/
axiom cfi_cascades_polynomially {n : Nat} {adj : AdjMatrix n}
    (h : IsCFI adj) (P : PMatrix n) :
    CascadesAt adj P (cfi_depth_bound n)

/-- **Theorem 1 (CFI form, polynomial-depth).** A CFI graph admits
orbit recovery at depth `cfi_depth_bound n ≤ n`. Conditional on the
Tier-1 placeholder axioms (`IsCFI`, `cfi_cascades_polynomially`). -/
theorem theorem_1_HOR_cfi {n : Nat} {adj : AdjMatrix n}
    (h : IsCFI adj) (P : PMatrix n) :
    ∃ S : Finset (Fin n),
      S.card ≤ cfi_depth_bound n ∧
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      ∀ v w,
        OrbitPartition adj P S v w ↔
        warmRefine adj P (individualizedColouring n S) v =
          warmRefine adj P (individualizedColouring n S) w :=
  theorem_1_HOR_at_depth (cfi_cascades_polynomially h P)

/-! ## §18 — Tier 2: orbit recovery for schurian scheme graphs

Formalisation of Theorem 2 of [`docs/chain-descent-orbit-recovery.md`](../docs/chain-descent-orbit-recovery.md):
for a graph admitting a vertex-transitive schurian association scheme,
1-WL refinement after a **single** fresh-colour individualization
recovers the `Aut_v`-orbit partition.

The paper proof (orbit-recovery doc §14.3) routes through:
- **Step 1** — schurian assumption ⟹ `Aut(G)_v` orbits = v-profile
  classes (scheme-relation classes relative to `v`).
- **Step 2** — 1-WL on `(G, v)` distinguishes v-profile classes (the
  intersection-number argument).
- **Step 3** — combine.

Lean structure mirrors Tier 1 (§17):
- §18.1 — `SchemeProfile` structure bundling Steps 1 and 2 as fields.
- §18.2 — Scheme profile existence axiom + Theorem 2 assembly.

The full association-scheme machinery (relations `R_0,…,R_d`,
intersection numbers, schurian property) is not yet in Mathlib —
multi-week infrastructure work tracked as G5 in the orbit-recovery
doc §14.5. Here we axiomatise the existence of a `SchemeProfile` so
the assembly can proceed, exactly as Tier 1 axiomatises
`cfi_cascade_exists`.

Once the scheme infrastructure lands, `schurian_scheme_profile_exists`
becomes a theorem — the SchemeProfile fields are constructible from
the scheme's intersection numbers and the schurian orbit identity.
-/

/-! ### §18.1 — `SchemeProfile`: the v-profile partition

A `SchemeProfile adj P v` is a colouring `profile : Colouring n`
that represents the **v-profile** (which scheme relation each w ≠ v
shares with v, relative to a fixed association scheme on `adj`),
together with two structural facts:

- **Step 1 field (`profile_iff_orbit`)**: profile classes coincide
  with Aut_v orbits. This is the schurian assumption's content —
  scheme-relation classes are exactly Aut-orbital classes.
- **Step 2 field (`warm_refines_profile`)**: 1-WL refinement on
  `(adj, P, χ_{v})` is at least as fine as the profile partition
  (i.e., cells ⊆ profile classes). This is the intersection-number
  argument.

The reverse inclusion (`profile classes ⊆ 1-WL cells`) follows
from §16.3's trivial direction plus the Step 1 field, so the
structure does not need to bundle it explicitly. Derived in
`SchemeProfile.warm_iff_profile`. -/
structure SchemeProfile {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (v : Fin n) where
  /-- The v-profile colouring: encodes which scheme relation each w
  shares with v. -/
  profile : Colouring n
  /-- `v` is a singleton in the profile partition. -/
  v_singleton : ∀ w, w ≠ v → profile w ≠ profile v
  /-- **Step 1 (schurian).** Profile classes equal Aut_v orbits. -/
  profile_iff_orbit :
    ∀ w u, profile w = profile u ↔ OrbitPartition adj P {v} w u
  /-- **Step 2 (intersection numbers).** 1-WL on (adj, P, χ_{v}) refines
  the profile partition. -/
  warm_refines_profile :
    ∀ w u,
      warmRefine adj P (individualizedColouring n {v}) w =
        warmRefine adj P (individualizedColouring n {v}) u →
      profile w = profile u

namespace SchemeProfile

variable {n : Nat} {adj : AdjMatrix n} {P : PMatrix n} {v : Fin n}

/-- **Squeeze: 1-WL fixpoint partition equals profile partition.**

The "←" direction comes from §16.3's trivial direction (orbits refine
1-WL cells) composed with Step 1 (orbits = profile classes). The "→"
direction is the Step 2 field directly. -/
theorem warm_iff_profile (sp : SchemeProfile adj P v) (w u : Fin n) :
    warmRefine adj P (individualizedColouring n {v}) w =
      warmRefine adj P (individualizedColouring n {v}) u ↔
    sp.profile w = sp.profile u := by
  constructor
  · exact sp.warm_refines_profile w u
  · intro h
    have horb := (sp.profile_iff_orbit w u).mp h
    exact OrbitPartition.subset_warmRefine horb

end SchemeProfile

/-! ### §18.2 — Existence axiom + Theorem 2 assembly

The existence of a `SchemeProfile` is the load-bearing axiom for
Tier 2 — the analogue of Tier 1's `cfi_cascade_exists`. It
encapsulates "this graph is a vertex-transitive schurian scheme
graph" without committing to a particular formalisation of
association schemes.

`IsSchurianSchemeGraph` is left as an `axiom`-declared Prop: a
constant predicate with no introduction rule. Concrete graphs
(Johnson `J(m,k)`, Hamming `H(d,q)`, distance-transitive DRGs) will
satisfy it once the scheme infrastructure provides a real
definition; for now no graph satisfies it, so the existence axiom
is dormant — it constrains nothing until a real
`IsSchurianSchemeGraph` proof appears. -/

/-- **Abstract predicate.** Placeholder for "the graph `adj` admits a
vertex-transitive schurian association scheme that contains its edge
relation." Declared as an axiom-Prop until the scheme machinery
lands; full formalization is G5 of the orbit-recovery doc. -/
axiom IsSchurianSchemeGraph {n : Nat} (adj : AdjMatrix n) : Prop

/-- **Scheme profile existence (Tier 2 Fact A analogue).** For any
graph satisfying `IsSchurianSchemeGraph` and any vertex `v`, a
`SchemeProfile adj P v` exists. The witness encodes:
- the v-profile colouring (which scheme relation each w ≠ v shares
  with v);
- the schurian identity (profile classes = Aut_v orbits);
- the intersection-number lemma (1-WL refines profile).

Becomes a theorem once association-scheme infrastructure lands. -/
axiom schurian_scheme_profile_exists {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph adj) (P : PMatrix n) (v : Fin n) :
    Nonempty (SchemeProfile adj P v)

/-- **Theorem 2 (HOR for schurian scheme graphs), assembly form.**

Given a SchemeProfile witness at vertex `v`, the 1-WL fixpoint
partition (at depth 1) equals the Aut_v orbit partition.

This is the assembly version — the actual content is the existence
of a SchemeProfile (`schurian_scheme_profile_exists`). Once we have a
witness, the equality follows from chaining the two iff-fields. -/
theorem theorem_2_HOR_of_profile {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {v : Fin n} (sp : SchemeProfile adj P v)
    (w u : Fin n) :
    OrbitPartition adj P {v} w u ↔
      warmRefine adj P (individualizedColouring n {v}) w =
        warmRefine adj P (individualizedColouring n {v}) u :=
  -- OrbitPartition ↔ profile (Step 1 backwards), then profile ↔ warmRefine
  -- (sp.warm_iff_profile backwards).
  (sp.profile_iff_orbit w u).symm.trans (sp.warm_iff_profile w u).symm

/-- **Theorem 2 (HOR for schurian scheme graphs), unconditional form.**

For any graph satisfying `IsSchurianSchemeGraph`, the 1-WL fixpoint
partition at depth 1 equals the Aut_v orbit partition.

Conditional on `schurian_scheme_profile_exists` (the Tier-2 Fact A
analogue). The Lean theorem becomes unconditional once the scheme
infrastructure provides a constructive witness. -/
theorem theorem_2_HOR {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph adj) (P : PMatrix n) (v : Fin n) :
    ∀ w u,
      OrbitPartition adj P {v} w u ↔
        warmRefine adj P (individualizedColouring n {v}) w =
          warmRefine adj P (individualizedColouring n {v}) u := by
  obtain ⟨sp⟩ := schurian_scheme_profile_exists h P v
  intro w u
  exact theorem_2_HOR_of_profile sp w u

