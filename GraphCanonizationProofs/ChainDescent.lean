import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.FinRange
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

/-! ### M3 — exchange (load-bearing, open)

The matroid exchange axiom: if `y` is forced by `S ∪ {x}` but not by `S` alone,
then `x` is forced by `S ∪ {y}` but not by `S` alone. This is the "if `x`
determines `y` then `y` determines `x`" symmetry — operating against an
arbitrary background `S`.

Per [`docs/chain-descent-matroid.md`](../docs/chain-descent-matroid.md) §6, the
intended proof is a chain-reversal induction on the propagation chain that
takes `cl(S ∪ {x}) ∋ y`. Each refinement-round signature-discrepancy
(`refineStep_iff`) is a *local* count-vector flip that is symmetric in its
two endpoints; chain-reversing flip-by-flip should yield a chain in the other
direction.

If exchange holds, the propagation closure is a matroid, and the binary /
non-binary classification (§7 of the matroid doc) gives a polynomial Tier-2
detection scheme. If it fails, the witness is a structural object worth
studying — it pins exactly where the matroid framing breaks.
-/

/-- **M3 — exchange axiom (open).** -/
theorem cl_exchange {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι : Colouring n) (S : Set (Fin n × Fin n))
    (x y : Fin n × Fin n)
    (hScanon : S ⊆ Egnd n) (hxcanon : x ∈ Egnd n) (hycanon : y ∈ Egnd n)
    (hy_in : y ∈ cl adj P₀ χι (S ∪ {x}))
    (hy_out : y ∉ cl adj P₀ χι S) :
    x ∈ cl adj P₀ χι (S ∪ {y}) ∧ x ∉ cl adj P₀ χι S := by
  sorry  -- TODO: chain-reversal induction; the load-bearing open claim

end ChainDescent
