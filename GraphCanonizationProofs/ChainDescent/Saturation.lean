import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate

/-!
# Iterated saturation of an extensive set operator

A small, **class-agnostic** engine: iterating an *extensive* operator
`f : Finset α → Finset α` (one with `s ⊆ f s`) on a finite carrier reaches a
fixpoint within `|α| − |s₀|` steps, by strict-cardinality growth. The carrier
need not be ordered beyond `Finset`'s subset order; the only inputs are
extensiveness and finiteness.

This is the shared skeleton behind two "bootstrap reaches the top within a
bounded number of rounds" arguments in the project — *same termination proof,
same forced/saturated endpoint, different operator* — so it lives here,
depending on nothing but Mathlib:

* **Schurian-scheme convergence** (`ChainDescent/Scheme.lean`): the operator
  adds every relation uniquely pinned by intersection-counts into the
  already-isolated relations; the fixpoint being `univ` is `EdgeGenerates`
  (a concrete instance of the oracle-capability seal's **D1** — "exposable by a
  poly-length symmetry-only process"), and the `− |s₀|` sharpness keeps the
  saturation depth `≤ rank ≤ n`.
* **Leg-A support induction** (planned, `ChainDescent/Cascade.lean`): the
  operator accumulates symmetry-only individualizations; the fixpoint is the
  residual base, reached within `|support|` rounds.

References: `docs/chain-descent-harvest-window.md` §2 (the trichotomy / forced
node), `docs/chain-descent-exhaustive-obstruction.md` §0.5 (D1).
-/

namespace ChainDescent.Saturation

variable {α : Type*}

/-- One iterate is contained in the next, for an extensive operator. -/
theorem iterate_subset_succ (f : Finset α → Finset α) (hf : ∀ s, s ⊆ f s)
    (s₀ : Finset α) (k : ℕ) : f^[k] s₀ ⊆ f^[k + 1] s₀ := by
  rw [Function.iterate_succ_apply']
  exact hf _

/-- Iterates of an extensive operator are monotone in the step count. -/
theorem iterate_mono (f : Finset α → Finset α) (hf : ∀ s, s ⊆ f s)
    (s₀ : Finset α) {k m : ℕ} (hkm : k ≤ m) : f^[k] s₀ ⊆ f^[m] s₀ := by
  induction m with
  | zero => rw [Nat.le_zero.mp hkm]
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hkm with h | h
    · rw [h]
    · exact (ih (Nat.le_of_lt_succ h)).trans (iterate_subset_succ f hf s₀ m)

/-- Once a fixpoint is reached, further iteration is inert. -/
theorem iterate_eq_of_isFixed (f : Finset α → Finset α) {t : Finset α}
    (ht : f t = t) (k : ℕ) : f^[k] t = t := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, ht]

/-- Iterates stay inside any `f`-invariant set containing the seed. -/
theorem iterate_subset_of_invariant (f : Finset α → Finset α) (B s₀ : Finset α)
    (hs₀ : s₀ ⊆ B) (hB : ∀ s, s ⊆ B → f s ⊆ B) (k : ℕ) : f^[k] s₀ ⊆ B := by
  induction k with
  | zero => exact hs₀
  | succ k ih => rw [Function.iterate_succ_apply']; exact hB _ ih

/-- **Interval-invariant** version of `iterate_subset_of_invariant`: iterates stay inside
`B` when `f` preserves `B` only on the *`f`-reachable* sets `s₀ ⊆ s ⊆ B`. Extensiveness
(`hf`) supplies `s₀ ⊆ f^[k] s₀`, so the inductive step only ever applies `hB` to a superset
of `s₀`. This is the form Leg A's support induction needs: `movedStep` preserves the
moved-set bound only on supersets of the seed, never on arbitrary `s ⊆ B`. -/
theorem iterate_subset_of_invariant' (f : Finset α → Finset α) (hf : ∀ s, s ⊆ f s)
    (B s₀ : Finset α) (hs₀ : s₀ ⊆ B) (hB : ∀ s, s₀ ⊆ s → s ⊆ B → f s ⊆ B)
    (k : ℕ) : f^[k] s₀ ⊆ B := by
  induction k with
  | zero => exact hs₀
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine hB _ ?_ ih
    have h := iterate_mono f hf s₀ (Nat.zero_le k)
    rwa [Function.iterate_zero_apply] at h

/-- A strictly-increasing `ℕ`-sequence over an initial range grows at least as
fast as the identity: `c 0 + M ≤ c M`. The pigeonhole that turns "no fixpoint
yet" into a cardinality blow-up. -/
private theorem card_add_le_of_strict (c : ℕ → ℕ) :
    ∀ M : ℕ, (∀ k < M, c k < c (k + 1)) → c 0 + M ≤ c M := by
  intro M
  induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro h
    have h1 : c 0 + M ≤ c M := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have h2 : c M < c (M + 1) := h M (Nat.lt_succ_self M)
    omega

/-- **Saturation within a bound, interval-invariant form.** As
`exists_iterate_isFixed_within`, but `f` need only preserve `B` on the *`f`-reachable*
sets `s₀ ⊆ s ⊆ B`, not on every `s ⊆ B`. This is the form Leg A's support induction uses
with `B = S₀ ∪ movedSet`: `movedStep` keeps the moved-set bound only on supersets of the
seed `S₀` (a vertex moved at `s ⊉ S₀` need not be moved at `S₀`), so full invariance fails
while interval invariance holds — yielding the tight `base(g) ≤ |support|` depth. -/
theorem exists_iterate_isFixed_within' (f : Finset α → Finset α)
    (hf : ∀ s, s ⊆ f s) (B s₀ : Finset α) (hs₀ : s₀ ⊆ B)
    (hB : ∀ s, s₀ ⊆ s → s ⊆ B → f s ⊆ B) :
    ∃ k, k ≤ B.card - s₀.card ∧ f (f^[k] s₀) = f^[k] s₀ := by
  classical
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  set N := B.card - s₀.card with hN
  have hsubB : ∀ k, f^[k] s₀ ⊆ B := iterate_subset_of_invariant' f hf B s₀ hs₀ hB
  have hstrict : ∀ k < N + 1, (f^[k] s₀).card < (f^[k + 1] s₀).card := by
    intro k hk
    have hsub : f^[k] s₀ ⊆ f^[k + 1] s₀ := iterate_subset_succ f hf s₀ k
    have hne : f^[k] s₀ ≠ f^[k + 1] s₀ := by
      intro he
      rw [Function.iterate_succ_apply' f k s₀] at he
      exact hcon k (by omega) he.symm
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hgrow := card_add_le_of_strict (fun k => (f^[k] s₀).card) (N + 1) hstrict
  simp only [Function.iterate_zero_apply] at hgrow
  have hcN : (f^[N + 1] s₀).card ≤ B.card := Finset.card_le_card (hsubB (N + 1))
  have hsc : s₀.card ≤ B.card := Finset.card_le_card hs₀
  omega

/-- **Saturation within a bound (the general form).** If `f` is extensive and
preserves a bound `B ⊇ s₀`, iterating from `s₀` reaches a fixpoint within
`|B| − |s₀|` steps. Seeded with a `c`-element set inside a carrier of effective
size `|B|`, saturation takes `|B| − c` rounds — this is the form the scheme
convergence uses with `B = occursFromV` (so the depth is `≤ n` even when empty
relations make the nominal carrier `Fin (rank+1)` larger than `n`). The
interval-invariant `exists_iterate_isFixed_within'` is the sharper form Leg A
uses with `B` the support set. -/
theorem exists_iterate_isFixed_within (f : Finset α → Finset α)
    (hf : ∀ s, s ⊆ f s) (B s₀ : Finset α) (hs₀ : s₀ ⊆ B)
    (hB : ∀ s, s ⊆ B → f s ⊆ B) :
    ∃ k, k ≤ B.card - s₀.card ∧ f (f^[k] s₀) = f^[k] s₀ :=
  exists_iterate_isFixed_within' f hf B s₀ hs₀ (fun s _ hsB => hB s hsB)

variable [Fintype α]

/-- **Saturation.** Iterating an extensive operator from `s₀` reaches a
fixpoint within `|α| − |s₀|` steps — the `B = univ` case of
`exists_iterate_isFixed_within`. -/
theorem exists_iterate_isFixed (f : Finset α → Finset α) (hf : ∀ s, s ⊆ f s)
    (s₀ : Finset α) :
    ∃ k, k ≤ Fintype.card α - s₀.card ∧ f (f^[k] s₀) = f^[k] s₀ := by
  have h := exists_iterate_isFixed_within f hf Finset.univ s₀
    (Finset.subset_univ _) (fun s _ => Finset.subset_univ _)
  rwa [Finset.card_univ] at h

end ChainDescent.Saturation
