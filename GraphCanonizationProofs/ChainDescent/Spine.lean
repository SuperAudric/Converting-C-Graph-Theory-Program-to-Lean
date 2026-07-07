/-
# ChainDescent/Spine.lean — §15 the descent spine + canonicalization (split from `ChainDescent.lean`).
IndivStep / DescentTrace / SpineChain + the spine branch-independence theorem, leaf characterisation,
`DirAssignment` / Z₂ flip, `IsAut` / `labelledAdj`, rank bijection, `canonAdj`, `matrixLT`, `canonForm`,
`LinearOracleSpec`. Imports `ChainDescent` (Core).
-/
import ChainDescent
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.PiLex
namespace ChainDescent

/-! ## §15 — the descent spine

Formalisation of the archived proving guide §11. The headline (spine) theorem is

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

See the archived proving guide §11 for the full informal argument and §10 item 1
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
private theorem samePartition_of_samePartition {n : Nat}
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
def partition (chain : SpineChain adj P₀ χι₀ sel k) :
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
private theorem IndivStep.samePartition_het {n : Nat}
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
def defaultColouring {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) : Nat → Colouring n
  | 0 => χι₀
  | k+1 =>
    let χι := defaultColouring adj P₀ χι₀ sel k
    let π := warmRefine adj P₀ χι
    (IndivStep.default π (sel π)).χ'

/-- The level-`k` decision set of the default chain: accumulate
`sel (warmRefine adj P₀ (defaultColouring k))` across all levels. -/
def defaultD {n : Nat} (adj : AdjMatrix n)
    (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) : Nat → Finset (Fin n)
  | 0 => ∅
  | k+1 =>
    let χι := defaultColouring adj P₀ χι₀ sel k
    let π := warmRefine adj P₀ χι
    defaultD adj P₀ χι₀ sel k ∪ sel π

/-- The concrete `DescentTrace` for the default construction. -/
def defaultTrace {n : Nat} (adj : AdjMatrix n)
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
def defaultSpineChain {n : Nat} (adj : AdjMatrix n)
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
private theorem SpineChain.isLeaf_iff_default {n : Nat} {adj : AdjMatrix n}
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
private theorem eq_of_σ_eq {σ₁ σ₂ : DirAssignment P₀ D}
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

private theorem vertexRankNat_lt_n (χ : Colouring n) (v : Fin n) :
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
private theorem vertexRank_strict_mono (χ : Colouring n) {v w : Fin n}
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
private theorem vertexRank_injective (χ : Colouring n) (h : Discrete χ) :
    Function.Injective (vertexRank χ) := by
  intro v w hvw
  by_contra hne
  have hχne : χ v ≠ χ w := fun e => hne (h v w e)
  rcases lt_or_gt_of_ne hχne with hlt | hgt
  · exact absurd hvw (ne_of_lt (vertexRank_strict_mono χ hlt))
  · exact absurd hvw (ne_of_gt (vertexRank_strict_mono χ hgt))

/-- Injective ⇒ bijective on `Fin n → Fin n` (pigeonhole). -/
private theorem vertexRank_bijective (χ : Colouring n) (h : Discrete χ) :
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

/-- Reindexing `vertexRank` along a permutation: the rank of `v` under `χ ∘ g`
equals the rank of `g v` under `χ`. Pure `Finset.card` reindex (mirrors
`signature_transport`'s reindex). *(Relocated from `LinearOracle.lean` so the
cascade oracle's `colourMatchPerm` (M-B) can consume it.)* -/
theorem vertexRank_comp {n : Nat} (χ : Colouring n) (g : Equiv.Perm (Fin n)) (v : Fin n) :
    Colouring.vertexRank (fun u => χ (g u)) v = Colouring.vertexRank χ (g v) := by
  apply Fin.ext
  show (Finset.univ.filter (fun u => χ (g u) < χ (g v))).card
     = (Finset.univ.filter (fun w => χ w < χ (g v))).card
  have key : (Finset.univ : Finset (Fin n)).filter (fun w => χ w < χ (g v))
      = ((Finset.univ : Finset (Fin n)).filter (fun u => χ (g u) < χ (g v))).map
          g.toEmbedding := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
               Equiv.coe_toEmbedding]
    constructor
    · intro hw
      exact ⟨g.symm w, by rw [g.apply_symm_apply]; exact hw, g.apply_symm_apply w⟩
    · rintro ⟨u, hu, rfl⟩; exact hu
  rw [key, Finset.card_map]

/-- **Rank permutation under relabelling (reindexing).** Relabelling a colouring by a
permutation `e` *conjugate-shifts* its rank permutation on the right:
`rankPerm (χ ∘ e) = rankPerm χ · e`. Pure combinatorics of `vertexRank` (count of
smaller colours), via a `Finset.card` reindex along `e`. The precise statement behind
the §L.5 conjugation gap. *(Relocated from `LinearOracle.lean`.)* -/
theorem rankPerm_comp {n : Nat} (χ : Colouring n) (e : Equiv.Perm (Fin n))
    (h : Discrete χ) (h' : Discrete (fun v => χ (e v))) :
    Colouring.rankPerm (fun v => χ (e v)) h' = Colouring.rankPerm χ h * e := by
  ext v
  simp only [Colouring.rankPerm_apply, Equiv.Perm.mul_apply]
  show (Finset.univ.filter (fun u => χ (e u) < χ (e v))).card
      = (Finset.univ.filter (fun w => χ w < χ (e v))).card
  have key : (Finset.univ.filter (fun u => χ (e u) < χ (e v)))
      = (Finset.univ.filter (fun w => χ w < χ (e v))).map e.symm.toEmbedding := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.coe_toEmbedding]
    constructor
    · intro hu; exact ⟨e u, hu, by simp⟩
    · rintro ⟨w, hw, rfl⟩; simpa using hw
  rw [key, Finset.card_map]

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
private theorem matrixLT_irrefl {n : Nat} (M : Fin n → Fin n → Nat) : ¬ matrixLT M M := by
  rintro ⟨_, _, _, _, hlt⟩
  exact lt_irrefl _ hlt

/-- `matrixLT` is asymmetric: `M₁ < M₂ → ¬ M₂ < M₁`. (Strict order.) -/
private theorem matrixLT_asymm {n : Nat} {M₁ M₂ : Fin n → Fin n → Nat}
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

private theorem toMatrixLex_injective {n : Nat} :
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

private theorem canonFormImages_nonempty {n : Nat} {adj : AdjMatrix n}
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


end ChainDescent
