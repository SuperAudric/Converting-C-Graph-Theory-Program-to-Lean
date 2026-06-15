import ChainDescent.Scheme
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# §CC — General (multi-fiber) coherent configurations: the Stage-1 substrate

This file opens the **general-CC separability build** (`docs/chain-descent-general-cc-separability.md`)
— the one remaining piece of the unconditional seal. It is the Stage-0 modeling decision made code,
plus the Stage-1.1/1.3 skeleton:

* **`CoherentConfig n`** — a general (multi-fiber) coherent configuration on `Fin n`, presented by its
  **colour function** `relOf : Fin n → Fin n → Fin rank` with four axioms (classes nonempty; transpose
  well-defined; reflexive classes purely diagonal; intersection numbers constant on classes). Fibers and
  their coherence are *derived* (`relOf_diag_left_eq`/`_right_eq`), not axiomatized — the minimal faithful
  presentation. This is exactly the object the empirical probe (`Theorem41ConditionsProbe.cs`, 2026-06-12)
  computes with, so every predicate below has a machine-checked finite mirror.
* **`ofScheme`** — the coercion from the project's homogeneous `AssociationScheme` (conditional on the
  seal's existing "every relation occurs" antecedent `hne`), reconciling the two substrates.
* **General `AlgIso` / `Separable` / `SeparablePointed`** — the §S.17 separability notions widened to
  general-CC partners. **This widening is deliberate** (the Stage-1.3 soundness gate, build doc §2): the
  homogeneous §S.17 `Separable` quantifies partners over `AssociationScheme` only, which omits exactly
  the extension algebraic isomorphisms the transport (B) consumes; here the partner ranges over all
  `CoherentConfig n`. (Same-`n` partners are faithful: an algebraic isomorphism preserves all valencies,
  hence the point count — Ponomarenko arXiv:2006.13592 §2.5.)
* **The Theorem-4.1 hypotheses** (`DominationCondition`, `CoupleExtensionCondition`) and the **cited
  statement** `Theorem41Statement` — the staging-fallback carry. Note the hypotheses need **no `Ωᵐ`
  substrate**: the "m-extension of a couple" (paper §3, (16)/(17)) is first-order in intersection
  numbers (complex-product membership + uniqueness), so Thm 4.1 is *statable* — and citable as a
  theorem-statement hypothesis, the project's G3 pattern — with only this file. The probe confirmed the
  hypotheses HOLD on the residue's one-point extension (ℤ₄²/ℤ₂⁴ Clebsch, every non-α `μ`, all witnesses
  geometric) and FAIL on the residue itself — the conditions activate exactly on the extension.
* **`Refines` / `SingletonFiber` / `IsPointExtension`** — the point extension `X_T` as a universal
  property (coarsest coherent fission of `X` with `T` singled out), with the discrete configuration
  `discreteCC` witnessing that the fission family is nonempty.
* **§CC.8 — the construction (Stage 1.2(a), landed 2026-06-12)**: `pointExtension X T`, the coherent
  closure computed by a pair-refinement saturation (`pairStep` on `Setoid (Fin n × Fin n)`, stabilized
  within `n²` rounds by the class-count pigeonhole), with `isPointExtension_pointExtension` discharging
  the universal property — so `IsPointExtension` is inhabited for every `(X, T)`
  (`exists_isPointExtension`), and unique up to mutual refinement (`isPointExtension_unique`).
  Consumers should still key on the predicate; the construction is the witness.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`;
cited results enter as theorem-statement hypotheses (`Theorem41Statement`), never `axiom`s.
-/

namespace ChainDescent

/-- A **general (multi-fiber) coherent configuration** on `Fin n`, presented by its colour function:
`relOf u v` is the (index of the) basis relation containing the ordered pair `(u, v)`.

The four axioms are the colour-function form of the classical ones (Ponomarenko arXiv:2006.13592 §2.1):
classes are nonempty (`relOf_surj`); the transpose of a class is a class (`transpose_eq`); a class
meeting the diagonal lies in the diagonal (`diag_eq` — its support is then a **fiber**); and the
intersection numbers are well defined (`inter_card_eq`). Homogeneous = one reflexive class; the
project's `AssociationScheme` coerces in via `ofScheme`. The point extension `X_T` — the central
object the build lacks a model for elsewhere — is *not* homogeneous (the `T`-points become singleton
fibers), which is why this type exists. -/
structure CoherentConfig (n : Nat) where
  /-- Number of basis relations (classes of the pair partition). -/
  rank : Nat
  /-- The colour function: `relOf u v` = the basis relation containing `(u, v)`. -/
  relOf : Fin n → Fin n → Fin rank
  /-- Every class is nonempty (the index set carries no phantom relations). -/
  relOf_surj : ∀ t : Fin rank, ∃ u v : Fin n, relOf u v = t
  /-- The transpose of a class is a class: `relOf v u` depends only on `relOf u v`. -/
  transpose_eq : ∀ {u v u' v' : Fin n}, relOf u v = relOf u' v' → relOf v u = relOf v' u'
  /-- Reflexive classes are purely diagonal: a class containing a loop contains only loops. -/
  diag_eq : ∀ {u v w : Fin n}, relOf u u = relOf v w → v = w
  /-- **The coherence axiom**: intersection numbers are constant on classes — for `(u, v)` and
  `(u', v')` in the same class, the number of `w` with `relOf u w = a` and `relOf w v = b` agree. -/
  inter_card_eq : ∀ {u v u' v' : Fin n}, relOf u v = relOf u' v' →
    ∀ a b : Fin rank,
      (Finset.univ.filter fun w => relOf u w = a ∧ relOf w v = b).card =
      (Finset.univ.filter fun w => relOf u' w = a ∧ relOf w v' = b).card

namespace CoherentConfig

variable {n : Nat} (X : CoherentConfig n)

/-! ### §CC.1 — Representatives, intersection numbers, transpose -/

/-- A chosen representative pair of the class `t`. -/
noncomputable def repPair (t : Fin X.rank) : Fin n × Fin n :=
  ⟨(X.relOf_surj t).choose, (X.relOf_surj t).choose_spec.choose⟩

theorem relOf_repPair (t : Fin X.rank) :
    X.relOf (X.repPair t).1 (X.repPair t).2 = t :=
  (X.relOf_surj t).choose_spec.choose_spec

/-- The **intersection number** `c^t_{a,b}`: for `(u, v) ∈ t`, the number of `w` with
`(u, w) ∈ a` and `(w, v) ∈ b` — well defined by `inter_card_eq`. -/
noncomputable def interNum (a b t : Fin X.rank) : Nat :=
  (Finset.univ.filter fun w =>
    X.relOf (X.repPair t).1 w = a ∧ X.relOf w (X.repPair t).2 = b).card

/-- The defining property of `interNum`: any pair of the class computes it. -/
theorem interNum_eq {u v : Fin n} {t : Fin X.rank} (h : X.relOf u v = t)
    (a b : Fin X.rank) :
    (Finset.univ.filter fun w => X.relOf u w = a ∧ X.relOf w v = b).card =
      X.interNum a b t :=
  X.inter_card_eq (h.trans (X.relOf_repPair t).symm) a b

/-- The **transpose class** `t*`: the class of the reversed pairs of `t`. -/
noncomputable def transposeRel (t : Fin X.rank) : Fin X.rank :=
  X.relOf (X.repPair t).2 (X.repPair t).1

/-- The defining property of `transposeRel`: reversing any pair of `t` lands in `t*`. -/
theorem relOf_swap_eq {u v : Fin n} {t : Fin X.rank} (h : X.relOf u v = t) :
    X.relOf v u = X.transposeRel t :=
  X.transpose_eq (h.trans (X.relOf_repPair t).symm)

@[simp] theorem transposeRel_transposeRel (t : Fin X.rank) :
    X.transposeRel (X.transposeRel t) = t := by
  have h1 : X.relOf (X.repPair t).2 (X.repPair t).1 = X.transposeRel t :=
    X.relOf_swap_eq (X.relOf_repPair t)
  have h2 : X.relOf (X.repPair t).1 (X.repPair t).2 = X.transposeRel (X.transposeRel t) :=
    X.relOf_swap_eq h1
  exact h2.symm.trans (X.relOf_repPair t)

/-! ### §CC.2 — Fibers are coherent (derived, not axiomatized)

A class determines the reflexive class of its sources (and targets): the **fiber structure** of a
coherent configuration is recoverable from `diag_eq` + `inter_card_eq` alone. This is the lemma that
makes the `IsPointExtension` universal property below complete: a configuration with `T`-singleton
fibers automatically refines the `T`-individualized starting partition. -/

/-- Same class ⟹ same source fiber: `relOf u v = relOf u' v'` forces `relOf u u = relOf u' u'`. -/
theorem relOf_diag_left_eq {u v u' v' : Fin n} (h : X.relOf u v = X.relOf u' v') :
    X.relOf u u = X.relOf u' u' := by
  have hmem : u ∈ Finset.univ.filter
      (fun w => X.relOf u w = X.relOf u u ∧ X.relOf w v = X.relOf u v) := by
    simp
  have hpos : 0 <
      (Finset.univ.filter fun w =>
        X.relOf u w = X.relOf u u ∧ X.relOf w v = X.relOf u v).card :=
    Finset.card_pos.mpr ⟨u, hmem⟩
  rw [X.inter_card_eq h (X.relOf u u) (X.relOf u v)] at hpos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hw
  obtain ⟨-, hw1, -⟩ := hw
  have hwu : u' = w := X.diag_eq hw1.symm
  rw [← hwu] at hw1
  exact hw1.symm

/-- Same class ⟹ same target fiber. -/
theorem relOf_diag_right_eq {u v u' v' : Fin n} (h : X.relOf u v = X.relOf u' v') :
    X.relOf v v = X.relOf v' v' :=
  X.relOf_diag_left_eq (X.transpose_eq h)

/-! ### §CC.3 — The homogeneous coercion: `AssociationScheme → CoherentConfig`

Conditional on the seal's existing "every relation occurs" antecedent (`hne`, carried by every seal
capstone) — `AssociationScheme`'s axioms do not force every index inhabited, but `CoherentConfig`'s
`relOf_surj` does (no phantom relations). -/

/-- The project's homogeneous `AssociationScheme` as a `CoherentConfig` (single reflexive class `R₀`),
given that every relation occurs. The colour function is `relOfPair`. -/
noncomputable def _root_.ChainDescent.AssociationScheme.toCoherentConfig
    (S : AssociationScheme n)
    (hne : ∀ i : Fin (S.rank + 1), ∃ v w, S.rel i v w = true) : CoherentConfig n where
  rank := S.rank + 1
  relOf := S.relOfPair
  relOf_surj := fun t => by
    obtain ⟨v, w, h⟩ := hne t
    exact ⟨v, w, (S.relOfPair_unique h).symm⟩
  transpose_eq := fun {u v u' v'} h => by
    rw [S.relOfPair_symm v u, S.relOfPair_symm v' u', h]
  diag_eq := fun {u v w} h => by
    have h0 : S.relOfPair u u = 0 := (S.relOfPair_eq_zero_iff u u).mpr rfl
    exact (S.relOfPair_eq_zero_iff v w).mp (h.symm.trans h0)
  inter_card_eq := fun {u v u' v'} h a b => by
    have hconv : ∀ p q : Fin n,
        (Finset.univ.filter fun w => S.relOfPair p w = a ∧ S.relOfPair w q = b).card =
        (Finset.univ.filter fun w => S.rel a p w = true ∧ S.rel b w q = true).card := by
      intro p q
      congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S.rel_iff_relOfPair]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
    have hk : S.rel (S.relOfPair u v) u v = true := S.rel_relOfPair u v
    have hk' : S.rel (S.relOfPair u v) u' v' = true :=
      (S.rel_iff_relOfPair).mpr h
    rw [hconv u v, hconv u' v',
      S.intersectionNumber_well_defined a b (S.relOfPair u v) u v hk,
      S.intersectionNumber_well_defined a b (S.relOfPair u v) u' v' hk']

/-! ### §CC.4 — Algebraic isomorphisms and separability (general-CC, the §S.17 widening)

`Separable` here quantifies the partner `Y` over **all** `CoherentConfig n` — multi-fiber included.
This is the deliberate strengthening of `Separability.lean §S.17`'s homogeneous `Separable` (which the
Stage-1.3 soundness gate flagged as potentially too weak to feed the transport (B): the algebraic
isomorphisms the transport consumes live between point extensions, which are multi-fiber). Same-`n`
partners are faithful — an algebraic isomorphism preserves all valencies and hence the point count. -/

/-- An **algebraic isomorphism** `X → Y` of general coherent configurations: a bijection of basis
relations preserving all intersection numbers (Ponomarenko arXiv:2006.13592 §2.5, eq. (8)). Stated
bare, exactly as in the paper — fiber/diagonal preservation is not a clause (the paper derives what
it needs from (8) via the complex-product calculus, Lemma 2.4). -/
structure AlgIso (X Y : CoherentConfig n) where
  /-- The relation bijection. -/
  relEquiv : Fin X.rank ≃ Fin Y.rank
  /-- Intersection numbers are preserved: `c^t_{a,b}(X) = c^{φt}_{φa,φb}(Y)`. -/
  pres_inter : ∀ a b t, X.interNum a b t =
    Y.interNum (relEquiv a) (relEquiv b) (relEquiv t)

/-- An algebraic isomorphism is **induced** by a vertex permutation `f` when `f` realises it
relation-by-relation: the class of `(f u, f v)` in `Y` is the `φ`-image of the class of `(u, v)`. -/
def AlgIso.InducedBy {X Y : CoherentConfig n} (φ : AlgIso X Y)
    (f : Equiv.Perm (Fin n)) : Prop :=
  ∀ u v : Fin n, Y.relOf (f u) (f v) = φ.relEquiv (X.relOf u v)

/-- The identity algebraic isomorphism (sanity inhabitant). -/
def idAlgIso (X : CoherentConfig n) : AlgIso X X where
  relEquiv := Equiv.refl _
  pres_inter := fun _ _ _ => rfl

theorem idAlgIso_inducedBy_refl (X : CoherentConfig n) :
    (idAlgIso X).InducedBy (Equiv.refl (Fin n)) := fun _ _ => rfl

/-- **Separability** (`s(X) = 1`), general-CC form: every algebraic isomorphism out of `X` is induced
by an isomorphism. The conclusion of Thm 4.1 (unpointed form). -/
def Separable (X : CoherentConfig n) : Prop :=
  ∀ (Y : CoherentConfig n) (φ : AlgIso X Y), ∃ f : Equiv.Perm (Fin n), φ.InducedBy f

/-- **Pointed separability at `μ`** — Thm 4.1's actual (stronger) conclusion: every algebraic
isomorphism is induced by an `f` taking `μ` to *any prescribed* `μ'` whose reflexive class matches.
The pointed form is what the transport (B) wants: the induced isomorphism must be steerable onto the
individualized base (build doc Stage 2.2(b)). -/
def SeparablePointed (X : CoherentConfig n) (μ : Fin n) : Prop :=
  ∀ (Y : CoherentConfig n) (φ : AlgIso X Y) (μ' : Fin n),
    Y.relOf μ' μ' = φ.relEquiv (X.relOf μ μ) →
    ∃ f : Equiv.Perm (Fin n), φ.InducedBy f ∧ f μ = μ'

/-! ### §CC.5 — The Theorem-4.1 hypotheses (probe-validated; no `Ωᵐ` substrate needed)

Conditions (i) and (ii) of Ponomarenko arXiv:2006.13592 Thm 4.1, stated exactly as probed
(`Theorem41ConditionsProbe.cs`, 2026-06-12: PASS on the residue's one-point extension at every
non-`α` `μ`, FAIL on the residue itself, checker validated on the §5-proved sparse control). The
"m-extension of a couple" is first-order in intersection numbers — the `Ωᵐ` tower is needed only for
*m-separability* (Lemma 2.6's conclusion), not to state Thm 4.1. -/

/-- Membership in the **complex product** `a · b`: the classes `w` with `c^w_{a,b} ≠ 0`. -/
def InComplexProduct (a b w : Fin X.rank) : Prop := X.interNum a b w ≠ 0

/-- **Point domination** `δ ← λ` w.r.t. the fixed `μ` (paper (9)/(11)):
`c^{r(μ,λ)}_{r(μ,δ), r(δ,λ)} = 1` — `λ` pins `δ` as the unique point with its
`(μ-relation, relation-to-λ)` signature. -/
def Dominates (μ δ lam : Fin n) : Prop :=
  X.interNum (X.relOf μ δ) (X.relOf δ lam) (X.relOf μ lam) = 1

/-- **Thm 4.1 condition (i)**: every `Δ ⊆ Ω` with `|Δ| ≤ 4` is dominated by some `λ`. -/
def DominationCondition (μ : Fin n) : Prop :=
  ∀ Δ : Finset (Fin n), Δ.card ≤ 4 → ∃ lam : Fin n, ∀ δ ∈ Δ, X.Dominates μ δ lam

/-- The triangle `(x̄, ȳ, z̄)` is an **`m`-extension of the couple** `Qμ(α,β,γ)` (paper §3,
(16)/(17)): each barred relation lies in the corresponding product `m* · r(μ,·)`, and each pairwise
product intersection collapses to the couple's side — e.g. `x̄*ȳ ∩ x*y = {r(α,β)}`. -/
def IsCoupleExtension (μ α β γ : Fin n) (m xb yb zb : Fin X.rank) : Prop :=
  X.InComplexProduct (X.transposeRel m) (X.relOf μ α) xb ∧
  X.InComplexProduct (X.transposeRel m) (X.relOf μ β) yb ∧
  X.InComplexProduct (X.transposeRel m) (X.relOf μ γ) zb ∧
  (∀ w, (X.InComplexProduct (X.transposeRel xb) yb w ∧
         X.InComplexProduct (X.transposeRel (X.relOf μ α)) (X.relOf μ β) w) ↔
       w = X.relOf α β) ∧
  (∀ w, (X.InComplexProduct (X.transposeRel yb) zb w ∧
         X.InComplexProduct (X.transposeRel (X.relOf μ β)) (X.relOf μ γ) w) ↔
       w = X.relOf β γ) ∧
  (∀ w, (X.InComplexProduct (X.transposeRel zb) xb w ∧
         X.InComplexProduct (X.transposeRel (X.relOf μ γ)) (X.relOf μ α) w) ↔
       w = X.relOf γ α)

/-- **Thm 4.1 condition (ii)**: every couple `Qμ(α,β,γ)` has an `m`-extension for some `m` with
`μm ≠ ∅`. (The probe found the witness always *geometric* on the residue's extension — `m = r(μ,λ)`,
`(x̄,ȳ,z̄) = (r(λ,α), r(λ,β), r(λ,γ))` — Lemma 5.3's shape; a future discharge can construct it.) -/
def CoupleExtensionCondition (μ : Fin n) : Prop :=
  ∀ α β γ : Fin n, ∃ (m xb yb zb : Fin X.rank),
    (∃ ν, X.relOf μ ν = m) ∧ X.IsCoupleExtension μ α β γ m xb yb zb

/-- The two hypotheses of Thm 4.1, bundled. -/
def Theorem41Hypotheses (μ : Fin n) : Prop :=
  X.DominationCondition μ ∧ X.CoupleExtensionCondition μ

end CoherentConfig

/-- **The cited Theorem 4.1** (Ponomarenko arXiv:2006.13592, §4) as a theorem-statement proposition —
the staging-fallback carry (the project's G3 pattern: cited classifications are *hypotheses* on the
final theorems, never fresh `axiom`s). A future increment either proves it (Stage 3, Route α/β) or
carries it into the seal capstone; either way every use site shows the citation. -/
def Theorem41Statement : Prop :=
  ∀ (n : Nat) (X : CoherentConfig n) (μ : Fin n),
    X.Theorem41Hypotheses μ → X.SeparablePointed μ

namespace CoherentConfig

variable {n : Nat}

/-! ### §CC.6 — Refinement and the point extension as a universal property

`X_T` (the point extension) is the **coarsest coherent fission of `X` in which every `t ∈ T` is a
singleton fiber**. We model it as a predicate; the §CC.2 fiber-coherence lemma is what makes this
universal property equivalent to the classical "coarsest CC finer than the `T`-individualized
starting partition" (a CC with `T`-singleton fibers cannot merge pairs across the `T`-flags: the
source/target fibers are class-determined). The closure's *construction* is §CC.8 (`pointExtension`
+ `isPointExtension_pointExtension`); consumers key on the predicate. -/

/-- `Y` **refines** `X`: `Y`'s pair partition is finer (each `Y`-class lies inside an `X`-class). -/
def Refines (Y X : CoherentConfig n) : Prop :=
  ∀ u v u' v' : Fin n, Y.relOf u v = Y.relOf u' v' → X.relOf u v = X.relOf u' v'

theorem Refines.refl (X : CoherentConfig n) : Refines X X := fun _ _ _ _ h => h

theorem Refines.trans {Z Y X : CoherentConfig n}
    (h1 : Refines Z Y) (h2 : Refines Y X) : Refines Z X :=
  fun u v u' v' h => h2 u v u' v' (h1 u v u' v' h)

/-- `t` is a **singleton fiber** of `Y`: no other point shares its reflexive class. -/
def SingletonFiber (Y : CoherentConfig n) (t : Fin n) : Prop :=
  ∀ u : Fin n, Y.relOf u u = Y.relOf t t → u = t

/-- `Y` is **the point extension** `X_T`: a coherent fission of `X` with every `t ∈ T` a singleton
fiber, coarsest among all such (the universal property). Unique up to relabelling when it exists. -/
def IsPointExtension (X : CoherentConfig n) (T : Finset (Fin n))
    (Y : CoherentConfig n) : Prop :=
  Refines Y X ∧ (∀ t ∈ T, SingletonFiber Y t) ∧
  ∀ Z : CoherentConfig n, Refines Z X → (∀ t ∈ T, SingletonFiber Z t) → Refines Z Y

/-- **The staging-fallback target predicate**: every point extension of `X` at `T` is separable.
This is the *separability-level* hypothesis the transport (B) consumes (build doc Stage 2.2) — for
schurian residues it is what Thm 4.1 (cited or proved) supplies, per the probe's verdict that the
hypotheses hold on the extension. -/
def ExtensionSeparable (X : CoherentConfig n) (T : Finset (Fin n)) : Prop :=
  ∀ Y : CoherentConfig n, IsPointExtension X T Y → Y.Separable

/-! ### §CC.7 — The discrete configuration (an inhabitant; the fission family is nonempty) -/

/-- The **discrete** coherent configuration: every ordered pair its own class. The finest CC — it
refines everything and has every point a singleton fiber, so the family `IsPointExtension` minimizes
over is nonempty for every `(X, T)`. -/
def discreteCC (n : Nat) : CoherentConfig n where
  rank := n * n
  relOf := fun u v => finProdFinEquiv (u, v)
  relOf_surj := fun t => by
    refine ⟨(finProdFinEquiv.symm t).1, (finProdFinEquiv.symm t).2, ?_⟩
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  transpose_eq := fun {u v u' v'} h => by
    have h' : (u, v) = (u', v') := finProdFinEquiv.injective h
    rw [Prod.mk.injEq] at h'
    rw [h'.1, h'.2]
  diag_eq := fun {u v w} h => by
    have h' : (u, u) = (v, w) := finProdFinEquiv.injective h
    rw [Prod.mk.injEq] at h'
    rw [← h'.1, ← h'.2]
  inter_card_eq := fun {u v u' v'} h a b => by
    have h' : (u, v) = (u', v') := finProdFinEquiv.injective h
    rw [Prod.mk.injEq] at h'
    rw [h'.1, h'.2]

/-- The discrete configuration refines every configuration. -/
theorem discreteCC_refines (X : CoherentConfig n) : Refines (discreteCC n) X := by
  intro u v u' v' h
  have h' : (u, v) = (u', v') := finProdFinEquiv.injective h
  rw [Prod.mk.injEq] at h'
  rw [h'.1, h'.2]

/-- Every point is a singleton fiber of the discrete configuration. -/
theorem discreteCC_singletonFiber (t : Fin n) : SingletonFiber (discreteCC n) t := by
  intro u h
  have h' : (u, u) = (t, t) := finProdFinEquiv.injective h
  rw [Prod.mk.injEq] at h'
  exact h'.1

/-! ### §CC.8 — The point-extension construction (pair-refinement saturation; Stage 1.2(a))

The actual witness for `IsPointExtension X T`: the coherent closure, computed as a saturation on
`Setoid (Fin n × Fin n)`. Starting from `X`'s classes split by the `T`-individualization flags
(`extInitSetoid`), one `pairStep` splits each class by all **representative-indexed intersection
counts** (`pairCount` — counts are indexed by reference *pairs*, not class indices, so no quotient
or encoding machinery enters the iteration). The class count `numClasses` (= `Nat.card` of the
quotient) strictly increases at every non-fixed step and is bounded by `n²`, so the chain stabilizes
within `n²` rounds (`pairStep_stableSetoid` — the `CascadeAffine §S-stab` pigeonhole, on pairs). At
the fixpoint the count conditions ARE the coherence axiom `inter_card_eq`; the transpose, diagonal,
and flag facts are split-only invariants carried from the start (`pairIter_swap`, `pairIter_le_init`).
The universal property is the standard closure-is-minimum induction: a coherent fission `Z` of `X`
with `T`-singleton fibers refines the start (fiber coherence `relOf_diag_left_eq` reads the flags off
`Z`'s classes) and refines each successive stage (`Z`'s own `inter_card_eq`, summed fiberwise over
`Z`'s class pairs — `pairCount_eq_of_zrel`). -/

section PointExtensionConstruction

open scoped Classical

variable (X : CoherentConfig n) (T : Finset (Fin n))

/-- The `T`-individualization flag: `t ∈ T` carries the unique flag `t.val + 1`, everything else `0`
(the `individualizedColouring` pattern — distinct `T`-points get distinct flags). -/
def extFlag (u : Fin n) : Nat := if u ∈ T then u.val + 1 else 0

theorem extFlag_eq_of_mem {t u : Fin n} (ht : t ∈ T) (h : extFlag T u = extFlag T t) : u = t := by
  unfold extFlag at h
  rw [if_pos ht] at h
  by_cases hu : u ∈ T
  · rw [if_pos hu] at h
    exact Fin.ext (Nat.succ_injective h)
  · rw [if_neg hu] at h
    exact absurd h.symm (Nat.succ_ne_zero _)

/-- The initial pair partition: `X`'s classes, split by the endpoint flags. -/
def extInitSetoid : Setoid (Fin n × Fin n) where
  r p q := X.relOf p.1 p.2 = X.relOf q.1 q.2 ∧
    extFlag T p.1 = extFlag T q.1 ∧ extFlag T p.2 = extFlag T q.2
  iseqv := ⟨fun _ => ⟨rfl, rfl, rfl⟩,
            fun h => ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩,
            fun h h' => ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩⟩

/-- The intersection count of `(u, v)` against the classes of the reference pairs `x`, `y` under the
pair partition `s` — the quantity one refinement round splits by. Representative-indexed: `x`, `y`
name their classes, so the iteration never materializes a quotient. -/
noncomputable def pairCount (s : Setoid (Fin n × Fin n)) (u v : Fin n)
    (x y : Fin n × Fin n) : Nat :=
  (Finset.univ.filter fun w => s (u, w) x ∧ s (w, v) y).card

/-- One pair-refinement round: split each class by all the intersection counts. -/
def pairStep (s : Setoid (Fin n × Fin n)) : Setoid (Fin n × Fin n) where
  r p q := s p q ∧ ∀ x y : Fin n × Fin n,
    pairCount s p.1 p.2 x y = pairCount s q.1 q.2 x y
  iseqv := ⟨fun p => ⟨s.iseqv.refl p, fun _ _ => rfl⟩,
            fun h => ⟨s.iseqv.symm h.1, fun x y => (h.2 x y).symm⟩,
            fun h h' => ⟨s.iseqv.trans h.1 h'.1, fun x y => (h.2 x y).trans (h'.2 x y)⟩⟩

/-- The saturation chain from the `T`-individualized start. -/
def pairIter (k : Nat) : Setoid (Fin n × Fin n) := pairStep^[k] (extInitSetoid X T)

theorem pairIter_zero : pairIter X T 0 = extInitSetoid X T := rfl

theorem pairIter_succ (k : Nat) : pairIter X T (k + 1) = pairStep (pairIter X T k) :=
  Function.iterate_succ_apply' _ _ _

theorem pairStep_le {s : Setoid (Fin n × Fin n)} {p q : Fin n × Fin n}
    (h : pairStep s p q) : s p q := h.1

/-- Every stage refines the start (split-only). -/
theorem pairIter_le_init (k : Nat) {p q : Fin n × Fin n}
    (h : pairIter X T k p q) : extInitSetoid X T p q := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [pairIter_succ] at h
    exact ih (pairStep_le h)

/-! #### Stabilization (the pigeonhole on the class count) -/

/-- The number of classes of a pair partition. -/
noncomputable def numClasses (s : Setoid (Fin n × Fin n)) : Nat := Nat.card (Quotient s)

/-- The canonical map between quotients of comparable partitions. -/
def quotMap {s s' : Setoid (Fin n × Fin n)}
    (h : ∀ p q : Fin n × Fin n, s' p q → s p q) : Quotient s' → Quotient s :=
  Quotient.lift (fun p => Quotient.mk s p) (fun a b hab => Quotient.sound (h a b hab))

theorem quotMap_surjective {s s' : Setoid (Fin n × Fin n)}
    (h : ∀ p q : Fin n × Fin n, s' p q → s p q) : Function.Surjective (quotMap h) := by
  intro qs
  obtain ⟨p, rfl⟩ := Quotient.exists_rep qs
  exact ⟨Quotient.mk s' p, rfl⟩

/-- Refining cannot lose classes: the coarser partition's quotient receives a surjection. -/
theorem numClasses_le_of_le {s s' : Setoid (Fin n × Fin n)}
    (h : ∀ p q : Fin n × Fin n, s' p q → s p q) : numClasses s ≤ numClasses s' :=
  Nat.card_le_card_of_surjective _ (quotMap_surjective h)

/-- The rigidity half of the pigeonhole: a refinement with no more classes is no refinement. -/
theorem le_of_numClasses_le {s s' : Setoid (Fin n × Fin n)}
    (hle : ∀ p q : Fin n × Fin n, s' p q → s p q)
    (hcard : numClasses s' ≤ numClasses s) :
    ∀ p q : Fin n × Fin n, s p q → s' p q := by
  have hbij : Function.Bijective (quotMap hle) :=
    (Nat.bijective_iff_surjective_and_card _).mpr
      ⟨quotMap_surjective hle, le_antisymm hcard (numClasses_le_of_le hle)⟩
  intro p q hpq
  have hmk : quotMap hle (Quotient.mk s' p) = quotMap hle (Quotient.mk s' q) := by
    show (Quotient.mk s p : Quotient s) = Quotient.mk s q
    exact Quotient.sound hpq
  exact Quotient.exact (hbij.injective hmk)

theorem numClasses_le_sq (s : Setoid (Fin n × Fin n)) : numClasses s ≤ n * n := by
  have hsurj : Function.Surjective (Quotient.mk s) := fun q => ⟨q.out, Quotient.out_eq q⟩
  calc numClasses s ≤ Nat.card (Fin n × Fin n) := Nat.card_le_card_of_surjective _ hsurj
    _ = n * n := by simp

/-- Strict growth before the fixpoint: `k` non-fixed rounds force `≥ k` extra classes. -/
theorem numClasses_growth (k : Nat)
    (h : ∀ j < k, pairStep (pairIter X T j) ≠ pairIter X T j) :
    numClasses (pairIter X T 0) + k ≤ numClasses (pairIter X T k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hle : numClasses (pairIter X T k) ≤ numClasses (pairIter X T (k + 1)) := by
      rw [pairIter_succ]
      exact numClasses_le_of_le (fun _ _ h => pairStep_le h)
    have hne : numClasses (pairIter X T k) ≠ numClasses (pairIter X T (k + 1)) := by
      intro heq
      refine h k (Nat.lt_succ_self k) (Setoid.ext fun p q => ?_)
      constructor
      · exact pairStep_le
      · intro hpq
        refine le_of_numClasses_le (fun _ _ h => pairStep_le h) ?_ p q hpq
        rw [← pairIter_succ]
        exact le_of_eq heq.symm
    omega

/-- The chain reaches a fixpoint within `n²` rounds. -/
theorem exists_pairIter_fixed :
    ∃ k ≤ n * n, pairStep (pairIter X T k) = pairIter X T k := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · refine ⟨0, Nat.zero_le _, Setoid.ext fun p _ => ?_⟩
    subst hn
    exact p.1.elim0
  · by_contra hcon
    push Not at hcon
    have hgrow := numClasses_growth X T (n * n + 1)
      (fun j hj => hcon j (by omega))
    have h1 : 1 ≤ numClasses (pairIter X T 0) := by
      haveI : Nonempty (Fin n × Fin n) := ⟨⟨⟨0, hn⟩, ⟨0, hn⟩⟩⟩
      haveI : Nonempty (Quotient (pairIter X T 0)) := Nonempty.map (Quotient.mk _) ‹_›
      exact Nat.card_pos
    have hb := numClasses_le_sq (pairIter X T (n * n + 1))
    omega

/-- The stable pair partition — the coherent closure of the `T`-individualized start. -/
def stableSetoid : Setoid (Fin n × Fin n) := pairIter X T (n * n)

/-- The stable partition is a `pairStep` fixpoint. -/
theorem pairStep_stableSetoid : pairStep (stableSetoid X T) = stableSetoid X T := by
  obtain ⟨k, hk, hfix⟩ := exists_pairIter_fixed X T
  have hstab : stableSetoid X T = pairIter X T k := by
    show pairStep^[n * n] (extInitSetoid X T) = pairIter X T k
    have hsplit : n * n = (n * n - k) + k := by omega
    rw [hsplit, Function.iterate_add_apply]
    exact Function.iterate_fixed hfix (n * n - k)
  rw [hstab, hfix]

/-- The fixpoint property, extracted: same stable class ⟹ all intersection counts agree. -/
theorem stableSetoid_pairCount {p q : Fin n × Fin n} (h : stableSetoid X T p q) :
    ∀ x y : Fin n × Fin n,
      pairCount (stableSetoid X T) p.1 p.2 x y = pairCount (stableSetoid X T) q.1 q.2 x y := by
  have h' : pairStep (stableSetoid X T) p q := by
    rw [pairStep_stableSetoid]
    exact h
  exact h'.2

/-! #### Split-only invariants: transpose and the swap -/

/-- Counts of the swapped pair, for a swap-stable partition: a pure reindexing. -/
theorem pairCount_swap {s : Setoid (Fin n × Fin n)}
    (hsw : ∀ p q : Fin n × Fin n, s p q → s p.swap q.swap)
    (u v : Fin n) (x y : Fin n × Fin n) :
    pairCount s v u x y = pairCount s u v y.swap x.swap := by
  have hiff : ∀ (p z : Fin n × Fin n), s p z ↔ s p.swap z.swap := by
    intro p z
    exact ⟨fun h => hsw _ _ h, fun h => by simpa using hsw _ _ h⟩
  unfold pairCount
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro w _
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(hiff (w, u) y).mp h2, (hiff (v, w) x).mp h1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := (hiff (w, v) x.swap).mp h2
      simpa using this
    · have := (hiff (u, w) y.swap).mp h1
      simpa using this

/-- Every stage is swap-stable (the transpose invariant). -/
theorem pairIter_swap (k : Nat) :
    ∀ p q : Fin n × Fin n, pairIter X T k p q → pairIter X T k p.swap q.swap := by
  induction k with
  | zero =>
    rintro p q ⟨hrel, h1, h2⟩
    exact ⟨X.transpose_eq hrel, h2, h1⟩
  | succ k ih =>
    intro p q h
    rw [pairIter_succ] at h ⊢
    refine ⟨ih p q h.1, ?_⟩
    intro x y
    have hp : pairCount (pairIter X T k) p.2 p.1 x y =
        pairCount (pairIter X T k) p.1 p.2 y.swap x.swap := pairCount_swap ih _ _ _ _
    have hq : pairCount (pairIter X T k) q.2 q.1 x y =
        pairCount (pairIter X T k) q.1 q.2 y.swap x.swap := pairCount_swap ih _ _ _ _
    calc pairCount (pairIter X T k) p.swap.1 p.swap.2 x y
        = pairCount (pairIter X T k) p.1 p.2 y.swap x.swap := hp
      _ = pairCount (pairIter X T k) q.1 q.2 y.swap x.swap := h.2 y.swap x.swap
      _ = pairCount (pairIter X T k) q.swap.1 q.swap.2 x y := hq.symm

/-! #### The universal-property induction -/

/-- **The counting heart of the universal property**: a coherent fission `Z` whose classes refine the
pair partition `s` has `s`-counts constant on `Z`-classes — `Z.inter_card_eq` summed fiberwise over
`Z`'s class pairs. -/
theorem pairCount_eq_of_zrel {Z : CoherentConfig n} {s : Setoid (Fin n × Fin n)}
    (hle : ∀ p q : Fin n × Fin n, Z.relOf p.1 p.2 = Z.relOf q.1 q.2 → s p q)
    {u v u' v' : Fin n} (h : Z.relOf u v = Z.relOf u' v') (x y : Fin n × Fin n) :
    pairCount s u v x y = pairCount s u' v' x y := by
  unfold pairCount
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun w => (Z.relOf u w, Z.relOf w v)) (t := Finset.univ)
        (fun w _ => Finset.mem_univ _),
      Finset.card_eq_sum_card_fiberwise
        (f := fun w => (Z.relOf u' w, Z.relOf w v')) (t := Finset.univ)
        (fun w _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [Finset.filter_filter, Finset.filter_filter]
  -- the bare Z-fibers have equal cardinality (Z's coherence axiom)
  have hZfib : (Finset.univ.filter fun w => (Z.relOf u w, Z.relOf w v) = ab).card =
      (Finset.univ.filter fun w => (Z.relOf u' w, Z.relOf w v') = ab).card := by
    have e1 : (Finset.univ.filter fun w => (Z.relOf u w, Z.relOf w v) = ab) =
        Finset.univ.filter fun w => Z.relOf u w = ab.1 ∧ Z.relOf w v = ab.2 :=
      Finset.filter_congr fun w _ => Prod.ext_iff
    have e2 : (Finset.univ.filter fun w => (Z.relOf u' w, Z.relOf w v') = ab) =
        Finset.univ.filter fun w => Z.relOf u' w = ab.1 ∧ Z.relOf w v' = ab.2 :=
      Finset.filter_congr fun w _ => Prod.ext_iff
    rw [e1, e2]
    exact Z.inter_card_eq h ab.1 ab.2
  by_cases hrep : ∃ w₀ : Fin n, Z.relOf u w₀ = ab.1 ∧ Z.relOf w₀ v = ab.2
  · obtain ⟨w₀, hw1, hw2⟩ := hrep
    -- a matching representative on the (u', v') side
    have hpos : 0 < (Finset.univ.filter fun w => (Z.relOf u' w, Z.relOf w v') = ab).card := by
      rw [← hZfib]
      refine Finset.card_pos.mpr ⟨w₀, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
      exact ⟨hw1, hw2⟩
    obtain ⟨w₀', hw₀'⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter, Prod.ext_iff] at hw₀'
    obtain ⟨-, hw1', hw2'⟩ := hw₀'
    -- the s-conditions are constant on each fiber, with the same value on both sides
    have htrans : ∀ {w : Fin n}, Z.relOf u w = ab.1 → Z.relOf w v = ab.2 →
        ((s (u, w) x ∧ s (w, v) y) ↔ (s (u, w₀) x ∧ s (w₀, v) y)) := by
      intro w hwa hwb
      have h1 : s (u, w) (u, w₀) := hle _ _ (by simp [hwa, hw1])
      have h2 : s (w, v) (w₀, v) := hle _ _ (by simp [hwb, hw2])
      constructor
      · rintro ⟨ha, hb⟩
        exact ⟨s.iseqv.trans (s.iseqv.symm h1) ha, s.iseqv.trans (s.iseqv.symm h2) hb⟩
      · rintro ⟨ha, hb⟩
        exact ⟨s.iseqv.trans h1 ha, s.iseqv.trans h2 hb⟩
    have htrans' : ∀ {w : Fin n}, Z.relOf u' w = ab.1 → Z.relOf w v' = ab.2 →
        ((s (u', w) x ∧ s (w, v') y) ↔ (s (u, w₀) x ∧ s (w₀, v) y)) := by
      intro w hwa hwb
      have h1 : s (u', w) (u, w₀) := hle _ _ (by simp [hwa, hw1])
      have h2 : s (w, v') (w₀, v) := hle _ _ (by simp [hwb, hw2])
      constructor
      · rintro ⟨ha, hb⟩
        exact ⟨s.iseqv.trans (s.iseqv.symm h1) ha, s.iseqv.trans (s.iseqv.symm h2) hb⟩
      · rintro ⟨ha, hb⟩
        exact ⟨s.iseqv.trans h1 ha, s.iseqv.trans h2 hb⟩
    by_cases hC : s (u, w₀) x ∧ s (w₀, v) y
    · -- the s-conditions hold on both fibers: counts reduce to the bare fibers
      have hu : (Finset.univ.filter fun w =>
          (s (u, w) x ∧ s (w, v) y) ∧ (Z.relOf u w, Z.relOf w v) = ab) =
          Finset.univ.filter fun w => (Z.relOf u w, Z.relOf w v) = ab := by
        refine Finset.filter_congr fun w _ => ?_
        constructor
        · exact And.right
        · intro hfib
          rw [Prod.ext_iff] at hfib
          refine ⟨(htrans hfib.1 hfib.2).mpr hC, ?_⟩
          rw [Prod.ext_iff]
          exact hfib
      have hu' : (Finset.univ.filter fun w =>
          (s (u', w) x ∧ s (w, v') y) ∧ (Z.relOf u' w, Z.relOf w v') = ab) =
          Finset.univ.filter fun w => (Z.relOf u' w, Z.relOf w v') = ab := by
        refine Finset.filter_congr fun w _ => ?_
        constructor
        · exact And.right
        · intro hfib
          rw [Prod.ext_iff] at hfib
          refine ⟨(htrans' hfib.1 hfib.2).mpr hC, ?_⟩
          rw [Prod.ext_iff]
          exact hfib
      rw [hu, hu']
      exact hZfib
    · -- the s-conditions fail on both fibers: both counts are zero
      have hu : (Finset.univ.filter fun w =>
          (s (u, w) x ∧ s (w, v) y) ∧ (Z.relOf u w, Z.relOf w v) = ab) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun w _ hw => ?_
        obtain ⟨hs, hfib⟩ := hw
        rw [Prod.ext_iff] at hfib
        exact hC ((htrans hfib.1 hfib.2).mp hs)
      have hu' : (Finset.univ.filter fun w =>
          (s (u', w) x ∧ s (w, v') y) ∧ (Z.relOf u' w, Z.relOf w v') = ab) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun w _ hw => ?_
        obtain ⟨hs, hfib⟩ := hw
        rw [Prod.ext_iff] at hfib
        exact hC ((htrans' hfib.1 hfib.2).mp hs)
      rw [hu, hu']
  · -- the fiber is empty on both sides
    push Not at hrep
    have hemptyU : (Finset.univ.filter fun w => (Z.relOf u w, Z.relOf w v) = ab) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun w _ hfib => ?_
      rw [Prod.ext_iff] at hfib
      exact hrep w hfib.1 hfib.2
    have hemptyU' : (Finset.univ.filter fun w => (Z.relOf u' w, Z.relOf w v') = ab) = ∅ := by
      rw [← Finset.card_eq_zero, ← hZfib, Finset.card_eq_zero]
      exact hemptyU
    have h1 : (Finset.univ.filter fun w =>
        (s (u, w) x ∧ s (w, v) y) ∧ (Z.relOf u w, Z.relOf w v) = ab) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun w _ hw => ?_
      exact Finset.filter_eq_empty_iff.mp hemptyU (Finset.mem_univ w) hw.2
    have h2 : (Finset.univ.filter fun w =>
        (s (u', w) x ∧ s (w, v') y) ∧ (Z.relOf u' w, Z.relOf w v') = ab) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun w _ hw => ?_
      exact Finset.filter_eq_empty_iff.mp hemptyU' (Finset.mem_univ w) hw.2
    rw [h1, h2]

/-- A coherent fission of `X` with `T`-singleton fibers refines every stage of the chain. -/
theorem zrel_le_pairIter (Z : CoherentConfig n) (hZX : Refines Z X)
    (hT : ∀ t ∈ T, SingletonFiber Z t) (k : Nat) :
    ∀ p q : Fin n × Fin n, Z.relOf p.1 p.2 = Z.relOf q.1 q.2 → pairIter X T k p q := by
  induction k with
  | zero =>
    intro p q h
    refine ⟨hZX _ _ _ _ h, ?_, ?_⟩
    · -- source flags, from fiber coherence + the singleton hypothesis
      have hd := Z.relOf_diag_left_eq h
      by_cases h1 : p.1 ∈ T
      · rw [(hT p.1 h1) q.1 hd.symm]
      · by_cases h2 : q.1 ∈ T
        · have heq := (hT q.1 h2) p.1 hd
          rw [heq] at h1
          exact absurd h2 h1
        · unfold extFlag
          rw [if_neg h1, if_neg h2]
    · have hd := Z.relOf_diag_right_eq h
      by_cases h1 : p.2 ∈ T
      · rw [(hT p.2 h1) q.2 hd.symm]
      · by_cases h2 : q.2 ∈ T
        · have heq := (hT q.2 h2) p.2 hd
          rw [heq] at h1
          exact absurd h2 h1
        · unfold extFlag
          rw [if_neg h1, if_neg h2]
  | succ k ih =>
    intro p q h
    rw [pairIter_succ]
    exact ⟨ih p q h, fun x y => pairCount_eq_of_zrel (fun p q h => ih p q h) h x y⟩

/-! #### The closure as a `CoherentConfig`, and the headline -/

/-- The class indexing of the stable partition. -/
noncomputable def stableEquiv :
    Quotient (stableSetoid X T) ≃ Fin (Nat.card (Quotient (stableSetoid X T))) :=
  Finite.equivFin _

theorem stableEquiv_eq_iff {p q : Fin n × Fin n} :
    stableEquiv X T (Quotient.mk _ p) = stableEquiv X T (Quotient.mk _ q) ↔
      stableSetoid X T p q := by
  rw [Equiv.apply_eq_iff_eq]
  exact ⟨Quotient.exact, Quotient.sound⟩

/-- **The point extension, constructed**: the stable pair partition as a `CoherentConfig`. The four
axioms are the §CC.8 invariants — surjectivity from the quotient, transpose from `pairIter_swap`,
diagonal and flags from `pairIter_le_init`, coherence from the fixpoint counts. -/
noncomputable def pointExtension : CoherentConfig n where
  rank := Nat.card (Quotient (stableSetoid X T))
  relOf := fun u v => stableEquiv X T (Quotient.mk _ (u, v))
  relOf_surj := fun t => by
    obtain ⟨⟨p1, p2⟩, hp⟩ := Quotient.exists_rep ((stableEquiv X T).symm t)
    refine ⟨p1, p2, ?_⟩
    rw [hp, Equiv.apply_symm_apply]
  transpose_eq := fun {u v u' v'} h => by
    rw [stableEquiv_eq_iff] at h ⊢
    exact pairIter_swap X T (n * n) (u, v) (u', v') h
  diag_eq := fun {u v w} h => by
    rw [stableEquiv_eq_iff] at h
    have h0 := pairIter_le_init X T (n * n) h
    exact X.diag_eq h0.1
  inter_card_eq := fun {u v u' v'} h a b => by
    rw [stableEquiv_eq_iff] at h
    have hconv : ∀ (w₁ w₂ : Fin n) (c : Fin (Nat.card (Quotient (stableSetoid X T)))),
        stableEquiv X T (Quotient.mk _ (w₁, w₂)) = c ↔
          stableSetoid X T (w₁, w₂) ((stableEquiv X T).symm c).out := by
      intro w₁ w₂ c
      constructor
      · intro hc
        have hmk : (Quotient.mk (stableSetoid X T) (w₁, w₂)) = (stableEquiv X T).symm c :=
          (Equiv.eq_symm_apply _).mpr hc
        exact Quotient.exact (hmk.trans (Quotient.out_eq _).symm)
      · intro hr
        have hmk : (Quotient.mk (stableSetoid X T) (w₁, w₂)) =
            Quotient.mk (stableSetoid X T) ((stableEquiv X T).symm c).out :=
          Quotient.sound hr
        rw [Quotient.out_eq] at hmk
        exact (Equiv.eq_symm_apply _).mp hmk
    have hcnt := stableSetoid_pairCount X T h
      ((stableEquiv X T).symm a).out ((stableEquiv X T).symm b).out
    calc (Finset.univ.filter fun w =>
          stableEquiv X T (Quotient.mk _ (u, w)) = a ∧
          stableEquiv X T (Quotient.mk _ (w, v)) = b).card
        = pairCount (stableSetoid X T) u v
            ((stableEquiv X T).symm a).out ((stableEquiv X T).symm b).out := by
          unfold pairCount
          refine congrArg Finset.card (Finset.filter_congr ?_)
          intro w _
          exact and_congr (hconv u w a) (hconv w v b)
      _ = pairCount (stableSetoid X T) u' v'
            ((stableEquiv X T).symm a).out ((stableEquiv X T).symm b).out := hcnt
      _ = (Finset.univ.filter fun w =>
            stableEquiv X T (Quotient.mk _ (u', w)) = a ∧
            stableEquiv X T (Quotient.mk _ (w, v')) = b).card := by
          unfold pairCount
          refine (congrArg Finset.card (Finset.filter_congr ?_)).symm
          intro w _
          exact and_congr (hconv u' w a) (hconv w v' b)

theorem pointExtension_relOf_eq_iff {u v u' v' : Fin n} :
    (pointExtension X T).relOf u v = (pointExtension X T).relOf u' v' ↔
      stableSetoid X T (u, v) (u', v') :=
  stableEquiv_eq_iff X T

/-- **Stage 1.2(a) headline: the construction satisfies the universal property.** The point
extension exists for every `(X, T)` — `IsPointExtension` is inhabited by `pointExtension`. -/
theorem isPointExtension_pointExtension : IsPointExtension X T (pointExtension X T) := by
  refine ⟨?_, ?_, ?_⟩
  · -- refines X
    intro u v u' v' h
    rw [pointExtension_relOf_eq_iff] at h
    exact (pairIter_le_init X T (n * n) h).1
  · -- T-singleton fibers
    intro t ht u h
    rw [pointExtension_relOf_eq_iff] at h
    exact extFlag_eq_of_mem T ht (pairIter_le_init X T (n * n) h).2.1
  · -- coarsest: any coherent fission with T-singletons refines it
    intro Z hZX hT u v u' v' h
    rw [pointExtension_relOf_eq_iff]
    exact zrel_le_pairIter X T Z hZX hT (n * n) (u, v) (u', v') h

/-- The fission family `IsPointExtension` quantifies over is inhabited for every `(X, T)`. -/
theorem exists_isPointExtension : ∃ Y : CoherentConfig n, IsPointExtension X T Y :=
  ⟨pointExtension X T, isPointExtension_pointExtension X T⟩

/-- Stage 1.2(b): the point extension is unique up to mutual refinement (same pair partition). -/
theorem isPointExtension_unique {Y Y' : CoherentConfig n}
    (h : IsPointExtension X T Y) (h' : IsPointExtension X T Y') :
    Refines Y Y' ∧ Refines Y' Y :=
  ⟨h'.2.2 Y h.1 h.2.1, h.2.2 Y' h'.1 h'.2.1⟩

end PointExtensionConstruction

/-! ### §CC.9 — The pointed transport core (Stage 2: extension separability realizes fiber-twins)

The Stage-2 transport's provable heart, **citation-free**: apply `SeparablePointed` of a point
extension `E` to the **identity** algebraic isomorphism. A same-fiber pair `(u, u')` of `E`
satisfies exactly the pointed condition (`E.relOf u' u' = E.relOf u u`), so pointedness hands back a
vertex permutation `f` inducing the identity — an automorphism of `E` — with `f u = u'`. Such an `f`
fixes every `t ∈ T` (singleton fibers) and descends to an automorphism of the base configuration
(`Refines`). Net: **pointed separability of the extension realizes every fiber-twin by a `T`-fixing
automorphism of `X`** — the object the seal's sink consumes. The 1-WL keying gap (`warmRefine` twins
need not be fiber-twins at arbitrary `T` — the 2026-06-12 direction-check refutation) is NOT bridged
here; it is isolated downstream as `WarmTwinsAreFiberTwins` (`CascadeAffine.lean §S-gate2`). -/

section PointedTransport

/-- **The pointed conclusion at the identity algebraic isomorphism**: pointed separability of `Y` at
`u` realizes every same-fiber `u'` by a class-preserving vertex automorphism. -/
theorem SeparablePointed.exists_aut_of_fiber_eq {Y : CoherentConfig n} {u : Fin n}
    (hsep : Y.SeparablePointed u) {u' : Fin n} (hfib : Y.relOf u' u' = Y.relOf u u) :
    ∃ f : Equiv.Perm (Fin n), (∀ v w, Y.relOf (f v) (f w) = Y.relOf v w) ∧ f u = u' := by
  obtain ⟨f, hind, hu⟩ := hsep Y (idAlgIso Y) u' hfib
  exact ⟨f, fun v w => hind v w, hu⟩

/-- An automorphism of a point extension fixes the individualized points (singleton fibers). -/
theorem IsPointExtension.aut_fixes {X E : CoherentConfig n} {T : Finset (Fin n)}
    (hext : IsPointExtension X T E) {f : Equiv.Perm (Fin n)}
    (hf : ∀ v w, E.relOf (f v) (f w) = E.relOf v w) : ∀ t ∈ T, f t = t :=
  fun t ht => hext.2.1 t ht (f t) (hf t t)

/-- An automorphism of a fission descends to the base configuration. -/
theorem Refines.aut_descends {E X : CoherentConfig n} (href : Refines E X)
    {f : Equiv.Perm (Fin n)} (hf : ∀ v w, E.relOf (f v) (f w) = E.relOf v w) :
    ∀ v w, X.relOf (f v) (f w) = X.relOf v w :=
  fun v w => href _ _ _ _ (hf v w)

/-- **THE STAGE-2 TRANSPORT CORE (citation-free).** Pointed separability of a point extension
realizes every same-fiber pair by a `T`-fixing automorphism of the base configuration. -/
theorem fiberTwin_realized_of_separablePointed {X E : CoherentConfig n} {T : Finset (Fin n)}
    (hext : IsPointExtension X T E) {u u' : Fin n}
    (hsep : E.SeparablePointed u) (hfib : E.relOf u' u' = E.relOf u u) :
    ∃ f : Equiv.Perm (Fin n),
      (∀ v w, X.relOf (f v) (f w) = X.relOf v w) ∧ (∀ t ∈ T, f t = t) ∧ f u = u' := by
  obtain ⟨f, hf, hu⟩ := hsep.exists_aut_of_fiber_eq hfib
  exact ⟨f, hext.1.aut_descends hf, hext.aut_fixes hf, hu⟩

/-- At a rigid base — only the identity `T`-fixing automorphism of `X` — pointed separability of the
extension (at every non-singleton fiber: the singleton fibers, e.g. the points of `T` themselves,
need no realizing and are exactly where the probe saw the conditions fail) forces the extension
**complete**: every fiber a singleton. The fiber-level `b(X) ≤ b(G)` collapse. -/
theorem extension_complete_of_separablePointed {X E : CoherentConfig n} {T : Finset (Fin n)}
    (hext : IsPointExtension X T E)
    (hsep : ∀ u : Fin n, ¬ E.SingletonFiber u → E.SeparablePointed u)
    (hbase : ∀ f : Equiv.Perm (Fin n),
      (∀ v w, X.relOf (f v) (f w) = X.relOf v w) → (∀ t ∈ T, f t = t) → f = 1) :
    ∀ u : Fin n, E.SingletonFiber u := by
  intro u
  by_contra hns
  have hex : ∃ u', E.relOf u' u' = E.relOf u u ∧ u' ≠ u := by
    by_contra hc
    push Not at hc
    exact hns fun s hs => hc s hs
  obtain ⟨u', hfib, hne⟩ := hex
  obtain ⟨f, hfX, hfT, hu⟩ :=
    fiberTwin_realized_of_separablePointed hext (hsep u hns) hfib
  rw [hbase f hfX hfT] at hu
  exact hne (by simpa using hu.symm)

end PointedTransport

variable (X : CoherentConfig n)

/-! ### §CC.10 — The forced-triangle dominator closure on a general CC (the δ′ engine, lifted)

The δ′ closure (`CascadeAffine §S-bridge-δ`) lives on the homogeneous `AssociationScheme` and pins
points using `X`'s **own** rank-`r` relations. The 2026-06-13 probe (`Probe_RainbowRigidFamily`) showed
that for the amorphic-NLS residue at `n ≥ 25` those scheme-level forced triangles **vanish** (`b(X) = 2`
recovery lives in the *extension* `X_T`'s finer colours, not `X`'s rank-4 ones). This section lifts the
forced-triangle closure to a general `CoherentConfig`, so it can run on the point extension `X_T`
(`pointExtension X T`) where the `c = 1` triangles reappear. The criterion is pure counting (mirrors the
scheme version); the discreteness payoff carries one named hypothesis `Sharp` — the coherent-closure
refinement "a singleton fiber sees the whole fiber structure" — which holds for `X_T` and is the
clearly-isolated next discharge. -/

/-- **The forced-triangle criterion on a general CC** (forward). `c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1` when
`γ` is the unique `u` sharing `γ`'s relation-profile to both `α` and `β`. Pure counting via
`inter_card_eq`; the CC mirror of `interNum_eq_one_of_forcedUnique`. -/
theorem interNum_eq_one_of_forcedUnique {α β γ : Fin n}
    (huniq : ∀ u : Fin n, X.relOf α u = X.relOf α γ → X.relOf u β = X.relOf γ β → u = γ) :
    X.interNum (X.relOf α γ) (X.relOf γ β) (X.relOf α β) = 1 := by
  classical
  rw [← X.interNum_eq (rfl : X.relOf α β = X.relOf α β) (X.relOf α γ) (X.relOf γ β),
      Finset.card_eq_one]
  refine ⟨γ, Finset.ext (fun u => ?_)⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun ⟨h1, h2⟩ => huniq u h1 h2, fun hu => hu ▸ ⟨rfl, rfl⟩⟩

/-- **The forced-triangle criterion, reverse direction.** `c = 1 ⟹` the profile-uniqueness pinning `γ`.
The half the singleton-fiber propagation consumes. -/
theorem forcedUnique_of_interNum_eq_one {α β γ : Fin n}
    (hone : X.interNum (X.relOf α γ) (X.relOf γ β) (X.relOf α β) = 1) :
    ∀ u : Fin n, X.relOf α u = X.relOf α γ → X.relOf u β = X.relOf γ β → u = γ := by
  classical
  intro u h1 h2
  have hcard := X.interNum_eq (rfl : X.relOf α β = X.relOf α β) (X.relOf α γ) (X.relOf γ β)
  rw [hone, Finset.card_eq_one] at hcard
  obtain ⟨x, hx⟩ := hcard
  have hγ : γ ∈ (Finset.univ.filter
      fun w => X.relOf α w = X.relOf α γ ∧ X.relOf w β = X.relOf γ β) := by simp
  have hu : u ∈ (Finset.univ.filter
      fun w => X.relOf α w = X.relOf α γ ∧ X.relOf w β = X.relOf γ β) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2⟩
  rw [hx, Finset.mem_singleton] at hγ hu
  exact hu.trans hγ.symm

/-- **The forced-triangle closure of `T` in a general CC** — the δ′ `DominatorReachable`, lifted from
`AssociationScheme` to `CoherentConfig` so it runs on the point extension `X_T`. -/
inductive DominatorReachable (T : Finset (Fin n)) : Fin n → Prop
  | base {t : Fin n} (ht : t ∈ T) : DominatorReachable T t
  | step {α β γ : Fin n} (hα : DominatorReachable T α) (hβ : DominatorReachable T β)
      (hone : X.interNum (X.relOf α γ) (X.relOf γ β) (X.relOf α β) = 1) :
      DominatorReachable T γ

/-- **The CC `DominatorReachable` step builder** from the profile-uniqueness pinning `γ`. -/
theorem dominatorReachable_step_of_unique {T : Finset (Fin n)} {α β γ : Fin n}
    (hα : X.DominatorReachable T α) (hβ : X.DominatorReachable T β)
    (huniq : ∀ u : Fin n, X.relOf α u = X.relOf α γ → X.relOf u β = X.relOf γ β → u = γ) :
    X.DominatorReachable T γ :=
  DominatorReachable.step hα hβ (X.interNum_eq_one_of_forcedUnique huniq)

/-- **The single-base closure from a pinning rank, on a general CC** (mirror of the scheme engine). -/
theorem dominatorReachable_of_rank {T : Finset (Fin n)} (rk : Fin n → Nat)
    (hbase : ∀ v : Fin n, rk v = 0 → v ∈ T)
    (hstep : ∀ γ : Fin n, 0 < rk γ → ∃ α β : Fin n, rk α < rk γ ∧ rk β < rk γ ∧
        ∀ u : Fin n, X.relOf α u = X.relOf α γ → X.relOf u β = X.relOf γ β → u = γ) :
    ∀ v : Fin n, X.DominatorReachable T v := by
  have key : ∀ k : Nat, ∀ v : Fin n, rk v = k → X.DominatorReachable T v := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv
      rcases Nat.eq_zero_or_pos (rk v) with h0 | hpos
      · exact DominatorReachable.base (hbase v h0)
      · obtain ⟨α, β, hα, hβ, huniq⟩ := hstep v hpos
        exact X.dominatorReachable_step_of_unique
          (ih (rk α) (hv ▸ hα) α rfl) (ih (rk β) (hv ▸ hβ) β rfl) huniq
  exact fun v => key (rk v) v rfl

/-- **`Sharp`** — the coherent-closure refinement property: a singleton fiber "sees" the whole fiber
structure (two points in one fiber have the same relation to any singleton fiber). FALSE for a general
CC, TRUE for the point extension `X_T` (its fibers are refined by relation to every individualized /
determined point). Carried here as the named hypothesis the discreteness payoff needs — the isolated
next discharge (prove `Sharp (pointExtension X T)`). -/
def Sharp : Prop :=
  ∀ (a u u' : Fin n), X.SingletonFiber a → X.relOf u u = X.relOf u' u' → X.relOf a u = X.relOf a u'

/-- **Forced-triangle reachability propagates the singleton-fiber property** (modulo `Sharp`). A point
dominator-reachable from a set of singleton fibers is itself a singleton fiber: at each step the two
pinning points `α, β` are singleton fibers (IH), `Sharp` makes a same-fiber twin `γ'` of `γ` share `γ`'s
relations to `α, β`, and the `c = 1` uniqueness then forces `γ' = γ`. -/
theorem singletonFiber_of_dominatorReachable {T : Finset (Fin n)} (hsharp : X.Sharp)
    (hT : ∀ t ∈ T, X.SingletonFiber t) :
    ∀ {v : Fin n}, X.DominatorReachable T v → X.SingletonFiber v := by
  intro v h
  induction h with
  | base ht => exact hT _ ht
  | @step α β γ _ _ hone ihα ihβ =>
    intro γ' hfib
    have h1 : X.relOf α γ' = X.relOf α γ := hsharp α γ' γ ihα hfib
    have hβfib : X.relOf β γ' = X.relOf β γ := hsharp β γ' γ ihβ hfib
    have h2 : X.relOf γ' β = X.relOf γ β := by
      have e1 : X.relOf γ' β = X.transposeRel (X.relOf β γ') := X.relOf_swap_eq rfl
      have e2 : X.relOf γ β = X.transposeRel (X.relOf β γ) := X.relOf_swap_eq rfl
      rw [e1, e2, hβfib]
    exact X.forcedUnique_of_interNum_eq_one hone γ' h1 h2

/-- **The δ′ engine on the extension: the forced-triangle closure ⟹ all fibers singleton.** If every
point is dominator-reachable from `T`, the `T`-points are singleton fibers, and `X` is `Sharp`, then `X`
is discrete (every point a singleton fiber) — the point extension is complete, i.e. `T` is a base. The
general-CC analogue of `CascadeAffine`'s `discrete_of_dominatorClosure`, the citation-free path the
`n ≥ 25` residue needs (the closure runs on `X_T`, not the bare scheme). The lone carried hypothesis is
`Sharp` (true for `X_T`; the isolated next discharge). -/
theorem allSingletonFiber_of_dominatorClosure {T : Finset (Fin n)} (hsharp : X.Sharp)
    (hT : ∀ t ∈ T, X.SingletonFiber t) (hclo : ∀ v, X.DominatorReachable T v) :
    ∀ v : Fin n, X.SingletonFiber v :=
  fun v => X.singletonFiber_of_dominatorReachable hsharp hT (hclo v)

/-- **`Sharp` holds for the point extension** — the isolated next discharge, now proved. The coherent
closure refines vertices by their relations to every singleton fiber: if `a` is a singleton fiber of
`pointExtension X T` and `u, u'` lie in one fiber (`relOf u u = relOf u' u'`), then they have equal
relations to `a` (`relOf a u = relOf a u'`). This is FALSE for a general CC but TRUE here because the
construction is a `pairStep` fixpoint. **Proof:** the count `#{w : r(u,w)=r(u,a) ∧ r(w,u)=r(a,u)}` is
exactly `1` — only `w = a` qualifies, since `r(u,w)=r(u,a)` forces `w` into `a`'s fiber
(`relOf_diag_right_eq`), which is the singleton `{a}` — and the fixpoint coherence
(`stableSetoid_pairCount`) transports that `= 1` to `u'`, producing a witness `w'` that must again be
`a` and so pins `r(a,u') = r(a,u)`. -/
theorem sharp_pointExtension (T : Finset (Fin n)) : (pointExtension X T).Sharp := by
  classical
  intro a u u' hsingle hfib
  -- A pair whose target is in `a`'s (singleton) fiber must have target `a` — regardless of its source.
  have iso_imp : ∀ p q w : Fin n, stableSetoid X T (p, w) (q, a) → w = a := by
    intro p q w h
    have hr : (pointExtension X T).relOf p w = (pointExtension X T).relOf q a :=
      (pointExtension_relOf_eq_iff X T).mpr h
    exact hsingle w ((pointExtension X T).relOf_diag_right_eq hr)
  have hfib' : stableSetoid X T (u, u) (u', u') :=
    (pointExtension_relOf_eq_iff X T).mp hfib
  -- The `a`-isolating count is exactly 1 (only `w = a`).
  have hcount : pairCount (stableSetoid X T) u u (u, a) (a, u) = 1 := by
    unfold pairCount
    rw [Finset.card_eq_one]
    refine ⟨a, ?_⟩
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, -⟩
      exact iso_imp u u w h1
    · rintro rfl
      exact ⟨(stableSetoid X T).iseqv.refl _, (stableSetoid X T).iseqv.refl _⟩
  -- Fixpoint coherence transports the count to `u'`, so the `u'` filter is nonempty.
  have hpc : pairCount (stableSetoid X T) u u (u, a) (a, u)
      = pairCount (stableSetoid X T) u' u' (u, a) (a, u) :=
    stableSetoid_pairCount X T hfib' (u, a) (a, u)
  have hpos : 0 < pairCount (stableSetoid X T) u' u' (u, a) (a, u) := by
    rw [← hpc, hcount]; exact Nat.one_pos
  unfold pairCount at hpos
  rw [Finset.card_pos] at hpos
  obtain ⟨w, hw⟩ := hpos
  rw [Finset.mem_filter] at hw
  obtain ⟨-, hw1, hw2⟩ := hw
  have hwa : w = a := iso_imp u' u w hw1
  rw [hwa] at hw2
  exact ((pointExtension_relOf_eq_iff X T).mpr hw2).symm

/-- **The δ′ closure is complete on the point extension, unconditionally.** If every point is
`DominatorReachable` from `T` in `pointExtension X T`, then `pointExtension X T` is discrete (every
point a singleton fiber) — i.e. `T` is a base. Both auxiliary hypotheses of
`allSingletonFiber_of_dominatorClosure` are now discharged for the extension: `Sharp` by
`sharp_pointExtension`, and the `T`-singleton-fiber property by the universal property
(`isPointExtension_pointExtension`). The sole remaining input is the closure `hclo` itself — the
genuine open `c(X_T)` content (a bounded-base pinning rank for the residue family on the extension). -/
theorem allSingletonFiber_of_dominatorClosure_pointExtension (T : Finset (Fin n))
    (hclo : ∀ v, (pointExtension X T).DominatorReachable T v) :
    ∀ v, (pointExtension X T).SingletonFiber v :=
  (pointExtension X T).allSingletonFiber_of_dominatorClosure (sharp_pointExtension X T)
    (isPointExtension_pointExtension X T).2.1 hclo

/-! ### §CC.11 — The sparse separability substrate on the general CC (A1, the citation-free `c(X_T)` route)

The CC-level port of `Separability.lean §S.1–S.16` (the PV-Thm-3.1 sparse machinery), begun so that the landed
sparse theorem `2c(k−1) < n ⟹ b(X) ≤ 2` can be applied to the **point extension `X_T`** — where M1
(`Probe_CXT_ScopingM1`) showed `c(X_T)` and `k(X_T)` both collapse to `O(1)`, so the sparse hypothesis holds.
This makes the seal closable **citation-free** (no Thm 4.1) — see `docs/chain-descent-cxt-scoping.md` §4-M3 (Option A).

This first increment ports the **indistinguishing number `c(X)`** and its geometric counting form (the shape the
§S.16 connectivity argument consumes), with the transpose bookkeeping the non-symmetric CC needs (the homogeneous
`AssociationScheme` had `s* = s`; here `s* = transposeRel s`). -/

/-- **Indistinguishing number of the class `r`** — `c(r) = Σ_b c^r_{b*,b}` (the CC form of
`Separability.indistinguishingNumberOf`; `b* = transposeRel b`, recovering `Σ_b c^r_{b,b}` when symmetric). -/
noncomputable def indistinguishingNumberOf (r : Fin X.rank) : Nat :=
  Finset.univ.sum (fun b : Fin X.rank => X.interNum (X.transposeRel b) b r)

/-- **The geometric meaning of `c(r)` (PV (7), CC form).** For a pair `(α, β) ∈ r`, `c(r)` counts the vertices
`γ` that relate to `α` and to `β` by the *same* class (`relOf γ α = relOf γ β`) — the `γ` that cannot tell `α`
from `β`. Proof: partition that set by the common value `b = relOf γ α`; each fiber is the forced-triangle count
`c^r_{b*,b}` (the path `α →_{b*} γ →_b β`, via `relOf_swap_eq`), summing to `indistinguishingNumberOf r`. -/
theorem indistinguishingNumberOf_eq_card {r : Fin X.rank} {α β : Fin n}
    (hr : X.relOf α β = r) :
    X.indistinguishingNumberOf r
      = (Finset.univ.filter (fun γ => X.relOf γ α = X.relOf γ β)).card := by
  classical
  rw [indistinguishingNumberOf,
    Finset.card_eq_sum_card_fiberwise (f := fun γ => X.relOf γ α) (t := Finset.univ)
      (fun γ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← X.interNum_eq hr (X.transposeRel b) b]
  congr 1
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    have hγα : X.relOf γ α = b := by
      have h := X.relOf_swap_eq h1
      rwa [transposeRel_transposeRel] at h
    exact ⟨hγα.trans h2.symm, hγα⟩
  · rintro ⟨heq, hb⟩
    exact ⟨X.relOf_swap_eq hb, heq.symm.trans hb⟩

/-- A class is **reflexive** (diagonal) if some loop lies in it. The indistinguishing number maxes over the
*non*-reflexive classes (a diagonal class has every off-pair distinguishing it). -/
def IsReflexive (r : Fin X.rank) : Prop := ∃ u : Fin n, X.relOf u u = r

open scoped Classical

/-- **The indistinguishing number `c(X)`** — `max_{r non-reflexive} c(r)`. -/
noncomputable def indistinguishingNumber : Nat :=
  (Finset.univ.filter (fun r : Fin X.rank => ¬ X.IsReflexive r)).sup X.indistinguishingNumberOf

/-- `c(r) ≤ c(X)` for every non-reflexive class `r`. -/
theorem indistinguishingNumberOf_le {r : Fin X.rank} (hr : ¬ X.IsReflexive r) :
    X.indistinguishingNumberOf r ≤ X.indistinguishingNumber :=
  Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_univ r, hr⟩)

/-- The **source fiber** of a class `r` — the reflexive class `relOf u u` of any `u` with `(u, ·) ∈ r`
(well-defined: `relOf_diag_left_eq`). On a homogeneous scheme this is always `R₀`; on a multi-fiber CC it
is the fiber `r` emanates from. -/
noncomputable def sourceFiber (r : Fin X.rank) : Fin X.rank :=
  X.relOf (X.repPair r).1 (X.repPair r).1

/-- **Valency of the class `r`** — its out-degree `#{w : relOf u w = r}` from a source point `u`. The CC
form of `Separability.valency`; expressed via `interNum` against the source fiber (`relOf u w = r` already
forces `relOf w u = transposeRel r`, so the second leg is free). -/
noncomputable def valency (r : Fin X.rank) : Nat :=
  X.interNum r (X.transposeRel r) (X.sourceFiber r)

/-- **Valency is the out-degree.** For any `(u, v) ∈ r`, `valency r = #{w : relOf u w = r}` (constant on the
source fiber, by coherence). -/
theorem valency_eq_card {u v : Fin n} {r : Fin X.rank} (h : X.relOf u v = r) :
    X.valency r = (Finset.univ.filter (fun w => X.relOf u w = r)).card := by
  have hfib : X.relOf u u = X.sourceFiber r :=
    X.relOf_diag_left_eq (h.trans (X.relOf_repPair r).symm)
  unfold valency
  rw [← hfib, ← X.interNum_eq (u := u) (v := u) rfl r (X.transposeRel r)]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hw => hw.1, fun hw => ⟨hw, X.relOf_swap_eq hw⟩⟩

/-- **The maximum valency `k(X)`** — the largest out-degree over all non-reflexive classes. -/
noncomputable def maxValency : Nat :=
  (Finset.univ.filter (fun r : Fin X.rank => ¬ X.IsReflexive r)).sup X.valency

/-- Every non-reflexive valency is `≤ k(X)`. -/
theorem valency_le_maxValency {r : Fin X.rank} (hr : ¬ X.IsReflexive r) :
    X.valency r ≤ X.maxValency :=
  Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_univ r, hr⟩)

/-- **The PV-Thm-3.1 sparsity hypothesis `2c(k−1) < n`, on a general CC.** When it holds on the point
extension `X_T` (M1: `c(X_T), k(X_T) = O(1)` ⟹ this holds for large `n`), the landed sparse theorem's
content discretizes `X_T` in `≤ 2` further points — the citation-free `c(X_T)` route (scoping §4-M3 Option A). -/
def SparseSeparable : Prop := 2 * X.indistinguishingNumber * (X.maxValency - 1) < n

/-! ### §CC.12 — The global estimate (19): `Σ_{δ∈Δ} pᵤ(δ) ≤ k(k−1)·c` (A1, the connectivity workhorse)

The CC port of `Separability.lean §S.6` (`sum_pu_le`), the counting workhorse the §S.16 connectivity
argument consumes. The proof is the same double-count swap + per-pair `c(r) ≤ c(X)` bound, but the
non-symmetric CC needs two pieces of transpose bookkeeping the homogeneous version got for free:
(a) the neighbour count is bounded by `k(X)` only for *non-reflexive* `u` (`card_relNeighbors_le_maxValency`,
in place of homogeneity's exact `= k` — on a multi-fiber CC `α` need not lie in `u`'s source fiber, in
which case the set is empty); and (b) the inner indistinguishing bound goes through the **transpose
bridge** `relOf_right_eq_iff_left` (the CC substitute for `relOfPair_symm`) so the pair-count
`#{δ : relOf β δ = relOf γ δ}` meets `indistinguishingNumberOf_eq_card`'s left-argument form. -/

/-- The transpose bridge: `δ` relates the same way to `a` and `b` on the *right* iff on the *left*.
The non-symmetric CC's substitute for `AssociationScheme.relOfPair_symm` in the (19) estimate. -/
theorem relOf_right_eq_iff_left (a b δ : Fin n) :
    X.relOf a δ = X.relOf b δ ↔ X.relOf δ a = X.relOf δ b := by
  constructor
  · intro h
    rw [X.relOf_swap_eq (rfl : X.relOf a δ = X.relOf a δ),
        X.relOf_swap_eq (rfl : X.relOf b δ = X.relOf b δ), h]
  · intro h
    rw [X.relOf_swap_eq (rfl : X.relOf δ a = X.relOf δ a),
        X.relOf_swap_eq (rfl : X.relOf δ b = X.relOf δ b), h]

/-- A non-diagonal pair lies in a non-reflexive class: `a ≠ b → ¬ IsReflexive (relOf a b)` (a
reflexive class is purely diagonal, `diag_eq`). -/
theorem not_isReflexive_relOf_of_ne {a b : Fin n} (hab : a ≠ b) :
    ¬ X.IsReflexive (X.relOf a b) := by
  rintro ⟨u, hu⟩
  exact hab (X.diag_eq hu)

/-- The `u`-out-neighbour set of `α` has at most `k(X)` elements when `u` is non-reflexive — the CC
replacement for homogeneity's exact `card = k`. (When `α` does not lie in `u`'s source fiber the set
is empty; otherwise it has size `valency u ≤ maxValency`.) -/
theorem card_relNeighbors_le_maxValency (α : Fin n) {u : Fin X.rank}
    (hu : ¬ X.IsReflexive u) :
    (Finset.univ.filter (fun w => X.relOf α w = u)).card ≤ X.maxValency := by
  classical
  by_cases h : ∃ v, X.relOf α v = u
  · obtain ⟨v, hv⟩ := h
    rw [← X.valency_eq_card hv]
    exact X.valency_le_maxValency hu
  · have he : (Finset.univ.filter (fun w => X.relOf α w = u)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro w _ hw
      exact h ⟨w, hw⟩
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

/-- **The pair-count `pᵤ(δ)`** (CC form) — the number of ordered distinct pairs `(β, γ)` of
`u`-out-neighbours of `α` that `δ` fails to distinguish (`relOf β δ = relOf γ δ`). The §3 counting
workhorse, on a general CC. -/
noncomputable def pu (α : Fin n) (u : Fin X.rank) (δ : Fin n) : Nat :=
  (Finset.univ.filter (fun bg : Fin n × Fin n =>
      X.relOf α bg.1 = u ∧ X.relOf α bg.2 = u ∧ bg.1 ≠ bg.2 ∧
      X.relOf bg.1 δ = X.relOf bg.2 δ)).card

/-- Reformulation of `pᵤ(δ)` over the off-diagonal of the `u`-neighbour set `αu`. -/
theorem pu_eq (α : Fin n) (u : Fin X.rank) (δ : Fin n) :
    X.pu α u δ
      = ((Finset.univ.filter (fun w => X.relOf α w = u)).offDiag.filter
          (fun bg => X.relOf bg.1 δ = X.relOf bg.2 δ)).card := by
  unfold pu
  congr 1
  ext bg
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩

private theorem nat_kk_sub_self (k : ℕ) : k * k - k = k * (k - 1) := by
  cases k with
  | zero => rfl
  | succ m => simp only [Nat.succ_sub_one, Nat.mul_succ, Nat.add_sub_cancel]

/-- **The global estimate (19), CC form** — `Σ_{δ∈Δ} pᵤ(δ) ≤ k(k−1)·c` for a non-reflexive class `u`
and any vertex set `Δ`. The double-count swap (`Finset.sum_comm`) bounds each `(β,γ)`-fiber by
`c(relOf β γ) ≤ c(X)` (through the transpose bridge `relOf_right_eq_iff_left` into
`indistinguishingNumberOf_eq_card`) and counts the `≤ k(k−1)` off-diagonal neighbour pairs. The
workhorse of the §S.16 connectivity port. Axiom-clean. -/
theorem sum_pu_le (α : Fin n) {u : Fin X.rank} (hu : ¬ X.IsReflexive u) (Δ : Finset (Fin n)) :
    (Δ.sum (fun δ => X.pu α u δ))
      ≤ X.maxValency * (X.maxValency - 1) * X.indistinguishingNumber := by
  classical
  set A := Finset.univ.filter (fun w => X.relOf α w = u) with hA
  have hAcard : A.card ≤ X.maxValency := X.card_relNeighbors_le_maxValency α hu
  -- Swap summation: `Σ_δ pᵤ(δ) = Σ_{(β,γ)∈A.offDiag} |{δ∈Δ : δ fails to split β,γ}|`.
  have hstep : (Δ.sum (fun δ => X.pu α u δ))
      = A.offDiag.sum (fun bg => (Δ.filter
          (fun δ => X.relOf bg.1 δ = X.relOf bg.2 δ)).card) := by
    simp_rw [X.pu_eq α u, Finset.card_filter]
    rw [Finset.sum_comm]
  -- Each inner term is bounded by `c(X)`, through the transpose bridge.
  have hbound : ∀ bg ∈ A.offDiag,
      (Δ.filter (fun δ => X.relOf bg.1 δ = X.relOf bg.2 δ)).card
        ≤ X.indistinguishingNumber := by
    intro bg hbg
    rw [Finset.mem_offDiag] at hbg
    obtain ⟨_, _, hne⟩ := hbg
    calc (Δ.filter (fun δ => X.relOf bg.1 δ = X.relOf bg.2 δ)).card
        ≤ (Finset.univ.filter (fun δ => X.relOf bg.1 δ = X.relOf bg.2 δ)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ Δ))
      _ = (Finset.univ.filter (fun δ => X.relOf δ bg.1 = X.relOf δ bg.2)).card := by
          congr 1; ext δ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact X.relOf_right_eq_iff_left bg.1 bg.2 δ
      _ = X.indistinguishingNumberOf (X.relOf bg.1 bg.2) :=
          (X.indistinguishingNumberOf_eq_card rfl).symm
      _ ≤ X.indistinguishingNumber :=
          X.indistinguishingNumberOf_le (X.not_isReflexive_relOf_of_ne hne)
  -- Assemble: `Σ ≤ |A.offDiag|·c = (k²−k)·c = k(k−1)·c`.
  rw [hstep]
  calc A.offDiag.sum (fun bg => (Δ.filter
          (fun δ => X.relOf bg.1 δ = X.relOf bg.2 δ)).card)
      ≤ A.offDiag.sum (fun _ => X.indistinguishingNumber) := Finset.sum_le_sum hbound
    _ = A.offDiag.card * X.indistinguishingNumber := by rw [Finset.sum_const, smul_eq_mul]
    _ = (A.card * A.card - A.card) * X.indistinguishingNumber := by rw [Finset.offDiag_card]
    _ = A.card * (A.card - 1) * X.indistinguishingNumber := by rw [nat_kk_sub_self]
    _ ≤ X.maxValency * (X.maxValency - 1) * X.indistinguishingNumber :=
        Nat.mul_le_mul (Nat.mul_le_mul hAcard (Nat.sub_le_sub_right hAcard 1)) (Nat.le_refl _)

/-! ### §CC.13 — Identity (20): `pᵤ(δ) = Σ_w cᵛ_{uw}(cᵛ_{uw}−1)` (A1, the pair-count ↔ intersection-number bridge)

The CC port of `Separability.lean §S.7` (`pu_eq_sum`). Group the `(β,γ)` counted by `pᵤ(δ)` by their common class
`w = relOf β δ = relOf γ δ` to the test point `δ` (with `v = relOf α δ`): each `w`-fiber is the off-diagonal of the
`interNum u w v`-element set `{β : relOf α β = u ∧ relOf β δ = w}`, contributing `c·(c−1)` ordered distinct pairs. The
bridge from the geometric pair-count to the intersection numbers, used by both halves of Lemma 3.5. The fiber-card step is
*more direct* than the homogeneous one — the CC's colour-function `interNum_eq` already matches the filter shape, with no
`rel`↔`relOfPair` conversion and no transpose subtlety (the orientation `relOf α β = u`, `relOf β δ = w` is exactly
`interNum u w (relOf α δ)`). -/

/-- **Identity (20), CC form** — `pᵤ(δ) = Σ_w c^v_{uw}(c^v_{uw}−1)` with `v = relOf α δ`. Fiber `pᵤ(δ)` by the common
class `w = relOf β δ`; each fiber is the off-diagonal of the `interNum u w v`-element set `{β : relOf α β = u ∧ relOf β δ
= w}`. The bridge from the pair-count to intersection numbers. Axiom-clean. -/
theorem pu_eq_sum (α : Fin n) (u : Fin X.rank) (δ : Fin n) :
    X.pu α u δ
      = Finset.univ.sum (fun w : Fin X.rank =>
          X.interNum u w (X.relOf α δ) * (X.interNum u w (X.relOf α δ) - 1)) := by
  classical
  unfold pu
  rw [Finset.card_eq_sum_card_fiberwise (f := fun bg : Fin n × Fin n => X.relOf bg.1 δ)
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  -- The `w`-fiber is the off-diagonal of `{β ∈ αu : relOf β δ = w}`.
  have hfib : ((Finset.univ.filter (fun bg : Fin n × Fin n =>
          X.relOf α bg.1 = u ∧ X.relOf α bg.2 = u ∧ bg.1 ≠ bg.2 ∧
          X.relOf bg.1 δ = X.relOf bg.2 δ)).filter
            (fun bg => X.relOf bg.1 δ = w))
        = (Finset.univ.filter (fun β => X.relOf α β = u ∧ X.relOf β δ = w)).offDiag := by
    ext bg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨h1, h2, hne, heq⟩, hw⟩
      exact ⟨⟨h1, hw⟩, ⟨h2, heq ▸ hw⟩, hne⟩
    · rintro ⟨⟨h1, hw1⟩, ⟨h2, hw2⟩, hne⟩
      exact ⟨⟨h1, h2, hne, hw1.trans hw2.symm⟩, hw1⟩
  rw [hfib, Finset.offDiag_card]
  -- The fiber's vertex set has `interNum u w (relOf α δ)` elements (directly, by `interNum_eq`).
  have hcard : (Finset.univ.filter (fun β => X.relOf α β = u ∧ X.relOf β δ = w)).card
      = X.interNum u w (X.relOf α δ) :=
    X.interNum_eq (rfl : X.relOf α δ = X.relOf α δ) u w
  rw [hcard, nat_kk_sub_self]

/-! ### §CC.14 — The triangle identity `n_k·c^k_{i,j} = n_i·c^i_{k,j*}` (A1, transpose-aware §S.8)

The CC port of `Separability.lean §S.8` (`valency_mul_intersectionNumber`). Double-count the coloured triangles
`x →ᵢ y →ⱼ z` with `x →ₖ z` through a fixed apex `x`: by the `z`-leg ⟹ `(out-degree to k)·c^k_{ij}`, by the `y`-leg ⟹
`(out-degree to i)·c^i_{k,j*}`. **The homogeneous proof used scheme symmetry (`rel_symm`) to flip the `j`-leg; on the
non-symmetric CC that flip introduces a transpose — `c^i_{k,j}` becomes `c^i_{k,j*}` (`j* = transposeRel j`).** This is the
first place M2-Q1's non-symmetry changes the *statement* (not just the proof). The core `outDeg_mul_interNum` is
hypothesis-free (out-degrees, not valencies); the valency form needs an apex realizing both source fibers (in the downstream
`saAdj`-triangle the apex `α` realizes them by construction). The graph layer (`smaxAdj`/`saAdj`/`saAdj_symm`) is the next
increment — `smaxAdj` is *not* symmetric on a general CC (`n_s ≠ n_{s*}` across fibers), so it needs separate care. -/

/-- **The triangle double-count (out-degree form, unconditional)** — `(deg_k x)·c^k_{i,j} = (deg_i x)·c^i_{k,j*}`,
where `deg_r x = #{w : relOf x w = r}`. Counting the triangles `x →ᵢ y →ⱼ z`, `x →ₖ z` by the `z`-leg vs the `y`-leg.
The transpose `j*` on the right is the non-symmetric CC's correction to the homogeneous identity. Axiom-clean. -/
theorem outDeg_mul_interNum (i j k : Fin X.rank) (x : Fin n) :
    (Finset.univ.filter (fun z => X.relOf x z = k)).card * X.interNum i j k
      = (Finset.univ.filter (fun y => X.relOf x y = i)).card
          * X.interNum k (X.transposeRel j) i := by
  classical
  set D := Finset.univ.filter (fun p : Fin n × Fin n =>
      X.relOf x p.1 = i ∧ X.relOf p.1 p.2 = j ∧ X.relOf x p.2 = k) with hD
  -- Count `D` by the `z`-coordinate ⟹ `(deg_k x)·c^k_{ij}`.
  have hA : D.card = (Finset.univ.filter (fun z => X.relOf x z = k)).card * X.interNum i j k := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Fin n × Fin n => p.2)
          (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    have hfz : ∀ z : Fin n,
        (D.filter (fun p => p.2 = z)).card
        = if X.relOf x z = k then X.interNum i j k else 0 := by
      intro z
      by_cases hk : X.relOf x z = k
      · rw [if_pos hk, ← X.interNum_eq hk i j]
        apply Finset.card_bij (fun p _ => p.1)
        · intro p hp
          simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          obtain ⟨⟨hi1, hj1, _⟩, hz⟩ := hp
          exact ⟨hi1, hz ▸ hj1⟩
        · intro p hp q hq hpq
          simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
          exact Prod.ext hpq (hp.2.trans hq.2.symm)
        · intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          refine ⟨(y, z), ?_, rfl⟩
          simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨⟨hy.1, hy.2, hk⟩, trivial⟩
      · rw [if_neg hk, Finset.card_eq_zero]
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        obtain ⟨⟨_, _, hk1⟩, hz⟩ := hp
        exact hk (hz ▸ hk1)
    rw [Finset.sum_congr rfl (fun z _ => hfz z), ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  -- Count `D` by the `y`-coordinate ⟹ `(deg_i x)·c^i_{k,j*}`.
  have hB : D.card = (Finset.univ.filter (fun y => X.relOf x y = i)).card
      * X.interNum k (X.transposeRel j) i := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Fin n × Fin n => p.1)
          (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    have hfy : ∀ y : Fin n,
        (D.filter (fun p => p.1 = y)).card
        = if X.relOf x y = i then X.interNum k (X.transposeRel j) i else 0 := by
      intro y
      by_cases hi' : X.relOf x y = i
      · rw [if_pos hi', ← X.interNum_eq hi' k (X.transposeRel j)]
        apply Finset.card_bij (fun p _ => p.2)
        · intro p hp
          simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          obtain ⟨⟨_, hj1, hk1⟩, hy⟩ := hp
          exact ⟨hk1, X.relOf_swap_eq (hy ▸ hj1)⟩
        · intro p hp q hq hpq
          simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
          exact Prod.ext (hp.2.trans hq.2.symm) hpq
        · intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
          refine ⟨(y, z), ?_, rfl⟩
          simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and]
          have hyz : X.relOf y z = j := by
            have h := X.relOf_swap_eq hz.2
            rwa [transposeRel_transposeRel] at h
          exact ⟨⟨hi', hyz, hz.1⟩, trivial⟩
      · rw [if_neg hi', Finset.card_eq_zero]
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        obtain ⟨⟨hi1, _, _⟩, hy⟩ := hp
        exact hi' (hy ▸ hi1)
    rw [Finset.sum_congr rfl (fun y _ => hfy y), ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  exact hA.symm.trans hB

/-- **The triangle identity (valency form), transpose-aware** — `n_k·c^k_{i,j} = n_i·c^i_{k,j*}`, given an apex `x`
realizing both source fibers (`relOf x y₀ = i`, `relOf x z₀ = k`, so `valency_eq_card` reads each out-degree as the
valency). The CC analogue of `Separability.valency_mul_intersectionNumber`; the `j*` is the non-symmetric correction.
Axiom-clean. -/
theorem valency_mul_interNum (i j k : Fin X.rank) {x y₀ z₀ : Fin n}
    (hi : X.relOf x y₀ = i) (hk : X.relOf x z₀ = k) :
    X.valency k * X.interNum i j k = X.valency i * X.interNum k (X.transposeRel j) i := by
  rw [X.valency_eq_card hk, X.valency_eq_card hi]
  exact X.outDeg_mul_interNum i j k x

/-! ### §CC.15 — The max-valency / local-rigidity graph layer (A1, §S.4 + `saAdj_symm`)

The CC port of `Separability.lean §S.4` (the `smax`/`sα` graph defs) and the `saAdj_symm` half of §S.8. `InSmax` is the
max-valency predicate; `smaxAdj` the (out-going) max-valency graph; `saAdj α` the local-rigidity relation on `α`'s
max-valency neighbourhood (the forced `c=1` triangle). **`smaxAdj` is NOT symmetric on a general CC** (`n_s ≠ n_{s*}` when
fibers differ in size — symmetric only *within* a fiber, where the pair-count identity gives `n_s = n_{s*}`; the homogeneous
`smaxAdj_symm` used `rel_symm`). The within-fiber `smaxAdj`-symmetry and the connectivity theorems (`smaxConnected`/
`saConnected_of_sparseSeparable`) — which are intrinsically *single-fiber* (the PV counting `valency_le_pu_of_valency_lt`
needs the apex in `u`'s source fiber) — are the next increment. **`saAdj_symm` is landed here** because it does *not* need a
symmetric `smaxAdj`: the two triangle legs are both out-going from `α` (so `InSmax` gives them *equal* valency directly), and
the §CC.14 transpose-aware identity supplies the cancellation — the `j*` it produces lands exactly on `relOf γ β =
(relOf β γ)*`, which is the reflected triangle's leg. -/

/-- A class is **max-valency** (`InSmax`): its out-degree equals `k(X)`. The `Smax`-membership predicate. -/
def InSmax (r : Fin X.rank) : Prop := X.valency r = X.maxValency

/-- The **`smax` graph** adjacency (out-going form): `relOf a b` is a max-valency class. *Not* symmetric on a general CC
(`n_s ≠ n_{s*}` across fibers); the connectivity treatment is the next increment. -/
def smaxAdj (a b : Fin n) : Prop := X.InSmax (X.relOf a b)

/-- Connectedness of the `smax` graph. -/
def SmaxConnected : Prop := ∀ a b : Fin n, Relation.ReflTransGen X.smaxAdj a b

/-- The **local-rigidity relation `sα`** on `αsmax`: for `β, γ` max-valency neighbours of `α`, the coloured triangle
`{α,β,γ}` is forced — `c^{r(α,γ)}_{r(α,β),r(β,γ)} = 1`. The CC port of `Separability.saAdj`. -/
def saAdj (α β γ : Fin n) : Prop :=
  X.smaxAdj α β ∧ X.smaxAdj α γ ∧
    X.interNum (X.relOf α β) (X.relOf β γ) (X.relOf α γ) = 1

/-- Connectedness of `sα` on `αsmax`: every two max-valency neighbours of `α` are joined by an `sα`-path. -/
def SaConnected (α : Fin n) : Prop :=
  ∀ β γ : Fin n, X.smaxAdj α β → X.smaxAdj α γ → Relation.ReflTransGen (X.saAdj α) β γ

/-- **`sα` is symmetric** (the CC port of `Separability.saAdj_symm`, via the transpose-aware triangle identity §CC.14).
Both legs `r = relOf α β`, `t = relOf α γ` have valency `k` (max), so `valency_mul_interNum` turns `c^t_{r,s} = 1` into
`c^r_{t,s*} = 1` — and `s* = relOf γ β`, so `c^r_{t,s*}` is exactly the reflected triangle `c^{r(α,β)}_{r(α,γ),r(γ,β)}`. This
makes the `sα`-components (`ReflTransGen (saAdj α)`) a genuine equivalence. Axiom-clean. -/
theorem saAdj_symm (α : Fin n) {β γ : Fin n} (h : X.saAdj α β γ) : X.saAdj α γ β := by
  obtain ⟨hβ, hγ, htri⟩ := h
  refine ⟨hγ, hβ, ?_⟩
  have hvβ : X.valency (X.relOf α β) = X.maxValency := hβ
  have hvγ : X.valency (X.relOf α γ) = X.maxValency := hγ
  have hpos : 0 < X.maxValency := by
    rw [← hvβ, X.valency_eq_card (rfl : X.relOf α β = X.relOf α β)]
    exact Finset.card_pos.2 ⟨β, by simp⟩
  have hid := X.valency_mul_interNum (X.relOf α β) (X.relOf β γ) (X.relOf α γ) rfl rfl
  rw [htri, Nat.mul_one, hvβ, hvγ] at hid
  rw [X.relOf_swap_eq (rfl : X.relOf β γ = X.relOf β γ)]
  exact (Nat.eq_of_mul_eq_mul_left hpos (by rw [Nat.mul_one]; exact hid)).symm

/-! ### §CC.16 — The summation identity (§S.5) + Lemma 3.5(1)'s `n_u>n_v` half (§S.9) (A1)

The CC ports of `Separability.lean §S.5` (`sum_intersectionNumber_eq_valency`) and §S.9 (the `n_u>n_v` half of Lemma 3.5(1)).
**§S.5** is stated in *out-degree* form (`Σ_w c^v_{uw} = deg_u α`, no fiber hypothesis); the homogeneous `= valency u` is the
special case where `α` is a source of `u`. **§S.9** is the first connectivity-counting lemma, and it carries an explicit
**source witness** `relOf α β₀ = u` (the apex `α` lies in `u`'s source fiber) — required because `valency_mul_interNum`
(§CC.14) needs the apex to realize the fiber (M2-Q1's single-fiber localization). The transpose `w*` the triangle identity
introduces is harmless here (the argument only case-splits on a multiplicand being `0` or `≥1`). -/

/-- **The summation identity (§S.5), out-degree form** — `Σ_w c^v_{uw} = deg_u α` (`= #{z : relOf α z = u}`), for any
`(α,δ) ∈ v`. Fixing the source `u` and the test pair `v = relOf α δ`, summing the intersection number over the middle
class `w` recovers the out-degree of `α` into `u`. (Equals `valency u` when `α` is a source of `u`.) Axiom-clean. -/
theorem sum_interNum_eq_outDeg (u v : Fin X.rank) (α δ : Fin n) (hv : X.relOf α δ = v) :
    (Finset.univ.sum (fun w => X.interNum u w v))
      = (Finset.univ.filter (fun z => X.relOf α z = u)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun z => X.relOf z δ) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
  exact Finset.sum_congr rfl (fun w _ => by rw [← X.interNum_eq hv u w, Finset.filter_filter])

/-- **The core of Lemma 3.5(1) (§S.9).** If every middle class `w` has `c^v_{uw} ≠ 1` (`v = relOf α δ`), then each term
`c^v_{uw}(c^v_{uw}−1) ≥ c^v_{uw}`, and summing (identity (20) `pu_eq_sum` + the summation identity §S.5) gives
`n_u ≤ pᵤ(δ)`. Carries the source witness `relOf α β₀ = u`. Axiom-clean. -/
theorem valency_le_pu_of_forall_ne_one {α : Fin n} (u : Fin X.rank) (δ : Fin n) {β₀ : Fin n}
    (hu : X.relOf α β₀ = u) (h : ∀ w, X.interNum u w (X.relOf α δ) ≠ 1) :
    X.valency u ≤ X.pu α u δ := by
  rw [X.pu_eq_sum α u δ, X.valency_eq_card hu,
    ← X.sum_interNum_eq_outDeg u (X.relOf α δ) α δ rfl]
  apply Finset.sum_le_sum
  intro w _
  rcases Nat.eq_zero_or_pos (X.interNum u w (X.relOf α δ)) with hc0 | hc0
  · simp [hc0]
  · calc X.interNum u w (X.relOf α δ)
        = X.interNum u w (X.relOf α δ) * 1 := (Nat.mul_one _).symm
      _ ≤ X.interNum u w (X.relOf α δ) * (X.interNum u w (X.relOf α δ) - 1) :=
          Nat.mul_le_mul (le_refl _) (by have := h w; omega)

/-- A `c^v_{uw} = 1` would force (triangle identity §CC.14) `n_u ≤ n_v`, so `n_v < n_u ⟹ c^v_{uw} ≠ 1` (`v = relOf α δ`).
Carries the source witness `relOf α β₀ = u`. The transpose `w*` from the identity is harmless (only `0`-vs-`≥1` is used).
Axiom-clean. -/
theorem interNum_ne_one_of_valency_lt {α : Fin n} (u w : Fin X.rank) (δ : Fin n) {β₀ : Fin n}
    (hu : X.relOf α β₀ = u) (hlt : X.valency (X.relOf α δ) < X.valency u) :
    X.interNum u w (X.relOf α δ) ≠ 1 := by
  intro h1
  have hid := X.valency_mul_interNum u w (X.relOf α δ) hu (rfl : X.relOf α δ = X.relOf α δ)
  rw [h1, Nat.mul_one] at hid
  rcases Nat.eq_zero_or_pos (X.interNum (X.relOf α δ) (X.transposeRel w) u) with hm | hm
  · rw [hm, Nat.mul_zero] at hid
    have hvpos : 0 < X.valency (X.relOf α δ) := by
      rw [X.valency_eq_card (rfl : X.relOf α δ = X.relOf α δ)]
      exact Finset.card_pos.2 ⟨δ, by simp⟩
    omega
  · have hle : X.valency u ≤ X.valency (X.relOf α δ) :=
      calc X.valency u = X.valency u * 1 := (Nat.mul_one _).symm
        _ ≤ X.valency u * X.interNum (X.relOf α δ) (X.transposeRel w) u :=
            Nat.mul_le_mul (le_refl _) hm
        _ = X.valency (X.relOf α δ) := hid.symm
    omega

/-- **Lemma 3.5(1), the `n_u > n_v` half** — `n_v < n_u ⟹ n_u ≤ pᵤ(δ)` (`v = relOf α δ`), the `≠1` core fed by the
triangle identity. Carries the source witness `relOf α β₀ = u`. Powers Lemma 3.6's `smax` branch. Axiom-clean. -/
theorem valency_le_pu_of_valency_lt {α : Fin n} (u : Fin X.rank) (δ : Fin n) {β₀ : Fin n}
    (hu : X.relOf α β₀ = u) (hlt : X.valency (X.relOf α δ) < X.valency u) :
    X.valency u ≤ X.pu α u δ :=
  X.valency_le_pu_of_forall_ne_one u δ hu
    (fun w => X.interNum_ne_one_of_valency_lt u w δ hu hlt)

/-! ### §CC.17 — The fiber-size identity + within-fiber `smaxAdj` symmetry (A1, §S.10 prerequisite)

The PV §S.10 `smaxConnected_of_sparseSeparable` runs the generic `exists_small_closed_of_not_connected`, which
needs a **symmetric** relation. On a homogeneous scheme `smaxAdj` is symmetric for free (`n_{s*} = n_s`); on the
multi-fiber CC it is **not** — a max-valency class in one fiber need not have a max-valency transpose into another
(`n_s ≠ n_{s*}` across fibers). This section establishes the one piece that survives: `smaxAdj` is symmetric
**within a fiber** (`relOf a a = relOf b b`), via the **fiber-size identity** `|F_src(r)|·n_r = |F_tgt(r)|·n_{r*}`
(double-count the class `{(u,v) : relOf u v = r}` by source vs. target). When `a,b` share a fiber the two source
fibers coincide and cancel, giving `n_r = n_{r*}`. `outDeg_eq_interNum` is the reusable brick (it also re-proves
`valency_eq_card` as the `relOf u u = sourceFiber r` case). **This is exactly the cross-fiber wall §6.1 predicted:
global `SmaxConnected` is unavailable; smax connectivity localizes to a single fiber.** -/

/-- **The fiber of a reflexive class `f`**, as a vertex set: the points whose loop lies in `f`. -/
def fiberSet (f : Fin X.rank) : Finset (Fin n) := Finset.univ.filter (fun u => X.relOf u u = f)

/-- **The out-degree depends only on the source fiber.** For any point `u` and class `r`,
`#{w : relOf u w = r} = c^{relOf u u}_{r, r*}`. Generalises `valency_eq_card` (the `relOf u u = sourceFiber r`
case): the second leg `relOf w u = r*` is automatic from `relOf u w = r` (`relOf_swap_eq`), so the filter against
the loop `(u,u)` is just the `u`-out-neighbours of `r`. Axiom-clean. -/
theorem outDeg_eq_interNum (u : Fin n) (r : Fin X.rank) :
    (Finset.univ.filter (fun w => X.relOf u w = r)).card
      = X.interNum r (X.transposeRel r) (X.relOf u u) := by
  rw [← X.interNum_eq (u := u) (v := u) rfl r (X.transposeRel r)]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hw => ⟨hw, X.relOf_swap_eq hw⟩, fun hw => hw.1⟩

/-- **The fiber-size identity** — `|F_src(r)|·n_r = |F_tgt(r)|·n_{r*}`. Double-count the class
`{(u,v) : relOf u v = r}`: by source `u` it is `Σ_u #{v : relOf u v = r}`, where each term is `n_r` on the source
fiber `F_src(r) = fiberSet (sourceFiber r)` and `0` elsewhere (`outDeg_eq_interNum` + `relOf_diag_left_eq`); by
target `v` (Fubini + `relOf_swap_eq`) it is `|F_tgt(r)|·n_{r*}` with `F_tgt(r) = fiberSet (sourceFiber r*)`. The new
content (homogeneity made this trivial, `F_src = F_tgt = Ω`). Axiom-clean. -/
theorem fiberSize_mul_valency (r : Fin X.rank) :
    (X.fiberSet (X.sourceFiber r)).card * X.valency r
      = (X.fiberSet (X.sourceFiber (X.transposeRel r))).card * X.valency (X.transposeRel r) := by
  classical
  -- the "out-degree sum = fiberSize · valency" building block
  have step : ∀ s : Fin X.rank,
      (Finset.univ.sum (fun u => (Finset.univ.filter (fun w => X.relOf u w = s)).card))
        = (X.fiberSet (X.sourceFiber s)).card * X.valency s := by
    intro s
    have hterm : ∀ u : Fin n, (Finset.univ.filter (fun w => X.relOf u w = s)).card
        = if X.relOf u u = X.sourceFiber s then X.valency s else 0 := by
      intro u
      by_cases h : X.relOf u u = X.sourceFiber s
      · rw [if_pos h, X.outDeg_eq_interNum u s, h]; rfl
      · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro w _ hw
        exact h (X.relOf_diag_left_eq (hw.trans (X.relOf_repPair s).symm))
    rw [Finset.sum_congr rfl (fun u _ => hterm u), ← Finset.sum_filter, Finset.sum_const,
      smul_eq_mul]
    rfl
  rw [← step r, ← step (X.transposeRel r)]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  by_cases hc : X.relOf b a = r
  · rw [if_pos hc, if_pos (X.relOf_swap_eq hc)]
  · rw [if_neg hc, if_neg ?_]
    intro hc2
    exact hc (by have h := X.relOf_swap_eq hc2; rwa [X.transposeRel_transposeRel] at h)

/-- **`smaxAdj` is symmetric within a fiber.** If `a, b` lie in one fiber (`relOf a a = relOf b b`) and
`relOf a b` is max-valency, so is `relOf b a`. The two share a source fiber, so the fiber-size identity cancels
`|F|` (`> 0`, `a ∈ F`) to give `n_{relOf a b} = n_{relOf b a}`. This is the only symmetry of `smaxAdj` available
on a multi-fiber CC — connectivity infrastructure must be fed the *intra-fiber* smax graph (§6.1's localization).
Axiom-clean. -/
theorem smaxAdj_symm_of_sameFiber {a b : Fin n} (hf : X.relOf a a = X.relOf b b)
    (h : X.smaxAdj a b) : X.smaxAdj b a := by
  have hr : X.valency (X.relOf a b) = X.maxValency := h
  have hba : X.relOf b a = X.transposeRel (X.relOf a b) := X.relOf_swap_eq rfl
  have hsrc1 : X.relOf a a = X.sourceFiber (X.relOf a b) :=
    X.relOf_diag_left_eq ((rfl : X.relOf a b = X.relOf a b).trans (X.relOf_repPair _).symm)
  have hsrc2 : X.relOf b b = X.sourceFiber (X.transposeRel (X.relOf a b)) :=
    X.relOf_diag_left_eq (hba.trans (X.relOf_repPair _).symm)
  have hfib := X.fiberSize_mul_valency (X.relOf a b)
  rw [← hsrc1, ← hsrc2, ← hf] at hfib
  have hpos : 0 < (X.fiberSet (X.relOf a a)).card := by
    apply Finset.card_pos.2
    exact ⟨a, by simp only [fiberSet, Finset.mem_filter, Finset.mem_univ, true_and]⟩
  have hval : X.valency (X.relOf a b) = X.valency (X.transposeRel (X.relOf a b)) :=
    Nat.eq_of_mul_eq_mul_left hpos hfib
  show X.valency (X.relOf b a) = X.maxValency
  rw [hba, ← hval, hr]

/-! ### §CC.18 — The abundance route: `(k−1)·c < |T| ⟹ T pins everything in one round` (A1, the direct discharge)

**The scouting payoff (2026-06-14).** The δ′ engine `dominatorReachable_of_rank` accepts *any* bounded base, so we
do **not** need PV Thm 3.1's sharp `b(X) ≤ 2` — a crude `b(X) ≤ (k−1)·c + 1` suffices, and it has a one-round
`basePinsAll` proof that skips the entire §S.10–§S.16 connectivity apparatus (smax/sα/components). The argument is
pure counting: for `γ ∉ T` and any `α ∈ T`, a base point `β` *fails* to pin `γ` (against `α`) only if `β` confuses
`γ` with one of the `≤ k−1` other `α`-out-neighbours in `γ`'s class — and each confusion set has size `≤ c` (it is
an indistinguishing-number count, `indistinguishingNumberOf_eq_card` + the transpose bridge). So at most `(k−1)·c`
base points fail; if `|T| > (k−1)·c` some `β ∈ T` pins `γ`. Cross-fiber is automatic (no smax needed): `α, β` range
over all of `T`, the forced triangle is `interNum`-level. **This is A1, citation-free, in `c`/`k` vocabulary (so it
composes directly with A2's `c(X_T), k(X_T) = O(1)`).** The only remaining A1→`hclo` step is A2 exhibiting a base
with `|T| > (k(X_T)−1)·c(X_T)` (an `O(1)` threshold). -/

/-- **One-round closure from base pinning (CC form).** If every non-base `γ` is forced-triangle-pinned (profile
uniqueness) by two base points `α, β ∈ T`, the dominator closure of `T` exhausts `Ω` in one round. The `rank∈{0,1}`
instance of `dominatorReachable_of_rank`; the CC mirror of `CascadeAffine.dominatorReachable_of_basePinsAll`. -/
theorem dominatorReachable_of_basePinsAll {T : Finset (Fin n)}
    (hpin : ∀ γ : Fin n, γ ∉ T → ∃ α ∈ T, ∃ β ∈ T,
        ∀ u : Fin n, X.relOf α u = X.relOf α γ → X.relOf u β = X.relOf γ β → u = γ) :
    ∀ v : Fin n, X.DominatorReachable T v := by
  classical
  refine X.dominatorReachable_of_rank (fun v => if v ∈ T then 0 else 1) (fun v hv => ?_)
    (fun γ hγ => ?_)
  · by_contra hvT
    have hv' : (if v ∈ T then (0:ℕ) else 1) = 0 := hv
    rw [if_neg hvT] at hv'
    exact one_ne_zero hv'
  · have hγT : γ ∉ T := by
      intro h
      have hγ' : 0 < (if γ ∈ T then (0:ℕ) else 1) := hγ
      rw [if_pos h] at hγ'
      exact lt_irrefl 0 hγ'
    obtain ⟨α, hαT, β, hβT, hu⟩ := hpin γ hγT
    refine ⟨α, β, ?_, ?_, hu⟩
    · show (if α ∈ T then (0:ℕ) else 1) < (if γ ∈ T then (0:ℕ) else 1)
      rw [if_pos hαT, if_neg hγT]; exact one_pos
    · show (if β ∈ T then (0:ℕ) else 1) < (if γ ∈ T then (0:ℕ) else 1)
      rw [if_pos hβT, if_neg hγT]; exact one_pos

/-- **The abundance estimate: `(k−1)·c < |T|` ⟹ `T` pins every non-base point in one round.** For `γ ∉ T`, fix any
`α ∈ T`; the "bad" base points (those confusing `γ` with another `α`-out-neighbour in `γ`'s class) number
`≤ (k−1)·c` (union bound over the `≤ k−1` other neighbours, each confusion set an indistinguishing-number count
`≤ c`). With `|T| > (k−1)·c` a good `β ∈ T` survives and pins `γ` by profile uniqueness. Axiom-clean. -/
theorem basePinsAll_of_card_gt {T : Finset (Fin n)}
    (hT : (X.maxValency - 1) * X.indistinguishingNumber < T.card) :
    ∀ γ : Fin n, γ ∉ T → ∃ α ∈ T, ∃ β ∈ T,
      ∀ u : Fin n, X.relOf α u = X.relOf α γ → X.relOf u β = X.relOf γ β → u = γ := by
  classical
  intro γ hγ
  obtain ⟨α, hα⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
  have hαγ : α ≠ γ := fun h => hγ (h ▸ hα)
  refine ⟨α, hα, ?_⟩
  -- the base points that FAIL to separate γ (against α)
  set Bad : Finset (Fin n) :=
    T.filter (fun β => ∃ u', u' ≠ γ ∧ X.relOf α u' = X.relOf α γ ∧ X.relOf u' β = X.relOf γ β)
    with hBad
  -- |Bad| ≤ (k−1)·c
  have hBadle : Bad.card ≤ (X.maxValency - 1) * X.indistinguishingNumber := by
    set Vf : Finset (Fin n) := Finset.univ.filter (fun u' => X.relOf α u' = X.relOf α γ) with hVf
    have hsub : Bad ⊆ (Vf.erase γ).biUnion
        (fun u' => Finset.univ.filter (fun β => X.relOf u' β = X.relOf γ β)) := by
      intro β hβ
      rw [hBad, Finset.mem_filter] at hβ
      obtain ⟨_, u', hu'ne, hu'v, hu'β⟩ := hβ
      rw [Finset.mem_biUnion]
      refine ⟨u', ?_, ?_⟩
      · rw [Finset.mem_erase]
        exact ⟨hu'ne, by rw [hVf, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hu'v⟩⟩
      · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hu'β⟩
    calc Bad.card
        ≤ ((Vf.erase γ).biUnion
            (fun u' => Finset.univ.filter (fun β => X.relOf u' β = X.relOf γ β))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ u' ∈ Vf.erase γ,
            (Finset.univ.filter (fun β => X.relOf u' β = X.relOf γ β)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _u' ∈ Vf.erase γ, X.indistinguishingNumber := by
          apply Finset.sum_le_sum
          intro u' hu'
          rw [Finset.mem_erase] at hu'
          have hcard : (Finset.univ.filter (fun β => X.relOf u' β = X.relOf γ β)).card
              = X.indistinguishingNumberOf (X.relOf u' γ) := by
            rw [X.indistinguishingNumberOf_eq_card (rfl : X.relOf u' γ = X.relOf u' γ)]
            congr 1
            ext β
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact X.relOf_right_eq_iff_left u' γ β
          rw [hcard]
          exact X.indistinguishingNumberOf_le (X.not_isReflexive_relOf_of_ne hu'.1)
      _ = (Vf.erase γ).card * X.indistinguishingNumber := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (X.maxValency - 1) * X.indistinguishingNumber := by
          refine Nat.mul_le_mul ?_ (le_refl _)
          have hγVf : γ ∈ Vf := by
            rw [hVf, Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩
          have hVfcard : Vf.card = X.valency (X.relOf α γ) := by
            rw [hVf, X.valency_eq_card (rfl : X.relOf α γ = X.relOf α γ)]
          have hkv : X.valency (X.relOf α γ) ≤ X.maxValency :=
            X.valency_le_maxValency (X.not_isReflexive_relOf_of_ne hαγ)
          rw [Finset.card_erase_of_mem hγVf, hVfcard]
          omega
  -- a good β survives in T
  obtain ⟨β, hβ⟩ : (T \ Bad).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  rw [Finset.mem_sdiff] at hβ
  refine ⟨β, hβ.1, ?_⟩
  intro u h1 h2
  by_contra hune
  exact hβ.2 (by rw [hBad, Finset.mem_filter]; exact ⟨hβ.1, u, hune, h1, h2⟩)

/-- **A1, the abundance discharge: a base with `(k−1)·c < |T|` is a δ′ base.** Composes `basePinsAll_of_card_gt`
with `dominatorReachable_of_basePinsAll`: if `|T| > (k(X)−1)·c(X)`, every point is forced-triangle dominator-
reachable from `T`. The citation-free "sparse ⟹ pinning rank" for the multi-fiber CC, skipping §S.10–§S.16; on
`X_T = pointExtension X T` it feeds `allSingletonFiber_of_dominatorClosure_pointExtension` (the open `hclo`). The
remaining content is A2: exhibit such a `T` (`c(X_T), k(X_T) = O(1)` ⟹ the threshold is `O(1)`). Axiom-clean. -/
theorem dominatorReachable_of_card_gt {T : Finset (Fin n)}
    (hT : (X.maxValency - 1) * X.indistinguishingNumber < T.card) :
    ∀ v : Fin n, X.DominatorReachable T v :=
  X.dominatorReachable_of_basePinsAll (X.basePinsAll_of_card_gt hT)

/-- **A1 capstone on the extension: a base above the extension's threshold makes `X_T` complete.** If
`(k(X_T)−1)·c(X_T) < |T|` then every point of `pointExtension X T` is a singleton fiber — i.e. `T` is a base of `X`.
Composes `dominatorReachable_of_card_gt` (on `X_T`) with `allSingletonFiber_of_dominatorClosure_pointExtension`
(`Sharp` and the `T`-singleton fibers discharged in §CC.10). **This is the entire A1 content reduced to a single
`O(1)` threshold on `X_T`'s own parameters — the crisp interface A2 must meet (`c(X_T), k(X_T) = O(1)` ⟹ a base of
size just above the threshold exists).** No smax/sα connectivity, no `SparseSeparable`, citation-free. Axiom-clean. -/
theorem allSingletonFiber_of_card_gt (T : Finset (Fin n))
    (hT : ((pointExtension X T).maxValency - 1) * (pointExtension X T).indistinguishingNumber
        < T.card) :
    ∀ v : Fin n, (pointExtension X T).SingletonFiber v :=
  X.allSingletonFiber_of_dominatorClosure_pointExtension T
    ((pointExtension X T).dominatorReachable_of_card_gt hT)

/-! ### §CC.19 — Monotonicity of `c`, `k` under refinement + the padding bridge (A2 interface)

The abundance threshold `(k(X_T)−1)·c(X_T) < |T|` can never be checked at a *non-discrete* `X_T` (its contrapositive
forces `(k−1)c ≥ |T|` there). It is used via **padding**: A2 bounds `c, k` at a *small* base `T₀`, then any superset
`T ⊇ T₀` inherits the bounds (more individualization only refines), and once `|T|` overtakes `(k(X_{T₀})−1)·c(X_{T₀})`
the abundance lemma fires. This section supplies the monotonicity (`c, k` non-increasing under `Refines`) and the
padding capstone `allSingletonFiber_of_card_gt_subset` — **the crisp A2 interface: bound `c(X_{T₀}), k(X_{T₀}) = O(1)`
at one `O(1)` base, and every larger base is a base of `X`.** -/

/-- **The indistinguishing number is monotone under refinement** — `Refines Y Z ⟹ c(Y) ≤ c(Z)`. A finer config
distinguishes more pairs, so each `{γ : relOf γ α = relOf γ β}` can only shrink. Axiom-clean. -/
theorem indistinguishingNumber_mono {Y Z : CoherentConfig n} (h : Refines Y Z) :
    Y.indistinguishingNumber ≤ Z.indistinguishingNumber := by
  classical
  apply Finset.sup_le
  intro r hr
  rw [Finset.mem_filter] at hr
  have hrep : Y.relOf (Y.repPair r).1 (Y.repPair r).2 = r := Y.relOf_repPair r
  have hαβ : (Y.repPair r).1 ≠ (Y.repPair r).2 := by
    intro he
    rw [he] at hrep
    exact hr.2 ⟨(Y.repPair r).2, hrep⟩
  rw [Y.indistinguishingNumberOf_eq_card hrep]
  have hsub : (Finset.univ.filter (fun γ => Y.relOf γ (Y.repPair r).1 = Y.relOf γ (Y.repPair r).2))
      ⊆ (Finset.univ.filter (fun γ => Z.relOf γ (Y.repPair r).1 = Z.relOf γ (Y.repPair r).2)) := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ ⊢
    exact ⟨Finset.mem_univ _, h _ _ _ _ hγ.2⟩
  calc (Finset.univ.filter
          (fun γ => Y.relOf γ (Y.repPair r).1 = Y.relOf γ (Y.repPair r).2)).card
      ≤ _ := Finset.card_le_card hsub
    _ = Z.indistinguishingNumberOf (Z.relOf (Y.repPair r).1 (Y.repPair r).2) :=
        (Z.indistinguishingNumberOf_eq_card rfl).symm
    _ ≤ Z.indistinguishingNumber :=
        Z.indistinguishingNumberOf_le (Z.not_isReflexive_relOf_of_ne hαβ)

/-- **The max valency is monotone under refinement** — `Refines Y Z ⟹ k(Y) ≤ k(Z)`. A finer class has a smaller
out-neighbour set, so each valency can only shrink. Axiom-clean. -/
theorem maxValency_mono {Y Z : CoherentConfig n} (h : Refines Y Z) :
    Y.maxValency ≤ Z.maxValency := by
  classical
  apply Finset.sup_le
  intro r hr
  rw [Finset.mem_filter] at hr
  have hrep : Y.relOf (Y.repPair r).1 (Y.repPair r).2 = r := Y.relOf_repPair r
  have hαβ : (Y.repPair r).1 ≠ (Y.repPair r).2 := by
    intro he
    rw [he] at hrep
    exact hr.2 ⟨(Y.repPair r).2, hrep⟩
  rw [Y.valency_eq_card hrep]
  have hsub : (Finset.univ.filter (fun w => Y.relOf (Y.repPair r).1 w = r))
      ⊆ (Finset.univ.filter
          (fun w => Z.relOf (Y.repPair r).1 w = Z.relOf (Y.repPair r).1 (Y.repPair r).2)) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨Finset.mem_univ _, h _ _ _ _ (by rw [hw.2, hrep])⟩
  calc (Finset.univ.filter (fun w => Y.relOf (Y.repPair r).1 w = r)).card
      ≤ _ := Finset.card_le_card hsub
    _ = Z.valency (Z.relOf (Y.repPair r).1 (Y.repPair r).2) := (Z.valency_eq_card rfl).symm
    _ ≤ Z.maxValency := Z.valency_le_maxValency (Z.not_isReflexive_relOf_of_ne hαβ)

/-- **Extending the base refines the point extension** — `T₀ ⊆ T ⟹ pointExtension X T` refines
`pointExtension X T₀`. Immediate from the universal property: `X_T` is a coherent fission of `X` with all
`T₀`-points singleton fibers (since `T₀ ⊆ T`), so the coarsest-such `X_{T₀}` is refined by it. Axiom-clean. -/
theorem refines_pointExtension_of_subset {T₀ T : Finset (Fin n)} (hsub : T₀ ⊆ T) :
    Refines (pointExtension X T) (pointExtension X T₀) :=
  (isPointExtension_pointExtension X T₀).2.2 (pointExtension X T)
    (isPointExtension_pointExtension X T).1
    (fun t ht => (isPointExtension_pointExtension X T).2.1 t (hsub ht))

/-- **The padding capstone — A1+A2 interface.** If `T₀ ⊆ T` and `|T|` exceeds the *small base's* threshold
`(k(X_{T₀})−1)·c(X_{T₀})`, then `pointExtension X T` is complete (`T` a base of `X`). The bounds on `X_{T₀}`
transport to `X_T` by monotonicity (`refines_pointExtension_of_subset` + `*_mono`), so the abundance lemma
`allSingletonFiber_of_card_gt` fires on `X_T`. **This is exactly the A2 deliverable: bound `c(X_{T₀}), k(X_{T₀}) =
O(1)` at one `O(1)` base `T₀`; then any `T ⊇ T₀` with `|T| > (k(X_{T₀})−1)·c(X_{T₀})` is a base of `X` — citation-
free, no smax/sα, no `SparseSeparable`.** Axiom-clean. -/
theorem allSingletonFiber_of_card_gt_subset {T₀ T : Finset (Fin n)} (hsub : T₀ ⊆ T)
    (hT : ((pointExtension X T₀).maxValency - 1) * (pointExtension X T₀).indistinguishingNumber
        < T.card) :
    ∀ v : Fin n, (pointExtension X T).SingletonFiber v := by
  have href := X.refines_pointExtension_of_subset hsub
  have hk := maxValency_mono href
  have hc := indistinguishingNumber_mono href
  refine X.allSingletonFiber_of_card_gt T (lt_of_le_of_lt ?_ hT)
  exact Nat.mul_le_mul (Nat.sub_le_sub_right hk 1) hc

/-- **The padded `DominatorReachable` closure — feeds the seal's `hclo` directly.** Same hypothesis as
`allSingletonFiber_of_card_gt_subset` but lands on the forced-triangle closure `∀ v, DominatorReachable T v`
(what `reachesRigidOrCameron_viaExtensionDominatorClosure` consumes), via the monotone transport of the
`X_{T₀}` bounds + `dominatorReachable_of_card_gt`. Axiom-clean. -/
theorem dominatorReachable_of_card_gt_subset {T₀ T : Finset (Fin n)} (hsub : T₀ ⊆ T)
    (hT : ((pointExtension X T₀).maxValency - 1) * (pointExtension X T₀).indistinguishingNumber
        < T.card) :
    ∀ v : Fin n, (pointExtension X T).DominatorReachable T v := by
  have href := X.refines_pointExtension_of_subset hsub
  exact (pointExtension X T).dominatorReachable_of_card_gt
    (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le_sub_right (maxValency_mono href) 1)
      (indistinguishingNumber_mono href)) hT)

/-! ### §CC.20 — The potential-drop route (the uniform attack on A2; `chain-descent-a2-potential-route.md`)

A1 reduced A2 to *bound `(k(X_{T₀})−1)·c(X_{T₀})` at one small base `T₀`* (`allSingletonFiber_of_card_gt_subset`).
The probe (`A2MonovariantProbe.cs`) found the route to that bound: a **potential drops by a bounded factor per
individualization** on the non-geometric residue (it climbs to 1 only on the geometric/Cameron-carved families).
This section lands the *iteration* half — the abstract engine that turns a per-step halving into an `O(log n)`
base — carrying the per-step drop (the genuine open combinatorial core) as the single hypothesis `PotentialDrops`.
The engine is the `Φ`-analogue of the greedy-base `Cascade.exists_greedy_base_aux` (which halves `|Aut|`). -/

/-- Folding `insert` over a list grows a `Finset` by at most the list length. (Local copy — the build places
this module before `CascadeAffine`'s `card_foldl_insert_le`.) -/
theorem card_foldl_insert_le {α : Type*} [DecidableEq α] (bs : List α) (s : Finset α) :
    (bs.foldl (fun s b => insert b s) s).card ≤ s.card + bs.length := by
  induction bs generalizing s with
  | nil => simp
  | cons b bs ih =>
      rw [List.foldl_cons, List.length_cons]
      exact le_trans (ih (insert b s)) (by have := Finset.card_insert_le b s; omega)

/-- **Abstract potential-descent engine.** A `Nat`-valued potential `Φ` with a per-step *halving* — from any `T`
with `Φ T > B`, some insertion at least halves `Φ` — reaches `Φ ≤ B` after a list of insertions whose length is
`≤ log₂(max 1 (Φ S))`. Pure `Finset`/`Nat` strong induction on a bound `N`; the `Φ`-analogue of
`exists_greedy_base_aux`. (`hB : 1 ≤ B` keeps the `2^len ≤ max 1 (Φ)` invariant clean across a drop to `0`.) -/
theorem exists_potential_descent {α : Type*} [DecidableEq α]
    (Φ : Finset α → Nat) (B : Nat) (hB : 1 ≤ B)
    (hdrop : ∀ T : Finset α, B < Φ T → ∃ v : α, 2 * Φ (insert v T) ≤ Φ T) :
    ∀ (N : Nat) (S : Finset α), Φ S ≤ N →
      ∃ bs : List α, Φ (bs.foldl (fun s b => insert b s) S) ≤ B ∧
        2 ^ bs.length ≤ max 1 (Φ S) := by
  intro N
  induction N with
  | zero =>
      intro S hS
      have h0 : Φ S = 0 := Nat.le_zero.1 hS
      exact ⟨[], by simp only [List.foldl_nil]; omega, by simp only [List.length_nil, pow_zero]; exact le_max_left 1 (Φ S)⟩
  | succ N ih =>
      intro S hS
      by_cases hbig : B < Φ S
      · obtain ⟨v, hv⟩ := hdrop S hbig
        have hins : Φ (insert v S) ≤ N := by omega
        obtain ⟨bs', hbs'B, hbs'pow⟩ := ih (insert v S) hins
        refine ⟨v :: bs', ?_, ?_⟩
        · rw [List.foldl_cons]; exact hbs'B
        · rw [List.length_cons]
          calc 2 ^ (bs'.length + 1)
              = 2 * 2 ^ bs'.length := by rw [pow_succ, Nat.mul_comm]
            _ ≤ 2 * max 1 (Φ (insert v S)) := Nat.mul_le_mul (le_refl 2) hbs'pow
            _ ≤ max 1 (Φ S) := by omega
      · exact ⟨[], by simp only [List.foldl_nil]; omega,
          by simp only [List.length_nil, pow_zero]; exact le_max_left 1 (Φ S)⟩

/-- **The A2 potential** `Φ(T) = (k(X_T) − 1)·c(X_T)` — the exact threshold quantity of
`allSingletonFiber_of_card_gt_subset` (a base `T ⊇ T₀` with `|T| > Φ(T₀)` is a base of `X`). -/
noncomputable def potential (T : Finset (Fin n)) : Nat :=
  ((pointExtension X T).maxValency - 1) * (pointExtension X T).indistinguishingNumber

/-- **The per-step drop hypothesis — the genuine open combinatorial core of A2.** From any base `T` whose
potential exceeds `B`, *some* individualization at least halves it. This is the "shattering" content the probe
found holds on the non-geometric residue (`chain-descent-a2-potential-route.md` §2-§3); proving it for the
residue (via the Neumaier/CGGP dichotomy that routes geometric→Cameron) closes A2. Carried as a hypothesis,
never an `axiom`. -/
def PotentialDrops (B : Nat) : Prop :=
  ∀ T : Finset (Fin n), B < X.potential T → ∃ v : Fin n, 2 * X.potential (insert v T) ≤ X.potential T

/-- **A2's small-base deliverable, from the per-step drop (the iteration half — LANDED).** If the potential
halves per seed down to `B`, there is a base `T₀` with `(k(X_{T₀})−1)·c(X_{T₀}) ≤ B` and a *logarithmic* size
certificate `2^|T₀| ≤ max 1 (Φ ∅)` (so `|T₀| ≤ log₂(Φ ∅) = O(log n)`, since `Φ ∅ ≤ n²`). Feeds
`allSingletonFiber_of_card_gt_subset` (pad `T₀` to `|T| > B`). The whole open content is now the single
hypothesis `PotentialDrops`. Axiom-clean. -/
theorem exists_small_base_of_potentialDrops {B : Nat} (hB : 1 ≤ B) (hdrop : X.PotentialDrops B) :
    ∃ T₀ : Finset (Fin n),
      X.potential T₀ ≤ B ∧ 2 ^ T₀.card ≤ max 1 (X.potential ∅) := by
  obtain ⟨bs, hle, hpow⟩ :=
    exists_potential_descent X.potential B hB hdrop (X.potential ∅) ∅ le_rfl
  refine ⟨bs.foldl (fun s b => insert b s) (∅ : Finset (Fin n)), hle, ?_⟩
  have hcard : (bs.foldl (fun s b => insert b s) (∅ : Finset (Fin n))).card ≤ bs.length := by
    simpa using card_foldl_insert_le bs (∅ : Finset (Fin n))
  exact le_trans (Nat.pow_le_pow_right (by norm_num) hcard) hpow

/-- **The indistinguishing-number "shattering" hypothesis (Stage 1b).** From any base `T` whose potential exceeds
`B`, *some* individualization at least **halves the indistinguishing number** `c(X_T)` of the point extension.
This is the genuine open core of A2, *sharpened*: the max valency `k(X_T)` need not be controlled directly — it
rides along free, monotone non-increasing under individualization (`maxValency_mono`, the build-doc §1B split:
`k` free, `c` the crux). A `c`-class that resists halving under *every* `v` is a **partial-geometry line system**
(the probe `A2MonovariantProbe.Probe_SmallestEigenvalueAxis` found the drop-obstruction is the line/grid geometry,
*not* the magnitude of the smallest eigenvalue — `chain-descent-a2-potential-route.md` §3/§5). Carried as a
hypothesis, never an `axiom`. -/
def IndistinguishingHalves (B : Nat) : Prop :=
  ∀ T : Finset (Fin n), B < X.potential T →
    ∃ v : Fin n,
      2 * (pointExtension X (insert v T)).indistinguishingNumber
        ≤ (pointExtension X T).indistinguishingNumber

/-- **The drop-lemma reduction (Stage 1b) — `c`-halving ⟹ `PotentialDrops`.** Halving the indistinguishing number
suffices for the *potential* `(k−1)·c` to halve: individualizing `v` refines `X_T`
(`refines_pointExtension_of_subset`), so `k(X_{T∪v}) ≤ k(X_T)` rides along free (`maxValency_mono`), and
`2·(k'−1)·c' = (k'−1)·(2c') ≤ (k−1)·c` from `2c' ≤ c`. **Reduces A2's open content from "the product `(k−1)c`
halves" to "`c` halves"** — the build-doc §1B split (`k` free, `c` the crux) made rigorous, and the form the
forced-triangle / `interNum_eq_one` calculus is the right language for (it counts the would-be line incidences).
Axiom-clean. -/
theorem potentialDrops_of_indistinguishingHalves {B : Nat}
    (h : X.IndistinguishingHalves B) : X.PotentialDrops B := by
  intro T hbig
  obtain ⟨v, hc⟩ := h T hbig
  refine ⟨v, ?_⟩
  have hk : (pointExtension X (insert v T)).maxValency ≤ (pointExtension X T).maxValency :=
    maxValency_mono (X.refines_pointExtension_of_subset (Finset.subset_insert v T))
  show 2 * X.potential (insert v T) ≤ X.potential T
  unfold potential
  calc 2 * (((pointExtension X (insert v T)).maxValency - 1)
              * (pointExtension X (insert v T)).indistinguishingNumber)
      = ((pointExtension X (insert v T)).maxValency - 1)
          * (2 * (pointExtension X (insert v T)).indistinguishingNumber) := by ring
    _ ≤ ((pointExtension X T).maxValency - 1) * (pointExtension X T).indistinguishingNumber :=
        Nat.mul_le_mul (by omega) hc

/-! ### §CC.21 — the geometric-obstruction framework (Stage 1b discharge, the CC-intrinsic core)

The Stage-1b open content is `IndistinguishingHalves`: from any over-`B` base, some individualization halves the
indistinguishing number `c(X_T)`. `c(X_T)` is the size of the largest **confusion set** `C(α,β) = {γ : relOf γ α =
relOf γ β}`. Individualizing `v` partitions `C` by the relation profile `γ ↦ relOf γ v`; the partition either
**balance-splits** `C` (every fiber `≤ |C|/2`) or has a **unique majority** fiber (`> |C|/2`). A class that *no*
external point can balance-split is seen monochromatically from everywhere — a **partial-geometry line system** (the
`Probe_SmallestEigenvalueAxis` finding: the drop-obstruction is the line/grid geometry, not the smallest-eigenvalue
magnitude). This section lands that framework on a general CC, with the genuine combinatorics proven: the
balanced/majority dichotomy and the intersecting-majority pigeonhole (majority fibers for different points pairwise
meet — the near-pencil structure the cited Neumaier/Cameron dichotomy attaches to). The bridge from a *relation-profile*
balanced splitter to the *coherent-closure* halving (`X_{T∪v}`) is the isolated open mechanics (route doc §4 G-mech). -/

/-- §CC.21 (Stage 1b) **The confusion set of a pair** — the vertices relating identically to `α` and `β`. Its card
is the geometric form of `indistinguishingNumberOf (relOf α β)` (PV eq. (7), `indistinguishingNumberOf_eq_card`). -/
def confusionSet (α β : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun γ => X.relOf γ α = X.relOf γ β)

/-- §CC.21 (Stage 1b) **`v` balance-splits the `(α,β)`-confusion** — every relation-`j` fiber of `C(α,β)` under the
profile `γ ↦ relOf γ v` has `≤ |C|/2` vertices. The relation-profile precondition of a `c`-halving (the closure
mechanics, route doc §4 G-mech, then upgrades it to an actual halving of `c` in `X_{T∪v}`). -/
def BalancedSplits (v α β : Fin n) : Prop :=
  ∀ j : Fin X.rank,
    2 * ((X.confusionSet α β).filter (fun γ => X.relOf γ v = j)).card ≤ (X.confusionSet α β).card

/-- §CC.21 (Stage 1b) **`v` sees a majority of the `(α,β)`-confusion in one relation** — the negation of a balanced
split: some relation-`j` fiber holds `> |C|/2` of `C(α,β)`. The local "monochromatic view" whose universality (over
all `v`) is the geometric (line-system) obstruction. -/
def MajorityRelation (v α β : Fin n) : Prop :=
  ∃ j : Fin X.rank,
    (X.confusionSet α β).card < 2 * ((X.confusionSet α β).filter (fun γ => X.relOf γ v = j)).card

/-- §CC.21 (Stage 1b) **The balanced/majority dichotomy** — every external point either balance-splits the
confusion class or sees a majority of it in one relation. Pure case-split. Axiom-clean. -/
theorem balancedSplits_or_majority (v α β : Fin n) :
    X.BalancedSplits v α β ∨ X.MajorityRelation v α β := by
  by_cases h : X.BalancedSplits v α β
  · exact Or.inl h
  · refine Or.inr ?_
    unfold BalancedSplits at h
    push_neg at h
    exact h

/-- §CC.21 (Stage 1b) **The intersecting-majority pigeonhole — the near-pencil structure.** Majority fibers for two
external points `v, w` (each `> |C|/2`) necessarily **overlap**: a vertex of `C` lies in both. This is the
combinatorial heart of "a class no point can balance-split is a partial-geometry line system" — every pair of
monochromatic views shares a witness, so the views form a pencil of lines through common points. Via
`card_union_add_card_inter` (`|A∪B| + |A∩B| = |A| + |B|`) against `|A∪B| ≤ |C|`. Axiom-clean. -/
theorem majority_fibers_inter (α β v w : Fin n) (j k : Fin X.rank)
    (hv : (X.confusionSet α β).card
            < 2 * ((X.confusionSet α β).filter (fun γ => X.relOf γ v = j)).card)
    (hw : (X.confusionSet α β).card
            < 2 * ((X.confusionSet α β).filter (fun γ => X.relOf γ w = k)).card) :
    (((X.confusionSet α β).filter (fun γ => X.relOf γ v = j)) ∩
      ((X.confusionSet α β).filter (fun γ => X.relOf γ w = k))).Nonempty := by
  set C := X.confusionSet α β with hC
  set A := C.filter (fun γ => X.relOf γ v = j) with hA
  set Bs := C.filter (fun γ => X.relOf γ w = k) with hBs
  rw [← Finset.card_pos]
  have hunion : (A ∪ Bs).card ≤ C.card :=
    Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hid : (A ∪ Bs).card + (A ∩ Bs).card = A.card + Bs.card := Finset.card_union_add_card_inter A Bs
  omega

/-- §CC.21 (Stage 1b) **The geometric (line-system) obstruction at scale `B`.** A confusion class larger than `B`
that *every* external point sees monochromatically (a majority in one relation) — i.e. no individualization can
balance-split it. By `majority_fibers_inter` its monochromatic views pairwise overlap (a near-pencil): the
CC-intrinsic partial-geometry line system the cited Neumaier/Cameron dichotomy routes to `Cameron ∨ finite`. -/
def GeometricObstruction (B : Nat) : Prop :=
  ∃ α β : Fin n, α ≠ β ∧ B < (X.confusionSet α β).card ∧ ∀ v, X.MajorityRelation v α β

/-- §CC.21 (Stage 1b) **No obstruction on a class ⟹ a balanced splitter exists for it.** If some external point
fails to see `(α,β)`'s confusion monochromatically, that point balance-splits it (dichotomy). The trivial-but-needed
bridge from "no geometric obstruction" to "the splitter the closure mechanics consumes." Axiom-clean. -/
theorem exists_balancedSplits_of_not_forall_majority (α β : Fin n)
    (h : ¬ ∀ v, X.MajorityRelation v α β) : ∃ v, X.BalancedSplits v α β := by
  push_neg at h
  obtain ⟨v, hv⟩ := h
  rcases X.balancedSplits_or_majority v α β with hb | hm
  · exact ⟨v, hb⟩
  · exact absurd hm hv

/-! ### §CC.22 — G-mech: the kill lemma (Stage 1b discharge, the closure mechanics)

The corrected G-mech (route doc §4c): individualizing `v` does NOT split a confusion set into relation-to-`v`
fibers (that 1-WL "balanced splitter" picture, §CC.21, is the cell model the probe measured). In the coherent
closure `W = pointExtension X (insert v T)` where `v` is a **singleton fiber**, individualizing `v` instead
*annihilates* the confusion of every pair it distinguishes — the **kill lemma**. So `c(W)` is bounded by the
largest confusion among pairs `v` does *not* distinguish, and a `v` outside all over-half confusion sets halves `c`
(the `IndistinguishingHalves` target). Proven purely from `interNum` coherence + singleton isolation (the
`sharp_pointExtension` toolkit); no construction internals, no point-extension tower. -/

/-- §CC.22 (G-mech, kill-lemma core). On a CC with `v` a **singleton fiber**, any `γ` failing to distinguish `α`
from `β` forces `v` not to distinguish them either: `relOf γ α = relOf γ β → relOf v α = relOf v β`. The singleton
fiber isolates the triangle count through `v` to the single point `z = v` (`relOf_diag_right_eq` + `SingletonFiber`),
so `interNum (relOf γ v) b (relOf γ α)` is `1` exactly at `b = relOf v α`; the *same* `interNum` computed against
`β` (same class, since `γ` is confused) is `1` exactly at `b = relOf v β`, forcing `relOf v α = relOf v β`.
Axiom-clean. -/
theorem relOf_v_eq_of_confused {v α β γ : Fin n} (hv : X.SingletonFiber v)
    (h : X.relOf γ α = X.relOf γ β) : X.relOf v α = X.relOf v β := by
  classical
  set a := X.relOf γ v with ha
  have hiso : ∀ z, X.relOf γ z = a → z = v := fun z hz =>
    hv z (X.relOf_diag_right_eq (hz.trans ha))
  have hαfilter :
      (Finset.univ.filter fun z => X.relOf γ z = a ∧ X.relOf z α = X.relOf v α) = {v} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨Finset.mem_filter.2 ⟨Finset.mem_univ v, ha.symm, rfl⟩,
      fun z hz => hiso z (Finset.mem_filter.1 hz).2.1⟩
  have hα1 : X.interNum a (X.relOf v α) (X.relOf γ α) = 1 := by
    rw [← X.interNum_eq (rfl : X.relOf γ α = X.relOf γ α) a (X.relOf v α), hαfilter,
      Finset.card_singleton]
  have hβcard :
      (Finset.univ.filter fun z => X.relOf γ z = a ∧ X.relOf z β = X.relOf v α).card = 1 := by
    rw [X.interNum_eq (rfl : X.relOf γ β = X.relOf γ β) a (X.relOf v α), ← h, hα1]
  have hβsub :
      (Finset.univ.filter fun z => X.relOf γ z = a ∧ X.relOf z β = X.relOf v α) ⊆ {v} :=
    fun z hz => Finset.mem_singleton.2 (hiso z (Finset.mem_filter.1 hz).2.1)
  have hvmem : v ∈ (Finset.univ.filter fun z => X.relOf γ z = a ∧ X.relOf z β = X.relOf v α) := by
    rw [Finset.eq_of_subset_of_card_le hβsub (by rw [Finset.card_singleton]; exact hβcard.ge)]
    exact Finset.mem_singleton_self v
  exact ((Finset.mem_filter.1 hvmem).2.2).symm

/-- §CC.22 (G-mech) **THE KILL LEMMA.** If `v` is a singleton fiber and *distinguishes* `α, β`
(`relOf v α ≠ relOf v β`), the confusion set `C(α,β)` is **empty** — individualizing `v` destroys that pair's
indistinguishing class outright. Contrapositive of `relOf_v_eq_of_confused`. The closure mechanism behind A2's
per-step `c`-drop (route doc §4c). Axiom-clean. -/
theorem confusionSet_eq_empty_of_relOf_v_ne {v α β : Fin n} (hv : X.SingletonFiber v)
    (h : X.relOf v α ≠ X.relOf v β) : X.confusionSet α β = ∅ := by
  rw [confusionSet, Finset.filter_eq_empty_iff]
  intro γ _ hγ
  exact h (X.relOf_v_eq_of_confused hv hγ)

/-- §CC.22 (G-mech, **the bound** — route doc §4c step 2). **The kill-lemma bound on `c(X_{T∪v})`.**
Individualizing `v` bounds the indistinguishing number of the extension `W = pointExtension X (insert v T)` by the
largest `X_T`-confusion among the pairs `v` does *not* distinguish: if every pair `(α,β)` with `α ≠ β` and
`relOf_{X_T} v α = relOf_{X_T} v β` has `|C_{X_T}(α,β)| ≤ M`, then `c(X_{T∪v}) ≤ M`. Each non-reflexive `W`-class
has a representative pair `(α,β)` (`α ≠ β`, else the class is reflexive); the kill lemma
(`confusionSet_eq_empty_of_relOf_v_ne`, `v` a singleton fiber of `W` by `isPointExtension_pointExtension`) zeroes
its `W`-confusion when `v` *distinguishes* it, and otherwise the `W`-confusion is `⊆ C_{X_T}(α,β)` (monotone via
`Refines W X_T`, `refines_pointExtension_of_subset`) while `v` fails to distinguish `(α,β)` in `X_T` too — landing
in the `≤ M` hypothesis. This dissolves the old G-sim (simultaneity) gap: the single covering hypothesis on `v`
replaces a per-class splitter. The brick step 3 (`indistinguishingHalves_of_exists_avoiding_v`) consumes with
`M = c(X_T)/2`. Axiom-clean. -/
theorem indistinguishingNumber_pointExtension_insert_le (v : Fin n) (T : Finset (Fin n)) (M : Nat)
    (hM : ∀ α β : Fin n, α ≠ β →
        (pointExtension X T).relOf v α = (pointExtension X T).relOf v β →
        ((pointExtension X T).confusionSet α β).card ≤ M) :
    (pointExtension X (insert v T)).indistinguishingNumber ≤ M := by
  classical
  set W := pointExtension X (insert v T) with hWdef
  set Y := pointExtension X T with hYdef
  have hrefW : Refines W Y := X.refines_pointExtension_of_subset (Finset.subset_insert v T)
  have hvsing : W.SingletonFiber v :=
    (isPointExtension_pointExtension X (insert v T)).2.1 v (Finset.mem_insert_self v T)
  unfold indistinguishingNumber
  apply Finset.sup_le
  intro r hr
  rw [Finset.mem_filter] at hr
  set α := (W.repPair r).1 with hαdef
  set β := (W.repPair r).2 with hβdef
  have hrep : W.relOf α β = r := W.relOf_repPair r
  have hαβ : α ≠ β := fun he => hr.2 ⟨β, by rw [← hrep, he]⟩
  have hcard : W.indistinguishingNumberOf r = (W.confusionSet α β).card :=
    W.indistinguishingNumberOf_eq_card hrep
  rw [hcard]
  by_cases hvd : W.relOf v α = W.relOf v β
  · -- `v` does not distinguish `(α,β)` in `W`: confusion `⊆ C_{X_T}`, and `v` fails to distinguish in `X_T` too.
    have hsub : W.confusionSet α β ⊆ Y.confusionSet α β := by
      intro γ hγ
      simp only [confusionSet, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      exact hrefW γ α γ β hγ
    exact le_trans (Finset.card_le_card hsub) (hM α β hαβ (hrefW v α v β hvd))
  · -- `v` distinguishes `(α,β)` in `W`: the kill lemma empties its confusion class.
    rw [W.confusionSet_eq_empty_of_relOf_v_ne hvsing hvd, Finset.card_empty]
    exact Nat.zero_le M

/-- §CC.22 (G-mech, **the halving wiring** — route doc §4c step 3). **`IndistinguishingHalves` from an avoiding `v`
per over-`B` base.** If for every base `T` with `Φ T > B` there is a `v` that **avoids every big confusion set** —
i.e. every pair `(α,β)` (`α ≠ β`) that `v` fails to distinguish in `X_T` has `2·|C_{X_T}(α,β)| ≤ c(X_T)` — then
`X.IndistinguishingHalves B`. Pure arithmetic on the step-2 bound: instantiate
`indistinguishingNumber_pointExtension_insert_le` at `M = c(X_T)/2` (the avoiding hypothesis gives `|C| ≤ c/2` for
every undistinguished pair), yielding `c(X_{T∪v}) ≤ c(X_T)/2`, hence `2·c(X_{T∪v}) ≤ c(X_T)`. The remaining open
content is **the existence of an avoiding `v`** — its negation is the `BigConfusionCover` obstruction (step 4: the
`>c/2` confusion sets cover `Fin n`), routed to `Cameron ∨ finite` by the cited dichotomy (step 5, G-cite).
Axiom-clean. -/
theorem indistinguishingHalves_of_exists_avoiding_v (B : Nat)
    (h : ∀ T : Finset (Fin n), B < X.potential T →
        ∃ v : Fin n, ∀ α β : Fin n, α ≠ β →
          (pointExtension X T).relOf v α = (pointExtension X T).relOf v β →
          2 * ((pointExtension X T).confusionSet α β).card
            ≤ (pointExtension X T).indistinguishingNumber) :
    X.IndistinguishingHalves B := by
  intro T hbig
  obtain ⟨v, hv⟩ := h T hbig
  refine ⟨v, ?_⟩
  have hbound :
      (pointExtension X (insert v T)).indistinguishingNumber
        ≤ (pointExtension X T).indistinguishingNumber / 2 :=
    X.indistinguishingNumber_pointExtension_insert_le v T
      ((pointExtension X T).indistinguishingNumber / 2)
      (fun α β hαβ hund => by have := hv α β hαβ hund; omega)
  omega

/-! ### §CC.22 (cont.) — the `BigConfusionCover` obstruction (Stage 1b discharge, route doc §4c step 4)

The step-3 wiring reduced the whole open content to *the existence of an avoiding `v`* — a vertex outside every
confusion set of size `> c(X_T)/2`. Its negation is a clean covering statement: the big (`>c/2`) confusion sets
**cover `Fin n`**. This section names that obstruction and proves `¬cover ⟹ ∃ avoiding v` (feeding step 3), pulling
the entire open content into the single predicate the cited Neumaier / primitive-CC dichotomy (G-cite, step 5)
attaches to: a cover forces `n ≤ (#big sets)·c(X_T)`, i.e. `≥ n/c` near-maximal confusion sets — a partial-geometry
/ near-pencil line system, routed to `Cameron ∨ finite`. The §CC.21 balanced-splitter primitives
(`BalancedSplits` / `MajorityRelation` / `majority_fibers_inter` / `GeometricObstruction`) model the 1-WL *cell* split
the probe measured, not this 2-WL `c` covering — they are parked as that cell model. -/

/-- §CC.22 (Stage 1b, route doc §4c step 4) **The big-confusion-set covering obstruction.** The confusion sets of
size `> c(X)/2` (`c(X) < 2·|C(α,β)|`, `α ≠ β`) **cover `Fin n`**: every vertex fails to distinguish some pair whose
confusion class is over-half. This is the exact negation of "an avoiding `v` exists" (step 3's hypothesis); a `v`
*outside* the cover halves `c` by the kill-lemma bound. A cover forces `n ≤ (#big sets)·c(X)`, hence `≥ n/c`
near-maximal confusion sets — the partial-geometry / near-pencil line system the cited Neumaier + primitive-CC
classification (G-cite, step 5) routes to `Cameron ∨ finite-exceptional`. The residue, being neither, has no cover. -/
def BigConfusionCover : Prop :=
  ∀ v : Fin n, ∃ α β : Fin n,
    α ≠ β ∧ X.indistinguishingNumber < 2 * (X.confusionSet α β).card ∧ v ∈ X.confusionSet α β

/-- §CC.22 (Stage 1b, route doc §4c step 4) **No cover ⟹ an avoiding `v` exists.** If the big (`>c/2`) confusion
sets do *not* cover `Fin n`, some `v` lies outside all of them — i.e. every pair `(α,β)` (`α ≠ β`) that `v` fails to
distinguish (`relOf v α = relOf v β`, `v ∈ C(α,β)`) has `2·|C(α,β)| ≤ c(X)`. Exactly the "avoiding `v`" hypothesis
of `indistinguishingHalves_of_exists_avoiding_v` (step 3). Axiom-clean. -/
theorem exists_avoiding_of_not_cover (h : ¬ X.BigConfusionCover) :
    ∃ v : Fin n, ∀ α β : Fin n, α ≠ β → X.relOf v α = X.relOf v β →
      2 * (X.confusionSet α β).card ≤ X.indistinguishingNumber := by
  unfold BigConfusionCover at h
  rw [not_forall] at h
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun α β hαβ hund => ?_⟩
  by_contra hlt
  push_neg at hlt
  refine hv ⟨α, β, hαβ, hlt, ?_⟩
  simp only [confusionSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hund

/-- §CC.22 (Stage 1b, route doc §4c step 4) **`IndistinguishingHalves` from no cover at every over-`B` base — the
capstone-facing wiring.** If for every base `T` with `Φ T > B` the point extension `X_T` has **no** big-confusion-set
cover, then `X.IndistinguishingHalves B`. Composes `exists_avoiding_of_not_cover` (per base) with the step-3 halving
wiring `indistinguishingHalves_of_exists_avoiding_v`. **This packages the entire open content of A2 as one predicate
on the extension:** G-cite (step 5) discharges `¬ BigConfusionCover (X_T)` for the residue (non-Cameron, non-finite)
via the cited near-pencil dichotomy. Axiom-clean. -/
theorem indistinguishingHalves_of_not_bigConfusionCover (B : Nat)
    (h : ∀ T : Finset (Fin n), B < X.potential T → ¬ (pointExtension X T).BigConfusionCover) :
    X.IndistinguishingHalves B :=
  X.indistinguishingHalves_of_exists_avoiding_v B
    (fun T hT => (pointExtension X T).exists_avoiding_of_not_cover (h T hT))

end CoherentConfig

end ChainDescent
