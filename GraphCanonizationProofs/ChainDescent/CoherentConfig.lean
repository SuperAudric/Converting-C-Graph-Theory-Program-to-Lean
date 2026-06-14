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

end CoherentConfig

end ChainDescent
