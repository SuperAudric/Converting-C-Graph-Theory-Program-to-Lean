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
  `discreteCC` witnessing that the fission family is nonempty. The *construction* of the closure (the
  pair-refinement saturation) is a later increment; consumers should key on the predicate.

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
source/target fibers are class-determined). The closure's *construction* (pair-refinement saturation)
is a later increment; consumers key on the predicate. -/

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

end CoherentConfig

end ChainDescent
