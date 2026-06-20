import ChainDescent.CascadeAffine

/-!
Experiment: reprove `separatesAtBase_of_isotropySeparates` from a WITT-FREE hypothesis
`RelationRefinesIsotropy` (`∃ g, isoClass = g ∘ relOfPair`, the EASY direction only),
instead of the full `OrbitIsIsotropyClass` (which needs the hard Witt transitivity).
-/

namespace ChainDescent
open QuadraticMap

variable {p d : ℕ} [Fact p.Prime]

open scoped Classical in
/-- The Witt-FREE easy half: the scheme relation refines the isotropy class. -/
def RelationRefinesIsotropy (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) : Prop :=
  ∃ g : Fin ((affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)).rank + 1) → Fin 3,
    ∀ w : Fin d → ZMod p,
      isoClass Q w
        = g ((affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)).relOfPair (affineE 0) (affineE w))

/-- Sanity: the full Witt deliverable implies the easy half. -/
theorem relationRefinesIsotropy_of_orbitIsIsotropyClass
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) (h : OrbitIsIsotropyClass Q) :
    RelationRefinesIsotropy Q := by
  classical
  obtain ⟨relOfIso, hinj, hrel⟩ := h
  refine ⟨fun r => if hr : ∃ a, relOfIso a = r then hr.choose else 0, fun w => ?_⟩
  rw [hrel w]
  have hex : ∃ a, relOfIso a = relOfIso (isoClass Q w) := ⟨isoClass Q w, rfl⟩
  simp only [hex, dif_pos]
  exact (hinj hex.choose_spec).symm

open scoped Classical in
/-- **The Witt-FREE bridge.** -/
theorem separatesAtBase_of_isotropySeparates_weak (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {T : Finset (Fin (p ^ d))} (hRefine : RelationRefinesIsotropy Q)
    (hIso : IsotropySeparatesAtBase Q T) : SeparatesAtBase Q T := by
  classical
  obtain ⟨g, hg⟩ := hRefine
  let Sc := affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)
  let rel : Fin (p ^ d) → Fin (p ^ d) → Fin (Sc.rank + 1) :=
    fun z t => Sc.relOfPair (affineE 0) (affineE (affineE.symm z - affineE.symm t))
  have hgrel : ∀ a b : Fin (p ^ d),
      isoClass Q (affineE.symm a - affineE.symm b) = g (rel a b) := fun a b => hg _
  let ProfT := (t : Fin (p ^ d)) → t ∈ T → Fin (Sc.rank + 1)
  let ext : ProfT → Fin (p ^ d) → Fin (Sc.rank + 1) := fun ρT v => if h : v ∈ T then ρT v h else 0
  have hext : ∀ (ρT : ProfT) (t : Fin (p ^ d)) (h : t ∈ T), ext ρT t = ρT t h :=
    fun ρT t h => dif_pos h
  let relcount : Fin (p ^ d) → (Fin (p ^ d) → Fin (Sc.rank + 1)) → Fin (Sc.rank + 1) → ℕ :=
    fun w ρ b => (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ w ∧
      (∀ t ∈ T, rel z t = ρ t) ∧ rel z w = b)).card
  intro u u' hrelcounts
  apply hIso u u'
  intro σ c
  have key : ∀ w : Fin (p ^ d),
      (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ w ∧
        (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σ t)
        ∧ isoClass Q (affineE.symm z - affineE.symm w) = c)).card
      = ∑ k : ProfT × Fin (Sc.rank + 1),
          if (∀ t (h : t ∈ T), g (k.1 t h) = σ t) ∧ g k.2 = c
          then relcount w (ext k.1) k.2 else 0 := by
    intro w
    let φ : Fin (p ^ d) → ProfT × Fin (Sc.rank + 1) := fun z => (fun t _ => rel z t, rel z w)
    rw [Finset.card_eq_sum_card_fiberwise (f := φ)
        (t := (Finset.univ : Finset (ProfT × Fin (Sc.rank + 1)))) (fun z _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hcons : (∀ t (h : t ∈ T), g (k.1 t h) = σ t) ∧ g k.2 = c
    · rw [if_pos hcons]
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hzw, _, _⟩, hφ⟩
        refine ⟨hzw, ?_, ?_⟩
        · intro t ht
          have h1 : rel z t = k.1 t ht := congrFun (congrFun (congrArg Prod.fst hφ) t) ht
          rw [h1, hext]
        · have h2 : rel z w = k.2 := congrArg Prod.snd hφ
          rw [h2]
      · rintro ⟨hzw, hT, hw⟩
        refine ⟨⟨hzw, ?_, ?_⟩, ?_⟩
        · intro t ht
          rw [hgrel z t, hT t ht, hext]; exact hcons.1 t ht
        · rw [hgrel z w, hw]; exact hcons.2
        · refine Prod.ext ?_ hw
          funext t ht
          change rel z t = k.1 t ht
          rw [hT t ht, hext]
    · rw [if_neg hcons, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z hz hφ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨hzw, hiso, hisow⟩ := hz
      apply hcons
      refine ⟨fun t ht => ?_, ?_⟩
      · have h1 : rel z t = k.1 t ht := congrFun (congrFun (congrArg Prod.fst hφ) t) ht
        rw [← h1, ← hgrel z t]; exact hiso t ht
      · have h2 : rel z w = k.2 := congrArg Prod.snd hφ
        rw [← h2, ← hgrel z w]; exact hisow
  rw [key u, key u']
  apply Finset.sum_congr rfl
  intro k _
  by_cases hcons : (∀ t (h : t ∈ T), g (k.1 t h) = σ t) ∧ g k.2 = c
  · rw [if_pos hcons, if_pos hcons]
    exact hrelcounts (ext k.1) k.2
  · rw [if_neg hcons, if_neg hcons]

/-- **Similitude invariance of `isoClass`** (Witt-free). A similitude (`Q(g₀ x) = μ·Q x`, `μ` a unit) preserves
the isotropy class: zero/nonzero is `LinearEquiv`-invariant, and `Q = 0` is preserved since `μ` is a unit. -/
theorem isoClass_similitude_invariant (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {g₀ : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)} (hg : g₀ ∈ similitudeGroup Q)
    (w : Fin d → ZMod p) : isoClass Q (g₀ w) = isoClass Q w := by
  obtain ⟨μ, hμ⟩ := hg
  unfold isoClass
  by_cases h0 : w = 0
  · simp [h0]
  · have hgw0 : g₀ w ≠ 0 := fun h => h0 (by have := g₀.injective (h.trans g₀.map_zero.symm); exact this)
    rw [if_neg h0, if_neg hgw0, hμ w]
    by_cases hQ : Q w = 0
    · simp [hQ]
    · rw [if_neg hQ, if_neg (by simp [hQ, Units.ne_zero μ])]

open scoped Classical in
/-- **`RelationRefinesIsotropy` is discharged Witt-FREE** for any `Q`: the scheme relation determines the
isotropy class, purely by similitude-invariance (no Witt transitivity). So the capstone's `OrbitIsIsotropyClass`
input is unnecessary. -/
theorem relationRefinesIsotropy_similitude (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) :
    RelationRefinesIsotropy Q := by
  classical
  refine ⟨fun r => if h : ∃ w, (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)).relOfPair
      (affineE 0) (affineE w) = r then isoClass Q h.choose else 0, fun w => ?_⟩
  simp only
  have hex : ∃ w', (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)).relOfPair
      (affineE 0) (affineE w') = (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)).relOfPair
      (affineE 0) (affineE w) := ⟨w, rfl⟩
  rw [dif_pos hex]
  have hch := hex.choose_spec
  rw [affineScheme_relOfPair_eq_iff, orbMk_affine_eq_iff] at hch
  obtain ⟨g₀, hg₀, hgeq⟩ := hch
  simp only [Equiv.symm_apply_apply, sub_zero] at hgeq
  -- hgeq : g₀ w = hex.choose
  rw [← hgeq, isoClass_similitude_invariant Q hg₀]

open scoped Classical in
/-- **THE WITT-FREE SEAL CAPSTONE.** The seal for the rank-3 SRG `VO^ε` residue from a bounded symmetry-broken
base with isotropy-count injectivity — carrying NO Witt input (`OrbitIsIsotropyClass` discharged Witt-free via
similitude-invariance). The ONLY remaining open input is the Gauss target `IsotropySeparatesAtBase Q T`. -/
theorem reachesRigidOrCameron_viaIsotropySeparates_wittFree
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (T : Finset (Fin (p ^ d))) (hcard : T.card ≤ bound)
    (hIso : IsotropySeparatesAtBase Q T) :
    ((SchemeBlockRecovered (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q))
        ∨ AbelianConsumed (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)))
        ∨ SchemeRecoveredByDepth (p ^ d)
            (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)) bound)
      ∨ IsCameronScheme (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)) :=
  reachesRigidOrCameron_viaSymmetryBrokenBase Q T hcard
    (separatesAtBase_of_isotropySeparates_weak Q (relationRefinesIsotropy_similitude Q) hIso)

end ChainDescent

#print axioms ChainDescent.separatesAtBase_of_isotropySeparates_weak
#print axioms ChainDescent.relationRefinesIsotropy_of_orbitIsIsotropyClass
#print axioms ChainDescent.isoClass_similitude_invariant
#print axioms ChainDescent.relationRefinesIsotropy_similitude
#print axioms ChainDescent.reachesRigidOrCameron_viaIsotropySeparates_wittFree
