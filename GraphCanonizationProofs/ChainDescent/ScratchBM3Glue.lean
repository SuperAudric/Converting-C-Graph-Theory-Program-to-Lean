import ChainDescent.CascadeAffine
import ChainDescent.ScratchLemmaB
import ChainDescent.ScratchBM3Bridge
/-!
# B-M3 wiring — `IsotropySeparatesAtBase Qbun T₉` and the `VO⁻₄(3)` seal.

Glues B-M1 (`incidence_agree_V`, restricted counts agree) + the bridge (`restricted_bridge`) + the decided
injectivity (`sigF_injective`) into `IsotropySeparatesAtBase Qbun T₉`, then feeds the Witt-free capstone.
-/
namespace ChainDescent
open QuadraticMap BM3Bridge

set_option maxHeartbeats 1000000

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- the VO⁻₄(3) bilinear form `B(x,y) = x₀y₁ + x₂y₂ + x₃y₃` (so `B x x = Qvo x`). -/
noncomputable def Bil : LinearMap.BilinForm (ZMod 3) (Fin 4 → ZMod 3) :=
  LinearMap.mk₂ (ZMod 3) (fun x y => x 0 * y 1 + x 2 * y 2 + x 3 * y 3)
    (fun x₁ x₂ y => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y₁ y₂ => by simp only [Pi.add_apply]; ring)
    (fun x c y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

/-- the bundled VO⁻₄(3) quadratic form. -/
noncomputable def Qbun : QuadraticForm (ZMod 3) (Fin 4 → ZMod 3) := Bil.toQuadraticMap

@[simp] lemma Qbun_apply (y : Fin 4 → ZMod 3) : Qbun y = Qvo y := by
  simp only [Qbun, Bil, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.mk₂_apply, Qvo]

/-- the 9 base vectors (T₉ in vector form); codes `[0,1,3,9,27,54,40,70,10]`. -/
def Bv : Fin 9 → (Fin 4 → ZMod 3) :=
  ![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
    ![0, 0, 0, 2], ![1, 1, 1, 1], ![1, 2, 1, 2], ![1, 0, 1, 0]]

/-- the size-9 base on the scheme. -/
noncomputable def T₉ : Finset (Fin (3 ^ 4)) := Finset.univ.image (fun k : Fin 9 => affineE (Bv k))

lemma hcard9 : T₉.card ≤ 9 := by
  refine le_trans Finset.card_image_le ?_
  simp [Finset.card_univ]

/-- the 2-element subset of `T₉` for base-pair `(i,j)` lies in `T₉`. -/
lemma Sij_subset (i j : Fin 9) :
    ({affineE (Bv i), affineE (Bv j)} : Finset (Fin (3 ^ 4))) ⊆ T₉ := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

/-- the B-M1 incidence count (for `S' = {affineE (Bv i), affineE (Bv j)}`, basepoint `w`) equals the bridged
`Nat`-predicate count `restrictedF` at the codes. -/
lemma vcount_eq (w : Fin (3 ^ 4)) (i j : Fin 9) :
    (Finset.univ.filter (fun y : Fin 4 → ZMod 3 => y ≠ 0 ∧ Qbun y = 0 ∧
        ∀ t ∈ ({affineE (Bv i), affineE (Bv j)} : Finset (Fin (3 ^ 4))),
          Qbun (y - (affineE.symm t - affineE.symm w)) = 0)).card
      = restrictedF (encV (affineE.symm w)).val (encV (Bv i)).val (encV (Bv j)).val := by
  rw [← restricted_bridge (affineE.symm w) (Bv i) (Bv j)]
  refine congrArg Finset.card ?_
  apply Finset.filter_congr
  intro y _
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Equiv.symm_apply_apply, Qbun_apply]

/-- per base-pair: the bridged counts agree between `u` and `u'` (from the fine antecedent, via B-M1). -/
lemma comp_eq (u u' : Fin (3 ^ 4))
    (hfine : ∀ (σ : Fin (3 ^ 4) → Fin 3) (c : Fin 3),
      (Finset.univ.filter (fun z : Fin (3 ^ 4) => z ≠ u ∧
        (∀ t ∈ T₉, isoClass Qbun (affineE.symm z - affineE.symm t) = σ t)
        ∧ isoClass Qbun (affineE.symm z - affineE.symm u) = c)).card
      = (Finset.univ.filter (fun z : Fin (3 ^ 4) => z ≠ u' ∧
        (∀ t ∈ T₉, isoClass Qbun (affineE.symm z - affineE.symm t) = σ t)
        ∧ isoClass Qbun (affineE.symm z - affineE.symm u') = c)).card)
    (i j : Fin 9) :
    restrictedF (encV (affineE.symm u)).val (encV (Bv i)).val (encV (Bv j)).val
      = restrictedF (encV (affineE.symm u')).val (encV (Bv i)).val (encV (Bv j)).val := by
  rw [← vcount_eq u i j, ← vcount_eq u' i j]
  exact incidence_agree_V Qbun T₉ u u' hfine (Sij_subset i j)

/-- **B-M3 — the seal's Gauss target.** `IsotropySeparatesAtBase Qbun T₉`: the fine isotropy-count antecedent
forces `u = u'`, via B-M1 + the bridge + the decided injectivity `sigF_injective`. -/
theorem isoSep : IsotropySeparatesAtBase Qbun T₉ := by
  intro u u' hfine
  have key : encV (affineE.symm u) = encV (affineE.symm u') := by
    apply sigF_injective
    show sigF (encV (affineE.symm u)) = sigF (encV (affineE.symm u'))
    simp only [sigF, fam]
    apply List.map_congr_left
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · have h := comp_eq u u' hfine 0 3
      rw [show (encV (Bv 0)).val = 0 from by decide,
        show (encV (Bv 3)).val = 9 from by decide] at h
      exact h
    · have h := comp_eq u u' hfine 4 8
      rw [show (encV (Bv 4)).val = 27 from by decide,
        show (encV (Bv 8)).val = 10 from by decide] at h
      exact h
    · have h := comp_eq u u' hfine 1 2
      rw [show (encV (Bv 1)).val = 1 from by decide,
        show (encV (Bv 2)).val = 3 from by decide] at h
      exact h
    · have h := comp_eq u u' hfine 4 7
      rw [show (encV (Bv 4)).val = 27 from by decide,
        show (encV (Bv 7)).val = 70 from by decide] at h
      exact h
    · have h := comp_eq u u' hfine 3 5
      rw [show (encV (Bv 3)).val = 9 from by decide,
        show (encV (Bv 5)).val = 54 from by decide] at h
      exact h
    · have h := comp_eq u u' hfine 1 6
      rw [show (encV (Bv 1)).val = 1 from by decide,
        show (encV (Bv 6)).val = 40 from by decide] at h
      exact h
  exact affineE.symm.injective (encV.injective key)

/-- **THE `VO⁻₄(3)` SEAL** (mod cited `{G3}`) — the Witt-free capstone instantiated. -/
def vo4minus_seal {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} :=
  reachesRigidOrCameron_viaIsotropySeparates_wittFree (IsCameronScheme := IsCameronScheme)
    (bound := 9) Qbun T₉ hcard9 isoSep

end ChainDescent

#print axioms ChainDescent.isoSep
#print axioms ChainDescent.vo4minus_seal
