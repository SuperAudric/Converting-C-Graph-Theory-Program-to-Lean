import ChainDescent.MatchSupply
import ChainDescent.CascadeAffine

/-!
# `P0` — THE VOCABULARY BRIDGE: the seal's localisation feeds the canonizer's supply

## Why this file is the highest-value-per-line item in the track

The whole orbit-recovery / seal corpus — `theorem_1_HOR_cfi_oddDeg`, `theorem_2_HOR_*`, the four sealed form
families, `reachesRigidOrCameron_*`, Spielman's `SeparatesAtBoundedBase` — states its conclusions in the **scheme /
spine** vocabulary: `warmRefine adj P (individualizedColouring n T)`, `OrbitPartition`, `ResidualAut`,
`CellsAreOrbits`. The canonizer states its firing obligation in the **descent** vocabulary:
`Consume.IsColAut adj χ α`, `branches χ`, `Consume.CellIsOrbit`.

Until this file the two could not talk. Every seal-level theorem was therefore **unusable** by the canonizer, and
any consume-side strength result would have had to be *re-proved from scratch* as a parallel theorem. This file is
the translation, and after it the seal results are **reusable as-is**.

The payoff is `horb_of_cellsAreOrbits`: `CellsAreOrbits adj (constP n) D` at the descent's committed set `D`
delivers **exactly** the `horb` hypothesis that `Consume.cellIsOrbit_matchSupply` already takes.

## The three gaps it closes, in increasing order of depth

1. **Two refiners.** The seal runs `refineStep = Encodable.encode ∘ sigKey`; the descent runs the *encode-free*
   `Refine.refineRound` (which ranks the `sigKey`s instead of encoding them — the encode is infeasible to `#eval`).
   They are different *functions*. They induce **the same partition** (`warmRefineR_samePartition`), which is all
   either side ever uses.

2. **Two individualizations.** The seal individualizes a **set** at once (`individualizedColouring n T`, distinct
   colours by index); the descent individualizes **one vertex at a time, interleaved with refinement**
   (`indivOne`, index-free — a choice forced by `①c`, since an index-dependent individualization does not
   transport). These give the same stable partition, but only because of:

3. **★ CONFLUENCE** (`warmRefine_indivOne_confluent`): *refining before individualizing does not change the final
   stable partition.* `W (indivOne (W χ) v) ≅ W (indivOne χ v)`. This is the load-bearing fact and it is not
   formal: it holds because `warmRefine` is the **coarsest stable refinement** of its input
   (`refines_warmRefine_of_stable`), so the extra refinement `W` performs before the individualization is one the
   later `W` would have performed anyway.

## What is deliberately NOT claimed

Nothing here makes the *oracle* stronger. `CellsAreOrbits` is the seal's **carried localisation hypothesis**, and
it is exactly as open here as it is there (it fails at generic intermediate nodes — that is the node-4 / WL-dimension
wall). This file only guarantees that when a seal theorem *does* discharge it, the canonizer can **use** it.
-/

namespace ChainDescent
namespace SealBridge

open ChainDescent.Descend
open ChainDescent.Consume (IsColAut)

variable {n : Nat}

/-! ## 1. The two refiners induce the SAME PARTITION -/

/-- One encode-free round has the same partition as one stock round at the constant `P`. Both are "same old
colour ∧ same signature" (`Refine.refineRound_eq_iff` ranks the `sigKey`; `refineStep_iff` encodes it). -/
theorem refineRound_samePartition (adj : AdjMatrix n) (χ : Colouring n) :
    samePartition (Refine.refineRound adj χ) (refineStep adj (Refine.constP n) χ) := by
  intro i j
  rw [Refine.refineRound_eq_iff, refineStep_iff]
  exact sigKey_eq_iff adj (Refine.constP n) χ i j

/-- **★ THE REFINER BRIDGE.** The descent's `Refine.warmRefineR` and the seal's `warmRefine … (constP n)` induce
**the same partition**. Every partition-level statement therefore crosses freely. -/
theorem warmRefineR_samePartition (adj : AdjMatrix n) (χ : Colouring n) :
    samePartition (Refine.warmRefineR adj χ) (warmRefine adj (Refine.constP n) χ) := by
  have key : ∀ k : Nat, samePartition ((Refine.refineRound adj)^[k] χ)
      ((refineStep adj (Refine.constP n))^[k] χ) := by
    intro k
    induction k with
    | zero => exact samePartition.refl χ
    | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact (refineRound_samePartition adj _).trans
          (refineStep_samePartition (adj := adj) (P := Refine.constP n) ih)
  exact key n

/-! ## 2. `warmRefine` is the COARSEST STABLE REFINEMENT

The one non-formal ingredient. `warmRefine` splits only (`warmRefine_refines`) and is a fixpoint up to partition
(`warmRefine_refineStep_samePartition`); what is needed on top is that **every** stable refinement of `χ` refines
`warmRefine χ` — i.e. `warmRefine` splits *no more than it must*. -/

private theorem refineStep_mono' {adj : AdjMatrix n} {P : PMatrix n} {χ₁ χ₂ : Colouring n}
    (href : Refines χ₁ χ₂) : Refines (refineStep adj P χ₁) (refineStep adj P χ₂) := by
  intro a b hab
  rw [refineStep_iff] at hab ⊢
  exact ⟨href _ _ hab.1, signature_refines (adj := adj) (P := P) href hab.2⟩

/-- Warm refinement refines its input. -/
theorem refines_warmRefine (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) :
    Refines (warmRefine adj P χ) χ := fun _ _ h => warmRefine_refines adj P χ h

/-- **★ THE COARSEST-STABLE-REFINEMENT PROPERTY.** A colouring that is itself stable and refines `χ` already
refines `warmRefine χ`. This is what makes the confluence work: refinement performed *early* is never refinement
the fixpoint would not have performed anyway. -/
theorem refines_warmRefine_of_stable {adj : AdjMatrix n} {P : PMatrix n} {ψ χ : Colouring n}
    (hstab : Refines ψ (refineStep adj P ψ)) (h : Refines ψ χ) :
    Refines ψ (warmRefine adj P χ) := by
  have key : ∀ k, Refines ψ ((refineStep adj P)^[k] χ) := by
    intro k
    induction k with
    | zero => exact h
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact fun a b hab => refineStep_mono' ih a b (hstab a b hab)
  exact key n

/-- `warmRefine χ` is stable, in `Refines` form. -/
theorem stable_warmRefine (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) :
    Refines (warmRefine adj P χ) (refineStep adj P (warmRefine adj P χ)) := fun a b hab =>
  (warmRefine_refineStep_samePartition (adj := adj) (P := P) χ a b).mp hab

/-! ## 3. `indivOne`, at the partition level -/

/-- Individualizing refines. -/
theorem indivOne_refines (χ : Colouring n) (v : Fin n) : Refines (indivOne χ v) χ := by
  intro a b hab
  have hab' : (if a = v then 2 * χ a + 1 else 2 * χ a)
      = (if b = v then 2 * χ b + 1 else 2 * χ b) := hab
  by_cases ha : a = v
  · by_cases hb : b = v
    · rw [ha, hb]
    · rw [if_pos ha, if_neg hb] at hab'; omega
  · by_cases hb : b = v
    · rw [if_neg ha, if_pos hb] at hab'; omega
    · rw [if_neg ha, if_neg hb] at hab'; omega

/-- Individualizing is **monotone** in the colouring it individualizes. -/
theorem indivOne_mono {χ₁ χ₂ : Colouring n} (h : Refines χ₁ χ₂) (v : Fin n) :
    Refines (indivOne χ₁ v) (indivOne χ₂ v) := by
  intro a b hab
  show (if a = v then 2 * χ₂ a + 1 else 2 * χ₂ a) = (if b = v then 2 * χ₂ b + 1 else 2 * χ₂ b)
  have hab' : (if a = v then 2 * χ₁ a + 1 else 2 * χ₁ a)
      = (if b = v then 2 * χ₁ b + 1 else 2 * χ₁ b) := hab
  by_cases ha : a = v
  · by_cases hb : b = v
    · rw [ha, hb]
    · rw [if_pos ha, if_neg hb] at hab' ⊢; omega
  · by_cases hb : b = v
    · rw [if_neg ha, if_pos hb] at hab' ⊢; omega
    · rw [if_neg ha, if_neg hb] at hab' ⊢
      rw [h a b (by omega)]

theorem indivOne_congr {χ₁ χ₂ : Colouring n} (h : samePartition χ₁ χ₂) (v : Fin n) :
    samePartition (indivOne χ₁ v) (indivOne χ₂ v) := fun i j =>
  ⟨fun hij => indivOne_mono (fun a b hab => (h a b).mp hab) v i j hij,
   fun hij => indivOne_mono (fun a b hab => (h a b).mpr hab) v i j hij⟩

/-! ## 4. ★★★ CONFLUENCE -/

/-- **★★★ REFINING BEFORE INDIVIDUALIZING DOES NOT CHANGE THE STABLE PARTITION.**

`W (indivOne (W χ) v) ≅ W (indivOne χ v)`. This is what reconciles the descent's *interleaved*
individualize-refine chain with the seal's *batch* `individualizedColouring n T`, and it is the only step that is
not bookkeeping.

`⟸` is monotonicity (`indivOne (W χ) v` refines `indivOne χ v`).
`⟹` is the coarsest-stable property: `W (indivOne χ v)` is stable and refines `χ`, hence refines `W χ`; it also
separates `v` (it refines `indivOne χ v`, which does); so it refines `indivOne (W χ) v`, hence — being stable —
refines `W (indivOne (W χ) v)`. -/
theorem warmRefine_indivOne_confluent (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n)
    (v : Fin n) :
    samePartition (warmRefine adj P (indivOne (warmRefine adj P χ) v))
                  (warmRefine adj P (indivOne χ v)) := by
  set W := fun ξ => warmRefine adj P ξ with hW
  set A := indivOne χ v with hA
  set B := indivOne (W χ) v with hB
  -- `⟸`: `B` refines `A`, so `W B` refines `W A`.
  have h1 : Refines (W B) (W A) :=
    warmRefine_refines_initial (indivOne_mono (refines_warmRefine adj P χ) v)
  -- `⟹`: `W A` is stable, and it refines `B`.
  have hstabA : Refines (W A) (refineStep adj P (W A)) := stable_warmRefine adj P A
  have hWA_A : Refines (W A) A := refines_warmRefine adj P A
  have hWA_Wχ : Refines (W A) (W χ) :=
    refines_warmRefine_of_stable hstabA
      (fun a b hab => indivOne_refines χ v a b (hWA_A a b hab))
  have hsep : ∀ a : Fin n, W A a = W A v → a = v := by
    intro a ha
    by_contra hne
    exact indivOne_singleton χ v a hne (hWA_A a v ha)
  have hWA_B : Refines (W A) B := by
    intro a b hab
    show (if a = v then 2 * W χ a + 1 else 2 * W χ a)
        = (if b = v then 2 * W χ b + 1 else 2 * W χ b)
    have hWχ : W χ a = W χ b := hWA_Wχ a b hab
    by_cases ha : a = v
    · have hb : b = v := hsep b (by rw [← ha]; exact hab.symm)
      rw [ha, hb]
    · have hb : b ≠ v := fun hbv => ha (hsep a (by rw [← hbv]; exact hab))
      rw [if_neg ha, if_neg hb, hWχ]
  have h2 : Refines (W A) (W B) := refines_warmRefine_of_stable hstabA hWA_B
  exact fun i j => ⟨fun h => h1 i j h, fun h => h2 i j h⟩

/-! ## 5. The seal's set-individualization, at the partition level -/

/-- Two vertices share an `individualizedColouring` colour iff they are equal or both uncommitted. -/
theorem indiv_eq_iff (T : Finset (Fin n)) (i j : Fin n) :
    individualizedColouring n T i = individualizedColouring n T j ↔ (i = j ∨ (i ∉ T ∧ j ∉ T)) := by
  unfold individualizedColouring
  by_cases hi : i ∈ T <;> by_cases hj : j ∈ T
  · rw [if_pos hi, if_pos hj]
    refine ⟨fun h => Or.inl (Fin.ext (by omega)), ?_⟩
    rintro (rfl | ⟨hc, _⟩)
    · rfl
    · exact absurd hi hc
  · rw [if_pos hi, if_neg hj]
    refine ⟨fun h => absurd h (by omega), ?_⟩
    rintro (rfl | ⟨hc, _⟩)
    · exact absurd hi hj
    · exact absurd hi hc
  · rw [if_neg hi, if_pos hj]
    refine ⟨fun h => absurd h (by omega), ?_⟩
    rintro (rfl | ⟨_, hc⟩)
    · exact absurd hj hi
    · exact absurd hj hc
  · rw [if_neg hi, if_neg hj]
    exact ⟨fun _ => Or.inr ⟨hi, hj⟩, fun _ => rfl⟩

/-- **Individualizing one more vertex on top of a set-individualization = individualizing the bigger set.** -/
theorem samePartition_indivOne_insert (D : Finset (Fin n)) (v : Fin n) :
    samePartition (indivOne (individualizedColouring n D) v)
                  (individualizedColouring n (insert v D)) := by
  have hval : ∀ u : Fin n, indivOne (individualizedColouring n D) v u
      = (if u = v then 2 * individualizedColouring n D u + 1
         else 2 * individualizedColouring n D u) := fun _ => rfl
  intro i j
  rw [indiv_eq_iff (insert v D) i j]
  by_cases hi : i = v
  · by_cases hj : j = v
    · subst hi; subst hj; simp
    · rw [hval, hval, if_pos hi, if_neg hj]
      refine ⟨fun h => absurd h (by omega), ?_⟩
      rintro (rfl | ⟨hni, _⟩)
      · exact absurd hi hj
      · exact absurd (Finset.mem_insert_self v D) (hi ▸ hni)
  · by_cases hj : j = v
    · rw [hval, hval, if_neg hi, if_pos hj]
      refine ⟨fun h => absurd h (by omega), ?_⟩
      rintro (rfl | ⟨_, hnj⟩)
      · exact absurd hj hi
      · exact absurd (Finset.mem_insert_self v D) (hj ▸ hnj)
    · rw [hval, hval, if_neg hi, if_neg hj]
      have hc := indiv_eq_iff D i j
      constructor
      · intro h
        rcases hc.mp (by omega) with rfl | ⟨h1, h2⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨by simp [Finset.mem_insert, hi, h1], by simp [Finset.mem_insert, hj, h2]⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · rfl
        · have : individualizedColouring n D i = individualizedColouring n D j :=
            hc.mpr (Or.inr ⟨fun hd => h1 (Finset.mem_insert_of_mem hd),
                            fun hd => h2 (Finset.mem_insert_of_mem hd)⟩)
          omega

/-! ## 6. The descent's committed path, and the bridge -/

/-- **The descent's colouring after committing the path `p`** (head = most recently individualized). This is
exactly the colouring `descend` carries at the node reached by branching on `p` in order. -/
def pathCol (adj : AdjMatrix n) : List (Fin n) → Colouring n
  | [] => Refine.warmRefineR adj (fun _ => 0)
  | v :: p => Refine.warmRefineR adj (indivOne (pathCol adj p) v)

/-- **★★ THE PARTITION BRIDGE.** The descent's node colouring and the seal's `warmRefine` at the committed set
induce **the same partition** — so "same cell" means the same thing on both sides. -/
theorem pathCol_samePartition (adj : AdjMatrix n) : ∀ p : List (Fin n),
    samePartition (pathCol adj p)
      (warmRefine adj (Refine.constP n) (individualizedColouring n p.toFinset))
  | [] => by
      have hz : individualizedColouring n (∅ : Finset (Fin n)) = (fun _ => 0) := by
        funext u; simp [individualizedColouring]
      show samePartition (Refine.warmRefineR adj (fun _ => 0)) _
      rw [List.toFinset_nil, hz]
      exact warmRefineR_samePartition adj (fun _ => 0)
  | v :: p => by
      have ih := pathCol_samePartition adj p
      set W := fun ξ => warmRefine adj (Refine.constP n) ξ with hW
      set C := pathCol adj p with hC
      set D := individualizedColouring n p.toFinset with hD
      show samePartition (Refine.warmRefineR adj (indivOne C v)) _
      rw [List.toFinset_cons]
      -- encode-free round ≅ stock round
      refine (warmRefineR_samePartition adj (indivOne C v)).trans ?_
      -- `C ≅ W D`, so individualizing and refining agree
      have s1 : samePartition (W (indivOne C v)) (W (indivOne (W D) v)) :=
        warmRefine_samePartition adj (Refine.constP n) (indivOne_congr ih v)
      -- confluence: the early refinement is free
      have s2 : samePartition (W (indivOne (W D) v)) (W (indivOne D v)) :=
        warmRefine_indivOne_confluent adj (Refine.constP n) D v
      -- and one more `indivOne` on a set-individualization is the bigger set
      have s3 : samePartition (W (indivOne D v))
          (W (individualizedColouring n (insert v p.toFinset))) :=
        warmRefine_samePartition adj (Refine.constP n) (samePartition_indivOne_insert p.toFinset v)
      exact (s1.trans s2).trans s3

/-! ## 7. A path-fixing automorphism preserves the descent's colouring -/

theorem relabel_of_isAut {adj : AdjMatrix n} {α : Equiv.Perm (Fin n)} (h : IsAut α adj) :
    relabelAdj α adj = adj := by
  cases adj with
  | mk f =>
      have key : (fun i j => f (α.symm i) (α.symm j)) = f := by
        funext i j
        simpa using (h (α.symm i) (α.symm j)).symm
      show AdjMatrix.mk (fun i j => f (α.symm i) (α.symm j)) = AdjMatrix.mk f
      rw [key]

/-- **A path-fixing automorphism preserves the descent's colouring — EXACTLY, not merely up to partition.**
(Both `indivOne` and the refiner are equivariant, and `α` fixes every committed vertex, so the whole chain of
colourings is `α`-invariant.) This is what upgrades the seal's `ResidualAut` into the descent's `IsColAut`. -/
theorem transport_pathCol {adj : AdjMatrix n} {α : Equiv.Perm (Fin n)}
    (hadj : relabelAdj α adj = adj) : ∀ p : List (Fin n), (∀ v ∈ p, α v = v) →
      transportColouring α (pathCol adj p) = pathCol adj p
  | [], _ => by
      have hz : transportColouring α (fun _ : Fin n => (0 : Nat)) = (fun _ => 0) := rfl
      have h := Refine.refineEquivariant_encodeFree α adj (fun _ : Fin n => (0 : Nat))
      rw [hadj, hz] at h
      simpa [Refine.refineV_encodeFree, pathCol] using h.symm
  | v :: p, hfix => by
      have ih := transport_pathCol hadj p (fun u hu => hfix u (List.mem_cons_of_mem v hu))
      have hv : α v = v := hfix v List.mem_cons_self
      have h := Refine.refineEquivariant_encodeFree α adj (indivOne (pathCol adj p) v)
      rw [hadj] at h
      -- `α · (indivOne χ v) = indivOne (α · χ) (α v) = indivOne χ v`
      have hind : transportColouring α (indivOne (pathCol adj p) v) = indivOne (pathCol adj p) v := by
        rw [← indivOne_transport α (pathCol adj p) v, ih, hv]
      rw [hind] at h
      show transportColouring α (Refine.warmRefineR adj (indivOne (pathCol adj p) v))
          = Refine.warmRefineR adj (indivOne (pathCol adj p) v)
      simpa [Refine.refineV_encodeFree] using h.symm

theorem isColAut_of_pathFixing {adj : AdjMatrix n} {α : Equiv.Perm (Fin n)} (haut : IsAut α adj)
    {p : List (Fin n)} (hfix : ∀ v ∈ p, α v = v) : IsColAut adj (pathCol adj p) α := by
  refine ⟨fun i j => haut i j, fun u => ?_⟩
  have h := congrFun (transport_pathCol (relabel_of_isAut haut) p hfix) (α u)
  show pathCol adj p (α u) = pathCol adj p u
  simpa [transportColouring] using h.symm

/-! ## 8. ★★★ THE DELIVERABLE — the seal's localisation IS the oracle's firing hypothesis -/

/-- **★★★ `CellsAreOrbits` ⟹ the `horb` hypothesis of `Consume.cellIsOrbit_matchSupply`.**

This is the bridge. The seal corpus proves `CellsAreOrbits` (equivalently `OrbitRecoverableAt`,
`TwinsRealizedByResidualAut`, the deep clause of `SchemeRecoveredByDepth`) on CFI, on rank-≤2 schemes, on the four
sealed form families, and — via Spielman — at a bounded base. **Every one of those now reaches the supply.** -/
theorem horb_of_cellsAreOrbits {adj : AdjMatrix n} {p : List (Fin n)}
    (hco : CellsAreOrbits adj (Refine.constP n) p.toFinset) {u w : Fin n}
    (hcell : pathCol adj p u = pathCol adj p w) :
    ∃ α : Equiv.Perm (Fin n), IsColAut adj (pathCol adj p) α ∧ α u = w := by
  have hcell' : warmRefine adj (Refine.constP n) (individualizedColouring n p.toFinset) u
      = warmRefine adj (Refine.constP n) (individualizedColouring n p.toFinset) w :=
    (pathCol_samePartition adj p u w).mp hcell
  obtain ⟨α, haut, _hP, hfixD, hαu⟩ := hco u w hcell'
  exact ⟨α, isColAut_of_pathFixing haut (fun v hv => hfixD v (List.mem_toFinset.mpr hv)), hαu⟩

/-- **★★★ THE ORACLE FIRES ON THE SEAL'S CLASS.** At a node whose committed set localises (`CellsAreOrbits` — the
seal's own hypothesis) and which discretizes in one step (`Discretizing` — the cascade oracle's `hdisc`),
`matchSupply` certifies the branch cell as an orbit and `consume` collapses it to one branch.

⚠ **The `Discretizing` half is the frontier, and it is the one this bridge does *not* close.** It is far stronger
than it sounds: an automorphism fixing a branch vertex would preserve its (discrete) refinement and so be the
identity, i.e. `Discretizing` forces **trivial point stabilizers** — which is why `matchSupply` flags on `C₇`
(whose reflections fix a vertex) and why the next build is a supply that recovers `stab(v)`. What this file
delivers is that the *other* half — localisation — is now importable from the seal instead of re-proved. -/
theorem cellIsOrbit_of_cellsAreOrbits {adj : AdjMatrix n} {p : List (Fin n)}
    (hco : CellsAreOrbits adj (Refine.constP n) p.toFinset)
    (hd : Consume.Discretizing adj (pathCol adj p)) :
    Consume.CellIsOrbit (Consume.matchSupply (n := n)) adj (pathCol adj p) := by
  refine Consume.cellIsOrbit_matchSupply hd (fun u hu w hw => ?_)
  obtain ⟨c, hc, huc⟩ := Consume.exists_targetColour_of_mem hu
  have hwc : pathCol adj p w = c := (mem_branches_iff hc w).mp hw
  exact horb_of_cellsAreOrbits hco (by rw [huc, hwc])

end SealBridge
end ChainDescent
