/-
# Matrix-pencil corank ≤ root-multiplicity (corank tightening, step 2 — the genuinely-new core).

The degenerate-bucket bound in `ScratchTBound.normT_bucket_bound` charges *every* degenerate pencil member the worst
corank `d−1` (uniform `radical_card_mul_card_le`), giving a deg term `(d·|K|)·(|V|/√|K|)` whose `d` factor forces the
threshold `64·d²≤q` (`ScratchBucket.c0_le` hyp `hq2`). To drop that `d` to a constant we need the corank-stratified fact
`∑_r corank(F_r) ≤ d` over the degenerate ratios `r`. Its crux — proved here — is the per-ratio matrix-pencil bound:

  **`corank(A + t₀·B) ≤ rootMultiplicity t₀ (det(A + X·B))`.**

(A naive `corank ≤ const` is FALSE: the pencil reaches corank `d−2` at one ratio. So this multiplicity comparison is
essential.) The route is the `N = M₀·D` column-scaling realization:
* `pencilPoly A B := A.map C + X • B.map C : Matrix _ _ K[X]`; `det` over `K[X]`.
* Given ANY invertible `Q` whose columns on a set `S` lie in `ker(A + t₀·B)`, the product `pencilPoly A B * Q.map C`
  equals `pencilPoly (A*Q) (B*Q)`, whose `S`-columns are each `(X − C t₀) • (constant)` — so it factors as `M₀' · D`
  with `D = diagonal (S ↦ X−C t₀, else 1)`, `det D = (X−C t₀)^|S|`. Hence `(X−C t₀)^|S| ∣ det(pencilPoly A B)`
  (the unit `C(det Q)` is absorbed), and `le_rootMultiplicity_iff` (`det ≠ 0`) gives `|S| ≤ rootMultiplicity`.
* `exists_cols_ker` builds such a `Q` with `|S| = finrank ker(A+t₀B)` from a basis of the kernel + a complement.

NOT in build (scratch; `lake env lean ChainDescent/ScratchPencilCorank.lean`).
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace ChainDescent

open Polynomial Matrix Finset Module

variable {K : Type*} [Field K] {d : ℕ}

/-- The **matrix pencil** `A + X·B` as a single matrix over `K[X]` (each entry `C(A i j) + X·C(B i j)`). -/
noncomputable def pencilPoly (A B : Matrix (Fin d) (Fin d) K) : Matrix (Fin d) (Fin d) K[X] :=
  A.map (C : K →+* K[X]) + (X : K[X]) • B.map (C : K →+* K[X])

/-- Right-multiplying the pencil by a constant matrix `Q` is the pencil of the products. -/
theorem pencilPoly_mul_map (A B Q : Matrix (Fin d) (Fin d) K) :
    pencilPoly A B * Q.map (C : K →+* K[X]) = pencilPoly (A * Q) (B * Q) := by
  unfold pencilPoly
  rw [Matrix.add_mul, Matrix.smul_mul, ← Matrix.map_mul, ← Matrix.map_mul]

/-- **The column-factoring core.** If `Q` is invertible and its columns on `S` lie in `ker(A + t₀·B)`, then
`(X − C t₀)^|S|` divides `det(pencilPoly A B)`. -/
theorem pow_card_dvd_pencilDet_of_cols (A B : Matrix (Fin d) (Fin d) K) (t₀ : K)
    (Q : Matrix (Fin d) (Fin d) K) (hQ : IsUnit Q.det) (S : Finset (Fin d))
    (hker : ∀ j ∈ S, (A + t₀ • B).mulVec (fun k => Q k j) = 0) :
    (X - C t₀) ^ S.card ∣ (pencilPoly A B).det := by
  classical
  set N : Matrix (Fin d) (Fin d) K[X] := pencilPoly A B * Q.map (C : K →+* K[X]) with hN
  have hNrw : N = pencilPoly (A * Q) (B * Q) := by rw [hN, pencilPoly_mul_map]
  set D : Matrix (Fin d) (Fin d) K[X] :=
    Matrix.diagonal (fun j => if j ∈ S then (X - C t₀) else 1) with hD
  set M₀' : Matrix (Fin d) (Fin d) K[X] :=
    Matrix.of (fun i j => if j ∈ S then C ((B * Q) i j) else N i j) with hM
  -- columns: for j ∈ S, N i j = (X - C t₀) * C ((B*Q) i j)
  have hcol : ∀ i j, j ∈ S → N i j = (X - C t₀) * C ((B * Q) i j) := by
    intro i j hjS
    have hk := congrFun (hker j hjS) i
    have he : ((A + t₀ • B).mulVec (fun k => Q k j)) i = (A * Q) i j + t₀ * (B * Q) i j := by
      simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [he] at hk
    simp only [Pi.zero_apply] at hk
    have hAB : (A * Q) i j = -(t₀ * (B * Q) i j) := eq_neg_of_add_eq_zero_left hk
    rw [hNrw]
    simp only [pencilPoly, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hAB, map_neg, map_mul]
    ring
  -- N = M₀' * D
  have hNeq : N = M₀' * D := by
    ext i j
    rw [hD, Matrix.mul_diagonal, hM, Matrix.of_apply]
    by_cases hjS : j ∈ S
    · rw [if_pos hjS, if_pos hjS, hcol i j hjS]; ring
    · rw [if_neg hjS, if_neg hjS, mul_one]
  -- det D = (X - C t₀)^|S|
  have hDdet : D.det = (X - C t₀) ^ S.card := by
    rw [hD, Matrix.det_diagonal, Finset.prod_ite_mem_eq S, Finset.prod_const]
  -- divisibility through N
  have hdvdN : (X - C t₀) ^ S.card ∣ N.det :=
    ⟨M₀'.det, by rw [hNeq, Matrix.det_mul, hDdet, mul_comm]⟩
  have hdetN : N.det = (pencilPoly A B).det * C Q.det := by
    rw [hN, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  obtain ⟨u, hu⟩ := (Polynomial.isUnit_C (R := K)).mpr hQ
  have hXdvd : (pencilPoly A B).det = N.det * ↑u⁻¹ := by
    rw [hdetN, ← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [hXdvd]
  exact hdvdN.mul_right _

/-- **The adapted invertible matrix.** For any square `M₀`, there is an invertible `Q` and an index set `S` of size
`finrank ker(M₀)` whose `S`-columns lie in `ker(M₀.mulVecLin)`. (A basis of the kernel + a complement, packaged as a
change-of-basis matrix.) -/
theorem exists_cols_ker (M₀ : Matrix (Fin d) (Fin d) K) :
    ∃ (Q : Matrix (Fin d) (Fin d) K) (S : Finset (Fin d)),
      IsUnit Q.det ∧ S.card = finrank K (LinearMap.ker M₀.mulVecLin) ∧
      ∀ j ∈ S, M₀.mulVec (fun k => Q k j) = 0 := by
  classical
  obtain ⟨W', hWW'⟩ := Submodule.exists_isCompl (LinearMap.ker M₀.mulVecLin)
  set W := LinearMap.ker M₀.mulVecLin with hWdef
  have hsum : finrank K W + finrank K W' = d := by
    rw [Submodule.finrank_add_eq_of_isCompl hWW', Module.finrank_fin_fun]
  set eqv : (Fin (finrank K W) ⊕ Fin (finrank K W')) ≃ Fin d :=
    finSumFinEquiv.trans (finCongr hsum) with heqv
  set bE : Basis (Fin (finrank K W) ⊕ Fin (finrank K W')) K (Fin d → K) :=
    ((Module.finBasis K W).prod (Module.finBasis K W')).map
      (Submodule.prodEquivOfIsCompl W W' hWW') with hbE
  set e : Basis (Fin d) K (Fin d → K) := bE.reindex eqv with hedef
  set Q : Matrix (Fin d) (Fin d) K := (Pi.basisFun K (Fin d)).toMatrix ⇑e with hQ
  -- the `inl`-columns equal kernel basis vectors
  have hval : ∀ i : Fin (finrank K W),
      e (eqv (Sum.inl i)) = ((Module.finBasis K W i : W) : Fin d → K) := by
    intro i
    rw [hedef, Basis.reindex_apply, Equiv.symm_apply_apply, hbE, Basis.map_apply,
      Submodule.coe_prodEquivOfIsCompl', Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd]
    simp
  refine ⟨Q, Finset.univ.image (fun i : Fin (finrank K W) => eqv (Sum.inl i)), ?_, ?_, ?_⟩
  · haveI := Basis.invertibleToMatrix (Pi.basisFun K (Fin d)) e
    rw [hQ]; exact isUnit_det_of_invertible _
  · have hinj : Function.Injective (fun i : Fin (finrank K W) => eqv (Sum.inl i)) :=
      eqv.injective.comp Sum.inl_injective
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro j hjS
    rw [Finset.mem_image] at hjS
    obtain ⟨i, _, hij⟩ := hjS
    have hjW : (e j : Fin d → K) ∈ W := by rw [← hij, hval i]; exact Submodule.coe_mem _
    have hcol : (fun k => Q k j) = (e j : Fin d → K) := by
      funext k; rw [hQ, Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [hcol, ← Matrix.mulVecLin_apply]
    exact LinearMap.mem_ker.mp hjW

/-- **CORANK ≤ ROOT-MULTIPLICITY** (the corank-tightening crux). For the matrix pencil `A + X·B` with nonzero
determinant, the corank `finrank ker(A + t₀·B)` is at most the multiplicity of `t₀` as a root of `det(A + X·B)`. -/
theorem finrankKer_le_rootMult (A B : Matrix (Fin d) (Fin d) K) (t₀ : K)
    (hp : (pencilPoly A B).det ≠ 0) :
    finrank K (LinearMap.ker (A + t₀ • B).mulVecLin)
      ≤ (pencilPoly A B).det.rootMultiplicity t₀ := by
  obtain ⟨Q, S, hQ, hScard, hker⟩ := exists_cols_ker (A + t₀ • B)
  rw [← hScard, le_rootMultiplicity_iff hp]
  exact pow_card_dvd_pencilDet_of_cols A B t₀ Q hQ S hker

/-- The pencil determinant has degree at most `d` (each entry is linear in `X`). -/
theorem pencilDet_natDegree_le (A B : Matrix (Fin d) (Fin d) K) :
    (pencilPoly A B).det.natDegree ≤ d := by
  have h := Polynomial.natDegree_det_X_add_C_le B A
  rw [Fintype.card_fin] at h
  rwa [show pencilPoly A B = (X : K[X]) • B.map C + A.map C by unfold pencilPoly; rw [add_comm]]

/-- **∑ corank ≤ d** (the corank-stratified budget). Over any finite set `T` of (degenerate) ratios `t`, the total
corank `∑ finrank ker(A + t·B)` is at most `d`. Sums the per-ratio `finrankKer_le_rootMult` against
`∑ rootMultiplicity ≤ card roots ≤ natDegree ≤ d`. This is the fact that breaks the uniform-bucket `d` factor. -/
theorem sum_finrankKer_le (A B : Matrix (Fin d) (Fin d) K) (T : Finset K)
    (hp : (pencilPoly A B).det ≠ 0) :
    ∑ t ∈ T, finrank K (LinearMap.ker (A + t • B).mulVecLin) ≤ d := by
  classical
  set p := (pencilPoly A B).det with hpd
  calc ∑ t ∈ T, finrank K (LinearMap.ker (A + t • B).mulVecLin)
      ≤ ∑ t ∈ T, p.rootMultiplicity t :=
        Finset.sum_le_sum (fun t _ => finrankKer_le_rootMult A B t hp)
    _ = ∑ t ∈ T, p.roots.count t := by
        exact Finset.sum_congr rfl (fun t _ => (Polynomial.count_roots p).symm ▸ rfl)
    _ ≤ ∑ t ∈ p.roots.toFinset, p.roots.count t :=
        Finset.sum_le_sum_of_ne_zero (fun t _ hne =>
          Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero hne)))
    _ = Multiset.card p.roots := Multiset.toFinset_sum_count_eq _
    _ ≤ p.natDegree := Polynomial.card_roots' _
    _ ≤ d := pencilDet_natDegree_le A B

end ChainDescent

#print axioms ChainDescent.pencilPoly_mul_map
#print axioms ChainDescent.pow_card_dvd_pencilDet_of_cols
#print axioms ChainDescent.exists_cols_ker
#print axioms ChainDescent.finrankKer_le_rootMult
#print axioms ChainDescent.pencilDet_natDegree_le
#print axioms ChainDescent.sum_finrankKer_le
