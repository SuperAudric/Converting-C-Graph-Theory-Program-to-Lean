/-
# The `‖T‖` magnitude bound (increment 3, step 3e-ii) — pencil radical + Schwartz–Zippel + bucket assembly.

Bounds the character sum `T = ∑_t χ(I_u t)·χ(I_v t)` that controls the per-anchor non-separation count, by splitting
`normT_le`'s RHS into nondegenerate and degenerate pencil members and bounding each bucket:

* **pencil radical** (was `ScratchCorank`): `polarRad` as a `Submodule` + the corank-uniform proper-subspace bound
  `|radical F|·q ≤ |V|` for every nonzero `F` (no corank stratification).
* **Schwartz–Zippel** (was `ScratchGoodAnchor`): `mvPoly_zeros_count_le` (`p ≠ 0 ⟹ #zeros ≤ totalDegree·|K|`) ⟹
  `degenerate_count_le` (#degenerate pencil ratios `≤ d·|K|`, given a good anchor). REUSABLE.
* **two-bucket arithmetic** (was `ScratchBucket`): `∑ g ≤ Ca·Ma + Cb·Mb`. REUSABLE.
* **‖χ‖** (was `ScratchChiNorm`): `‖χ-into-ℂ‖ = [·≠0]`.
* **assembly** (was `ScratchTBound`): `normT_bucket_bound` — `|K|·‖T‖ ≤ q²√n + (d·q)(n/√q)`.

(Merge of the former `ScratchCorank` + `ScratchGoodAnchor` + `ScratchBucket` + `ScratchChiNorm` + `ScratchTBound`.)
-/
import ChainDescent.PairForm
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace ChainDescent

section -- ═══════════ was ScratchCorank ═══════════

open Module

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The polar-radical of a quadratic form `F`, bundled as a submodule:
`{ h | ∀ x, polar F x h = 0 }`. (Right radical of `F.polarBilin`.) -/
def polarRad (F : QuadraticForm K V) : Submodule K V where
  carrier := {h | ∀ x, QuadraticMap.polar F x h = 0}
  zero_mem' := fun x => QuadraticMap.polar_zero_right F x
  add_mem' := by
    intro a b ha hb x
    rw [QuadraticMap.polar_add_right, ha x, hb x, add_zero]
  smul_mem' := by
    intro c a ha x
    rw [QuadraticMap.polar_smul_right, ha x, smul_zero]

@[simp] theorem mem_polarRad {F : QuadraticForm K V} {h : V} :
    h ∈ polarRad F ↔ ∀ x, QuadraticMap.polar F x h = 0 := Iff.rfl

/-- The `Finset.filter` cardinality used in `normT_le`'s RHS equals `Nat.card` of `polarRad F`.
Routed through `Nat.card`/`Set.ncard` (instance-free) to avoid `Fintype`-on-submodule instance mismatches. -/
theorem polarRad_card_filter [Fintype V] [DecidableEq K] (F : QuadraticForm K V) :
    (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar F x h = 0)).card
      = Nat.card (polarRad F) := by
  classical
  rw [show Nat.card (polarRad F) = (polarRad F : Set V).ncard from rfl,
    Set.ncard_eq_toFinset_card' (polarRad F : Set V)]
  congr 1
  ext h
  simp only [Set.mem_toFinset, SetLike.mem_coe, mem_polarRad, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- **`F ≠ 0 ⟹ its polar-radical is a PROPER subspace** (char ≠ 2).** If the radical were everything, then
`polar F x x = 0` for all `x`, i.e. `2 • F x = 0`, i.e. `F x = 0` (invertible 2), forcing `F = 0`. -/
theorem polarRad_ne_top_of_ne_zero [Invertible (2 : K)] (F : QuadraticForm K V) (hF : F ≠ 0) :
    polarRad F ≠ ⊤ := by
  intro htop
  apply hF
  have hzero : ∀ x, F x = 0 := by
    intro x
    have hx : QuadraticMap.polar F x x = 0 := by
      have hmem : x ∈ polarRad F := htop ▸ Submodule.mem_top
      exact hmem x
    rw [QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat] at hx
    exact (mul_eq_zero.1 hx).resolve_left (Invertible.ne_zero (2 : K))
  exact QuadraticMap.ext (fun x => by simp [hzero x])

/-- **The corank-uniform proper-subspace bound (the corank ≥ 2 enabler).** For any NONZERO quadratic form `F`
on a finite space `V` over a finite field `K` (char ≠ 2), `|radical F| · |K| ≤ |V|` — equivalently
`|radical F| ≤ q^{d-1}`, regardless of the corank. -/
theorem radical_card_mul_card_le [Fintype K] [DecidableEq K] [Fintype V] [Invertible (2 : K)]
    (F : QuadraticForm K V) (hF : F ≠ 0) :
    (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar F x h = 0)).card * Fintype.card K
      ≤ Fintype.card V := by
  classical
  rw [polarRad_card_filter, ← Nat.card_eq_fintype_card (α := K), ← Nat.card_eq_fintype_card (α := V),
    Module.natCard_eq_pow_finrank (K := K) (V := polarRad F),
    Module.natCard_eq_pow_finrank (K := K) (V := V)]
  have hlt : finrank K (polarRad F) < finrank K V :=
    Submodule.finrank_lt (polarRad_ne_top_of_ne_zero F hF)
  calc Nat.card K ^ finrank K (polarRad F) * Nat.card K
      = Nat.card K ^ (finrank K (polarRad F) + 1) := by rw [pow_succ]
    _ ≤ Nat.card K ^ finrank K V := Nat.pow_le_pow_right Nat.card_pos hlt

end

section -- ═══════════ was ScratchGoodAnchor ═══════════

open Finset Module

/-- **The Schwartz–Zippel count (n = 2).** For a nonzero polynomial `p` in two variables over a finite field `K`,
the number of common zeros over `K²` is at most `p.totalDegree · |K|`. This is the analytic core of the good-anchor
count: applied to the pencil discriminant `disc(y,z)` (degree `d`, `≢ 0` at a good anchor) it gives `#degenerate ≤ d·q`. -/
theorem mvPoly_zeros_count_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : MvPolynomial (Fin 2) K} (hp : p ≠ 0) :
    (Finset.univ.filter (fun f : Fin 2 → K => MvPolynomial.eval f p = 0)).card
      ≤ p.totalDegree * Fintype.card K := by
  have hq : 0 < Fintype.card K := Fintype.card_pos
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset K)
  -- rewrite `piFinset (fun _ => univ) = univ` and `#univ = card K`
  rw [Fintype.piFinset_univ, Finset.card_univ] at hsz
  set Sz : ℕ := (Finset.univ.filter (fun f : Fin 2 → K => MvPolynomial.eval f p = 0)).card with hSz
  -- hsz : (Sz : ℚ≥0) / (card K)^2 ≤ totalDegree / card K
  set q : ℕ := Fintype.card K with hqdef
  have hqQ : (0 : ℚ≥0) < (q : ℚ≥0) := by exact_mod_cast hq
  -- clear the LHS denominator, then cancel one factor of q from the RHS
  rw [div_le_iff₀ (by positivity : (0 : ℚ≥0) < (q : ℚ≥0) ^ 2), sq, ← mul_assoc,
    div_mul_cancel₀ _ hqQ.ne'] at hsz
  -- hsz : (Sz : ℚ≥0) ≤ (p.totalDegree : ℚ≥0) * q
  exact_mod_cast hsz

/-- **The pencil-discriminant degree bound.** The determinant of a `d × d` matrix whose every entry is a
2-variable polynomial of `totalDegree ≤ 1` (a *linear pencil* `y·A + z·B`) has `totalDegree ≤ d`. This caps the
discriminant `disc(y,z) = det(y·G_u + z·G_v)` at degree `d`, the `p.totalDegree` fed into `mvPoly_zeros_count_le`. -/
theorem det_totalDegree_le {K : Type*} [CommRing K] {d : ℕ}
    (M : Matrix (Fin d) (Fin d) (MvPolynomial (Fin 2) K))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) :
    M.det.totalDegree ≤ d := by
  rw [Matrix.det_apply]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le (fun σ _ => ?_))
  refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  calc ∑ i : Fin d, (M (σ i) i).totalDegree
      ≤ ∑ _i : Fin d, 1 := Finset.sum_le_sum (fun i _ => hM (σ i) i)
    _ = d := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

open MvPolynomial in
/-- The **pencil discriminant** of two matrices `A, B` over `K`: the determinant of the linear-pencil matrix
`y·A + z·B` packaged as a 2-variable polynomial `det(X₀·A + X₁·B) : MvPolynomial (Fin 2) K`. -/
noncomputable def pencilDisc {K : Type*} [CommRing K] {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) K) : MvPolynomial (Fin 2) K :=
  (Matrix.of fun i j => X (0 : Fin 2) * C (A i j) + X 1 * C (B i j)).det

open MvPolynomial in
/-- `pencilDisc A B` has `totalDegree ≤ d` (each entry is linear in `(X₀, X₁)`). -/
theorem pencilDisc_totalDegree_le {K : Type*} [CommRing K] [Nontrivial K] {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) K) : (pencilDisc A B).totalDegree ≤ d := by
  refine det_totalDegree_le _ (fun i j => ?_)
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  rw [max_le_iff]
  refine ⟨?_, ?_⟩ <;>
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, add_zero, MvPolynomial.totalDegree_X]

open MvPolynomial in
/-- Evaluating `pencilDisc A B` at `(y, z)` recovers `det(y·A + z·B)`. -/
theorem pencilDisc_eval {K : Type*} [CommRing K] {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) K) (y z : K) :
    MvPolynomial.eval ![y, z] (pencilDisc A B) = (y • A + z • B).det := by
  rw [pencilDisc, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply]

section Bridge
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Polar of the pencil form `y•P + z•R` is the linear combination of the polars. -/
theorem polar_pencil (P R : QuadraticForm K V) (y z : K) (x h : V) :
    QuadraticMap.polar (y • P + z • R) x h
      = y * QuadraticMap.polar P x h + z * QuadraticMap.polar R x h := by
  simp only [QuadraticMap.polar, QuadraticMap.add_apply, QuadraticMap.smul_apply, smul_eq_mul]
  ring

/-- The polar-radical is trivial ⟺ the polar bilinear form separates on the right. -/
theorem polarRad_eq_bot_iff_separatingRight (G : QuadraticForm K V) :
    polarRad G = ⊥ ↔ (QuadraticMap.polarBilin G).SeparatingRight := by
  rw [Submodule.eq_bot_iff]
  constructor
  · intro hh y hy
    refine hh y (mem_polarRad.2 (fun x => ?_))
    rw [← QuadraticMap.polarBilin_apply_apply]; exact hy x
  · intro hh y hy
    refine hh y (fun x => ?_)
    rw [QuadraticMap.polarBilin_apply_apply]; exact (mem_polarRad.1 hy) x

/-- **Degeneracy ⟺ vanishing determinant** (the bridge linchpin). For a basis `b`, the pencil member `G` is degenerate
(`polarRad G ≠ ⊥`) iff the determinant of the Gram matrix of its polar form vanishes. -/
theorem polarRad_ne_bot_iff_det_eq_zero {d : ℕ} (b : Basis (Fin d) K V) (G : QuadraticForm K V) :
    polarRad G ≠ ⊥ ↔ (LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin G)).det = 0 := by
  rw [ne_eq, polarRad_eq_bot_iff_separatingRight, LinearMap.separatingRight_iff_det_ne_zero b,
    not_ne_iff]

/-- The Gram matrix of the pencil's polar form is the linear pencil `y•A + z•B` of the Gram matrices. -/
theorem toMatrix₂_polarBilin_pencil {d : ℕ} (b : Basis (Fin d) K V)
    (P R : QuadraticForm K V) (y z : K) :
    LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin (y • P + z • R))
      = y • LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin P)
        + z • LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin R) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, LinearMap.toMatrix₂_apply,
    LinearMap.toMatrix₂_apply, LinearMap.toMatrix₂_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply, polar_pencil,
    smul_eq_mul, smul_eq_mul]

end Bridge

/-- The Schwartz–Zippel count over `K × K` (via the `(y,z) ↦ ![y,z]` bijection). -/
theorem pencilZeros_count_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : MvPolynomial (Fin 2) K} (hp : p ≠ 0) :
    (Finset.univ.filter (fun yz : K × K => MvPolynomial.eval ![yz.1, yz.2] p = 0)).card
      ≤ p.totalDegree * Fintype.card K := by
  refine le_trans (le_of_eq ?_) (mvPoly_zeros_count_le hp)
  refine Finset.card_nbij' (fun yz => ![yz.1, yz.2]) (fun f => (f 0, f 1)) ?_ ?_ ?_ ?_
  · intro yz hyz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hyz ⊢
    exact hyz
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    rwa [show (![(f 0), (f 1)] : Fin 2 → K) = f from by ext i; fin_cases i <;> rfl]
  · intro yz _; rfl
  · intro f _; ext i; fin_cases i <;> rfl

/-- **THE GOOD-ANCHOR COUNT.** For a good anchor (∃ nondegenerate pencil member `polarRad (y•P+z•R) = ⊥`), the number of
*degenerate* ratios `(y,z)` is at most `d·|K|`. Assembles the analytic cores (`pencilZeros_count_le`,
`pencilDisc_totalDegree_le`) with the bridge (`polarRad_ne_bot_iff_det_eq_zero`, `toMatrix₂_polarBilin_pencil`,
`pencilDisc_eval`) on the pencil discriminant `disc = det(X₀·A + X₁·B)`, `A,B` the Gram matrices of `polar P, polar R`. -/
theorem degenerate_count_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {V : Type*} [AddCommGroup V] [Module K V] {d : ℕ} (b : Basis (Fin d) K V)
    (P R : QuadraticForm K V) (hgood : ∃ y z : K, polarRad (y • P + z • R) = ⊥) :
    (Finset.univ.filter (fun yz : K × K => polarRad (yz.1 • P + yz.2 • R) ≠ ⊥)).card
      ≤ d * Fintype.card K := by
  set A := LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin P) with hA
  set B' := LinearMap.toMatrix₂ b b (QuadraticMap.polarBilin R) with hB
  have hiff : ∀ y z : K, polarRad (y • P + z • R) ≠ ⊥
      ↔ MvPolynomial.eval ![y, z] (pencilDisc A B') = 0 := by
    intro y z
    rw [polarRad_ne_bot_iff_det_eq_zero b, toMatrix₂_polarBilin_pencil b, ← hA, ← hB,
      ← pencilDisc_eval A B' y z]
  obtain ⟨y₀, z₀, h0⟩ := hgood
  have hne0 : MvPolynomial.eval ![y₀, z₀] (pencilDisc A B') ≠ 0 :=
    fun heq => (hiff y₀ z₀).mpr heq h0
  have hdisc : pencilDisc A B' ≠ 0 := fun hc => hne0 (by rw [hc, map_zero])
  calc (Finset.univ.filter (fun yz : K × K => polarRad (yz.1 • P + yz.2 • R) ≠ ⊥)).card
      = (Finset.univ.filter
          (fun yz : K × K => MvPolynomial.eval ![yz.1, yz.2] (pencilDisc A B') = 0)).card := by
        refine Finset.card_bij (fun yz _ => yz) ?_ (fun _ _ _ _ h => h) ?_
        · intro yz hyz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyz ⊢
          exact (hiff yz.1 yz.2).1 hyz
        · intro yz hyz
          refine ⟨yz, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyz ⊢
          exact (hiff yz.1 yz.2).2 hyz
    _ ≤ (pencilDisc A B').totalDegree * Fintype.card K := pencilZeros_count_le hdisc
    _ ≤ d * Fintype.card K := by gcongr; exact pencilDisc_totalDegree_le A B'

end

section -- ═══════════ was ScratchBucket ═══════════

open Finset

/-- **Two-bucket sum bound.** Split `s` by predicate `p`; if `g ≤ Ma` on the `¬p` bucket and `g ≤ Mb` on the `p`
bucket, with cardinalities `≤ Ca`, `≤ Cb` respectively (and `Ma, Mb ≥ 0`), then `∑_{i∈s} g i ≤ Ca·Ma + Cb·Mb`. -/
theorem sum_two_bucket_le {ι : Type*} (s : Finset ι) (g : ι → ℝ) (p : ι → Prop) [DecidablePred p]
    (Ma Mb Ca Cb : ℝ) (hMa : 0 ≤ Ma) (hMb : 0 ≤ Mb)
    (ha : ∀ i ∈ s, ¬ p i → g i ≤ Ma) (hb : ∀ i ∈ s, p i → g i ≤ Mb)
    (hca : ((s.filter (fun i => ¬ p i)).card : ℝ) ≤ Ca)
    (hcb : ((s.filter p).card : ℝ) ≤ Cb) :
    ∑ i ∈ s, g i ≤ Ca * Ma + Cb * Mb := by
  rw [← Finset.sum_filter_add_sum_filter_not s p g, add_comm]
  refine add_le_add ?_ ?_
  · calc ∑ i ∈ s.filter (fun i => ¬ p i), g i
        ≤ ∑ _i ∈ s.filter (fun i => ¬ p i), Ma :=
          Finset.sum_le_sum (fun i hi => ha i (Finset.mem_filter.1 hi).1 (Finset.mem_filter.1 hi).2)
      _ = ((s.filter (fun i => ¬ p i)).card : ℝ) * Ma := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Ca * Ma := mul_le_mul_of_nonneg_right hca hMa
  · calc ∑ i ∈ s.filter p, g i
        ≤ ∑ _i ∈ s.filter p, Mb :=
          Finset.sum_le_sum (fun i hi => hb i (Finset.mem_filter.1 hi).1 (Finset.mem_filter.1 hi).2)
      _ = ((s.filter p).card : ℝ) * Mb := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Cb * Mb := mul_le_mul_of_nonneg_right hcb hMb

/-- **Deg-bucket magnitude.** If `r·k ≤ V` (the proper-subspace radical bound), then `√(V·r) ≤ V/√k`. Used with
`r = |radical F_{y,z}|`, `k = |K|`, `V = card V`: a degenerate member contributes at most `card V / √|K|`. -/
theorem sqrt_mul_le_div {V k r : ℝ} (hV : 0 ≤ V) (hk : 0 < k) (h : r * k ≤ V) :
    Real.sqrt (V * r) ≤ V / Real.sqrt k := by
  have hr2 : r ≤ V / k := (le_div_iff₀ hk).2 h
  have h1 : V * r ≤ V ^ 2 / k := by
    rw [sq, mul_div_assoc]; exact mul_le_mul_of_nonneg_left hr2 hV
  calc Real.sqrt (V * r) ≤ Real.sqrt (V ^ 2 / k) := Real.sqrt_le_sqrt h1
    _ = V / Real.sqrt k := by rw [Real.sqrt_div (by positivity), Real.sqrt_sq hV]

/-- **The final c₀ bound (3e-iii finish).** From the counting bound `2·NS ≤ 2·z_u + n + T` (`card_agree_le`), the `|T|`
bound `T ≤ q·√n + d·n/√q` (`normT_bucket_bound`, ÷q), and the zero-count `z_u·q ≤ n + (q−1)·n/√q` (`zeroCount_sq_le` with
the proper-subspace radical bound), under the threshold `64q² ≤ n` (i.e. `d ≥ 3`), `64d² ≤ q`, `256 ≤ q`: `NS ≤ ¾·n`, i.e.
`c₀ = NS/n ≤ ¾`. -/
theorem c0_le {n q dR T zu NS : ℝ} (hn : 0 < n) (hq : 0 < q) (hd : 0 ≤ dR)
    (hcount : 2 * NS ≤ 2 * zu + n + T)
    (hT : T ≤ q * Real.sqrt n + dR * n / Real.sqrt q)
    (hzu : zu * q ≤ n + (q - 1) * n / Real.sqrt q)
    (hq1 : 64 * q ^ 2 ≤ n) (hq2 : 64 * dR ^ 2 ≤ q) (hq3 : 256 ≤ q) :
    NS ≤ 3 / 4 * n := by
  set r := Real.sqrt q with hrdef
  set m := Real.sqrt n with hmdef
  have hr : 0 < r := Real.sqrt_pos.2 hq
  have hm : 0 ≤ m := Real.sqrt_nonneg _
  have hnn : m * m = n := Real.mul_self_sqrt hn.le
  have h8q : 8 * q ≤ m := by
    rw [hmdef, show (8 : ℝ) * q = Real.sqrt ((8 * q) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hq1])
  have h8d : 8 * dR ≤ r := by
    rw [hrdef, show (8 : ℝ) * dR = Real.sqrt ((8 * dR) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hq2])
  have h16 : (16 : ℝ) ≤ r := by
    rw [hrdef, show (16 : ℝ) = Real.sqrt (16 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hq3])
  -- T ≤ n/4
  have hA : q * m ≤ n / 8 := by nlinarith [mul_le_mul_of_nonneg_right h8q hm, hnn]
  have hB : dR * n / r ≤ n / 8 := by
    rw [div_le_iff₀ hr]; nlinarith [mul_le_mul_of_nonneg_right h8d hn.le]
  have hTb : T ≤ n / 4 := by linarith [hT, hA, hB]
  -- z_u ≤ n/8
  have hC : n ≤ q * n / 16 := by nlinarith [hq3, hn]
  have hD : (q - 1) * n / r ≤ q * n / 16 := by
    rw [div_le_iff₀ hr]; nlinarith [mul_le_mul_of_nonneg_left h16 hq.le, hn.le, mul_nonneg hq.le hn.le]
  have hzub : zu ≤ n / 8 := by
    have hzq : zu * q ≤ n / 8 * q := by nlinarith [hzu, hC, hD]
    exact le_of_mul_le_mul_right hzq hq
  linarith [hcount, hTb, hzub]

end

section -- ═══════════ was ScratchChiNorm ═══════════

open scoped Classical

/-- The quadratic character composed into `ℂ` has norm `0` at `0` and `1` elsewhere. -/
theorem norm_quadraticChar {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (y : K) :
    ‖((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) y‖ = if y = 0 then 0 else 1 := by
  rw [MulChar.ringHomComp_apply]
  split_ifs with hy
  · subst hy
    rw [quadraticChar_zero]
    simp
  · have h2 : (quadraticChar K y) ^ 2 = 1 := quadraticChar_sq_one hy
    have hc : ((Int.castRingHom ℂ) (quadraticChar K y)) ^ 2 = 1 := by
      rw [← map_pow, h2, map_one]
    have hsq : ‖(Int.castRingHom ℂ) (quadraticChar K y)‖ ^ 2 = 1 := by
      rw [← norm_pow, hc, norm_one]
    nlinarith [norm_nonneg ((Int.castRingHom ℂ) (quadraticChar K y)), hsq]

end

section -- ═══════════ was ScratchTBound ═══════════

open Finset Module

/-- **The `|T|` bound (3e-ii).** For a good anchor with no zero member (`hnz`, `hgood`), the per-pair character sum `T`
satisfies `|K|·‖T‖ ≤ |K|²·√|V| + (d·|K|)·(|V|/√|K|)`. The nondeg bucket contributes `≤ |K|²·√|V|`, the deg bucket
`≤ (d·|K|)·(|V|/√|K|)`. -/
theorem normT_bucket_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
    (hF : ringChar K ≠ 2) {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (u v t₀ : V) {d : ℕ} (b : Basis (Fin d) K V)
    (hnz : ∀ y z : K, y ≠ 0 → z ≠ 0 →
      y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v) ≠ 0)
    (hgood : ∃ y z : K, polarRad (y • pairForm Q (t₀ - u) + z • pairForm Q (t₀ - v)) = ⊥) :
    (Fintype.card K : ℝ)
        * ‖∑ t : V, ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - u) (t - u))
            * ((quadraticChar K).ringHomComp (Int.castRingHom ℂ)) (pairForm Q (t₀ - v) (t - v))‖
      ≤ (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V)
        + (d * Fintype.card K) * (Fintype.card V / Real.sqrt (Fintype.card K)) := by
  classical
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom ℂ) with hχ
  set P := pairForm Q (t₀ - u) with hP
  set R := pairForm Q (t₀ - v) with hR
  -- abbreviations
  set p : K × K → Prop := fun x => polarRad (x.1 • P + x.2 • R) ≠ ⊥ with hp
  set s : Finset (K × K) := Finset.univ.filter (fun x : K × K => x.1 ≠ 0 ∧ x.2 ≠ 0) with hs
  -- the per-term magnitude `g`
  set g : K × K → ℝ := fun x => Real.sqrt ((Fintype.card V : ℝ)
      * (Finset.univ.filter (fun h : V => ∀ y, QuadraticMap.polar (x.1 • P + x.2 • R) y h = 0)).card)
    with hg
  -- pointwise: χ-weights collapse the summand onto the support `s`
  have hF0 : ∀ x : K × K, ‖χ x.1‖ * ‖χ x.2‖ * g x = if (x.1 ≠ 0 ∧ x.2 ≠ 0) then g x else 0 := by
    intro x
    rw [norm_quadraticChar, norm_quadraticChar]
    by_cases h1 : x.1 = 0
    · simp [h1]
    · by_cases h2 : x.2 = 0
      · simp [h1, h2]
      · simp [h1, h2]
  -- the double sum collapses to `∑ over s`
  have hsum : (∑ y : K, ∑ z : K, ‖χ y‖ * ‖χ z‖ * g (y, z)) = ∑ x ∈ s, g x := by
    rw [← Finset.sum_product', Finset.univ_product_univ, hs, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun x _ => hF0 x)
  -- magnitude bounds
  have hMa : (0 : ℝ) ≤ Real.sqrt (Fintype.card V) := Real.sqrt_nonneg _
  have hMb : (0 : ℝ) ≤ (Fintype.card V : ℝ) / Real.sqrt (Fintype.card K) :=
    div_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hcardK : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  -- nondeg bucket: `g x = √|V|`
  have ha : ∀ x ∈ s, ¬ p x → g x ≤ Real.sqrt (Fintype.card V) := by
    intro x _ hx
    rw [hp] at hx
    have hbot : polarRad (x.1 • P + x.2 • R) = ⊥ := not_not.1 hx
    have hone : (Finset.univ.filter
        (fun h : V => ∀ y, QuadraticMap.polar (x.1 • P + x.2 • R) y h = 0)).card = 1 := by
      rw [polarRad_card_filter, hbot]
      simp
    rw [hg]; simp only; rw [hone]; simp
  -- deg bucket: `g x ≤ |V|/√|K|`
  have hb : ∀ x ∈ s, p x → g x ≤ (Fintype.card V : ℝ) / Real.sqrt (Fintype.card K) := by
    intro x hxs _
    rw [hs, Finset.mem_filter] at hxs
    obtain ⟨_, h1, h2⟩ := hxs
    have hGne : x.1 • P + x.2 • R ≠ 0 := hnz x.1 x.2 h1 h2
    have hcount := radical_card_mul_card_le (x.1 • P + x.2 • R) hGne
    rw [hg]; simp only
    refine sqrt_mul_le_div (by positivity) hcardK ?_
    exact_mod_cast hcount
  -- count bounds
  have hca : ((s.filter (fun x => ¬ p x)).card : ℝ) ≤ (Fintype.card K : ℝ) ^ 2 := by
    rw [sq]
    calc ((s.filter (fun x => ¬ p x)).card : ℝ) ≤ (Fintype.card (K × K) : ℝ) := by
          exact_mod_cast Finset.card_le_univ _
      _ = (Fintype.card K : ℝ) * Fintype.card K := by rw [Fintype.card_prod]; push_cast; ring
  have hcb : ((s.filter p).card : ℝ) ≤ (d * Fintype.card K : ℝ) := by
    have hsub : s.filter p ⊆
        Finset.univ.filter (fun x : K × K => polarRad (x.1 • P + x.2 • R) ≠ ⊥) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, hx.2⟩
    calc ((s.filter p).card : ℝ)
        ≤ ((Finset.univ.filter (fun x : K × K => polarRad (x.1 • P + x.2 • R) ≠ ⊥)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (d * Fintype.card K : ℝ) := by exact_mod_cast degenerate_count_le b P R hgood
  -- assemble
  calc (Fintype.card K : ℝ) * ‖∑ t : V, χ (P (t - u)) * χ (R (t - v))‖
      ≤ ∑ y : K, ∑ z : K, ‖χ y‖ * ‖χ z‖ * g (y, z) := normT_le hF hψ Q u v t₀
    _ = ∑ x ∈ s, g x := hsum
    _ ≤ (Fintype.card K : ℝ) ^ 2 * Real.sqrt (Fintype.card V)
          + (d * Fintype.card K) * (Fintype.card V / Real.sqrt (Fintype.card K)) :=
        sum_two_bucket_le s g p _ _ _ _ hMa hMb ha hb hca hcb

end

end ChainDescent

#print axioms ChainDescent.polarRad_card_filter
#print axioms ChainDescent.polarRad_ne_top_of_ne_zero
#print axioms ChainDescent.radical_card_mul_card_le
#print axioms ChainDescent.mvPoly_zeros_count_le
#print axioms ChainDescent.det_totalDegree_le
#print axioms ChainDescent.pencilDisc_totalDegree_le
#print axioms ChainDescent.pencilDisc_eval
#print axioms ChainDescent.polarRad_ne_bot_iff_det_eq_zero
#print axioms ChainDescent.degenerate_count_le
#print axioms ChainDescent.sum_two_bucket_le
#print axioms ChainDescent.sqrt_mul_le_div
#print axioms ChainDescent.c0_le
#print axioms ChainDescent.norm_quadraticChar
#print axioms ChainDescent.normT_bucket_bound
