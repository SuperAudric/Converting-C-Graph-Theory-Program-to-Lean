/-
# Nullstellensatz discharge — the cone-covering count (WIP, route B)

The connectivity fact `hconn` (⟹ `nullstellensatz_of_connectivity`) reduces, via the route-A scaffold, to ONE
classical counting lemma:
  `cone_not_covered` — nondeg `Q` on `𝔽_q^d`, vectors `u₁,…,u_k` (`k ≤ 2` suffices via the `A_e`-hub walk) ⟹ ∃
  isotropic `a` with `polar Q uᵢ a ≠ 0` ∀`i` (the isotropic cone is not covered by `k` hyperplanes `uᵢ^⊥`).

This file builds it from the project's OWN Gauss-sum count machinery (`ChainDescent.zeroCount_sq_le` in `PairForm`,
which for a quadratic `P` bounds `(|{P=0}|·q − qᵈ)² ≤ (q−1)²·(qᵈ·|radical P|)`), avoiding any from-scratch magnitude
work. For nondegenerate `Q` the radical is `{0}`, giving the cone size `|cone| ≥ (qᵈ − (q−1)·√(qᵈ))/q`.

**STATUS (2026-07-06 — cone brick landed; section design refined by probe).** `radical_card_one` + `cone_card_lower`
landed (axiom-clean). **★ KEY DESIGN FINDING (`/tmp/sec_probe.py`, 2026-07-06):** for a hyperplane `u^⊥`,
`|cone ∩ u^⊥|` is **EXACTLY `q^{d-2}` when `u` is ANISOTROPIC** (`u^⊥` is odd-dim `d−1`, so the `card_quadForm_eq`
bracket `∑_{t≠0}χ(t)^{d-1} = ∑χ(t) = 0` kills the error term), but VARIES (can exceed `q^{d-2}`) when `u` is isotropic.
⟹ **design the covering to use ONLY ANISOTROPIC hyperplane-vectors:** then `cone_not_covered` for `k=2` is the clean
union bound `|cone| > 2·q^{d-2}`, which holds for ALL `q ≥ 3` (`d=4,q=3` minus: `21 > 18` ✓) with NO small-`q` tail —
because both sections are the EXACT `q^{d-2}`, not a loose magnitude bound. (An isotropic hub-vector `e` reintroduces the
tight `d=4 q=3` boundary where the magnitude bound is insufficient — AVOID it.)

**LANDED (2026-07-06, axiom-clean):** `radical_card_one`, `cone_card_lower`, **`card_zeros_odd`** (the reusable heart:
nondeg quadric in ODD dim `m` ⟹ `|{Q=0}|·q = |V|` exactly, via the `∑χ(t)=0` bracket vanishing).

**FINISH PLAN (remaining bricks):**
- (i) **`sec_aniso`** — for anisotropic `u`, the section `|{x | Q x = 0 ∧ polar Q u x = 0}| · q = |u^⊥|` (`= q^{d-2}·q`).
  Clean reduction: `u` anisotropic ⟹ `V = ⟨u⟩ ⊕ u^⊥` orthogonally and `polar Q u x = 2λ·Q u` (`x = λu + w`), so the
  section is EXACTLY `{w ∈ u^⊥ | Q w = 0}` = a `card_zeros_odd` on `(u^⊥, Q|_{u^⊥})`. Needs: `Q|_{u^⊥}` nondeg (Mathlib
  `nondegenerate_restrict_of_disjoint_orthogonal` + `orthogonal_orthogonal`, with `Disjoint u^⊥ ⟨u⟩` from `Q u ≠ 0`);
  `finrank u^⊥ = d−1` odd (`finrank_orthogonal`); `polarBilin (Q.comp u^⊥.subtype) = (polarBilin Q).restrict u^⊥`.
- (ii) **`cone_not_covered` (k=2, both aniso `u₁,u₂`)** — `cone_card_lower` (`|cone|·q ≥ q^d − (q−1)√(q^d)`) + 2×`sec_aniso`
  (`|cone ∩ uᵢ^⊥|·q = |u^⊥| = q^{d-1}`, i.e. section `= q^{d-2}`) + union `|cone| > 2q^{d-2}` (holds `q ≥ 3`).
- (iii) **walk/hub** (structural, no counting), redesigned for aniso-only coverings, → `hub` → `hconn`.
- (iv) **final discharge** — construct primitive `ψ` via `AddChar.FiniteField.primitiveChar_to_Complex`, `hF` from `p`
  odd; instantiate `nullstellensatz_of_connectivity` ⟹ `NondegQuadricDeterminesForm`; delete the carried premise.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`/`axiom`, `native_decide` banned. WIP.
-/
import ChainDescent.PairForm
import ChainDescent.Coordinatization
import ChainDescent.ScratchNullstellensatz
import ChainDescent.ScratchNullstellensatzStructural

namespace ChainDescent.Nullstellensatz

open QuadraticMap

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false in
/-- **The radical of a nondegenerate `Q` is trivial** (the `zeroCount_sq_le` "radical filter" has card 1). -/
theorem radical_card_one (Q : QuadraticForm K V) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    (Finset.univ.filter (fun h : V => ∀ x, QuadraticMap.polar Q x h = 0)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hh
    refine hQnd.1 h (fun x => ?_)
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact hh x
  · rintro rfl x
    simp [QuadraticMap.polar]

/-- **The isotropic cone is large.** For a nondegenerate `Q` over `ℂ`-valued primitive `ψ`,
`qᵈ − (q−1)·√(qᵈ) ≤ |cone|·q`, i.e. `|cone| ≥ q^{d−1} − (q−1)q^{d/2−1}` (the classical count with the Gauss
error term). Direct from `zeroCount_sq_le` (radical trivial) + `√` monotonicity. `N := |V| = qᵈ`. -/
theorem cone_card_lower {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    (Fintype.card V : ℝ) - ((Fintype.card K : ℝ) - 1) * Real.sqrt (Fintype.card V)
      ≤ ((Finset.univ.filter (fun x : V => Q x = 0)).card : ℝ) * (Fintype.card K) := by
  have hsq := zeroCount_sq_le hψ Q
  rw [radical_card_one Q hQnd, Nat.cast_one, mul_one] at hsq
  set z : ℝ := ((Finset.univ.filter (fun x : V => Q x = 0)).card : ℝ) with hz
  set q : ℝ := (Fintype.card K : ℝ) with hq
  set N : ℝ := (Fintype.card V : ℝ) with hN
  -- hsq : (z*q - N)^2 ≤ (q-1)^2 * N
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hq1 : (0 : ℝ) ≤ q - 1 := by
    have : (1 : ℝ) ≤ q := by rw [hq]; exact_mod_cast Fintype.card_pos
    linarith
  -- |z*q - N| ≤ (q-1)*√N
  have habs : |z * q - N| ≤ (q - 1) * Real.sqrt N := by
    have hrhs : ((q - 1) * Real.sqrt N) ^ 2 = (q - 1) ^ 2 * N := by
      rw [mul_pow, Real.sq_sqrt hNnonneg]
    have hle2 : (z * q - N) ^ 2 ≤ ((q - 1) * Real.sqrt N) ^ 2 := by rw [hrhs]; exact hsq
    have hle := Real.sqrt_le_sqrt hle2
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by positivity)] at hle
  have := (abs_le.mp habs).1
  linarith
/-- **A nondegenerate quadric in ODD dimension has exactly `q^{m-1}` zeros** — stated as the clean Nat identity
`|{Q=0}|·|K| = |V|`. The error term in `card_quadForm_eq` vanishes because for odd `finrank` the bracket
`∑_{t≠0} χ(t)^{finrank} = ∑_{t≠0} χ(t) = 0` (`quadraticChar_sum_zero`). The reusable heart of the section bound. -/
theorem card_zeros_odd {ψ : AddChar K ℂ} (hF : ringChar K ≠ 2) (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hodd : Odd (Module.finrank K V)) :
    (Finset.univ.filter (fun x : V => Q x = 0)).card * Fintype.card K = Fintype.card V := by
  classical
  have hsep : (QuadraticMap.associated (R := K) Q).SeparatingLeft :=
    separatingLeft_associated_of_polarBilin_nondeg Q hQnd
  obtain ⟨vb, hv, hw⟩ := exists_orthoAnisotropic_basis Q hsep
  have hcard := card_quadForm_eq hF hψ Q vb hv hw 0
  set χ := (quadraticChar K).ringHomComp (Int.castRingHom ℂ) with hχ
  -- χ t = ((quadraticChar K t : ℤ) : ℂ)
  have hχval : ∀ t : K, χ t = ((quadraticChar K t : ℤ) : ℂ) := fun t => rfl
  -- the bracket vanishes (odd power ⟹ χ^m = χ ⟹ ∑_{t≠0} χ = 0)
  have hbracket : (∑ t ∈ Finset.univ.erase (0 : K), ψ (-(t * 0)) * χ t ^ Module.finrank K V) = 0 := by
    have hterm : ∀ t ∈ Finset.univ.erase (0 : K),
        ψ (-(t * 0)) * χ t ^ Module.finrank K V = χ t := by
      intro t ht
      have ht0 : t ≠ 0 := Finset.ne_of_mem_erase ht
      rw [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
      have hsq : χ t ^ 2 = 1 := by
        rw [hχval, ← Int.cast_pow, quadraticChar_sq_one ht0, Int.cast_one]
      obtain ⟨k, hk⟩ := hodd
      rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
    rw [Finset.sum_congr rfl hterm]
    -- ∑_{t≠0} χ t = ∑_all χ t - χ 0 = 0 - 0
    have h0 : χ (0 : K) = 0 := by rw [hχval, quadraticChar_zero, Int.cast_zero]
    have hall : (∑ t : K, χ t) = 0 := by
      simp only [hχval]
      rw [← Int.cast_sum, quadraticChar_sum_zero hF, Int.cast_zero]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : K)), hall, h0, sub_zero]
  rw [hbracket, zero_mul, add_zero] at hcard
  -- cast back to ℕ
  have : ((Finset.univ.filter (fun x : V => Q x = 0)).card * Fintype.card K : ℕ) = (Fintype.card V : ℕ) := by
    have := hcard
    push_cast at this ⊢
    exact_mod_cast this
  exact this
