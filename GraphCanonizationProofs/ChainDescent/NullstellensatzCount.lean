/-
# Nullstellensatz discharge — the cone-covering count (LANDED)

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

**★ COUNTING CORE COMPLETE (2026-07-06, all axiom-clean).**
- ✅ (i) **`sec_aniso`** — for anisotropic `u`, `|{x | Q x = 0 ∧ polar Q u x = 0}| · q · q = |V|` (section `= q^{d-2}`).
  Reduction: `u` anisotropic ⟹ `V = ⟨u⟩ ⊕ u^⊥` and `polar Q u x = 0 ⟺ x ∈ u^⊥`, so the section is EXACTLY
  `{w ∈ u^⊥ | Q w = 0}` = a `card_zeros_odd` on `(u^⊥, Q|_{u^⊥})`. `Q|_{u^⊥}` nondeg proved DIRECTLY (via `V = ⟨u⟩ + u^⊥`);
  `finrank u^⊥ = d−1` odd via `Module.Dual.finrank_ker_add_one_of_ne_zero`; card via `Module.card_eq_pow_finrank`.
- ✅ (ii) **`cone_not_covered` (k=2, both aniso `u₁,u₂`)** — `cone_card_lower` + 2×`sec_aniso` + union `|cone| > 2q^{d-2}`
  (nlinarith over ℝ; needs `finrank ≥ 4`, `q ≥ 3`, even finrank). ∃ isotropic `a` non-tangent to both `u₁,u₂`.

**✅ DISCHARGE COMPLETE (2026-07-06, all axiom-clean, in `build.sh`).** The scope correction (the honest 2-step /
`hconn` walk needs a `k=4` cover that PROVABLY FAILS at `q=3, d=4` elliptic VO⁻₄(3), which the citation's scope
`p ≠ 2` — INCLUDES `p=3` — forces us to cover) was resolved by taking the **structural route** (`hspan+hlink`) with
the **exact** isotropic-`u` section count instead of the crude magnitude bound. The chain, all landed here + in
`NullstellensatzHlink`:
- (iii-a) **`section_iso_count`** — exact `section·q² + (q−1)|V| = |cone|·q²` (equivalently the type-independent gap
  `(q−2)q² > 0` at `q ≥ 3`), via a two-constraint character sum — the crux that clears the `q=3` boundary.
- (iii-b) **`cone_not_covered_gen`** — `y` aniso + `u` ANY nonzero ⟹ isotropic `a` off `y^⊥ ∪ u^⊥`.
- (iii-c) **`cone_punctured_span`** (hspan) — the punctured cone spans (polar-orthogonal complement `= ⊥`).
- (iii-d) **`aniso_polar_diameter_two`** (hlink, in `NullstellensatzHlink`) — anisotropic polar-diameter ≤ 2, a
  `q=3`-tight union-bound count using `cone_card_upper` + the exact section saving.
- (iv) **discharge** — `nondegQuadric_{determines_of,zmod}_of_even` (in `NullstellensatzHlink`) instantiate
  `nullstellensatz_of_structural` (even `d`); `RouteC.nondegQuadricDeterminesForm_of_even` proves the exact
  `NondegQuadricDeterminesForm` predicate, and `recoveredForm_colouring_equivariant` no longer carries the citation
  (its `hcite` premise deleted; `#print axioms` = `[propext, Classical.choice, Quot.sound]`).

Scope note: the structural section count (`sec_aniso`, `u^⊥` odd-dim) covers **even `finrank`** — which is exactly
every Route-C instantiation (`VO^ε_{2m}`, `m ≥ 2`); odd `d` (not used) is left open. The old
`nullstellensatz_of_connectivity`/hub route is a valid but strictly harder alternative (its walk needs the `k=4`
cover that fails `q=3`) — kept as a proven spare.

Quality bar (met): axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`/`axiom`, `native_decide` banned.
-/
import ChainDescent.PairForm
import ChainDescent.Coordinatization
import ChainDescent.Nullstellensatz
import ChainDescent.NullstellensatzStructural
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

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

open Module in
/-- **The exact anisotropic hyperplane section.** For a nondegenerate `Q` on `V` with even `finrank` and an
anisotropic `u`, the section `{x | Q x = 0 ∧ polar Q u x = 0}` satisfies `section·q·q = |V|` (i.e. `= q^{d-2}`).
Because `u` is anisotropic, `polar Q u x = 0 ⟺ x ∈ u^⊥` and `V = ⟨u⟩ ⊕ u^⊥`, so the section is exactly the
isotropic cone of `Q|_{u^⊥}`, which is ODD-dimensional — `card_zeros_odd` gives the exact count. -/
theorem sec_aniso {ψ : AddChar K ℂ} (hF : ringChar K ≠ 2) (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (heven : Even (Module.finrank K V)) {u : V} (hu : Q u ≠ 0) :
    (Finset.univ.filter (fun x : V => Q x = 0 ∧ QuadraticMap.polar Q u x = 0)).card
        * Fintype.card K * Fintype.card K = Fintype.card V := by
  classical
  have h2ne : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  set f : V →ₗ[K] K := (QuadraticMap.polarBilin Q) u with hf
  have hfx : ∀ x, f x = QuadraticMap.polar Q u x := fun x => by
    rw [hf, QuadraticMap.polarBilin_apply_apply]
  have hfune : f u ≠ 0 := by
    rw [hfx, QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat]
    exact mul_ne_zero h2ne hu
  have hfne : f ≠ 0 := fun h => hfune (by rw [h]; rfl)
  set H : Submodule K V := LinearMap.ker f with hH
  have hmemH : ∀ x, x ∈ H ↔ QuadraticMap.polar Q u x = 0 := fun x => by
    rw [hH, LinearMap.mem_ker, hfx]
  -- projection: x − (f x / f u)•u ∈ H
  have hproj : ∀ x : V, x - (f x * (f u)⁻¹) • u ∈ H := by
    intro x
    rw [hH, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, mul_assoc,
      inv_mul_cancel₀ hfune, mul_one, sub_self]
  set Q' : QuadraticForm K H := Q.comp H.subtype with hQ'
  have hpol' : ∀ w w' : H, QuadraticMap.polar Q' w w' = QuadraticMap.polar Q (w : V) (w' : V) := by
    intro w w'
    simp only [hQ', QuadraticMap.polar, QuadraticMap.comp_apply, Submodule.coe_subtype,
      Submodule.coe_add]
  -- Q' is nondegenerate: a vector polar-orthogonal to all of H is orthogonal to all of V (using V = ⟨u⟩+H)
  have hgen : ∀ w : V, w ∈ H → (∀ w' : V, w' ∈ H → QuadraticMap.polar Q w w' = 0) → w = 0 := by
    intro w hw hwall
    refine hQnd.1 w (fun y => ?_)
    rw [QuadraticMap.polarBilin_apply_apply]
    have hwu : QuadraticMap.polar Q w u = 0 := by
      rw [QuadraticMap.polar_comm]; exact (hmemH w).mp hw
    have hyH : y - (f y * (f u)⁻¹) • u ∈ H := hproj y
    have hyw := hwall _ hyH
    have hexp : QuadraticMap.polar Q w y
        = QuadraticMap.polar Q w (y - (f y * (f u)⁻¹) • u)
          + (f y * (f u)⁻¹) * QuadraticMap.polar Q w u := by
      rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, smul_eq_mul]; ring
    rw [hexp, hyw, hwu, mul_zero, add_zero]
  have hQ'nd : (QuadraticMap.polarBilin Q').Nondegenerate := by
    refine ⟨fun w hwall => Subtype.ext (hgen w.val w.property (fun w'' hw'' => ?_)),
      fun w hwall => Subtype.ext (hgen w.val w.property (fun w'' hw'' => ?_))⟩
    · have := hwall ⟨w'', hw''⟩
      rwa [QuadraticMap.polarBilin_apply_apply, hpol'] at this
    · have := hwall ⟨w'', hw''⟩
      rw [QuadraticMap.polarBilin_apply_apply, hpol'] at this
      rwa [QuadraticMap.polar_comm]
  -- finrank H = d − 1, odd
  have hrankH : Module.finrank K H + 1 = Module.finrank K V :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hfne
  have hoddH : Odd (Module.finrank K H) := by
    rcases heven with ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  -- the exact odd-dim count on H
  have hcz := card_zeros_odd hF hψ Q' hQ'nd hoddH
  -- section over V ≃ zeros of Q' over H
  have hcardeq : (Finset.univ.filter (fun x : V => Q x = 0 ∧ QuadraticMap.polar Q u x = 0)).card
      = (Finset.univ.filter (fun w : H => Q' w = 0)).card := by
    refine Finset.card_bij' (fun x hx => (⟨x, (hmemH x).mpr (by
        simp only [Finset.mem_filter] at hx; exact hx.2.2)⟩ : H))
      (fun w _ => (w : V)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [hQ', QuadraticMap.comp_apply, Submodule.coe_subtype]; exact hx.1
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      refine ⟨?_, (hmemH w.val).mp w.property⟩
      rw [hQ', QuadraticMap.comp_apply, Submodule.coe_subtype] at hw; exact hw
    · intro x hx; rfl
    · intro w hw; rfl
  -- assemble: section·q = |H|, |H|·q = |V|
  have hcardV : Fintype.card V = Fintype.card K ^ Module.finrank K V := Module.card_eq_pow_finrank
  have hcardH : Fintype.card H = Fintype.card K ^ Module.finrank K H := Module.card_eq_pow_finrank
  rw [hcardeq, hcz, hcardH, hcardV, ← hrankH, pow_succ]

open Module in
/-- **The isotropic cone is not covered by two anisotropic hyperplanes.** For nondeg `Q` on `V` (finrank even,
`≥ 4`, `q ≥ 3`) and anisotropic `u₁, u₂`, there is an isotropic `a` non-tangent to both:
`Q a = 0 ∧ polar Q u₁ a ≠ 0 ∧ polar Q u₂ a ≠ 0`. Union bound: each section has exactly `q^{d-2}` points
(`sec_aniso`), the cone has `≥ q^{d-1} − …` (`cone_card_lower`), and `q^{d-1} > 2q^{d-2}` for `q ≥ 3` — with NO
small-`q` tail because the sections are exact (both hyperplane-vectors anisotropic). -/
theorem cone_not_covered {ψ : AddChar K ℂ} (hF : ringChar K ≠ 2) (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (heven : Even (Module.finrank K V)) (hdim : 4 ≤ Module.finrank K V)
    (hq : 3 ≤ Fintype.card K) {u₁ u₂ : V} (hu₁ : Q u₁ ≠ 0) (hu₂ : Q u₂ ≠ 0) :
    ∃ a : V, Q a = 0 ∧ QuadraticMap.polar Q u₁ a ≠ 0 ∧ QuadraticMap.polar Q u₂ a ≠ 0 := by
  classical
  set cone := Finset.univ.filter (fun a : V => Q a = 0) with hcone
  set sec₁ := Finset.univ.filter (fun a : V => Q a = 0 ∧ QuadraticMap.polar Q u₁ a = 0) with hsec1
  set sec₂ := Finset.univ.filter (fun a : V => Q a = 0 ∧ QuadraticMap.polar Q u₂ a = 0) with hsec2
  set good := Finset.univ.filter
    (fun a : V => Q a = 0 ∧ QuadraticMap.polar Q u₁ a ≠ 0 ∧ QuadraticMap.polar Q u₂ a ≠ 0) with hgood
  -- section counts (exact) and cone lower bound
  have hs1 : sec₁.card * Fintype.card K * Fintype.card K = Fintype.card V :=
    sec_aniso hF hψ Q hQnd heven hu₁
  have hs2 : sec₂.card * Fintype.card K * Fintype.card K = Fintype.card V :=
    sec_aniso hF hψ Q hQnd heven hu₂
  have hcl := cone_card_lower hψ Q hQnd
  -- reals
  set c : ℝ := (cone.card : ℝ) with hcdef
  set s₁ : ℝ := (sec₁.card : ℝ) with hs1def
  set s₂ : ℝ := (sec₂.card : ℝ) with hs2def
  set N : ℝ := (Fintype.card V : ℝ) with hNdef
  set q : ℝ := (Fintype.card K : ℝ) with hqdef
  have hq3 : (3 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; exact_mod_cast Fintype.card_pos
  have hN4 : q ^ 4 ≤ N := by
    have hnat : Fintype.card K ^ 4 ≤ Fintype.card K ^ Module.finrank K V :=
      Nat.pow_le_pow_right (le_trans (by norm_num) hq) hdim
    rw [hqdef, hNdef, Module.card_eq_pow_finrank (K := K) (V := V)]
    calc (Fintype.card K : ℝ) ^ 4 = ((Fintype.card K ^ 4 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((Fintype.card K ^ Module.finrank K V : ℕ) : ℝ) := by exact_mod_cast hnat
  set r : ℝ := Real.sqrt N with hrdef
  have hrsq : r ^ 2 = N := Real.sq_sqrt hNpos.le
  have hrpos : (0 : ℝ) < r := Real.sqrt_pos.mpr hNpos
  have hrq : q ^ 2 ≤ r := by
    rw [hrdef, show (q ^ 2 : ℝ) = Real.sqrt (q ^ 4) from by
      rw [show (q:ℝ)^4 = (q^2)^2 by ring, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hN4
  have hs1r : s₁ * q * q = N := by rw [hs1def, hqdef, hNdef]; exact_mod_cast hs1
  have hs2r : s₂ * q * q = N := by rw [hs2def, hqdef, hNdef]; exact_mod_cast hs2
  -- `hcl` is now `N - (q-1)*r ≤ c*q` after the `set`s
  have hclr : N - (q - 1) * r ≤ c * q := hcl
  -- key: s₁ + s₂ < c
  have hrbig : q * (q - 1) < r * (q - 2) := by nlinarith [hrq, hq3, sq_nonneg (q - 1)]
  have hcqq : 2 * N < c * (q * q) := by
    nlinarith [mul_le_mul_of_nonneg_right hclr hqpos.le, hrsq, hrpos, hrbig, mul_pos hrpos hrpos]
  have hlt : s₁ + s₂ < c := by nlinarith [hs1r, hs2r, hcqq, mul_pos hqpos hqpos]
  -- cone ⊆ good ∪ sec₁ ∪ sec₂
  have hsub : cone ⊆ good ∪ sec₁ ∪ sec₂ := by
    intro a ha
    simp only [hcone, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_union, hgood, hsec1, hsec2, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h1 : QuadraticMap.polar Q u₁ a = 0
    · left; right; exact ⟨ha, h1⟩
    · by_cases h2 : QuadraticMap.polar Q u₂ a = 0
      · right; exact ⟨ha, h2⟩
      · left; left; exact ⟨ha, h1, h2⟩
  have hcard : cone.card ≤ good.card + sec₁.card + sec₂.card := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (good ∪ sec₁) sec₂
    have h3 := Finset.card_union_le good sec₁
    omega
  -- so good is nonempty
  have hgoodpos : 0 < good.card := by
    have hcast : sec₁.card + sec₂.card < cone.card := by
      have h := hlt; rw [hs1def, hs2def, hcdef] at h; exact_mod_cast h
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hgoodpos
  simp only [hgood, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  exact ⟨a, ha.1, ha.2.1, ha.2.2⟩

/-- **The exact ISOTROPIC-`u` hyperplane section (the crux).** For nondegenerate `Q` and a NONZERO ISOTROPIC `u`
(`Q u = 0`, `u ≠ 0`), the tangent section `{x | Q x = 0 ∧ polar Q u x = 0}` and the full cone are related by the
**type-independent** identity (no discriminant / Witt index):
`section·q² + (q−1)·|V| = cone·q²` (equivalently `section = |cone| − (q−1)q^{d−2}`).
Proof by the two-constraint character-sum count (`count2_eq_charsum`): the `q²·section` sum splits over the dual
variable `r` for `Q`. The `r = 0` slice is `q·|ker(polar Q u)| = |V|` (a nonzero-functional hyperplane); every `r ≠ 0`
slice is **independent of** the second dual variable `s` because `Q u = 0` kills the linear shift
(`sum_addChar_quadForm_linear` with `a' = s•u`, `Q(s•u) = s²·Q u = 0`), collapsing to `q·∑ₓ ψ(r·Q x)`, whose `r`-sum is
`q·|cone| − |V|`. The type-dependent Gauss terms never appear. -/
theorem section_iso_count {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    {u : V} (hu : Q u = 0) (hu0 : u ≠ 0) :
    (Finset.univ.filter (fun x : V => Q x = 0 ∧ QuadraticMap.polar Q u x = 0)).card
        * (Fintype.card K * Fintype.card K)
      + (Fintype.card K - 1) * Fintype.card V
      = (Finset.univ.filter (fun x : V => Q x = 0)).card
          * (Fintype.card K * Fintype.card K) := by
  classical
  have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
  -- `polar Q u` is a nonzero linear functional (nondegeneracy).
  have hfne : Q.polarBilin u ≠ 0 := by
    have hex : ∃ w, QuadraticMap.polar Q u w ≠ 0 := by
      by_contra h; push_neg at h
      exact hu0 (hQnd.1 u (fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact h y))
    obtain ⟨w, hw⟩ := hex
    intro hz; apply hw
    rw [← QuadraticMap.polarBilin_apply_apply, hz, LinearMap.zero_apply]
  -- (A) the two-constraint count: `∑ₓ (∑ᵣ ψ(r·Qx))·(∑ₛ ψ(s·polar u x)) = Scard·q²`.
  have hcount := count2_eq_charsum hψ (fun x : V => Q x)
    (fun x : V => QuadraticMap.polar Q u x) 0 0
  simp only [sub_zero] at hcount
  -- (B) expand the product of sums and reorder to `∑ᵣ ∑ₛ ∑ₓ ψ(r·Qx + s·polar u x)`.
  have hexpand : (∑ x : V, (∑ r : K, ψ (r * Q x)) *
        (∑ s : K, ψ (s * QuadraticMap.polar Q u x)))
      = ∑ r : K, ∑ s : K, ∑ x : V, ψ (r * Q x + s * QuadraticMap.polar Q u x) := by
    simp_rw [Finset.sum_mul_sum, ← AddChar.map_add_eq_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun r _ => Finset.sum_comm)
  -- ker-cardinality helper: `q · |ker(polar Q u)| = |V|` (nonzero-functional hyperplane).
  have hkc : (Finset.univ.filter (fun x : V => QuadraticMap.polar Q u x = 0)).card
      = Fintype.card (LinearMap.ker (Q.polarBilin u)) := by
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.mem_ker,
      QuadraticMap.polarBilin_apply_apply]
  have hkerV : (Fintype.card K : ℂ)
      * ((Finset.univ.filter (fun x : V => QuadraticMap.polar Q u x = 0)).card : ℂ)
      = (Fintype.card V : ℂ) := by
    rw [hkc]
    have hrank : Module.finrank K (LinearMap.ker (Q.polarBilin u)) + 1 = Module.finrank K V :=
      Module.Dual.finrank_ker_add_one_of_ne_zero hfne
    have hkerpow : (Fintype.card (LinearMap.ker (Q.polarBilin u)) : ℂ)
        = (Fintype.card K : ℂ) ^ Module.finrank K (LinearMap.ker (Q.polarBilin u)) := by
      rw [Module.card_eq_pow_finrank (K := K)]; push_cast; ring
    have hVpow : (Fintype.card V : ℂ) = (Fintype.card K : ℂ) ^ Module.finrank K V := by
      rw [Module.card_eq_pow_finrank (K := K)]; push_cast; ring
    rw [hkerpow, hVpow, ← hrank, pow_succ]; ring
  -- (C) the `r = 0` slice equals `|V|`.
  have hr0 : (∑ s : K, ∑ x : V, ψ ((0 : K) * Q x + s * QuadraticMap.polar Q u x))
      = (Fintype.card V : ℂ) := by
    rw [Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun x _ => by rw [zero_mul, zero_add])),
      Finset.sum_comm]
    have h2 : ∀ x : V, (∑ s : K, ψ (s * QuadraticMap.polar Q u x))
        = ((if QuadraticMap.polar Q u x = 0 then Fintype.card K else 0 : ℕ) : ℂ) :=
      fun x => AddChar.sum_mulShift (QuadraticMap.polar Q u x) hψ
    rw [Finset.sum_congr rfl (fun x _ => h2 x)]
    simp only [Nat.cast_ite, Nat.cast_zero]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    exact hkerV
  -- (D) each `r ≠ 0` slice is independent of `s` (`Q u = 0`), giving `q·∑ₓ ψ(r·Qx)`.
  have hrne : ∀ r : K, r ≠ 0 →
      (∑ s : K, ∑ x : V, ψ (r * Q x + s * QuadraticMap.polar Q u x))
        = (Fintype.card K : ℂ) * ∑ x : V, ψ (r * Q x) := by
    intro r hr
    have hslice : ∀ s : K, (∑ x : V, ψ (r * Q x + s * QuadraticMap.polar Q u x))
        = ∑ x : V, ψ (r * Q x) := by
      intro s
      have hsu : Q (s • u) = 0 := by rw [QuadraticMap.map_smul, hu, smul_zero]
      rw [Finset.sum_congr rfl (fun x _ => by
        rw [show r * Q x + s * QuadraticMap.polar Q u x
              = r * Q x + QuadraticMap.polar Q x (s • u) by
          rw [QuadraticMap.polar_smul_right, smul_eq_mul, QuadraticMap.polar_comm]])]
      have hlin := sum_addChar_quadForm_linear ψ Q (Units.mk0 r hr) (s • u)
      rw [Units.val_mk0] at hlin
      rw [hlin, hsu, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
    rw [Finset.sum_congr rfl (fun s _ => hslice s), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  -- (E) the `r ≠ 0` block sums to `q·(q·|cone| − |V|)`.
  have hconesum : (∑ r ∈ Finset.univ.erase (0 : K), ∑ x : V, ψ (r * Q x))
      = (Fintype.card K : ℂ) * ((Finset.univ.filter (fun x : V => Q x = 0)).card : ℂ)
        - (Fintype.card V : ℂ) := by
    have hfull : (∑ r : K, ∑ x : V, ψ (r * Q x))
        = (Fintype.card K : ℂ) * ((Finset.univ.filter (fun x : V => Q x = 0)).card : ℂ) := by
      rw [Finset.sum_comm]
      have hin : ∀ x : V, (∑ r : K, ψ (r * Q x)) = ((if Q x = 0 then Fintype.card K else 0 : ℕ) : ℂ) :=
        fun x => AddChar.sum_mulShift (Q x) hψ
      rw [Finset.sum_congr rfl (fun x _ => hin x)]
      simp only [Nat.cast_ite, Nat.cast_zero]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hzero : (∑ x : V, ψ ((0 : K) * Q x)) = (Fintype.card V : ℂ) := by
      simp [AddChar.map_zero_eq_one, Finset.card_univ]
    have hsplit : (∑ x : V, ψ ((0 : K) * Q x))
          + (∑ r ∈ Finset.univ.erase (0 : K), ∑ x : V, ψ (r * Q x))
        = ∑ r : K, ∑ x : V, ψ (r * Q x) :=
      Finset.add_sum_erase Finset.univ (fun r : K => ∑ x : V, ψ (r * Q x)) (Finset.mem_univ (0 : K))
    rw [hzero, hfull] at hsplit
    linear_combination hsplit
  -- (F) assemble: `Scard·q² = |V| + q·(q·|cone| − |V|) = q²·|cone| − (q−1)·|V|`.
  have hL := hcount
  rw [hexpand] at hL
  have hsplitr : (∑ r : K, ∑ s : K, ∑ x : V, ψ (r * Q x + s * QuadraticMap.polar Q u x))
        = (∑ s : K, ∑ x : V, ψ ((0 : K) * Q x + s * QuadraticMap.polar Q u x))
          + ∑ r ∈ Finset.univ.erase (0 : K),
              (∑ s : K, ∑ x : V, ψ (r * Q x + s * QuadraticMap.polar Q u x)) :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : K))).symm
  rw [hsplitr, hr0, Finset.sum_congr rfl (fun r hr => hrne r (Finset.ne_of_mem_erase hr)),
    ← Finset.mul_sum, hconesum] at hL
  -- hL : |V| + q·(q·|cone| − |V|) = Scard·(q*q)
  -- (G) cast the ℂ identity back to ℕ.
  have hcast : ((((Finset.univ.filter (fun x : V => Q x = 0 ∧ QuadraticMap.polar Q u x = 0)).card
        * (Fintype.card K * Fintype.card K) + (Fintype.card K - 1) * Fintype.card V) : ℕ) : ℂ)
      = ((((Finset.univ.filter (fun x : V => Q x = 0)).card
        * (Fintype.card K * Fintype.card K)) : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub hq1]
    linear_combination -hL
  exact_mod_cast hcast

open Module in
/-- **The isotropic cone is not covered by `y^⊥ ∪ u^⊥` for an anisotropic `y` and ANY nonzero `u`.**
Generalizes `cone_not_covered` (which needs both hyperplane-vectors anisotropic) to an ARBITRARY second vector
`u ≠ 0` — the form `hspan` needs. For anisotropic `u` it is `cone_not_covered`; for isotropic `u` the union bound
uses the **exact** section identity `section_iso_count` (the crude Gauss bound fails at `q = 3`): the two sections
have total card `≤ |cone| − (q−2)·|V| < |cone|`, so a non-tangent isotropic vector survives. Uniform at `q ≥ 3`,
both types. -/
theorem cone_not_covered_gen {ψ : AddChar K ℂ} (hF : ringChar K ≠ 2) (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (heven : Even (Module.finrank K V)) (hdim : 4 ≤ Module.finrank K V)
    (hq : 3 ≤ Fintype.card K) {y u : V} (hy : Q y ≠ 0) (hu0 : u ≠ 0) :
    ∃ a : V, Q a = 0 ∧ QuadraticMap.polar Q y a ≠ 0 ∧ QuadraticMap.polar Q u a ≠ 0 := by
  classical
  by_cases hu : Q u = 0
  · -- isotropic `u`: union bound via the exact section identity
    set cone := Finset.univ.filter (fun a : V => Q a = 0) with hcone
    set secy := Finset.univ.filter (fun a : V => Q a = 0 ∧ QuadraticMap.polar Q y a = 0) with hsecy
    set secu := Finset.univ.filter (fun a : V => Q a = 0 ∧ QuadraticMap.polar Q u a = 0) with hsecu
    set good := Finset.univ.filter
      (fun a : V => Q a = 0 ∧ QuadraticMap.polar Q y a ≠ 0 ∧ QuadraticMap.polar Q u a ≠ 0) with hgood
    have hNV : 0 < Fintype.card V := Fintype.card_pos
    have hsecyE : secy.card * Fintype.card K * Fintype.card K = Fintype.card V :=
      sec_aniso hF hψ Q hQnd heven hy
    have hsecuE : secu.card * (Fintype.card K * Fintype.card K)
        + (Fintype.card K - 1) * Fintype.card V
        = cone.card * (Fintype.card K * Fintype.card K) := section_iso_count hψ Q hQnd hu hu0
    -- `secy.card + secu.card < cone.card`
    have hlt : secy.card + secu.card < cone.card := by
      have hqqpos : 0 < Fintype.card K * Fintype.card K := by positivity
      have hstep : Fintype.card V < (Fintype.card K - 1) * Fintype.card V := by
        have h1 : 1 < Fintype.card K - 1 := by omega
        exact (lt_mul_iff_one_lt_left hNV).mpr h1
      have hAqq : secy.card * (Fintype.card K * Fintype.card K) = Fintype.card V := by
        rw [← mul_assoc]; exact hsecyE
      have hmul : (secy.card + secu.card) * (Fintype.card K * Fintype.card K)
          < cone.card * (Fintype.card K * Fintype.card K) := by
        calc (secy.card + secu.card) * (Fintype.card K * Fintype.card K)
            = Fintype.card V + secu.card * (Fintype.card K * Fintype.card K) := by
              rw [add_mul, hAqq]
          _ < (Fintype.card K - 1) * Fintype.card V
                + secu.card * (Fintype.card K * Fintype.card K) := by
              exact Nat.add_lt_add_right hstep _
          _ = secu.card * (Fintype.card K * Fintype.card K)
                + (Fintype.card K - 1) * Fintype.card V := by ring
          _ = cone.card * (Fintype.card K * Fintype.card K) := hsecuE
      exact lt_of_mul_lt_mul_right hmul (Nat.zero_le _)
    -- cover: `cone ⊆ good ∪ secy ∪ secu`
    have hsub : cone ⊆ good ∪ secy ∪ secu := by
      intro a ha
      simp only [hcone, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp only [Finset.mem_union, hgood, hsecy, hsecu, Finset.mem_filter, Finset.mem_univ,
        true_and]
      by_cases h1 : QuadraticMap.polar Q y a = 0
      · left; right; exact ⟨ha, h1⟩
      · by_cases h2 : QuadraticMap.polar Q u a = 0
        · right; exact ⟨ha, h2⟩
        · left; left; exact ⟨ha, h1, h2⟩
    have hcard : cone.card ≤ good.card + secy.card + secu.card := by
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (good ∪ secy) secu
      have h3 := Finset.card_union_le good secy
      omega
    have hgoodpos : 0 < good.card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hgoodpos
    simp only [hgood, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact ⟨a, ha.1, ha.2.1, ha.2.2⟩
  · -- anisotropic `u`: the landed two-anisotropic-vector case
    exact cone_not_covered hF hψ Q hQnd heven hdim hq hy hu

open Module in
/-- **`hspan`: the punctured isotropic cone spans.** For anisotropic `y`, the set of isotropic vectors NON-tangent
to `y` (`{x | Q x = 0 ∧ polar Q x y ≠ 0}`) spans `V`. Proof: its polar-orthogonal complement is `⊥` — any `u ≠ 0`
orthogonal to the whole punctured cone contradicts `cone_not_covered_gen` (which supplies an isotropic `a`
non-tangent to `y` AND to `u`) — so by nondegeneracy the span is everything. This is exactly the `hspan` hypothesis
of `nullstellensatz_of_structural`. -/
theorem cone_punctured_span {ψ : AddChar K ℂ} (hF : ringChar K ≠ 2) (hψ : ψ.IsPrimitive)
    (Q : QuadraticForm K V) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (heven : Even (Module.finrank K V)) (hdim : 4 ≤ Module.finrank K V)
    (hq : 3 ≤ Fintype.card K) {y : V} (hy : Q y ≠ 0) :
    Submodule.span K {x : V | Q x = 0 ∧ QuadraticMap.polar Q x y ≠ 0} = ⊤ := by
  classical
  set S : Set V := {x : V | Q x = 0 ∧ QuadraticMap.polar Q x y ≠ 0} with hSdef
  have hperp : LinearMap.BilinForm.orthogonal (Q.polarBilin) (Submodule.span K S) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_bot]
    by_contra hune
    obtain ⟨a, haQ, hay, hau⟩ := cone_not_covered_gen hF hψ Q hQnd heven hdim hq hy hune
    have haS : a ∈ S := ⟨haQ, by rw [QuadraticMap.polar_comm]; exact hay⟩
    have horth : LinearMap.BilinForm.IsOrtho (Q.polarBilin) a u :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hu) a (Submodule.subset_span haS)
    rw [LinearMap.BilinForm.isOrtho_def, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_comm] at horth
    exact hau horth
  have hfr := LinearMap.BilinForm.finrank_orthogonal hQnd (Submodule.span K S)
  rw [hperp, finrank_bot] at hfr
  have hle : Module.finrank K (Submodule.span K S) ≤ Module.finrank K V := Submodule.finrank_le _
  exact Submodule.eq_top_of_finrank_eq (le_antisymm hle (by omega))
