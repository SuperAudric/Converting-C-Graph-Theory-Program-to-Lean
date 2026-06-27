/-
# Increment 5 — the matching assembly (`c̄₀ < 1` ⟹ a separating base ⟹ `zSep` ⟹ seal).

The final wiring of the affine-polar `VO^ε` seal in the regime the landed increment-4 inputs support
(`q ≳ 32 d`, hence `q ≥ 256` for the lead `d`): the per-good-anchor fail bound `c = 15/16·|V|`
(`good_anchor_fail_le_const`) plus the bad-anchor density `β = O(d/q)` (`beta_full_count_closed`) give
`c̄₀ = c/|V| + β/|V| < 1`; the matching trick (`exists_separating_base`) then turns that into a base whose
2-element sub-frames separate every pair in the joint isotropic counts (`zSep`), discharging
`ZProfileSeparatesK` → `IsotropySeparatesAtBaseK` → the seal.

This file starts with the scope-independent **ℕ-smallness helper** feeding `exists_separating_base`'s `hlt`.

NOTE (scope): the matching has an INDEPENDENT `q`-floor from the isotropic-shell counts `#{I_u=0}+#{I_v=0}`,
which `good_anchor_fail_le` folds into `c` and `good_anchor_fail_le_const` controls only via the loose
`zeroCountShift_card_le` (`q ≥ 256`). The small-`q` per-anchor tail (`c0_le_route2`) tightens `NS` but does
NOT remove the shell overhead, so it does not lower this matching's floor; that is a separate follow-up.

Axiom-clean target `[propext, Classical.choice, Quot.sound]`; NOT in build.
-/
import ChainDescent.ScratchMatching
import ChainDescent.ScratchIncr4
import ChainDescent.ScratchIncr4d
import ChainDescent.ScratchBridgeAllK
import ChainDescent.ScratchBridgeK
import ChainDescent.ScratchFieldGenAdapter
import Mathlib.Tactic

namespace ChainDescent

open Finset

/-- **ℕ-smallness helper for the matching trick.** If the per-target fail count `F` is strictly below the
anchor-space size `|W|`, then for some base length `m` the matching inequality `|ι|·Fᵐ < |W|ᵐ` holds — exactly
`exists_separating_base`'s `hlt`. (Real proof: `F/|W| < 1` ⟹ `(|W|/F)ᵐ → ∞`, so `|ι| < (|W|/F)ᵐ` eventually.) -/
theorem exists_pow_matching_lt {ι W : Type*} [Fintype ι] [Fintype W] (F : ℕ)
    (hF : F < Fintype.card W) :
    ∃ m : ℕ, Fintype.card ι * F ^ m < Fintype.card W ^ m := by
  have hw : 0 < Fintype.card W := lt_of_le_of_lt (Nat.zero_le F) hF
  rcases Nat.eq_zero_or_pos F with hF0 | hFpos
  · refine ⟨1, ?_⟩
    subst hF0
    simpa using hw
  · have hFR : (0 : ℝ) < F := by exact_mod_cast hFpos
    have hr : (1 : ℝ) < (Fintype.card W : ℝ) / F :=
      (one_lt_div hFR).2 (by exact_mod_cast hF)
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (Fintype.card ι : ℝ) hr
    refine ⟨m, ?_⟩
    rw [div_pow, lt_div_iff₀ (pow_pos hFR m)] at hm
    exact_mod_cast hm

/-- **The matching mechanics, packaged.** Given a per-pair fail predicate `Fail g t t₀` over probe `t` and anchor
`t₀`, with a uniform per-good-anchor probe-fail bound `cN`, a uniform bad-anchor count bound `βN`, and the
`c̄₀ < 1` condition `cN + βN < |V|`, there is a base `P : Fin m → V × V` such that every target `g` has a
base-pair `P j = (t, t₀)` it does NOT fail. Pure matching-trick assembly: `matching_F_bound` →
`exists_pow_matching_lt` → `exists_separating_base` over `W = V × V`. -/
theorem exists_separating_base_of_split
    {ι : Type*} [Fintype ι] {V : Type*} [Fintype V] [DecidableEq V]
    (Fail : ι → V → V → Prop) [∀ g t₀, DecidablePred (fun t => Fail g t t₀)]
    (Good : ι → V → Prop) [∀ g, DecidablePred (Good g)] (cN βN : ℕ)
    (hc : ∀ g t₀, Good g t₀ → (Finset.univ.filter (fun t => Fail g t t₀)).card ≤ cN)
    (hβ : ∀ g, (Finset.univ.filter (fun t₀ => ¬ Good g t₀)).card ≤ βN)
    (hlt : cN + βN < Fintype.card V) :
    ∃ (m : ℕ) (P : Fin m → V × V), ∀ g : ι, ∃ j, ¬ Fail g (P j).1 (P j).2 := by
  classical
  have hvpos : 0 < Fintype.card V := lt_of_le_of_lt (Nat.zero_le _) hlt
  have hFlt : cN * Fintype.card V + Fintype.card V * βN < Fintype.card (V × V) := by
    rw [Fintype.card_prod]
    calc cN * Fintype.card V + Fintype.card V * βN
        = Fintype.card V * (cN + βN) := by ring
      _ < Fintype.card V * Fintype.card V := mul_lt_mul_of_pos_left hlt hvpos
  obtain ⟨m, hm⟩ := exists_pow_matching_lt (ι := ι) (W := V × V)
    (cN * Fintype.card V + Fintype.card V * βN) hFlt
  have hFbound := matching_F_bound (fun g a b => Fail g a b) (fun g b => Good g b) cN βN hc hβ
  obtain ⟨P, hP⟩ := exists_separating_base (fun (g : ι) (w : V × V) => Fail g w.1 w.2) m
    (cN * Fintype.card V + Fintype.card V * βN) (fun g => hFbound g) hm
  exact ⟨m, P, hP⟩

/-- **The `c̄₀ < 1` arithmetic.** From the good-anchor fail bound `16·cN ≤ 15·N` (i.e. `cN ≤ 15/16·N`) and the
bad-anchor density `q·βN ≤ (2d+4)·N + 2·q` (i.e. `βN ≤ (2d+4)·N/q + 2`), with `q ≥ 32·(2d+4)` and `N > 64`,
the matching threshold `cN + βN < N` holds. Proved over `ℝ` (multiply by `16q`) then cast back. -/
theorem cbar_lt {N q d cN βN : ℕ}
    (h16 : 16 * cN ≤ 15 * N) (hqβ : q * βN ≤ (2 * d + 4) * N + 2 * q)
    (hqthr : 32 * (2 * d + 4) ≤ q) (hNthr : 64 < N) (hqpos : 0 < q) :
    cN + βN < N := by
  have h16' : (16 : ℝ) * cN ≤ 15 * N := by exact_mod_cast h16
  have hqβ' : (q : ℝ) * βN ≤ (2 * d + 4) * N + 2 * q := by exact_mod_cast hqβ
  have hqthr' : (32 : ℝ) * (2 * d + 4) ≤ q := by exact_mod_cast hqthr
  have hNthr' : (64 : ℝ) < N := by exact_mod_cast hNthr
  have hqpos' : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hNpos' : (0 : ℝ) < N := by linarith
  have goalR : (cN : ℝ) + βN < N := by
    nlinarith [h16', hqβ', hqthr', hNthr', hqpos', hNpos',
      mul_le_mul_of_nonneg_left h16' hqpos'.le,
      mul_le_mul_of_nonneg_right hqthr' hNpos'.le,
      mul_lt_mul_of_pos_right hNthr' hqpos']
  exact_mod_cast goalR

open QuadraticMap in
/-- **Piece 3 — bridge wiring: the separation event fires the count inequality.** If at the sub-frame `{t, t₀}`
the two pair invariants have different (ℤ-valued) quadratic characters, both config invariants are nonzero, and
the anchor is `Q`-nondegenerate at both `u, v` (`Q(t₀-u), Q(t₀-v) ≠ 0`), then the joint isotropic counts differ.
Repackages `ScratchBridgeAllK.jointIsoCountK_ne_of_chiSep_pair`: `I≠0 ⟹` config Gram unit
(`configPolarDet_eq_pairFormK`+`isUnit_iff_ne_zero`); `Q(t₀-·)≠0 ⟹ hcorr`; ℤ-`χ`-inequality casts to `R'`. -/
theorem jointIsoCountK_ne_of_sep {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) (hcardK : 2 < Fintype.card K) (hd : Even d)
    {R' : Type*} [Field R'] [CharZero R'] {ψ : AddChar K R'} (hψ : ψ.IsPrimitive)
    (vb : Module.Basis (Fin (Module.finrank K (Fin d → K))) K (Fin d → K))
    (hv : (QuadraticMap.associated (R := K) Q).IsOrthoᵢ vb) (hw : ∀ i, Q (vb i) ≠ 0)
    (u v t t₀ : Fin d → K)
    (hIu : pairForm Q (t₀ - u) (t - u) ≠ 0) (hIv : pairForm Q (t₀ - v) (t - v) ≠ 0)
    (hQu : Q (t₀ - u) ≠ 0) (hQv : Q (t₀ - v) ≠ 0)
    (hchi : quadraticChar K (pairForm Q (t₀ - u) (t - u))
          ≠ quadraticChar K (pairForm Q (t₀ - v) (t - v))) :
    jointIsoCountK Q u {t, t₀} ≠ jointIsoCountK Q v {t, t₀} := by
  refine jointIsoCountK_ne_of_chiSep_pair Q hF hcardK u v t t₀ hd ?_ ?_ hψ vb hv hw ?_ ?_ ?_
  · rw [configPolarDet_eq_pairFormK Q u t t₀]; exact isUnit_iff_ne_zero.mpr hIu
  · rw [configPolarDet_eq_pairFormK Q v t t₀]; exact isUnit_iff_ne_zero.mpr hIv
  · exact fun h => hQu h.2
  · exact fun h => hQv h.2
  · intro heq
    rw [MulChar.ringHomComp_apply, MulChar.ringHomComp_apply, eq_intCast, eq_intCast] at heq
    exact hchi (by exact_mod_cast heq)

open QuadraticMap in
/-- **Piece 5 — the family assembly: a bounded base whose joint isotropic counts separate every pair.**
For a nondegenerate quadratic form `Q` on `Fin d → K` (even `d`), with the family thresholds `q ≳ 32d`, `q ≥ 256`,
the matching trick produces a finite base `T` with `ZProfileSeparatesK Q T`. Wires: `good_anchor_fail_le_const`
(input `c = 15/16·|V|`) + `beta_full_count_closed`/`exists_hgood` (bad-anchor `β = O(d/q)`) + `cbar_lt` (`c̄₀<1`)
→ `exists_separating_base_of_split` → `jointIsoCountK_ne_of_sep` per pair → `zProfileSeparatesK_of_zSep`. -/
theorem exists_zProfileSeparatesK {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) (hd : Even d) (hdge : 2 ≤ d)
    {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (hQrad : polarRad Q = ⊥)
    (hq1 : 64 * (Fintype.card K : ℝ) ^ 2 ≤ Fintype.card (Fin d → K))
    (hq2 : 64 * (d : ℝ) ^ 2 ≤ Fintype.card K) (hq3 : 256 ≤ (Fintype.card K : ℝ))
    (hqthr : 32 * (2 * d + 4) ≤ Fintype.card K)
    (hNthr : 64 < Fintype.card (Fin d → K)) :
    ∃ T : Finset (Fin d → K), ZProfileSeparatesK Q T := by
  classical
  set V := Fin d → K
  set cardV := Fintype.card V with hcardVdef
  set cardK := Fintype.card K with hcardKdef
  -- threshold consequences in ℕ
  have h256 : (256 : ℕ) ≤ cardK := by rw [hcardKdef]; exact_mod_cast hq3
  have hcardK7 : 7 ≤ cardK := by omega
  have hcardK2 : 2 < cardK := by omega
  have hKpos : 0 < cardK := by omega
  have hfinrank : 2 ≤ Module.finrank K V := by
    have : Module.finrank K V = d := by
      show Module.finrank K (Fin d → K) = d
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  have hsepL : (QuadraticMap.associated Q).SeparatingLeft := associated_separatingLeft_of_polarRad Q hQrad
  obtain ⟨vb, hv, hw⟩ := exists_orthoAnisotropic_basis Q hsepL
  -- Nontrivial V (for exists_anisotropic)
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial V := by
    show Nontrivial (Fin d → K); infer_instance
  obtain ⟨w₀, hw₀⟩ := exists_anisotropic Q hQrad
  let b : Module.Basis (Fin d) K V := Pi.basisFun K (Fin d)
  -- the matching predicates
  set Good : {p : V × V // p.1 ≠ p.2} → V → Prop := fun g t₀ =>
    (∀ y z : K, y ≠ 0 → z ≠ 0 → y • pairForm Q (t₀ - g.1.1) + z • pairForm Q (t₀ - g.1.2) ≠ 0)
      ∧ (∃ y z : K, polarRad (y • pairForm Q (t₀ - g.1.1) + z • pairForm Q (t₀ - g.1.2)) = ⊥)
      ∧ pairForm Q (t₀ - g.1.1) ≠ 0 ∧ pairForm Q (t₀ - g.1.2) ≠ 0
      ∧ Q (t₀ - g.1.1) ≠ 0 ∧ Q (t₀ - g.1.2) ≠ 0 with hGoodDef
  set Fail : {p : V × V // p.1 ≠ p.2} → V → V → Prop := fun g t t₀ =>
    ¬ (quadraticChar K (pairForm Q (t₀ - g.1.1) (t - g.1.1))
          ≠ quadraticChar K (pairForm Q (t₀ - g.1.2) (t - g.1.2))
        ∧ pairForm Q (t₀ - g.1.1) (t - g.1.1) ≠ 0 ∧ pairForm Q (t₀ - g.1.2) (t - g.1.2) ≠ 0
        ∧ Q (t₀ - g.1.1) ≠ 0 ∧ Q (t₀ - g.1.2) ≠ 0) with hFailDef
  set cN : ℕ := 15 * cardV / 16 with hcNdef
  set βN : ℕ := ((2 * d + 4) * cardV + 2 * cardK) / cardK with hβNdef
  -- hc : per-good-anchor fail bound
  have hc : ∀ g t₀, Good g t₀ → (Finset.univ.filter (fun t => Fail g t t₀)).card ≤ cN := by
    intro g t₀ hG
    obtain ⟨hnz, hgood, hPu, hPv, hQu0, hQv0⟩ := hG
    have hsetEq : (Finset.univ.filter (fun t => Fail g t t₀))
        = (Finset.univ.filter (fun t : V => ¬ (quadraticChar K (pairForm Q (t₀ - g.1.1) (t - g.1.1))
              ≠ quadraticChar K (pairForm Q (t₀ - g.1.2) (t - g.1.2))
            ∧ pairForm Q (t₀ - g.1.1) (t - g.1.1) ≠ 0 ∧ pairForm Q (t₀ - g.1.2) (t - g.1.2) ≠ 0))) := by
      apply Finset.filter_congr
      intro t _
      simp only [hFailDef, not_iff_not]
      constructor
      · rintro ⟨h1, h2, h3, _, _⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3, hQu0, hQv0⟩
    rw [hsetEq]
    have hreal := good_anchor_fail_le_const (b := b) hF hψ Q g.1.1 g.1.2 t₀ hnz hgood hPu hPv hq1 hq2 hq3
    -- (#fail : ℝ) ≤ 15/16·cardV ⟹ #fail ≤ (15·cardV)/16 (ℕ)
    have h16 : 16 * (Finset.univ.filter (fun t : V => ¬ (quadraticChar K (pairForm Q (t₀ - g.1.1) (t - g.1.1))
              ≠ quadraticChar K (pairForm Q (t₀ - g.1.2) (t - g.1.2))
            ∧ pairForm Q (t₀ - g.1.1) (t - g.1.1) ≠ 0 ∧ pairForm Q (t₀ - g.1.2) (t - g.1.2) ≠ 0))).card
        ≤ 15 * cardV := by
      have : (16 : ℝ) * ((Finset.univ.filter (fun t : V => ¬ (quadraticChar K (pairForm Q (t₀ - g.1.1) (t - g.1.1))
              ≠ quadraticChar K (pairForm Q (t₀ - g.1.2) (t - g.1.2))
            ∧ pairForm Q (t₀ - g.1.1) (t - g.1.1) ≠ 0 ∧ pairForm Q (t₀ - g.1.2) (t - g.1.2) ≠ 0))).card : ℝ)
          ≤ 15 * cardV := by rw [hcardVdef]; linarith [hreal]
      exact_mod_cast this
    rw [hcNdef]
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith [h16])
  -- hβ : bad-anchor count bound
  have hβ : ∀ g, (Finset.univ.filter (fun t₀ => ¬ Good g t₀)).card ≤ βN := by
    intro g
    obtain ⟨t₀₀, y₀, z₀, hrad, _, _⟩ := exists_hgood Q hQrad g.1.1 g.1.2 g.2 hfinrank hcardK7
    have hbeta := beta_full_count_closed (b := b) Q y₀ z₀ g.1.1 g.1.2 t₀₀ w₀ hrad hw₀
    rw [hβNdef]
    refine (Nat.le_div_iff_mul_le hKpos).mpr ?_
    refine le_trans (le_of_eq ?_) hbeta
    congr 1
  -- hlt : c̄₀ < 1
  have hlt : cN + βN < cardV := by
    have hA : 16 * cN ≤ 15 * cardV := by rw [hcNdef, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    have hB : cardK * βN ≤ (2 * d + 4) * cardV + 2 * cardK := by
      rw [hβNdef, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    exact cbar_lt hA hB hqthr hNthr hKpos
  -- run the matching
  obtain ⟨m, P, hP⟩ := exists_separating_base_of_split Fail Good cN βN hc hβ hlt
  refine ⟨(Finset.univ.image (fun j => (P j).1)) ∪ (Finset.univ.image (fun j => (P j).2)), ?_⟩
  -- zSep ⟹ ZProfileSeparatesK
  apply zProfileSeparatesK_of_zSep
  intro u u' hne
  obtain ⟨j, hj⟩ := hP ⟨(u, u'), hne⟩
  rw [hFailDef] at hj
  simp only [not_not] at hj
  obtain ⟨hchi, hIu, hIv, hQu, hQv⟩ := hj
  refine ⟨{(P j).1, (P j).2}, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx <;> subst hx
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩)
  · exact jointIsoCountK_ne_of_sep Q hF hcardK2 hd hψ vb hv hw u u' (P j).1 (P j).2 hIu hIv hQu hQv hchi

open QuadraticMap in
/-- **Increment 5, the seal-ready deliverable.** The matching base `T` of `exists_zProfileSeparatesK` discharges the
Witt-free seal input `IsotropySeparatesAtBaseK Q T` (via `isotropySeparatesK_of_zProfileSeparatesK`, needing only
`Q.polarBilin` nondegenerate). So the affine-polar `VO^ε` residue at `q ≳ 32d` has a finite separating base whose
fine isotropy-count profile pins every vertex — the predicate the Witt-free capstone
`reachesRigidOrCameron_viaIsotropySeparatesK_wittFree` consumes (modulo mapping `T` through `affineE` + a base-size
bound; that bound = the explicit `m` from a refined `exists_pow_matching_lt`, a follow-up). -/
theorem exists_isotropySeparatesAtBaseK {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) [Invertible (2 : K)]
    (hF : ringChar K ≠ 2) (hd : Even d) (hdge : 2 ≤ d)
    {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (hQrad : polarRad Q = ⊥) (hQnd : (Q.polarBilin).Nondegenerate)
    (hq1 : 64 * (Fintype.card K : ℝ) ^ 2 ≤ Fintype.card (Fin d → K))
    (hq2 : 64 * (d : ℝ) ^ 2 ≤ Fintype.card K) (hq3 : 256 ≤ (Fintype.card K : ℝ))
    (hqthr : 32 * (2 * d + 4) ≤ Fintype.card K)
    (hNthr : 64 < Fintype.card (Fin d → K)) :
    ∃ T : Finset (Fin d → K), IsotropySeparatesAtBaseK Q T := by
  obtain ⟨T, hT⟩ := exists_zProfileSeparatesK Q hF hd hdge hψ hQrad hq1 hq2 hq3 hqthr hNthr
  exact ⟨T, isotropySeparatesK_of_zProfileSeparatesK Q hQnd hT⟩

open QuadraticMap in
/-- **Piece 6 — the q = p seal.** The matching base of `exists_isotropySeparatesAtBaseK`, transported through the
digit bijection `affineE`, feeds the Witt-free seal capstone: for an odd prime `p` and a nondegenerate `Q` on
`Fin d → ZMod p` with the family thresholds (`p ≥ 256`, `p ≳ 32d`), the affine-polar `VO^ε` residue **reaches
`reachesRigidOrCameron` modulo `{G3}`** — no Witt, no `hSmallAutThin`. The base is `T = (matching base).image affineE`
and the depth bound is `T.card` (HONEST GAP: that `T.card` is polynomially bounded is not yet exposed — it is the
matching length `≤ 2m`, with `m` from the still-existential `exists_pow_matching_lt`; the explicit log bound is the
remaining analysis). -/
theorem reachesRigidOrCameron_affinePolar {p d : ℕ} [Fact p.Prime]
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (hp2 : p ≠ 2) (hd : Even d) (hdge : 2 ≤ d)
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (hQrad : polarRad Q = ⊥) (hQnd : (Q.polarBilin).Nondegenerate)
    (hq1 : 64 * (Fintype.card (ZMod p) : ℝ) ^ 2 ≤ Fintype.card (Fin d → ZMod p))
    (hq2 : 64 * (d : ℝ) ^ 2 ≤ Fintype.card (ZMod p))
    (hq3 : 256 ≤ (Fintype.card (ZMod p) : ℝ))
    (hqthr : 32 * (2 * d + 4) ≤ Fintype.card (ZMod p))
    (hNthr : 64 < Fintype.card (Fin d → ZMod p)) :
    ∃ T : Finset (Fin (p ^ d)),
      ((SchemeBlockRecovered (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q))
          ∨ AbelianConsumed (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)))
          ∨ SchemeRecoveredByDepth (p ^ d)
              (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)) T.card)
        ∨ IsCameronScheme (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  haveI : Invertible (2 : ZMod p) := invertibleOfNonzero (Ring.two_ne_zero hF)
  obtain ⟨myT, hsep⟩ :=
    exists_isotropySeparatesAtBaseK Q hF hd hdge hψ hQrad hQnd hq1 hq2 hq3 hqthr hNthr
  refine ⟨myT.image affineE, ?_⟩
  have himg : (myT.image affineE).image affineE.symm = myT := by
    rw [Finset.image_image,
      show (affineE.symm ∘ affineE) = id from funext (fun x => affineE.symm_apply_apply x),
      Finset.image_id]
  exact reachesRigidOrCameron_viaIsotropySeparatesK_wittFree Q (myT.image affineE) (le_refl _)
    (by rw [himg]; exact hsep)

end ChainDescent

#print axioms ChainDescent.exists_pow_matching_lt
#print axioms ChainDescent.exists_separating_base_of_split
#print axioms ChainDescent.cbar_lt
#print axioms ChainDescent.jointIsoCountK_ne_of_sep
#print axioms ChainDescent.exists_zProfileSeparatesK
#print axioms ChainDescent.exists_isotropySeparatesAtBaseK
#print axioms ChainDescent.reachesRigidOrCameron_affinePolar
