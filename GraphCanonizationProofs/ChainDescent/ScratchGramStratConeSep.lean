/-
# Route A, Step C — Piece 1c: `IsoConeSumSeparatesGram` (the cone non-degeneracy) — DISCHARGED

**What this module builds (recovery doc §9.7).** The isolated crux `IsoConeSumSeparatesGram` (`ScratchGramStratGaussReduce`):
at a `GoodBase` with even ambient dimension, equal factored transforms `ψ(⟨t,gramK u⟩)·isoConeSum(t₀•u+t₁•a+t₂•b)`
for all `t` force `gramK u = gramK u'` and the plane flag. This module **proves it** from the closed form + non-vanishing
of `isoConeSum` (`ScratchGramStratConeEval`). Discharging this closes Route A's Piece 1 to `bᵢ = 1` modulo only the
carried Witt citation (`RefinedWittExtends`).

**The argument (clean, uniform — `isoConeSum_ne_zero` does the heavy lifting).**
* **Off-diagonal** (`polar u a = polar u' a`, `polar u b = polar u' b`): the `t₀ = 0` slice makes `y = t₁•a + t₂•b`
  *`u`-independent*, so `isoConeSum(y)` is a common nonzero factor; cancelling it gives
  `ψ(t₁·polar u a + t₂·polar u b) = ψ(t₁·polar u' a + t₂·polar u' b)`, and primitivity (`t₂=0`, resp. `t₁=0`) forces
  the polars equal.
* **Diagonal** (`Q u = Q u'`): the `(t₀,0,0)` slice gives `ψ(t₀·Qu)·L_u = ψ(t₀·Qu')·L_{u'}` with `L_u = isoConeSum(t₀•u)`
  *constant in `t₀≠0`* (closed form) and *nonzero*; cross-multiplying two values `t₀,t₀'` cancels `L_u,L_{u'}` and yields
  `ψ((t₀−t₀')·(Qu−Qu')) = 1`; as `t₀−t₀'` covers all of `K`, primitivity forces `Qu = Qu'`.
* **Flag**: with `gramK u = gramK u'` the phases coincide, so `isoConeSum(y_u) = isoConeSum(y_u')` for all `t`; the closed
  form's `Q y_u = Q y_u'` parts cancel, leaving `𝟙[y_u=0] = 𝟙[y_u'=0]`; at `t₀=1` this is `u∈span{a,b} ⟺ u'∈span{a,b}`.

Reuses `ScratchGramStratConeEval` (`isoConeSum_eval_even`, `isoConeSum_ne_zero`), `ScratchGramStratGauss` (`isoConeSum`),
`ScratchGramStratGaussReduce` (`IsoConeSumSeparatesGram`), `ScratchGramStratOrbit` (`GoodBase`). Axiom-clean
`[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchGramStratConeEval
import ChainDescent.ScratchGramStratGaussReduce

namespace ChainDescent.GramStrat

open QuadraticMap ChainDescent.OrbitBaseCase

set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] {Q : QuadraticForm K V}

/-- **★ The cone non-degeneracy, discharged.** `IsoConeSumSeparatesGram Q a b` holds (char ≠ 2, `2` invertible,
finite-dimensional): the factored-transform equality determines the exact Gram to `{a,b}` and the plane flag. -/
theorem isoConeSumSeparatesGram [Invertible (2 : K)] (hF : ringChar K ≠ 2) [FiniteDimensional K V]
    {a b : V} : IsoConeSumSeparatesGram Q a b := by
  intro hbase heven R' hfield hcz ψ hψ u u' hyp
  obtain ⟨hQa, hQb, hab, h2, hnd⟩ := hbase
  -- ψ values are units, so nonzero
  have hψne : ∀ c : K, ψ c ≠ 0 := by
    intro c hc
    have h1 : ψ c * ψ (-c) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hc, zero_mul] at h1; exact one_ne_zero h1.symm
  -- primitivity: (∀ v, ψ(v·r) = 1) → r = 0
  have hprim_zero : ∀ r : K, (∀ v : K, ψ (v * r) = 1) → r = 0 := by
    intro r hr; by_contra hr0
    refine hψ hr0 ?_
    ext x
    rw [AddChar.mulShift_apply, AddChar.one_apply, mul_comm]; exact hr x
  -- ψ A = ψ B → ψ (A − B) = 1
  have hpsi_sub : ∀ A B : K, ψ A = ψ B → ψ (A - B) = 1 := by
    intro A B h
    have hBB : ψ B * ψ (-B) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, h]; exact hBB
  -- ═══ Off-diagonal ═══
  have key_off : ∀ t1 t2 : K,
      ψ (t1 * QuadraticMap.polar Q u a + t2 * QuadraticMap.polar Q u b)
        = ψ (t1 * QuadraticMap.polar Q u' a + t2 * QuadraticMap.polar Q u' b) := by
    intro t1 t2
    have h := hyp (0, t1, t2)
    simp only [zero_mul, zero_add, zero_smul] at h
    exact mul_right_cancel₀ (isoConeSum_ne_zero hF hψ hnd heven (t1 • a + t2 • b)) h
  have hda : QuadraticMap.polar Q u a = QuadraticMap.polar Q u' a := by
    have hr : QuadraticMap.polar Q u a - QuadraticMap.polar Q u' a = 0 := by
      refine hprim_zero _ (fun v => ?_)
      have h := key_off v 0
      simp only [zero_mul, add_zero] at h
      have hs := hpsi_sub _ _ h
      rwa [← mul_sub] at hs
    exact sub_eq_zero.mp hr
  have hdb : QuadraticMap.polar Q u b = QuadraticMap.polar Q u' b := by
    have hr : QuadraticMap.polar Q u b - QuadraticMap.polar Q u' b = 0 := by
      refine hprim_zero _ (fun v => ?_)
      have h := key_off 0 v
      simp only [zero_mul, zero_add] at h
      have hs := hpsi_sub _ _ h
      rwa [← mul_sub] at hs
    exact sub_eq_zero.mp hr
  -- ═══ Diagonal ═══
  -- L_u = isoConeSum (t₀ • w) is constant in t₀ ≠ 0
  have hscale : ∀ (w : V) (t0 : K), t0 ≠ 0 → isoConeSum Q ψ (t0 • w) = isoConeSum Q ψ w := by
    intro w t0 ht0
    have e1 := isoConeSum_eval_even hF hψ hnd heven (t0 • w)
    have e2 := isoConeSum_eval_even hF hψ hnd heven w
    have e0 : (t0 • w = 0) ↔ (w = 0) := by rw [smul_eq_zero]; simp [ht0]
    have eQ : (Q (t0 • w) = 0) ↔ (Q w = 0) := by
      rw [QuadraticMap.map_smul, smul_eq_mul, mul_eq_zero, mul_eq_zero]; simp [ht0]
    simp only [e0, eQ] at e1
    exact mul_left_cancel₀ (show (Fintype.card K : R') ≠ 0 by exact_mod_cast Fintype.card_ne_zero)
      (e1.trans e2.symm)
  have hcov : ∀ v : K, ∃ t0 t0' : K, t0 ≠ 0 ∧ t0' ≠ 0 ∧ t0 - t0' = v := by
    intro v
    by_cases h : (1 : K) + v = 0
    · refine ⟨-2, -1, neg_ne_zero.mpr h2, neg_ne_zero.mpr one_ne_zero, ?_⟩
      have hv : v = -1 := by linear_combination h
      rw [hv]; ring
    · exact ⟨1 + v, 1, h, one_ne_zero, by ring⟩
  have hdiag : Q u = Q u' := by
    have hstep : ∀ t0 t0' : K, t0 ≠ 0 → t0' ≠ 0 → ψ ((t0 - t0') * (Q u - Q u')) = 1 := by
      intro t0 t0' h0 h0'
      have Da := hyp (t0, 0, 0)
      have Db := hyp (t0', 0, 0)
      simp only [zero_mul, add_zero, zero_smul] at Da Db
      rw [hscale u t0 h0, hscale u' t0 h0] at Da
      rw [hscale u t0' h0', hscale u' t0' h0'] at Db
      have hLu : isoConeSum Q ψ u ≠ 0 := isoConeSum_ne_zero hF hψ hnd heven u
      have key : ψ (t0 * Q u) * ψ (t0' * Q u') = ψ (t0 * Q u') * ψ (t0' * Q u) := by
        have e1 : ψ (t0 * Q u) * ψ (t0' * Q u') * isoConeSum Q ψ u
            = ψ (t0 * Q u') * ψ (t0' * Q u) * isoConeSum Q ψ u := by
          calc ψ (t0 * Q u) * ψ (t0' * Q u') * isoConeSum Q ψ u
              = (ψ (t0 * Q u) * isoConeSum Q ψ u) * ψ (t0' * Q u') := by ring
            _ = (ψ (t0 * Q u') * isoConeSum Q ψ u') * ψ (t0' * Q u') := by rw [Da]
            _ = ψ (t0 * Q u') * (ψ (t0' * Q u') * isoConeSum Q ψ u') := by ring
            _ = ψ (t0 * Q u') * (ψ (t0' * Q u) * isoConeSum Q ψ u) := by rw [← Db]
            _ = ψ (t0 * Q u') * ψ (t0' * Q u) * isoConeSum Q ψ u := by ring
        exact mul_right_cancel₀ hLu e1
      have hAB : ψ (t0 * Q u + t0' * Q u') = ψ (t0 * Q u' + t0' * Q u) := by
        rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, key]
      have hsub := hpsi_sub _ _ hAB
      rwa [show t0 * Q u + t0' * Q u' - (t0 * Q u' + t0' * Q u) = (t0 - t0') * (Q u - Q u') from by
        ring] at hsub
    have hz : Q u - Q u' = 0 := by
      refine hprim_zero _ (fun v => ?_)
      obtain ⟨t0, t0', h0, h0', hd⟩ := hcov v
      rw [← hd]; exact hstep t0 t0' h0 h0'
    exact sub_eq_zero.mp hz
  -- ═══ gramK equal ═══
  have hgramK : gramK Q a b u = gramK Q a b u' := by
    simp only [gramK, hdiag, hda, hdb]
  -- ═══ Flag ═══
  have hind : ∀ t : K × K × K,
      (t.1 • u + t.2.1 • a + t.2.2 • b = 0) ↔ (t.1 • u' + t.2.1 • a + t.2.2 • b = 0) := by
    intro t
    -- isoConeSum(y_u) = isoConeSum(y_u') from equal phases
    have hiso : isoConeSum Q ψ (t.1 • u + t.2.1 • a + t.2.2 • b)
        = isoConeSum Q ψ (t.1 • u' + t.2.1 • a + t.2.2 • b) := by
      have h := hyp t
      rw [hdiag, hda, hdb] at h
      exact mul_left_cancel₀ (hψne _) h
    have hadd : ∀ x y : V, Q (x + y) = QuadraticMap.polar Q x y + Q x + Q y := by
      intro x y; rw [QuadraticMap.polar]; ring
    have hQy : Q (t.1 • u + t.2.1 • a + t.2.2 • b) = Q (t.1 • u' + t.2.1 • a + t.2.2 • b) := by
      simp only [hadd, QuadraticMap.map_smul, QuadraticMap.polar_add_left,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
        smul_eq_mul, hdiag, hda, hdb]
    have e1 := isoConeSum_eval_even hF hψ hnd heven (t.1 • u + t.2.1 • a + t.2.2 • b)
    have e2 := isoConeSum_eval_even hF hψ hnd heven (t.1 • u' + t.2.1 • a + t.2.2 • b)
    rw [hiso, hQy] at e1
    have hBB := e1.symm.trans e2
    have hii : (Fintype.card V : R') * (if (t.1 • u + t.2.1 • a + t.2.2 • b) = 0 then (1 : R') else 0)
        = (Fintype.card V : R') * (if (t.1 • u' + t.2.1 • a + t.2.2 • b) = 0 then (1 : R') else 0) :=
      add_right_cancel hBB
    have hV : (Fintype.card V : R') ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hii2 := mul_left_cancel₀ hV hii
    by_cases hP : (t.1 • u + t.2.1 • a + t.2.2 • b = 0)
    · by_cases hP' : (t.1 • u' + t.2.1 • a + t.2.2 • b = 0)
      · exact ⟨fun _ => hP', fun _ => hP⟩
      · rw [if_pos hP, if_neg hP'] at hii2; exact absurd hii2 one_ne_zero
    · by_cases hP' : (t.1 • u' + t.2.1 • a + t.2.2 • b = 0)
      · rw [if_neg hP, if_pos hP'] at hii2; exact absurd hii2.symm one_ne_zero
      · exact ⟨fun h => absurd h hP, fun h => absurd h hP'⟩
  have hspan_iff : ∀ w : V,
      (w ∈ Submodule.span K ({a, b} : Set V)) ↔ ∃ t1 t2 : K, (1 : K) • w + t1 • a + t2 • b = 0 := by
    intro w
    rw [Submodule.mem_span_pair]
    constructor
    · rintro ⟨c, d, hcd⟩; exact ⟨-c, -d, by rw [one_smul, ← hcd]; module⟩
    · rintro ⟨t1, t2, ht⟩
      refine ⟨-t1, -t2, ?_⟩
      rw [one_smul] at ht
      linear_combination (norm := module) -ht
  refine ⟨hgramK, ?_⟩
  rw [hspan_iff u, hspan_iff u']
  constructor
  · rintro ⟨t1, t2, h⟩; exact ⟨t1, t2, (hind (1, t1, t2)).mp h⟩
  · rintro ⟨t1, t2, h⟩; exact ⟨t1, t2, (hind (1, t1, t2)).mpr h⟩

/-- **★★ CAPSTONE — `bᵢ = 1` for the round-3 observable, modulo ONLY the Witt citation.** With the cone non-degeneracy
now *proved* (`isoConeSumSeparatesGram`), the round-3 count profile determines the `Stab({a,b})`-orbit exactly: at a
`GoodBase` of even ambient dimension, `SameGramStratCounts u u' ↔ StabOrbit`, carrying only `RefinedWittExtends` (the
carried Witt-extension theorem, Mathlib-absent). The entire Gauss/analytic content is discharged and axiom-clean; the
primitive additive character is constructed internally (no `hψ` carried). -/
theorem gramCountsEq_iff_stabOrbit_wittOnly [Invertible (2 : K)] (hF : ringChar K ≠ 2)
    [FiniteDimensional K V] {a b : V} (hbase : GoodBase Q a b)
    (heven : Even (Module.finrank K V)) (hwitt : RefinedWittExtends Q a b) {u u' : V} :
    SameGramStratCounts Q a b u u' ↔ StabOrbit Q ({a, b} : Set V) u u' :=
  gramCountsEq_iff_stabOrbit_of_isoConeSep hbase heven (isoConeSumSeparatesGram hF) hwitt

end ChainDescent.GramStrat
