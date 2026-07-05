/-
# Profile reduction — reduce the forms-graph crux to `ZProfileSeparates`, and the B-M1 incidence step.

Two reduction layers feeding the observable↔count bridge:

* **`ScratchCrux` part (D1 + D2-bridge)** — `jointIsoCount Q u S = Z_u(S)` (the joint isotropic count over a sub-frame
  `S ⊆ T`), the predicate `ZProfileSeparates Q T` (agreeing `Z(S)` over all `S ⊆ T` ⟹ the `Q`-profile agrees), and
  `qProfileSeparatesAtBase_of_zProfileSeparates` (the fine `QProfileSeparatesAtBase` antecedent ⟹ the `Z(S)`
  antecedent). This collapses the whole generalization's open content to `ZProfileSeparates`.
* **`ScratchLemmaB` part (B-M1)** — the fine isotropy-count antecedent of `IsotropySeparatesAtBase` ⟹ isotropic-
  incidence agreement (`incidence_agree_V`), with the `y=0` correction split (`cone_count_zero_split`).

(Merge of the former `ScratchCrux` + `ScratchLemmaB`.)
-/
import ChainDescent.CascadeAffine
import ChainDescent.FormsGraphConcrete

namespace ChainDescent

section -- ═══════════ was ScratchCrux ═══════════

open QuadraticMap

variable {p d : ℕ} [Fact p.Prime]

open scoped Classical in
/-- **The joint isotropic count `Z_u(S)`** = `#{z ≠ u : z isotropic-to-u, and isotropic-to-every t ∈ S}`, where
"isotropic" is `isoClass ≠ 2` (the dictionary: `isoClass w = 2 ⟺ Q w ≠ 0`). This is the joint-incidence content the
crux reduces to (the `VO⁻₄(3)` `sigF` counts at `|S| = 2`). -/
noncomputable def jointIsoCount (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (u : Fin (p ^ d)) (S : Finset (Fin (p ^ d))) : ℕ :=
  (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
    isoClass Q (affineE.symm z - affineE.symm u) ≠ 2 ∧
    ∀ t ∈ S, isoClass Q (affineE.symm z - affineE.symm t) ≠ 2)).card

open scoped Classical in
/-- **The reduced crux predicate.** Agreeing joint isotropic counts `Z(S)` over every sub-frame `S ⊆ T` ⟹ the same
`Q`-profile over the standard frame (the `QProfileSeparatesAtBase` conclusion). This is the genuine open content
(D3): the joint `Z(S)`-profile separates `u`. Probe-validated (SPIKE-K; `VO⁻₄(3)` 81/81). -/
noncomputable def ZProfileSeparates (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (T : Finset (Fin (p ^ d))) : Prop :=
  ∀ u u' : Fin (p ^ d),
    (∀ S : Finset (Fin (p ^ d)), S ⊆ T → jointIsoCount Q u S = jointIsoCount Q u' S)
    → Q (affineE.symm u) = Q (affineE.symm u') ∧
        ∀ i : Fin d, Q (affineE.symm u - Pi.single i 1) = Q (affineE.symm u' - Pi.single i 1)

/-- Extend a `T`-indexed isotropy profile to a full profile (junk `0` off `T`). -/
noncomputable def extProfile {p d : ℕ} {T : Finset (Fin (p ^ d))}
    (σ : {x // x ∈ T} → Fin 3) : Fin (p ^ d) → Fin 3 :=
  fun x => if h : x ∈ T then σ ⟨x, h⟩ else 0

theorem extProfile_mem {p d : ℕ} {T : Finset (Fin (p ^ d))} (σ : {x // x ∈ T} → Fin 3)
    {t : Fin (p ^ d)} (ht : t ∈ T) : extProfile σ t = σ ⟨t, ht⟩ := dif_pos ht

open scoped Classical in
/-- **D1 — the marginalisation reduction.** The `QProfileSeparatesAtBase` fine antecedent ⟹ the `Z(S)` antecedent, so
`ZProfileSeparates` (the joint-incidence crux) discharges `QProfileSeparatesAtBase`. Proof: fiber `Z_w(S)` by each
point's `(T`-profile`, pivot-class)`; "good" fibers (`c ≠ 2`, profile `≠ 2` on `S`) are exactly the fine counts (matched
via `hfine`), "bad" fibers are empty. So `Z_u(S) = Z_{u'}(S)`, uniform in the choice of base — landed-tool-only. -/
theorem qProfileSeparatesAtBase_of_zProfileSeparates
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) {T : Finset (Fin (p ^ d))}
    (h : ZProfileSeparates Q T) : QProfileSeparatesAtBase Q T := by
  intro u u' hfine
  refine h u u' (fun S hS => ?_)
  have main : ∀ w : Fin (p ^ d), jointIsoCount Q w S
      = ∑ b : ({x // x ∈ T} → Fin 3) × Fin 3,
          (Finset.univ.filter (fun z : Fin (p ^ d) =>
            (z ≠ w ∧ isoClass Q (affineE.symm z - affineE.symm w) ≠ 2 ∧
              ∀ t ∈ S, isoClass Q (affineE.symm z - affineE.symm t) ≠ 2) ∧
            ((fun τ : {x // x ∈ T} => isoClass Q (affineE.symm z - affineE.symm τ.1)) = b.1 ∧
              isoClass Q (affineE.symm z - affineE.symm w) = b.2))).card := by
    intro w
    rw [jointIsoCount,
      Finset.card_eq_sum_card_fiberwise
        (f := fun z => ((fun τ : {x // x ∈ T} => isoClass Q (affineE.symm z - affineE.symm τ.1)),
          isoClass Q (affineE.symm z - affineE.symm w)))
        (t := Finset.univ) (fun z _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro z _
    rw [Prod.ext_iff]
  rw [main u, main u']
  apply Finset.sum_congr rfl
  rintro ⟨σ, c⟩ _
  by_cases hgood : c ≠ 2 ∧ ∀ t (ht : t ∈ S), σ ⟨t, hS ht⟩ ≠ 2
  · obtain ⟨hc, hσS⟩ := hgood
    have setEq : ∀ w : Fin (p ^ d),
        (Finset.univ.filter (fun z : Fin (p ^ d) =>
          (z ≠ w ∧ isoClass Q (affineE.symm z - affineE.symm w) ≠ 2 ∧
            ∀ t ∈ S, isoClass Q (affineE.symm z - affineE.symm t) ≠ 2) ∧
          ((fun τ : {x // x ∈ T} => isoClass Q (affineE.symm z - affineE.symm τ.1)) = σ ∧
            isoClass Q (affineE.symm z - affineE.symm w) = c)))
        = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ w ∧
            (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = extProfile σ t) ∧
            isoClass Q (affineE.symm z - affineE.symm w) = c)) := by
      intro w
      apply Finset.filter_congr
      intro z _
      constructor
      · rintro ⟨⟨hzw, _, _⟩, hσeq, hcw⟩
        refine ⟨hzw, ?_, hcw⟩
        intro t ht
        have hcg := congrFun hσeq ⟨t, ht⟩
        simp only at hcg
        rw [extProfile_mem σ ht, hcg]
      · rintro ⟨hzw, hTeq, hcw⟩
        refine ⟨⟨hzw, ?_, ?_⟩, ?_, hcw⟩
        · rw [hcw]; exact hc
        · intro t ht
          rw [hTeq t (hS ht), extProfile_mem σ (hS ht)]
          exact hσS t ht
        · funext τ
          have htt := hTeq τ.1 τ.2
          rw [extProfile_mem σ τ.2] at htt
          exact htt
    rw [setEq u, setEq u']
    exact hfine (extProfile σ) c
  · have empty : ∀ w : Fin (p ^ d),
        (Finset.univ.filter (fun z : Fin (p ^ d) =>
          (z ≠ w ∧ isoClass Q (affineE.symm z - affineE.symm w) ≠ 2 ∧
            ∀ t ∈ S, isoClass Q (affineE.symm z - affineE.symm t) ≠ 2) ∧
          ((fun τ : {x // x ∈ T} => isoClass Q (affineE.symm z - affineE.symm τ.1)) = σ ∧
            isoClass Q (affineE.symm z - affineE.symm w) = c))).card = 0 := by
      intro w
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z _
      rintro ⟨⟨_, hw2, hS2⟩, hσeq, hcw⟩
      apply hgood
      refine ⟨by rw [← hcw]; exact hw2, ?_⟩
      intro t ht
      have hcg := congrFun hσeq ⟨t, hS ht⟩
      simp only at hcg
      rw [← hcg]
      exact hS2 t ht
    rw [empty u, empty u']

/-- **The D1 chain, end-to-end.** `ZProfileSeparates` + nondegeneracy ⟹ `IsotropySeparatesAtBase` (the wittFree
capstone's target) — composes D1 with the landed `isotropySeparates_of_qProfileSeparates`. So the *entire* open content
of the generalization is now the single predicate `ZProfileSeparates Q T` (joint `Z(S)`-profile injectivity, D3). -/
theorem isotropySeparates_of_zProfileSeparates
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) {T : Finset (Fin (p ^ d))}
    (hQ : (Q.polarBilin).Nondegenerate) (h : ZProfileSeparates Q T) :
    IsotropySeparatesAtBase Q T :=
  isotropySeparates_of_qProfileSeparates Q hQ (qProfileSeparatesAtBase_of_zProfileSeparates Q h)

open scoped Classical in
/-- **D2 (bridge) — `Z_u(S)` as the restricted isotropic count over `V`.** Unfolding the dictionary
(`isoClass ≠ 2 ⟺ Q = 0`), transporting `Fin (p^d) ↔ V` (`count_transport`), and shifting `w = x − ū`, the joint
isotropic count is the Lemma-A-ready restricted count: nonzero `w` on the cone `Q w = 0` whose shift by each config
vector `t̄ − ū` (`t ∈ S`) stays isotropic. This is exactly the instance's `restrictedF` for general `Q, u, S` — the
entry to Lemma A (`reduction_to_levelset_nondeg`, with config `a t = affineE.symm t − affineE.symm u`). -/
theorem jointIsoCount_eq_restricted (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (u : Fin (p ^ d)) (S : Finset (Fin (p ^ d))) :
    jointIsoCount Q u S
      = (Finset.univ.filter (fun w : Fin d → ZMod p => w ≠ 0 ∧ Q w = 0 ∧
          ∀ t ∈ S, Q (w - (affineE.symm t - affineE.symm u)) = 0)).card := by
  rw [jointIsoCount]
  have hdict : (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
        isoClass Q (affineE.symm z - affineE.symm u) ≠ 2 ∧
        ∀ t ∈ S, isoClass Q (affineE.symm z - affineE.symm t) ≠ 2))
      = (Finset.univ.filter (fun z : Fin (p ^ d) =>
        affineE.symm z ≠ affineE.symm u ∧ Q (affineE.symm z - affineE.symm u) = 0 ∧
        ∀ t ∈ S, Q (affineE.symm z - affineE.symm t) = 0)) := by
    apply Finset.filter_congr
    intro z _
    refine and_congr (affineE.symm.injective.ne_iff).symm
      (and_congr (isoClass_ne_two_iff Q _)
        (forall_congr' (fun t => imp_congr_right (fun _ => isoClass_ne_two_iff Q _))))
  rw [hdict, count_transport (fun x : Fin d → ZMod p => x ≠ affineE.symm u ∧
    Q (x - affineE.symm u) = 0 ∧ ∀ t ∈ S, Q (x - affineE.symm t) = 0)]
  apply Finset.card_bij' (fun x _ => x - affineE.symm u) (fun w _ => w + affineE.symm u)
  · rintro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨hne, hQ, hS⟩ := hx
    refine ⟨sub_ne_zero.mpr hne, hQ, fun t ht => ?_⟩
    rw [show x - affineE.symm u - (affineE.symm t - affineE.symm u) = x - affineE.symm t from by abel]
    exact hS t ht
  · rintro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨hne, hQ, hS⟩ := hw
    refine ⟨?_, ?_, fun t ht => ?_⟩
    · rw [← sub_ne_zero, add_sub_cancel_right]; exact hne
    · rw [add_sub_cancel_right]; exact hQ
    · rw [show w + affineE.symm u - affineE.symm t = w - (affineE.symm t - affineE.symm u) from by abel]
      exact hS t ht
  · rintro x _; abel
  · rintro w _; abel

end

section -- ═══════════ was ScratchLemmaB ═══════════
open QuadraticMap

variable {p d : ℕ} [Fact p.Prime]

open scoped Classical in
/-- **B-M1 core — isotropic-incidence agreement from the fine isotropy-count antecedent.** -/
theorem coarse_incidence_agree (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (T : Finset (Fin (p ^ d))) (u u' : Fin (p ^ d))
    (hfine : ∀ (σ : Fin (p ^ d) → Fin 3) (c : Fin 3),
      (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
        (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σ t)
        ∧ isoClass Q (affineE.symm z - affineE.symm u) = c)).card
      = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u' ∧
        (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σ t)
        ∧ isoClass Q (affineE.symm z - affineE.symm u') = c)).card)
    {S' : Finset (Fin (p ^ d))} (hS : S' ⊆ T) :
    (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
        Q (affineE.symm z - affineE.symm u) = 0 ∧ ∀ t ∈ S', Q (affineE.symm z - affineE.symm t) = 0)).card
      = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u' ∧
        Q (affineE.symm z - affineE.symm u') = 0 ∧ ∀ t ∈ S', Q (affineE.symm z - affineE.symm t) = 0)).card := by
  classical
  let ProfT := (t : Fin (p ^ d)) → t ∈ T → Fin 3
  let ext : ProfT → Fin (p ^ d) → Fin 3 := fun σ v => if h : v ∈ T then σ v h else 0
  have hext : ∀ (σ : ProfT) (t : Fin (p ^ d)) (h : t ∈ T), ext σ t = σ t h := fun σ t h => dif_pos h
  -- the count appearing in the antecedent, as a function of the extended profile
  let cnt : Fin (p ^ d) → ProfT → Fin 3 → ℕ := fun w σ c =>
    (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ w ∧
      (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = ext σ t)
      ∧ isoClass Q (affineE.symm z - affineE.symm w) = c)).card
  have key : ∀ w : Fin (p ^ d),
      (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ w ∧
        Q (affineE.symm z - affineE.symm w) = 0 ∧ ∀ t ∈ S', Q (affineE.symm z - affineE.symm t) = 0)).card
      = ∑ k : ProfT × Fin 3,
          if (∀ t (h : t ∈ T), t ∈ S' → k.1 t h ≠ 2) ∧ k.2 ≠ 2 then cnt w k.1 k.2 else 0 := by
    intro w
    let φ : Fin (p ^ d) → ProfT × Fin 3 :=
      fun z => (fun t _ => isoClass Q (affineE.symm z - affineE.symm t),
        isoClass Q (affineE.symm z - affineE.symm w))
    rw [Finset.card_eq_sum_card_fiberwise (f := φ)
        (t := (Finset.univ : Finset (ProfT × Fin 3))) (fun z _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hcons : (∀ t (h : t ∈ T), t ∈ S' → k.1 t h ≠ 2) ∧ k.2 ≠ 2
    · rw [if_pos hcons]
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hzw, _, _⟩, hφ⟩
        refine ⟨hzw, ?_, ?_⟩
        · intro t ht
          have h1 : isoClass Q (affineE.symm z - affineE.symm t) = k.1 t ht :=
            congrFun (congrFun (congrArg Prod.fst hφ) t) ht
          rw [h1, hext]
        · exact congrArg Prod.snd hφ
      · rintro ⟨hzw, hT, hw⟩
        refine ⟨⟨hzw, ?_, fun t ht => ?_⟩, ?_⟩
        · rw [← isoClass_ne_two_iff, hw]; exact hcons.2
        · rw [← isoClass_ne_two_iff, hT t (hS ht), hext]; exact hcons.1 t (hS ht) ht
        · refine Prod.ext ?_ hw
          funext t ht
          change isoClass Q (affineE.symm z - affineE.symm t) = k.1 t ht
          rw [hT t ht, hext]
    · rw [if_neg hcons, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z hz hφ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨hzw, hQw, hQS⟩ := hz
      apply hcons
      refine ⟨fun t ht htS => ?_, ?_⟩
      · have h1 : isoClass Q (affineE.symm z - affineE.symm t) = k.1 t ht :=
          congrFun (congrFun (congrArg Prod.fst hφ) t) ht
        rw [← h1, isoClass_ne_two_iff]; exact hQS t htS
      · have h2 : isoClass Q (affineE.symm z - affineE.symm w) = k.2 := congrArg Prod.snd hφ
        rw [← h2, isoClass_ne_two_iff]; exact hQw
  rw [key u, key u']
  apply Finset.sum_congr rfl
  intro k _
  by_cases hcons : (∀ t (h : t ∈ T), t ∈ S' → k.1 t h ≠ 2) ∧ k.2 ≠ 2
  · rw [if_pos hcons, if_pos hcons]
    exact hfine (ext k.1) k.2
  · rw [if_neg hcons, if_neg hcons]

open scoped Classical in
/-- **B-M1, transport+translate — the incidence count moves to `V` in Lemma-A coordinates.** The cone-incidence
count over `Fin (p^d)` (basepoint `w`) equals the count over `V` of `y ≠ 0` with `Q y = 0` and `Q (y − aₜ) = 0`
for the config differences `aₜ = t̄ − w̄`. One bijection `z ↦ affineE.symm z − affineE.symm w` does both transport
and translation. (The `y ≠ 0` restriction is the surviving `z ≠ w`; the `y = 0` term is the `z≠u` correction,
split off separately.) -/
theorem incidence_to_V (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (w : Fin (p ^ d)) (S' : Finset (Fin (p ^ d))) :
    (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ w ∧
        Q (affineE.symm z - affineE.symm w) = 0 ∧ ∀ t ∈ S', Q (affineE.symm z - affineE.symm t) = 0)).card
      = (Finset.univ.filter (fun y : Fin d → ZMod p => y ≠ 0 ∧ Q y = 0 ∧
        ∀ t ∈ S', Q (y - (affineE.symm t - affineE.symm w)) = 0)).card := by
  refine Finset.card_bij' (fun z _ => affineE.symm z - affineE.symm w)
    (fun y _ => affineE (y + affineE.symm w)) ?_ ?_ ?_ ?_
  · rintro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    obtain ⟨hzw, hQw, hQS⟩ := hz
    refine ⟨sub_ne_zero.mpr (affineE.symm.injective.ne hzw), hQw, fun t ht => ?_⟩
    rw [show affineE.symm z - affineE.symm w - (affineE.symm t - affineE.symm w)
        = affineE.symm z - affineE.symm t from by abel]
    exact hQS t ht
  · rintro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply] at hy ⊢
    obtain ⟨hy0, hQy, hQS⟩ := hy
    refine ⟨?_, ?_, fun t ht => ?_⟩
    · intro h
      apply hy0
      have h2 : y + affineE.symm w = affineE.symm w := by
        have := congrArg affineE.symm h; rwa [Equiv.symm_apply_apply] at this
      exact add_right_cancel (h2.trans (zero_add _).symm)
    · rwa [add_sub_cancel_right]
    · rw [show y + affineE.symm w - affineE.symm t = y - (affineE.symm t - affineE.symm w) from by abel]
      exact hQS t ht
  · rintro z _; simp only [sub_add_cancel, Equiv.apply_symm_apply]
  · rintro y _; simp only [Equiv.symm_apply_apply, add_sub_cancel_right]

open scoped Classical in
/-- **B-M1 capstone — the incidence counts agree in `V` (Lemma-A coordinates).** Composing the fiberwise
agreement (`coarse_incidence_agree`) with the transport/translate (`incidence_to_V`): from the fine isotropy-count
antecedent, the `V`-side incidence count `#{y ≠ 0 : Q y = 0 ∧ ∀ t∈S', Q (y − (t̄−ū)) = 0}` agrees between `u` and
`u'`, for every `S' ⊆ T`. This is exactly Lemma A's count minus the `y = 0` term (the `z≠u` correction), with the
config differences `aₜ = t̄ − ū`. The remaining bridge to B-M2: add back the `y=0` term and reindex `S'`(Finset) to
Lemma A's `Fin m` argument. -/
theorem incidence_agree_V (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (T : Finset (Fin (p ^ d))) (u u' : Fin (p ^ d))
    (hfine : ∀ (σ : Fin (p ^ d) → Fin 3) (c : Fin 3),
      (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
        (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σ t)
        ∧ isoClass Q (affineE.symm z - affineE.symm u) = c)).card
      = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u' ∧
        (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σ t)
        ∧ isoClass Q (affineE.symm z - affineE.symm u') = c)).card)
    {S' : Finset (Fin (p ^ d))} (hS : S' ⊆ T) :
    (Finset.univ.filter (fun y : Fin d → ZMod p => y ≠ 0 ∧ Q y = 0 ∧
        ∀ t ∈ S', Q (y - (affineE.symm t - affineE.symm u)) = 0)).card
      = (Finset.univ.filter (fun y : Fin d → ZMod p => y ≠ 0 ∧ Q y = 0 ∧
        ∀ t ∈ S', Q (y - (affineE.symm t - affineE.symm u')) = 0)).card := by
  rw [← incidence_to_V Q u S', ← incidence_to_V Q u' S']
  exact coarse_incidence_agree Q T u u' hfine hS

open scoped Classical in
/-- **B-M2 bridge — the `y=0` correction.** Lemma A's full cone-count equals B-M1's `y≠0` (restricted) count plus
the `y=0` term, which is present iff all config differences `aₜ = t̄−w̄` are isotropic (`∀ t∈S', Q aₜ = 0`) — a
Gram-determined indicator. Connects `incidence_agree_V` (restricted) to the full count Lemma A evaluates. -/
theorem cone_count_zero_split (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (S' : Finset (Fin (p ^ d))) (w : Fin (p ^ d)) :
    (Finset.univ.filter (fun y : Fin d → ZMod p =>
        Q y = 0 ∧ ∀ t ∈ S', Q (y - (affineE.symm t - affineE.symm w)) = 0)).card
      = (Finset.univ.filter (fun y : Fin d → ZMod p =>
        y ≠ 0 ∧ Q y = 0 ∧ ∀ t ∈ S', Q (y - (affineE.symm t - affineE.symm w)) = 0)).card
        + (if ∀ t ∈ S', Q (affineE.symm t - affineE.symm w) = 0 then 1 else 0) := by
  classical
  have hP0 : (Q (0 : Fin d → ZMod p) = 0
        ∧ ∀ t ∈ S', Q ((0 : Fin d → ZMod p) - (affineE.symm t - affineE.symm w)) = 0)
      ↔ ∀ t ∈ S', Q (affineE.symm t - affineE.symm w) = 0 := by
    constructor
    · intro h t ht; have := h.2 t ht; rwa [zero_sub, QuadraticMap.map_neg] at this
    · exact fun h => ⟨by simp, fun t ht => by rw [zero_sub, QuadraticMap.map_neg]; exact h t ht⟩
  by_cases h0 : ∀ t ∈ S', Q (affineE.symm t - affineE.symm w) = 0
  · rw [if_pos h0]
    have hmem : (0 : Fin d → ZMod p) ∈ Finset.univ.filter (fun y : Fin d → ZMod p =>
        Q y = 0 ∧ ∀ t ∈ S', Q (y - (affineE.symm t - affineE.symm w)) = 0) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hP0.mpr h0⟩
    have heq : (Finset.univ.filter (fun y : Fin d → ZMod p =>
          Q y = 0 ∧ ∀ t ∈ S', Q (y - (affineE.symm t - affineE.symm w)) = 0)).erase 0
        = Finset.univ.filter (fun y : Fin d → ZMod p =>
          y ≠ 0 ∧ Q y = 0 ∧ ∀ t ∈ S', Q (y - (affineE.symm t - affineE.symm w)) = 0) := by
      ext y; simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← heq, Finset.card_erase_add_one hmem]
  · rw [if_neg h0, add_zero]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun hy => ⟨?_, hy⟩, fun hy => hy.2⟩
    rintro rfl
    exact h0 (hP0.mp hy)

open scoped Classical in
/-- **B-M2 bridge capstone — the FULL Lemma-A-shaped counts agree modulo the Gram-determined `y=0` correction.**
From the fine isotropy-count antecedent: `fullcount_u(S') + corr_{u'} = fullcount_{u'}(S') + corr_u`, where
`fullcount_w(S') = #{y : Q y=0 ∧ ∀t∈S', Q(y−(t̄−w̄))=0}` (Lemma A's count, `aₜ = t̄−w̄`) and `corr_w` is the
isotropic-differences indicator. Combining `cone_count_zero_split` (full = restricted + corr) with
`incidence_agree_V` (restricted agree). Ready to consume Lemma A's `fullcount = f(Gram)` (A-M4) in B-M3. -/
theorem fullcount_agree_modulo_corr (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (T : Finset (Fin (p ^ d))) (u u' : Fin (p ^ d))
    (hfine : ∀ (σ : Fin (p ^ d) → Fin 3) (c : Fin 3),
      (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
        (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σ t)
        ∧ isoClass Q (affineE.symm z - affineE.symm u) = c)).card
      = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u' ∧
        (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σ t)
        ∧ isoClass Q (affineE.symm z - affineE.symm u') = c)).card)
    {S' : Finset (Fin (p ^ d))} (hS : S' ⊆ T) :
    (Finset.univ.filter (fun y : Fin d → ZMod p =>
          Q y = 0 ∧ ∀ t ∈ S', Q (y - (affineE.symm t - affineE.symm u)) = 0)).card
        + (if ∀ t ∈ S', Q (affineE.symm t - affineE.symm u') = 0 then 1 else 0)
      = (Finset.univ.filter (fun y : Fin d → ZMod p =>
          Q y = 0 ∧ ∀ t ∈ S', Q (y - (affineE.symm t - affineE.symm u')) = 0)).card
        + (if ∀ t ∈ S', Q (affineE.symm t - affineE.symm u) = 0 then 1 else 0) := by
  have hu := cone_count_zero_split Q S' u
  have hu' := cone_count_zero_split Q S' u'
  have hres := incidence_agree_V Q T u u' hfine hS
  omega

end

end ChainDescent

--#print axioms ChainDescent.qProfileSeparatesAtBase_of_zProfileSeparates
--#print axioms ChainDescent.isotropySeparates_of_zProfileSeparates
--#print axioms ChainDescent.jointIsoCount_eq_restricted
--#print axioms ChainDescent.coarse_incidence_agree
--#print axioms ChainDescent.incidence_to_V
--#print axioms ChainDescent.incidence_agree_V
--#print axioms ChainDescent.cone_count_zero_split
--#print axioms ChainDescent.fullcount_agree_modulo_corr
