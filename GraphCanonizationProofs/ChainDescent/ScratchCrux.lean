/-
# Discharge of the forms-graph crux (plan §13) — `ZProfileSeparates` reduction

The generalization's one open lemma is `QProfileSeparatesAtBase Q T` (FormsGraphConcrete:157). Per the project's
own framing (FormsGraphConcrete:144–148) the recovery is *irreducibly the joint incidence content*
`Z(S) = #{z : z≠u, Q(z−u)=0, Q(z−t)=0 ∀t∈S}` over sub-frames `S ⊆ T`. This module isolates that:

* `jointIsoCount Q u S` = `Z_u(S)` (the joint isotropic count; `isoClass = 2 ⟺ Q≠0`, so "isotropic" = `≠ 2`);
* `ZProfileSeparates Q T` = the clean crux: agreeing `Z(S)` over all `S ⊆ T` ⟹ the `Q`-profile agrees;
* **D1** (`qProfileSeparatesAtBase_of_zProfileSeparates`): the `QProfileSeparatesAtBase` fine antecedent ⟹ the
  `Z(S)` antecedent (marginalise the fine profile over base-points ∉ S and the pivot class), reducing the open
  content to `ZProfileSeparates`.

Then `ZProfileSeparates` is the single open predicate (D3, the uniform injectivity research). Axiom-clean target.
-/
import ChainDescent.FormsGraphConcrete

namespace ChainDescent

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

end ChainDescent

#print axioms ChainDescent.qProfileSeparatesAtBase_of_zProfileSeparates
#print axioms ChainDescent.isotropySeparates_of_zProfileSeparates
#print axioms ChainDescent.jointIsoCount_eq_restricted
