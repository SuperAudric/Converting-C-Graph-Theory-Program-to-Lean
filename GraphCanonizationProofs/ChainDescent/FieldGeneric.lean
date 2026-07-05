/-
# Field-generic substrate (abstract `K`) + the q=p adapter.

Lifts the forms-graph WL-dim chain to an abstract finite field `K` with `V = Fin d → K` indexed **directly** (no
`Fin (p^d)` digit encoding), and connects the prime-field case `q = p` back to the in-build scheme machinery.

* **V-indexed predicates + reductions** (was `ScratchFieldGen`): `isoClassK`, `coords_determineK`, `jointIsoCountK`,
  `ZProfileSeparatesK`, `QProfileSeparatesAtBaseK`, `IsotropySeparatesAtBaseK`, D1
  `qProfileSeparatesAtBaseK_of_zProfileSeparatesK`, end-to-end `isotropySeparatesK_of_zProfileSeparatesK`, D2
  `jointIsoCountK_eq_restricted`. The analytic content is field-generic — no `ZMod p`-specific fact is used.
* **The soft bridge endpoint** (was `ScratchBridgeK`): `zProfileSeparatesK_of_zSep` (a `Z`-separating base ⟹
  `ZProfileSeparatesK`).
* **The q=p adapter** (was `ScratchFieldGenAdapter`): the abstract-`K` predicate `IsotropySeparatesAtBaseK Q (T.image
  affineE.symm)` ⟹ the build's `Fin (p^d)`-indexed seal capstone `reachesRigidOrCameron_viaIsotropySeparatesK_wittFree`
  (a pure `affineE` relabel — the digit encoding is the only difference). The q=pᵉ case uses the same chain + the
  separate Layer-D `efield` scheme seam.
-/
import ChainDescent.CascadeAffine
import ChainDescent.GaussCount

namespace ChainDescent

section -- ═══════════ was ScratchFieldGen ═══════════

open QuadraticMap

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}

/-! ### The isotropy class + dictionary (V-indexed, abstract `K`) -/

open scoped Classical in
/-- **Isotropy class** of `w : Fin d → K` under `Q`: `0` (zero vector), `1` (nonzero isotropic), `2` (anisotropic). -/
noncomputable def isoClassK (Q : QuadraticForm K (Fin d → K)) (w : Fin d → K) : Fin 3 :=
  if w = 0 then 0 else if Q w = 0 then 1 else 2

omit [Fintype K] in
/-- Class `0` ⟺ the zero vector. -/
theorem isoClassK_eq_zero_iff (Q : QuadraticForm K (Fin d → K)) (w : Fin d → K) :
    isoClassK Q w = 0 ↔ w = 0 := by
  unfold isoClassK
  split_ifs with h1 h2
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩

omit [Fintype K] in
/-- Class `2` ⟺ anisotropic (`Q w ≠ 0`). A *pure* `Q`-value condition. -/
theorem isoClassK_eq_two_iff (Q : QuadraticForm K (Fin d → K)) (w : Fin d → K) :
    isoClassK Q w = 2 ↔ Q w ≠ 0 := by
  unfold isoClassK
  split_ifs with h1 h2
  · subst h1; exact ⟨fun h => absurd h (by decide), fun h => absurd Q.map_zero h⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h2 h⟩
  · exact ⟨fun _ => h2, fun _ => rfl⟩

omit [Fintype K] in
/-- Class `1` ⟺ nonzero isotropic (`w ≠ 0 ∧ Q w = 0`). -/
theorem isoClassK_eq_one_iff (Q : QuadraticForm K (Fin d → K)) (w : Fin d → K) :
    isoClassK Q w = 1 ↔ w ≠ 0 ∧ Q w = 0 := by
  unfold isoClassK
  split_ifs with h1 h2
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h1 h.1⟩
  · exact ⟨fun _ => ⟨h1, h2⟩, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h.2 h2⟩

omit [Fintype K] in
/-- The coarse "isotropic-or-zero" split: `isoClassK ≠ 2` ⟺ `Q w = 0`. -/
theorem isoClassK_ne_two_iff (Q : QuadraticForm K (Fin d → K)) (w : Fin d → K) :
    isoClassK Q w ≠ 2 ↔ Q w = 0 := by
  rw [ne_eq, isoClassK_eq_two_iff, not_not]

/-! ### The Witt-free back-half — form coordinates determine the vector -/

omit [Fintype K] [DecidableEq K] in
/-- `polar Q v e = Q v + Q e − Q (v − e)`. -/
theorem polar_eq_of_subK (Q : QuadraticForm K (Fin d → K)) (v e : Fin d → K) :
    polar Q v e = Q v + Q e - Q (v - e) := by
  have h2 : polar Q v (-e) = Q (v - e) - Q v - Q e := by
    unfold QuadraticMap.polar
    rw [← sub_eq_add_neg, QuadraticMap.map_neg]
  rw [polar_neg_right] at h2
  linear_combination -h2

omit [Fintype K] [DecidableEq K] in
/-- **The back-half — form coordinates determine the vector.** Same `Q`-profile on the standard basis frame +
nondegenerate polar form ⟹ `v = v'`. (V-indexed; the `affineE.symm.injective` step of the original vanishes.) -/
theorem coords_determineK (Q : QuadraticForm K (Fin d → K))
    (hQ : (Q.polarBilin).Nondegenerate) {v v' : Fin d → K}
    (h0 : Q v = Q v')
    (hi : ∀ i : Fin d, Q (v - Pi.single i 1) = Q (v' - Pi.single i 1)) :
    v = v' := by
  have key : ∀ i : Fin d, Q.polarBilin v (Pi.single i 1) = Q.polarBilin v' (Pi.single i 1) := by
    intro i
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_eq_of_subK, polar_eq_of_subK, h0, hi i]
  have hzero : Q.polarBilin (v - v') = 0 := by
    apply (Pi.basisFun K (Fin d)).ext
    intro i
    rw [LinearMap.zero_apply, map_sub, LinearMap.sub_apply, Pi.basisFun_apply, key i, sub_self]
  have hsep := hQ.1 (v - v') (fun y => by rw [hzero, LinearMap.zero_apply])
  exact sub_eq_zero.mp hsep

/-! ### The count predicates (V-indexed, abstract `K`) -/

open scoped Classical in
/-- **The joint isotropic count `Z_u(S)`** over `V = Fin d → K`, indexed directly (no `affineE`). -/
noncomputable def jointIsoCountK (Q : QuadraticForm K (Fin d → K))
    (u : Fin d → K) (S : Finset (Fin d → K)) : ℕ :=
  (Finset.univ.filter (fun z : Fin d → K => z ≠ u ∧
    isoClassK Q (z - u) ≠ 2 ∧
    ∀ t ∈ S, isoClassK Q (z - t) ≠ 2)).card

open scoped Classical in
/-- **The reduced crux predicate `ZProfileSeparates`** (V-indexed). Agreeing joint isotropic counts over every
sub-frame `S ⊆ T` ⟹ the same `Q`-profile over the standard basis frame. -/
noncomputable def ZProfileSeparatesK (Q : QuadraticForm K (Fin d → K))
    (T : Finset (Fin d → K)) : Prop :=
  ∀ u u' : Fin d → K,
    (∀ S : Finset (Fin d → K), S ⊆ T → jointIsoCountK Q u S = jointIsoCountK Q u' S)
    → Q u = Q u' ∧ ∀ i : Fin d, Q (u - Pi.single i 1) = Q (u' - Pi.single i 1)

open scoped Classical in
/-- **`QProfileSeparatesAtBase`** (V-indexed): agreeing fine isotropy counts at `T` ⟹ the `Q`-profile agrees. -/
noncomputable def QProfileSeparatesAtBaseK (Q : QuadraticForm K (Fin d → K))
    (T : Finset (Fin d → K)) : Prop :=
  ∀ u u' : Fin d → K,
    (∀ (σ : (Fin d → K) → Fin 3) (c : Fin 3),
      (Finset.univ.filter (fun z : Fin d → K => z ≠ u ∧
        (∀ t ∈ T, isoClassK Q (z - t) = σ t)
        ∧ isoClassK Q (z - u) = c)).card
      = (Finset.univ.filter (fun z : Fin d → K => z ≠ u' ∧
        (∀ t ∈ T, isoClassK Q (z - t) = σ t)
        ∧ isoClassK Q (z - u') = c)).card)
    → Q u = Q u' ∧ ∀ i : Fin d, Q (u - Pi.single i 1) = Q (u' - Pi.single i 1)

open scoped Classical in
/-- **`IsotropySeparatesAtBase`** (V-indexed): the fine isotropy-count profile at `T` separates all vertices. -/
noncomputable def IsotropySeparatesAtBaseK (Q : QuadraticForm K (Fin d → K))
    (T : Finset (Fin d → K)) : Prop :=
  ∀ u u' : Fin d → K,
    (∀ (σ : (Fin d → K) → Fin 3) (c : Fin 3),
      (Finset.univ.filter (fun z : Fin d → K => z ≠ u ∧
        (∀ t ∈ T, isoClassK Q (z - t) = σ t)
        ∧ isoClassK Q (z - u) = c)).card
      = (Finset.univ.filter (fun z : Fin d → K => z ≠ u' ∧
        (∀ t ∈ T, isoClassK Q (z - t) = σ t)
        ∧ isoClassK Q (z - u') = c)).card)
      → u = u'

/-! ### D1 — the marginalisation reduction -/

/-- Extend a `T`-indexed isotropy profile to a full profile (junk `0` off `T`). -/
noncomputable def extProfileK {T : Finset (Fin d → K)}
    (σ : {x // x ∈ T} → Fin 3) : (Fin d → K) → Fin 3 :=
  fun x => if h : x ∈ T then σ ⟨x, h⟩ else 0

omit [Field K] [Fintype K] in
theorem extProfileK_mem {T : Finset (Fin d → K)} (σ : {x // x ∈ T} → Fin 3)
    {t : Fin d → K} (ht : t ∈ T) : extProfileK σ t = σ ⟨t, ht⟩ := dif_pos ht

open scoped Classical in
/-- **D1 — `ZProfileSeparatesK` ⟹ `QProfileSeparatesAtBaseK`.** Marginalise the fine profile over base-points ∉ `S`
and the pivot class. (Faithful V-indexed copy of `ScratchCrux.qProfileSeparatesAtBase_of_zProfileSeparates`.) -/
theorem qProfileSeparatesAtBaseK_of_zProfileSeparatesK
    (Q : QuadraticForm K (Fin d → K)) {T : Finset (Fin d → K)}
    (h : ZProfileSeparatesK Q T) : QProfileSeparatesAtBaseK Q T := by
  intro u u' hfine
  refine h u u' (fun S hS => ?_)
  have main : ∀ w : Fin d → K, jointIsoCountK Q w S
      = ∑ b : ({x // x ∈ T} → Fin 3) × Fin 3,
          (Finset.univ.filter (fun z : Fin d → K =>
            (z ≠ w ∧ isoClassK Q (z - w) ≠ 2 ∧
              ∀ t ∈ S, isoClassK Q (z - t) ≠ 2) ∧
            ((fun τ : {x // x ∈ T} => isoClassK Q (z - τ.1)) = b.1 ∧
              isoClassK Q (z - w) = b.2))).card := by
    intro w
    rw [jointIsoCountK,
      Finset.card_eq_sum_card_fiberwise
        (f := fun z => ((fun τ : {x // x ∈ T} => isoClassK Q (z - τ.1)),
          isoClassK Q (z - w)))
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
    have setEq : ∀ w : Fin d → K,
        (Finset.univ.filter (fun z : Fin d → K =>
          (z ≠ w ∧ isoClassK Q (z - w) ≠ 2 ∧
            ∀ t ∈ S, isoClassK Q (z - t) ≠ 2) ∧
          ((fun τ : {x // x ∈ T} => isoClassK Q (z - τ.1)) = σ ∧
            isoClassK Q (z - w) = c)))
        = (Finset.univ.filter (fun z : Fin d → K => z ≠ w ∧
            (∀ t ∈ T, isoClassK Q (z - t) = extProfileK σ t) ∧
            isoClassK Q (z - w) = c)) := by
      intro w
      apply Finset.filter_congr
      intro z _
      constructor
      · rintro ⟨⟨hzw, _, _⟩, hσeq, hcw⟩
        refine ⟨hzw, ?_, hcw⟩
        intro t ht
        have hcg := congrFun hσeq ⟨t, ht⟩
        simp only at hcg
        rw [extProfileK_mem σ ht, hcg]
      · rintro ⟨hzw, hTeq, hcw⟩
        refine ⟨⟨hzw, ?_, ?_⟩, ?_, hcw⟩
        · rw [hcw]; exact hc
        · intro t ht
          rw [hTeq t (hS ht), extProfileK_mem σ (hS ht)]
          exact hσS t ht
        · funext τ
          have htt := hTeq τ.1 τ.2
          rw [extProfileK_mem σ τ.2] at htt
          exact htt
    rw [setEq u, setEq u']
    exact hfine (extProfileK σ) c
  · have empty : ∀ w : Fin d → K,
        (Finset.univ.filter (fun z : Fin d → K =>
          (z ≠ w ∧ isoClassK Q (z - w) ≠ 2 ∧
            ∀ t ∈ S, isoClassK Q (z - t) ≠ 2) ∧
          ((fun τ : {x // x ∈ T} => isoClassK Q (z - τ.1)) = σ ∧
            isoClassK Q (z - w) = c))).card = 0 := by
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

/-- **`QProfileSeparatesAtBaseK` ⟹ `IsotropySeparatesAtBaseK`** (V-indexed): the recovered `Q`-profile pins the
vector via `coords_determineK` directly (no `affineE.symm.injective`). -/
theorem isotropySeparatesK_of_qProfileSeparatesK (Q : QuadraticForm K (Fin d → K))
    {T : Finset (Fin d → K)} (hQ : (Q.polarBilin).Nondegenerate)
    (h : QProfileSeparatesAtBaseK Q T) : IsotropySeparatesAtBaseK Q T := by
  intro u u' hfine
  obtain ⟨h0, hi⟩ := h u u' hfine
  exact coords_determineK Q hQ h0 hi

/-- **The D1 chain, end-to-end** (V-indexed): `ZProfileSeparatesK` + nondegeneracy ⟹ `IsotropySeparatesAtBaseK`. -/
theorem isotropySeparatesK_of_zProfileSeparatesK
    (Q : QuadraticForm K (Fin d → K)) {T : Finset (Fin d → K)}
    (hQ : (Q.polarBilin).Nondegenerate) (h : ZProfileSeparatesK Q T) :
    IsotropySeparatesAtBaseK Q T :=
  isotropySeparatesK_of_qProfileSeparatesK Q hQ (qProfileSeparatesAtBaseK_of_zProfileSeparatesK Q h)

/-! ### D2 — `Z_u(S)` as the restricted isotropic count (V-indexed; `count_transport` vanishes) -/

open scoped Classical in
/-- **D2 (bridge)** — `jointIsoCountK Q u S` as the Lemma-A-ready restricted count over `V`: nonzero `w` on the cone
`Q w = 0` whose shift by each config vector `t − u` (`t ∈ S`) stays isotropic. The original's `count_transport`
(`Fin (p^d) ↔ V`) step is gone — we are already in `V`. -/
theorem jointIsoCountK_eq_restricted (Q : QuadraticForm K (Fin d → K))
    (u : Fin d → K) (S : Finset (Fin d → K)) :
    jointIsoCountK Q u S
      = (Finset.univ.filter (fun w : Fin d → K => w ≠ 0 ∧ Q w = 0 ∧
          ∀ t ∈ S, Q (w - (t - u)) = 0)).card := by
  rw [jointIsoCountK]
  apply Finset.card_bij' (fun z _ => z - u) (fun w _ => w + u)
  · rintro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    obtain ⟨hne, hQu, hS⟩ := hz
    rw [isoClassK_ne_two_iff] at hQu
    refine ⟨sub_ne_zero.mpr hne, hQu, fun t ht => ?_⟩
    have := hS t ht
    rw [isoClassK_ne_two_iff] at this
    rw [show z - u - (t - u) = z - t from by abel]
    exact this
  · rintro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨hne, hQw, hS⟩ := hw
    refine ⟨?_, ?_, fun t ht => ?_⟩
    · rw [← sub_ne_zero, add_sub_cancel_right]; exact hne
    · rw [isoClassK_ne_two_iff, add_sub_cancel_right]; exact hQw
    · rw [isoClassK_ne_two_iff, show w + u - t = w - (t - u) from by abel]
      exact hS t ht
  · rintro z _; abel
  · rintro w _; abel

end

section -- ═══════════ was ScratchBridgeK ═══════════

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}

/-- **The bridge reduction (abstract `K`).** If every pair of distinct points is separated by some sub-frame `S ⊆ T`
in the joint isotropic counts, then `ZProfileSeparatesK Q T` holds. -/
theorem zProfileSeparatesK_of_zSep (Q : QuadraticForm K (Fin d → K))
    (T : Finset (Fin d → K))
    (hsep : ∀ u u' : Fin d → K, u ≠ u' →
      ∃ S, S ⊆ T ∧ jointIsoCountK Q u S ≠ jointIsoCountK Q u' S) :
    ZProfileSeparatesK Q T := by
  intro u u' hall
  by_cases h : u = u'
  · subst h; exact ⟨rfl, fun _ => rfl⟩
  · obtain ⟨S, hS, hne⟩ := hsep u u' h
    exact absurd (hall S hS) hne

end

section -- ═══════════ was ScratchFieldGenAdapter ═══════════

open QuadraticMap

variable {p d : ℕ} [Fact p.Prime]

/-- The V-indexed `isoClassK` (abstract `K`, here `K = ZMod p`) agrees with the build's `Fin (p^d)`-flavoured
`isoClass` on the vector space — both are `if w = 0 then 0 else if Q w = 0 then 1 else 2`. -/
theorem isoClassK_eq_isoClass (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) (w : Fin d → ZMod p) :
    isoClassK Q w = isoClass Q w := by
  rcases eq_or_ne w 0 with h1 | h1
  · rw [(isoClassK_eq_zero_iff Q w).2 h1, (isoClass_eq_zero_iff Q w).2 h1]
  · rcases eq_or_ne (Q w) 0 with h2 | h2
    · rw [(isoClassK_eq_one_iff Q w).2 ⟨h1, h2⟩, (isoClass_eq_one_iff Q w).2 ⟨h1, h2⟩]
    · rw [(isoClassK_eq_two_iff Q w).2 h2, (isoClass_eq_two_iff Q w).2 h2]

open scoped Classical in
/-- **The relabel.** For a single pivot `w : Fin (p^d)`, the V-indexed isotropy-profile count (at base
`T.image affineE.symm`, profile `σV`, pivot class `c`) equals the build's `Fin (p^d)`-indexed count (at base `T`,
profile `σV ∘ affineE.symm`, pivot class `c`), via the bijection `affineE`. -/
theorem isoCount_transport
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) {T : Finset (Fin (p ^ d))}
    (σV : (Fin d → ZMod p) → Fin 3) (c : Fin 3) (w : Fin (p ^ d)) :
    (Finset.univ.filter (fun y : Fin d → ZMod p => y ≠ affineE.symm w ∧
      (∀ t ∈ T.image affineE.symm, isoClassK Q (y - t) = σV t) ∧
      isoClassK Q (y - affineE.symm w) = c)).card
    = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ w ∧
      (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σV (affineE.symm t)) ∧
      isoClass Q (affineE.symm z - affineE.symm w) = c)).card := by
  refine Finset.card_nbij' (fun y => affineE y) (fun z => affineE.symm z) ?_ ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_coe, Finset.mem_filter] at hy
    rw [Finset.mem_coe, Finset.mem_filter]
    obtain ⟨_, hne, hprof, hc⟩ := hy
    refine ⟨Finset.mem_univ _, fun h => hne (by rw [← h, Equiv.symm_apply_apply]), fun t ht => ?_, ?_⟩
    · rw [Equiv.symm_apply_apply, ← isoClassK_eq_isoClass]
      exact hprof (affineE.symm t) (Finset.mem_image_of_mem _ ht)
    · rw [Equiv.symm_apply_apply, ← isoClassK_eq_isoClass]; exact hc
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_filter] at hz
    rw [Finset.mem_coe, Finset.mem_filter]
    obtain ⟨_, hne, hprof, hc⟩ := hz
    refine ⟨Finset.mem_univ _, fun h => hne (affineE.symm.injective h), fun tv htv => ?_, ?_⟩
    · rw [Finset.mem_image] at htv
      obtain ⟨t, ht, rfl⟩ := htv
      rw [isoClassK_eq_isoClass]; exact hprof t ht
    · rw [isoClassK_eq_isoClass]; exact hc
  · intro y _; exact affineE.symm_apply_apply y
  · intro z _; exact affineE.apply_symm_apply z

/-- **The q = p adapter.** `IsotropySeparatesAtBaseK Q (T.image affineE.symm)` (the abstract-K, V-indexed predicate
of `ScratchFieldGen`) ⟹ `IsotropySeparatesAtBase Q T` (the build's `Fin (p^d)`-indexed predicate). Pure relabel:
descend to `V` via `affineE.symm.injective`, transport the count agreement with `isoCount_transport`, and feed the
profile `σ = σV ∘ affineE.symm`. -/
theorem isotropySeparatesAtBase_of_K
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) {T : Finset (Fin (p ^ d))}
    (hK : IsotropySeparatesAtBaseK Q (T.image affineE.symm)) :
    IsotropySeparatesAtBase Q T := by
  intro u u' hcounts
  apply affineE.symm.injective
  apply hK (affineE.symm u) (affineE.symm u')
  intro σV c
  rw [isoCount_transport Q σV c u, isoCount_transport Q σV c u']
  exact hcounts (fun x => σV (affineE.symm x)) c

/-- **The abstract-K predicate reaches the capstone (q = p).** Composing the adapter with the build's Witt-free seal
capstone: `IsotropySeparatesAtBaseK Q (T.image affineE.symm)` at a bounded base seals the `VO^ε` residue modulo
`{G3}` — no Witt, no `hSmallAutThin`. Confirms the abstract analytic chain subsumes the prime-field result. -/
theorem reachesRigidOrCameron_viaIsotropySeparatesK_wittFree
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (T : Finset (Fin (p ^ d))) (hcard : T.card ≤ bound)
    (hK : IsotropySeparatesAtBaseK Q (T.image affineE.symm)) :
    ((SchemeBlockRecovered (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q))
        ∨ AbelianConsumed (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)))
        ∨ SchemeRecoveredByDepth (p ^ d)
            (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)) bound)
      ∨ IsCameronScheme (p ^ d) (affineScheme (similitudeGroup Q) (neg_mem_similitudeGroup Q)) :=
  reachesRigidOrCameron_viaIsotropySeparates_wittFree Q T hcard (isotropySeparatesAtBase_of_K Q hK)

end

end ChainDescent

--#print axioms ChainDescent.isoClassK_ne_two_iff
--#print axioms ChainDescent.coords_determineK
--#print axioms ChainDescent.qProfileSeparatesAtBaseK_of_zProfileSeparatesK
--#print axioms ChainDescent.isotropySeparatesK_of_zProfileSeparatesK
--#print axioms ChainDescent.jointIsoCountK_eq_restricted
--#print axioms ChainDescent.zProfileSeparatesK_of_zSep
--#print axioms ChainDescent.isoClassK_eq_isoClass
--#print axioms ChainDescent.isoCount_transport
--#print axioms ChainDescent.isotropySeparatesAtBase_of_K
--#print axioms ChainDescent.reachesRigidOrCameron_viaIsotropySeparatesK_wittFree
