/-
# Forms-graph node-4 discharge (consumer module)

The `FormsGraph`-side consumer that discharges `IsotropySeparatesAtBase Q T` (CascadeAffine §OrthogonalForm) for the
rank-3 SRG `VO^ε` residue, by combining:
* the **Gauss-sum point-count toolkit** (`ChainDescent.GaussCount`) — the closed-form multi-point `Q`-count
  (`countk_eq_sum_charsum` + `multiQuad`/`multiQuad_zero`/`linearMap`) and the value-set inclusion–exclusion
  (`count_pi_setValued`);
* the **affine forms-graph substrate** (`ChainDescent.CascadeAffine`) — `affineScheme`, `affineE`, `isoClass` and
  the isotropy dictionary `isoClass_eq_*`, and the seal capstone `reachesRigidOrCameron_viaIsotropySeparates`.

Build order (the planned increments): (1) transport counts `Fin (p^d) ↔ V` along `affineE` — **landed below**;
(2) the isotropy-count → `Q`-value-set-count conversion (`count_pi_setValued` + the dictionary, with the single-point
origin correction); (3) the injectivity argument at a symmetry-broken base, proving `IsotropySeparatesAtBase Q T`
for `VO^ε_4(3)`, then feeding the capstone. All decls axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import ChainDescent.CascadeAffine
import ChainDescent.GaussCount

namespace ChainDescent

open QuadraticMap

variable {p d : ℕ} [Fact p.Prime]

/-- **Count transport `Fin (p^d) ↔ V` along `affineE`.** A vertex count over the affine point set `Fin (p^d)`,
with a predicate that factors through `affineE.symm` (the coordinate vector), equals the corresponding count over
the vector space `V = Fin d → ZMod p`. This moves the `IsotropySeparatesAtBase` counts — whose predicate is a
function of `affineE.symm z` (the difference relations `isoClass Q (affineE.symm z − affineE.symm t)`, and
`z ≠ u ↔ affineE.symm z ≠ affineE.symm u`) — into the vector space where the Gauss toolkit's point counts live.
Proved by the `affineE` bijection (`Finset.card_image_of_injective`). -/
theorem count_transport (P : (Fin d → ZMod p) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun z : Fin (p ^ d) => P (affineE.symm z))).card
      = (Finset.univ.filter (fun x : Fin d → ZMod p => P x)).card := by
  classical
  rw [← Finset.card_image_of_injective (Finset.univ.filter (fun x : Fin d → ZMod p => P x))
      affineE.injective]
  congr 1
  ext z
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz; exact ⟨affineE.symm z, hz, Equiv.apply_symm_apply _ _⟩
  · rintro ⟨x, hx, rfl⟩; rwa [Equiv.symm_apply_apply]

open scoped Classical in
/-- **`Q`-value-set count on the affine point set, reduced to pointwise `Q`-counts in `V` (step 2, value-set part).**
Chains `count_transport` (`Fin (p^d) → V`) with `count_pi_setValued` (value-SET → value-POINT): a count of affine
points `z` whose difference values `Q(z̄ − t_j)` each lie in a prescribed `Finset A_j` equals the sum, over all
value selections `c ∈ ∏_j A_j`, of the pointwise counts `#{x : ∀j, Q(x − t_j) = c_j}` — exactly the counts the Gauss
toolkit (`countk_eq_sum_charsum` + `multiQuad`/`multiQuad_zero`/`linearMap`) puts in closed form. The isotropy-class
conditions of `IsotropySeparatesAtBase` reduce to such `Q`-value-set conditions via the dictionary `isoClass_eq_*`
(anisotropic ↔ `A_j = {x | x ≠ 0}`, isotropic-or-zero ↔ `A_j = {0}`), modulo the single-point origin correction
(class `0` vs `1`). -/
theorem qvalue_count_transport (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → (Fin d → ZMod p)) (A : ι → Finset (ZMod p)) :
    (Finset.univ.filter (fun z : Fin (p ^ d) => ∀ j, Q (affineE.symm z - t j) ∈ A j)).card
      = ∑ c ∈ Fintype.piFinset A,
          (Finset.univ.filter (fun x : Fin d → ZMod p => ∀ j, Q (x - t j) = c j)).card :=
  (count_transport (fun x => ∀ j, Q (x - t j) ∈ A j)).trans
    (count_pi_setValued (fun j x => Q (x - t j)) A)

/-! ### Milestone 1 — the isotropy-count → pointwise-Q-count conversion (coarse route, no origin correction)

M0 established that **coarse** counts (`Q=0` vs `Q≠0`) separate exactly when the fine isotropy counts do, so the
conversion needs no single-point origin correction: fine-count agreement ⟹ coarse(value-set)-count agreement (each
coarse count is a sum of fine counts over the refining isotropy profiles), and the coarse counts are pure
`Q`-value-set counts that `qvalue_count_transport` lands on pointwise `Q`-counts. -/

open scoped Classical in
/-- **Transport the `IsotropySeparatesAtBase` count into `V` (M1, step 1).** The fine isotropy count over the affine
point set `Fin (p^d)` equals the corresponding count over `V = Fin d → ZMod p` (`z ≠ u ↔ affineE.symm z ≠ affineE.symm u`
+ `count_transport`). So the `IsotropySeparatesAtBase` hypothesis transports to a count agreement in `V`, where the
isotropy → `Q`-value-set conversion and the Gauss closed form live. -/
theorem isotropy_count_transport (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (T : Finset (Fin (p ^ d))) (u : Fin (p ^ d)) (σ : Fin (p ^ d) → Fin 3) (c : Fin 3) :
    (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
        (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σ t) ∧
        isoClass Q (affineE.symm z - affineE.symm u) = c)).card
      = (Finset.univ.filter (fun x : Fin d → ZMod p => x ≠ affineE.symm u ∧
        (∀ t ∈ T, isoClass Q (x - affineE.symm t) = σ t) ∧
        isoClass Q (x - affineE.symm u) = c)).card := by
  classical
  have hcongr : (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
        (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σ t) ∧
        isoClass Q (affineE.symm z - affineE.symm u) = c))
      = (Finset.univ.filter (fun z : Fin (p ^ d) => affineE.symm z ≠ affineE.symm u ∧
        (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σ t) ∧
        isoClass Q (affineE.symm z - affineE.symm u) = c)) := by
    apply Finset.filter_congr
    intro z _
    simp only [ne_eq, Equiv.apply_eq_iff_eq]
  rw [hcongr]
  exact count_transport (fun x => x ≠ affineE.symm u ∧
    (∀ t ∈ T, isoClass Q (x - affineE.symm t) = σ t) ∧ isoClass Q (x - affineE.symm u) = c)

/-- The isotropy-class value-set for a coarse bit: anisotropic (`true`) ↦ `{2}`, isotropic-or-zero (`false`) ↦ `{0,1}`. -/
def isoSetOf : Bool → Finset (Fin 3)
  | true => {2}
  | false => {0, 1}

/-- The matching `Q`-value-set: anisotropic (`true`) ↦ `{x | x ≠ 0}`, isotropic-or-zero (`false`) ↦ `{0}`. -/
def qSetOf : Bool → Finset (ZMod p)
  | true => Finset.univ.erase 0
  | false => {0}

/-- **The per-coordinate dictionary (M1).** The isotropy class lies in `isoSetOf b` iff the `Q`-value lies in
`qSetOf b` — i.e. the coarse split is a pure `Q`-value condition. From `isoClass_ne_two_iff` / `isoClass_eq_two_iff`. -/
theorem mem_isoSetOf_iff (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) (w : Fin d → ZMod p) (b : Bool) :
    isoClass Q w ∈ isoSetOf b ↔ Q w ∈ qSetOf b := by
  cases b
  · have key : ∀ a : Fin 3, a ∈ isoSetOf false ↔ a ≠ 2 := by decide
    rw [key, isoClass_ne_two_iff]; simp [qSetOf]
  · have key : ∀ a : Fin 3, a ∈ isoSetOf true ↔ a = 2 := by decide
    rw [key, isoClass_eq_two_iff]; simp [qSetOf, Finset.mem_erase]

open scoped Classical in
/-- **Fine → coarse (M1 core).** A coarse `Q`-value-set count `#{x : ∀j, Q(x−t_j) ∈ qSetOf(τ_j)}` equals the sum,
over all refining isotropy profiles `σ ∈ ∏_j isoSetOf(τ_j)`, of the fine isotropy counts `#{x : ∀j, isoClass(x−t_j)=σ_j}`.
(`count_pi_setValued` at the isotropy value-type, after the per-coordinate dictionary rewrite.) So fine-count
agreement ⟹ coarse-count agreement, and the coarse counts are pure `Q`-value-set counts (`count_pi_setValued` at
`Q` → pointwise `Q`-counts via `qvalue_count_transport`). No origin correction (M0: coarse suffices). -/
theorem coarse_eq_sum_iso (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → (Fin d → ZMod p)) (τ : ι → Bool) :
    (Finset.univ.filter (fun x : Fin d → ZMod p => ∀ j, Q (x - t j) ∈ qSetOf (τ j))).card
      = ∑ σ ∈ Fintype.piFinset (fun j => isoSetOf (τ j)),
          (Finset.univ.filter (fun x : Fin d → ZMod p => ∀ j, isoClass Q (x - t j) = σ j)).card := by
  classical
  rw [show (Finset.univ.filter (fun x : Fin d → ZMod p => ∀ j, Q (x - t j) ∈ qSetOf (τ j)))
        = (Finset.univ.filter (fun x : Fin d → ZMod p => ∀ j, isoClass Q (x - t j) ∈ isoSetOf (τ j)))
      from ?_]
  · exact count_pi_setValued (fun j x => isoClass Q (x - t j)) (fun j => isoSetOf (τ j))
  · apply Finset.filter_congr
    intro x _
    exact forall_congr' (fun j => (mem_isoSetOf_iff Q (x - t j) (τ j)).symm)

/-! ### Milestone 3 — the injectivity crux: reduce to "counts recover the Q-profile"

M0/M3 probes (`/tmp/m0probe.py`, `/tmp/m3probe.py`) establish, for `VO^-_4(3)` at `T = frameBase ∪ {2e₃}`:
* coarse-count agreement ⟹ `Q`-profile `(Q(ū−t))_{t∈frame}` agreement (**81/81, no counterexamples**);
* so `IsotropySeparatesAtBase` reduces, via the **landed `coords_determine`** (Q-profile + nondegeneracy ⟹ vector),
  to the predicate "counts recover the Q-profile" — the corrected, base-`T` version of the superseded
  `IsotropyCountsRecoverFrameQ` (which was false at the *symmetric* frame).

**The hard kernel (`QProfileSeparatesAtBase`) is NOT resolved here** — it is the genuine uncited content. The exact
gap (probe-pinned): the counts see only the `Q`-zero pattern (`isoClass` is shell-blind — `Q(ū−t)=1` and `=2` give
*identical* common-isotropic counts pairwise), so the recovery is irreducibly the **joint** incidence content
`Z(S) = #{x : Q(x−t)=0 ∀t∈S}` over all sub-frames `S` (which DO determine `u`, 81/81), not a pointwise `Q`-count.
Hence the M2 `multiCharSum` hinge (pointwise) does not directly discharge it; the joint `Z(S)` extraction is the
remaining work. This block lands the reduction and isolates the kernel as one named, probe-validated predicate. -/

open scoped Classical in
/-- **The M3 crux predicate — "counts recover the Q-profile" at a base `T` (the corrected `IsotropyCountsRecoverFrameQ`).**
Agreeing fine isotropy-counts at `T` ⟹ the same `Q`-value profile over the standard basis frame (`Q ū = Q ū'` and
`Q(ū − eᵢ) = Q(ū' − eᵢ)` ∀ basis `eᵢ`). Unlike the superseded frame-locked predicate, this is at an arbitrary
(symmetry-broken) base `T`, where it is **probe-validated** (`VO^-_4(3)`, `T = frameBase ∪ {2e₃}`, 81/81). **OPEN** —
the genuine uncited joint-incidence content (`Z(S)` over sub-frames). -/
noncomputable def QProfileSeparatesAtBase (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (T : Finset (Fin (p ^ d))) : Prop :=
  ∀ u u' : Fin (p ^ d),
    (∀ (σ : Fin (p ^ d) → Fin 3) (c : Fin 3),
      (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u ∧
        (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σ t)
        ∧ isoClass Q (affineE.symm z - affineE.symm u) = c)).card
      = (Finset.univ.filter (fun z : Fin (p ^ d) => z ≠ u' ∧
        (∀ t ∈ T, isoClass Q (affineE.symm z - affineE.symm t) = σ t)
        ∧ isoClass Q (affineE.symm z - affineE.symm u') = c)).card)
    → Q (affineE.symm u) = Q (affineE.symm u') ∧
        ∀ i : Fin d, Q (affineE.symm u - Pi.single i 1) = Q (affineE.symm u' - Pi.single i 1)

/-- **The M3 reduction (resolved part) — `QProfileSeparatesAtBase` ⟹ `IsotropySeparatesAtBase`.** If the counts
recover the `Q`-profile and the polar form is nondegenerate, then the counts separate vertices: the recovered
`Q`-profile pins the vector via the landed `coords_determine`, and `affineE.symm` is injective. So the entire
remaining Gauss-work content for this residue is the single predicate `QProfileSeparatesAtBase Q T`. -/
theorem isotropySeparates_of_qProfileSeparates (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {T : Finset (Fin (p ^ d))} (hQ : (Q.polarBilin).Nondegenerate)
    (h : QProfileSeparatesAtBase Q T) : IsotropySeparatesAtBase Q T := by
  intro u u' hfine
  obtain ⟨h0, hi⟩ := h u u' hfine
  exact affineE.symm.injective (coords_determine Q hQ h0 hi)

end ChainDescent
