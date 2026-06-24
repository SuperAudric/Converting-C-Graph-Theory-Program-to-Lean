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

/-!
### D1 (next increment) — `qProfileSeparatesAtBase_of_zProfileSeparates`

Goal: `ZProfileSeparates Q T → QProfileSeparatesAtBase Q T`. Given the fine antecedent `hfine` (∀ σ c,
fineCount_u σ c = fineCount_{u'} σ c), derive the `Z(S)` antecedent and apply `ZProfileSeparates`.

The core obligation — **the marginalisation `jointIsoCount Q u S = (a fixed sum of) fineCount_u σ c`:**
`Z_u(S)` filters `{z : z≠u ∧ isoClass(z−u)≠2 ∧ ∀t∈S, isoClass(z−t)≠2}`. Fiber this set (`Finset.card_eq_sum_card_fiberwise`)
by `z ↦ (σ_z|_T, c_z)` where `σ_z t = isoClass(affineE.symm z − affineE.symm t)`, `c_z = isoClass(z−u)`. The fiber at
`(σ_T, c)` with `c ≠ 2 ∧ ∀t∈S, σ_T t ≠ 2` is exactly `fineCount_u σ c` (any extension of `σ_T`; the `≠2` constraints
on `S`/pivot are implied by membership). So `Z_u(S) = ∑_{(σ_T,c) : c≠2, σ_T|_S≠2} fineCount_u σ c` over a `u`-independent
index; termwise `hfine` ⟹ `Z_u(S) = Z_{u'}(S)`.

Lean cost: `Finset.card_eq_sum_card_fiberwise` with fiber type `(↥T → Fin 3) × Fin 3`, plus matching the fiber filter to
the `QProfileSeparatesAtBase` fine filter (extend `↥T → Fin 3` to a full `Fin (p^d) → Fin 3`; the `∀ t ∈ T` predicate
reads only `T`-values). Intricate but landed-tool-only — no new math. THEN `ZProfileSeparates` is the sole open content (D3).
-/

end ChainDescent
