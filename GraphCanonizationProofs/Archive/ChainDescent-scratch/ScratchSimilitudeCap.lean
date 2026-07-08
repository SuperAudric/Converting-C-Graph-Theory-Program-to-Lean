/-
# The similitude cap — refinement is provably capped at the square class (plan §13 tail; verdict closure)

**What this module formalizes.** The "last experiment" for an *in-architecture polynomial* forms-graph route
asked: can refinement recover the **exact form value** `Q(x−y)` at a frame (which would feed B.0 / `coords_determine`
and give poly with no behavioural change)? The answer is **no, and provably so** — but for a reason sharper than a
refinement weakness: *the exact value is not a graph invariant at all*.

The affine-polar graph has adjacency `Q(x−y)=0`. Scaling the form by any `c ≠ 0` leaves the cone `{Q=0}` — hence the
graph — **identical** (`affinePolarAdj_smul_eq`). So `Q` is only determined by its graph up to scaling (a similitude),
and any graph-isomorphism-invariant of a vertex pair must be invariant under `Q ↦ c•Q`. This pins the refinement
ceiling exactly:

* `affinePolarAdj_smul_eq`  — **the cap**: the graph of `c•Q` *equals* the graph of `Q`.
* `chi_pairForm_smul`        — the **pair** observable `χ(det G₂) = χ(pairForm)` IS invariant (`det G₂` scales by
  `c²`, killed by `χ`). This is *why* the canonizer's pair observable is well-defined.
* `chi_singleton_smul`       — the **singleton** square-class `χ(Q(x−y))` flips by `χ(c)`, so it is NOT invariant —
  the formal explanation of the empirical "singleton `Z_u({t})` is binary" finding (`Probe_D3cObservable`): only the
  `χ(c)`-invariant fact `Q=0` survives.
* `pairForm_value_not_invariant` — the **exact** pair value scales by `c²`, so two presentations `Q`, `c•Q` of the
  *same graph* disagree on it whenever `c² ≠ 1`. Hence no iso-invariant procedure (refinement of any dimension —
  *or* Route C) can recover the exact form value; only its square class.

**Consequence (corrects the dividing line).** Refinement is capped at *similitude-invariant* data, and `χ(det G₂)`
saturates that ceiling. So the poly question does NOT reduce to "exact vs square-class value" (impossible for both
sides). It reduces to *coloring vs group*: refinement produces a coloring it cannot certify as orbits without the
open `CellsAreOrbits` core; Route C builds the algebraic group object (a scaling-representative form + its isometry
group `O(Q) = O(c•Q)`) and canonicalizes. This module closes the last "maybe" for in-architecture poly.

**NOT proved here** (out of scope, deliberately): (i) the converse "same graph ⟹ proportional" (classical, unneeded);
(ii) the orbit-certification cap = bounded WL-dimension = the open GI-frontier core.

Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.PairForm

namespace ChainDescent.SimilitudeCap

open QuadraticMap

-- The algebra-only lemmas (`quad_smul_apply`, `polar_smul`, `adj_smul_iff`, …) don't use the finiteness
-- instances; the χ lemmas do. Silence the unused-section-var linter rather than split the variable block.
set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V]

/-- Scaling the form scales its values: `(c • Q) x = c * Q x`. -/
@[simp] theorem quad_smul_apply (Q : QuadraticForm K V) (c : K) (x : V) :
    (c • Q) x = c * Q x := by
  rw [QuadraticMap.smul_apply, smul_eq_mul]

/-- Scaling the form scales its polar: `polar (c • Q) s a = c * polar Q s a`. -/
theorem polar_smul (Q : QuadraticForm K V) (c : K) (s a : V) :
    QuadraticMap.polar (c • Q) s a = c * QuadraticMap.polar Q s a := by
  simp only [QuadraticMap.polar, quad_smul_apply]; ring

/-- **The similitude cap (T1).** The affine-polar adjacency `Q(x)=0` is unchanged by scaling the form. -/
theorem adj_smul_iff (Q : QuadraticForm K V) {c : K} (hc : c ≠ 0) (x : V) :
    (c • Q) x = 0 ↔ Q x = 0 := by
  rw [quad_smul_apply, mul_eq_zero, or_iff_right hc]

/-- **The graph is identical for `Q` and `c•Q`.** The affine-polar adjacency relation is literally equal, so the
graph determines `Q` only up to scaling. -/
theorem affinePolarAdj_smul_eq (Q : QuadraticForm K V) {c : K} (hc : c ≠ 0) :
    (fun x y : V => (c • Q) (x - y) = 0) = (fun x y : V => Q (x - y) = 0) := by
  ext x y
  exact adj_smul_iff Q hc (x - y)

/-- The pair invariant scales by `c²`: `pairForm (c • Q) a s = c² · pairForm Q a s`. -/
theorem pairForm_smul_apply (Q : QuadraticForm K V) (c : K) (a s : V) :
    pairForm (c • Q) a s = c ^ 2 * pairForm Q a s := by
  rw [pairForm_apply, pairForm_apply]
  simp only [polar_smul, quad_smul_apply]
  ring

/-- `χ(c² · v) = χ(v)` for `c ≠ 0` — the square multiplier is invisible to the quadratic character. -/
theorem chi_sq_mul {c : K} (hc : c ≠ 0) (v : K) :
    quadraticChar K (c ^ 2 * v) = quadraticChar K v := by
  have h1 : quadraticChar K (c ^ 2) = 1 := by
    rw [pow_two, map_mul]
    have h := quadraticChar_sq_one hc
    rw [pow_two] at h
    exact h
  rw [map_mul, h1, one_mul]

/-- **The square class is a graph invariant (T2).** `χ(det G₂) = χ(pairForm)` is unchanged by scaling the form —
the `c²` multiplier is killed by the quadratic character. So the canonizer's pair observable is well-defined on the
graph (= on the scaling class of `Q`). -/
theorem chi_pairForm_smul (Q : QuadraticForm K V) {c : K} (hc : c ≠ 0) (a s : V) :
    quadraticChar K (pairForm (c • Q) a s) = quadraticChar K (pairForm Q a s) := by
  rw [pairForm_smul_apply, chi_sq_mul hc]

/-- **The singleton square class is NOT a graph invariant (T3a).** `χ(Q(x−y))` flips by `χ(c)` under scaling, so it
is not recoverable from the graph — formally explaining why the singleton observable `Z_u({t})` is binary (it can
only see the `χ(c)`-invariant fact `Q=0`). For nonsquare `c`, `χ(c) = -1` and the value genuinely flips. -/
theorem chi_singleton_smul (Q : QuadraticForm K V) (c : K) (a : V) :
    quadraticChar K ((c • Q) a) = quadraticChar K c * quadraticChar K (Q a) := by
  rw [quad_smul_apply, map_mul]

/-- **The exact value is NOT a graph invariant (T3b).** The exact pair value scales by `c²`, so two presentations
`Q` and `c•Q` of the *same graph* assign different exact values whenever `c² ≠ 1`. Hence no graph-isomorphism-
invariant procedure (refinement of any dimension) can recover the exact form value — only its square class. -/
theorem pairForm_value_not_invariant (Q : QuadraticForm K V) (c : K) (a s : V) :
    pairForm (c • Q) a s = c ^ 2 * pairForm Q a s :=
  pairForm_smul_apply Q c a s

end ChainDescent.SimilitudeCap
