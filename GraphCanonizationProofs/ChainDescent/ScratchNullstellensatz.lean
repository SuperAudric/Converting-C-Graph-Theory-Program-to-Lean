/-
# Discharging `NondegQuadricDeterminesForm` — the quadric Nullstellensatz (WIP)

**Target.** Replace the carried citation
`NondegQuadricDeterminesForm (p d) : p ≠ 2 → 4 ≤ d → ∀ Q R, Q.polarBilin.Nondegenerate →
  (∀ v, Q v = 0 ↔ R v = 0) → ∃ μ : (ZMod p)ˣ, ∀ v, R v = μ * Q v`
(RouteCFormAdapters.lean) with a full Lean proof. "A nondegenerate quadric determines its quadratic form up to a
nonzero scalar" — the projective Nullstellensatz for a nondegenerate quadric, scoped `p ≠ 2`, `d ≥ 4` (the exact TRUE
range: at `d = 3, q = 3` a conic's 4 points lie on a pencil, `vanishDim = 2`).

**The elementary proof path (probe-validated 2026-07-05, `nullstellensatz_path_probe.py` / `nsp.py`).** Avoids Witt
decomposition. Char `≠ 2` ⟹ identify a quadratic form with its polar bilinear form. For an anisotropic `y` and an
isotropic `x`, restrict `Q` to the line `x + t·y`: it is a quadratic in `t` with a root at `t = 0` (giving `x`) and a
second root giving another isotropic point `w`. Since `Z(Q) ⊆ Z(R)`, `R(w) = 0` too — and expanding that identity
yields the **line-restriction identity** `polar Q x y · R y = Q y · polar R x y` (for `polar Q x y ≠ 0`). Reading it as
a linear functional in `x`, it says `polar R (·) y = (R y / Q y) · polar Q (·) y` on the isotropic cone; since the
isotropic cone **spans** `V` (structural fact 1) the identity extends to all `x`, and comparing across anisotropic `y`
via **anisotropic B-connectivity** (structural fact 2) makes the ratio `R y / Q y` a global constant `μ`. Then
`polar R = μ · polar Q` ⟹ `R = μ · Q` (char `≠ 2`), with `μ ≠ 0` from the *reverse* cone inclusion (`Q y ≠ 0 ⟹ R y ≠ 0`).

**STATUS (2026-07-05 — REROUTED: `hspan` ELIMINATED).**
- ✅ **The mathematical heart is LANDED, axiom-clean, ring-general:** `quad_lin_combo` (the `Q(c•x+d•y)` expansion) and
  **`nullstellensatz_core`** (the `w`-construction: `polar Q x y · (polar Q x y · R y − Q y · polar R x y) = 0` for
  isotropic `x`, any `y`, over ANY `CommRing`), plus the field-level cancellation `nullstellensatz_pointwise`
  (`polar Q x y ≠ 0 ⟹ polar Q x y · R y = Q y · polar R x y`). This is the genuinely non-obvious, reusable content.
- ✅ **THE HSPAN-FREE ASSEMBLY IS LANDED, axiom-clean (`nullstellensatz_of_connectivity` + supporting lemmas).** A
  better cut: the μ-scalar conclusion follows from ratio-CONSTANCY on anisotropic vectors alone (the finish is a case
  split, no polar-form extension, no spanning). `ratio_step` proves the ratio is preserved along an isotropic edge
  `y → y+a` (`Q a = 0`, `polar Q a y ≠ 0`) using only `nullstellensatz_pointwise`; `ratioEdge`/`ratio_step_edge`
  package this as a graph edge, and `ratio_const_of_reflTransGen` propagates constancy along any PATH
  (`Relation.ReflTransGen`). So constancy reduces to a single CONNECTIVITY fact.
- ✅ **CONNECTIVITY SCAFFOLD + EDGE BRICKS LANDED, axiom-clean:** `ratioEdge_symm` (edges symmetric on anisotropic
  vertices), `reflTransGen_ratioEdge_symm` (walks reverse), `hconn_of_hub` (reduces `hconn` to a one-sided HUB lemma
  `∀ z, Q z ≠ 0 → ReflTransGen (ratioEdge Q) r z`), plus the step primitives `ratioEdge_smul` (step `y → y+t•a` along an
  isotropic direction) and `ratioEdge_line` (all anisotropic points on an isotropic line form a clique).
- ◻ **REMAINING = ONE classical counting lemma** (feeds the hub, then `hconn`). Probe-CONFIRMED the graph is connected
  (`nullstellensatz_hconn_probe.py`, 2026-07-05): 1 component, **diameter 3–4 for `VO^±_{4,6}(3,5,7)` INCLUDING the `d=4`
  elliptic `q=3` boundary**. The one hard fact, after ruling out every elementary shortcut:
  > **`cone_not_covered`** — for a nondegenerate `Q` on `𝔽_q^d` (`d ≥ 4`, `q` odd not tiny) and vectors `u₁,…,u_k`
  > (`k ≤ 3`), there is an isotropic vector `a` with `polar Q uᵢ a ≠ 0` for all `i` (the isotropic cone is not covered
  > by `k` hyperplanes `uᵢ^⊥`).
  With it, each walk step is exhibited (`ratioEdge_smul`/`_line`) and the hub/`hconn` close. **Unification insight:**
  this is *equivalent to the old `hspan`* (`hspan` = the `k=2` case, `∀ w`), so proving it also closes the spare
  `nullstellensatz_of_structural`. **Route (only viable one):** `GaussCount` — the evaluated quadric point count
  `|cone| = q^{d-1} + O(q^{d/2})` (`card_quadForm_eq` + a Gauss-sum magnitude bound `|∑ψ(Q)| = q^{d/2}`) and hyperplane
  sections `|cone ∩ u^⊥| = q^{d-2}+O(q^{(d-1)/2})`, then a union bound `|cone| > Σ|cone ∩ uᵢ^⊥|` for `q > k`. Mathlib has
  NO quadric cardinality, so this is project-`GaussCount` work (needs diagonalizing to the anisotropic basis, already
  done in the structural file). **Elementary shortcuts RULED OUT** (all recurse to this same fact): fiber-scaling (fails
  by the Gauss error term, `nullstellensatz_fiber_probe.py`); single-hyperplane-only walks (free from `isotropic_span`
  but insufficient — need ≥2). The old `hspan`/`isotropic_span` route is a proven spare; `nullstellensatz_of_structural`
  retained as an alternative reduction. Until `cone_not_covered` lands the citation stays carried.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`, `native_decide` banned.
NOT in `build.sh` yet (WIP scratch).
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.LinearCombination

namespace ChainDescent.Nullstellensatz

open QuadraticMap

section Ring
variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

/-- **The two-vector expansion of a quadratic form.** `Q(c•x + d•y) = c²·Qx + d²·Qy + c·d·polar Q x y`. Pure
`QuadraticMap` API (`map_add`, `map_smul`, `polar_smul_{left,right}`). The workhorse for the `w`-construction. -/
theorem quad_lin_combo (Q : QuadraticForm K V) (c d : K) (x y : V) :
    Q (c • x + d • y) = c * c * Q x + d * d * Q y + c * d * QuadraticMap.polar Q x y := by
  rw [QuadraticMap.map_add (⇑Q) (c • x) (d • y), QuadraticMap.map_smul, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
  simp only [smul_eq_mul]; ring

/-- **The line-restriction core (ring-general).** For quadratic forms `Q, R` with `R` vanishing on the `Q`-cone
(`∀ v, Q v = 0 → R v = 0`) and any isotropic `x` (`Q x = 0`): the "second intersection" vector
`w = Q y • x − polar Q x y • y` is `Q`-isotropic, hence `R`-isotropic, and expanding `R(w) = 0` gives
`polar Q x y · (polar Q x y · R y − Q y · polar R x y) = 0` for every `y`. This is the elementary heart of the
quadric Nullstellensatz — no field, no finiteness, no dimension hypothesis. -/
theorem nullstellensatz_core (Q R : QuadraticForm K V)
    (hcone : ∀ v, Q v = 0 → R v = 0) {x y : V} (hx : Q x = 0) :
    QuadraticMap.polar Q x y *
      (QuadraticMap.polar Q x y * R y - Q y * QuadraticMap.polar R x y) = 0 := by
  -- `w := Q y • x + (−polar Q x y) • y` is Q-isotropic
  have hw : Q ((Q y) • x + (-(QuadraticMap.polar Q x y)) • y) = 0 := by
    rw [quad_lin_combo, hx]; ring
  -- hence R-isotropic; expand and use R x = 0
  have hRw := hcone _ hw
  rw [quad_lin_combo, hcone x hx] at hRw
  linear_combination hRw

end Ring

section Field
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- **The line-restriction identity (field version).** Cancelling the nonzero factor `polar Q x y` in
`nullstellensatz_core`: for isotropic `x` and `y` with `polar Q x y ≠ 0`,
`polar Q x y · R y = Q y · polar R x y`. Equivalently `polar R x y = (R y / Q y) · polar Q x y` — the linear
functional `polar R (·) y` equals `(R y / Q y) · polar Q (·) y` at isotropic `x`. -/
theorem nullstellensatz_pointwise (Q R : QuadraticForm K V)
    (hcone : ∀ v, Q v = 0 → R v = 0) {x y : V} (hx : Q x = 0)
    (hxy : QuadraticMap.polar Q x y ≠ 0) :
    QuadraticMap.polar Q x y * R y = Q y * QuadraticMap.polar R x y := by
  rcases mul_eq_zero.mp (nullstellensatz_core Q R hcone hx) with h0 | h0
  · exact absurd h0 hxy
  · exact sub_eq_zero.mp h0

/-- **The finish (char `≠ 2`): `polar R = μ · polar Q` ⟹ `R = μ · Q`.** Over a field of characteristic `≠ 2`, a
quadratic form is recovered from its polar bilinear form via `polar Q x x = 2 • Q x`; so if the polar forms are
proportional by `μ`, the quadratic forms are too. The last step of the assembly, once the structural facts have made
the ratio `μ` global. Elementary. -/
theorem form_eq_of_polar_eq_smul (Q R : QuadraticForm K V) (μ : K) (h2 : (2 : K) ≠ 0)
    (h : ∀ x y, QuadraticMap.polar R x y = μ * QuadraticMap.polar Q x y) (x : V) :
    R x = μ * Q x := by
  have hxx := h x x
  rw [QuadraticMap.polar_self, QuadraticMap.polar_self] at hxx
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hxx
  exact mul_left_cancel₀ h2 (by linear_combination hxx)

/-- **Ratio-preservation step (from the line-restriction core — NO structural input).** If `a` is isotropic
(`Q a = 0`) and `polar Q a y ≠ 0`, then the anisotropic ratio `R/Q` is *unchanged* along the isotropic edge
`y → y + a`: `R y · Q (y + a) = R (y + a) · Q y`. Proof: `Q(y+a) = Q y + polar Q y a`, `R(y+a) = R y + polar R y a`
(with `R a = 0` from the cone), and `nullstellensatz_pointwise` supplies `polar R a y = (R y / Q y)·polar Q a y`
— the two lines then match by `ring`. This is the engine that spreads the constant `μ` across anisotropic vectors
along isotropic steps; it uses only `nullstellensatz_core` (hence no spanning, no dimension, no finiteness, no
char hypothesis). It REPLACES the `hspan`-dependent per-`y` identity of the older assembly. -/
theorem ratio_step (Q R : QuadraticForm K V) (hcone : ∀ v, Q v = 0 → R v = 0)
    {a y : V} (ha : Q a = 0) (hay : QuadraticMap.polar Q a y ≠ 0) :
    R y * Q (y + a) = R (y + a) * Q y := by
  have hQya : Q (y + a) = Q y + QuadraticMap.polar Q y a := by
    rw [QuadraticMap.map_add (⇑Q) y a, ha]; ring
  have hRya : R (y + a) = R y + QuadraticMap.polar R y a := by
    rw [QuadraticMap.map_add (⇑R) y a, hcone a ha]; ring
  have hp := nullstellensatz_pointwise Q R hcone ha hay
  rw [hQya, hRya, QuadraticMap.polar_comm Q y a, QuadraticMap.polar_comm R y a]
  linear_combination hp

/-- **The isotropic-edge relation on anisotropic vectors.** `b` is one non-tangent isotropic step from `a`:
`b` is anisotropic, `b − a` is isotropic, and `a` is not `Q`-orthogonal to `b − a`. `ratio_step_edge` shows the
ratio `R/Q` is preserved along such an edge; connectivity of this graph (probe-confirmed, diameter 3–4 for all
`VO^ε` incl. the `d=4` elliptic boundary) makes the ratio globally constant. -/
def ratioEdge (Q : QuadraticForm K V) (a b : V) : Prop :=
  Q b ≠ 0 ∧ Q (b - a) = 0 ∧ QuadraticMap.polar Q a (b - a) ≠ 0

/-- **One isotropic edge preserves the ratio** (repackaging `ratio_step`): `ratioEdge Q a b ⟹ R a·Q b = R b·Q a`. -/
theorem ratio_step_edge (Q R : QuadraticForm K V) (hcone : ∀ v, Q v = 0 → R v = 0)
    {a b : V} (h : ratioEdge Q a b) : R a * Q b = R b * Q a := by
  obtain ⟨_, hiso, hpol⟩ := h
  have hrs := ratio_step Q R hcone (a := b - a) hiso
    (by rw [QuadraticMap.polar_comm]; exact hpol)
  rwa [show a + (b - a) = b by abel] at hrs

/-- **The isotropic-edge relation is symmetric on anisotropic vectors.** If `ratioEdge Q a b` and `a` is
anisotropic, then `ratioEdge Q b a`. (The isotropy `Q(b−a)=0` is even; the non-tangency flips sign:
`polar Q b (a−b) = −polar Q a (b−a)`, using `Q(b−a)=0 ⟹ polar Q a b = Q a + Q b`.) Lets us reverse walks. -/
theorem ratioEdge_symm (Q : QuadraticForm K V) {a b : V}
    (h : ratioEdge Q a b) (ha : Q a ≠ 0) : ratioEdge Q b a := by
  obtain ⟨_, hiso, hpol⟩ := h
  -- Q(b−a)=0 rewritten as `polar Q a b = Q a + Q b`
  have hQ' : QuadraticMap.polar Q a b = Q a + Q b := by
    have h0 : Q (b + -a) = Q b + Q a - QuadraticMap.polar Q b a := by
      rw [QuadraticMap.map_add (⇑Q) b (-a), QuadraticMap.map_neg, QuadraticMap.polar_neg_right]; ring
    have h1 : Q b + Q a - QuadraticMap.polar Q b a = 0 := by
      rw [← h0, show b + -a = b - a by abel]; exact hiso
    rw [QuadraticMap.polar_comm]; linear_combination -h1
  refine ⟨ha, ?_, ?_⟩
  · rw [show a - b = -(b - a) by abel, QuadraticMap.map_neg]; exact hiso
  · have key : QuadraticMap.polar Q b (a - b) = - QuadraticMap.polar Q a (b - a) := by
      rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_sub_right, QuadraticMap.polar_self,
        QuadraticMap.polar_self, QuadraticMap.polar_comm Q b a, two_nsmul, two_nsmul]
      linear_combination 2 * hQ'
    rw [key]; exact neg_ne_zero.mpr hpol

/-- **Edge along an isotropic direction.** For isotropic `a` non-tangent to `y` (`polar Q y a ≠ 0`), any `t ≠ 0`
with `y + t•a` anisotropic gives an edge `y — y + t•a`. The basic "take a step" primitive. -/
theorem ratioEdge_smul (Q : QuadraticForm K V) {y a : V} {t : K}
    (ha : Q a = 0) (hpol : QuadraticMap.polar Q y a ≠ 0) (ht : t ≠ 0)
    (hb : Q (y + t • a) ≠ 0) : ratioEdge Q y (y + t • a) := by
  refine ⟨hb, ?_, ?_⟩
  · rw [add_sub_cancel_left, QuadraticMap.map_smul, ha, smul_zero]
  · rw [add_sub_cancel_left, QuadraticMap.polar_smul_right, smul_eq_mul]
    exact mul_ne_zero ht hpol

/-- **Two anisotropic points on an isotropic line are one edge apart.** For isotropic `a` non-tangent to `y`,
any two distinct anisotropic points `y + s•a`, `y + t•a` on the line are directly connected. So all anisotropic
points on such a line form a clique — the "slide freely along an isotropic direction" primitive. -/
theorem ratioEdge_line (Q : QuadraticForm K V) {y a : V} {s t : K}
    (ha : Q a = 0) (hpol : QuadraticMap.polar Q y a ≠ 0) (hst : s ≠ t)
    (hbt : Q (y + t • a) ≠ 0) :
    ratioEdge Q (y + s • a) (y + t • a) := by
  have hdiff : (y + t • a) - (y + s • a) = (t - s) • a := by rw [sub_smul]; abel
  refine ⟨hbt, ?_, ?_⟩
  · rw [hdiff, QuadraticMap.map_smul, ha, smul_zero]
  · rw [hdiff, QuadraticMap.polar_smul_right, smul_eq_mul, QuadraticMap.polar_add_left,
      QuadraticMap.polar_smul_left, smul_eq_mul,
      show QuadraticMap.polar Q a a = 2 • Q a from Q.polar_self a, ha, smul_zero, mul_zero, add_zero]
    exact mul_ne_zero (sub_ne_zero.mpr hst.symm) hpol

/-- **Ratio constancy along a path** — the reflexive-transitive closure of `ratioEdge` preserves `R/Q`. By
induction on the path: each edge preserves the ratio (`ratio_step_edge`) and the relation `R a·Q b = R b·Q a`
is transitive on anisotropic vectors. Carries anisotropy of the endpoint so intermediate cancellations are valid. -/
theorem ratio_const_of_reflTransGen (Q R : QuadraticForm K V) (hcone : ∀ v, Q v = 0 → R v = 0)
    {y : V} (hy : Q y ≠ 0) {y' : V} (h : Relation.ReflTransGen (ratioEdge Q) y y') :
    Q y' ≠ 0 ∧ R y * Q y' = R y' * Q y := by
  induction h with
  | refl => exact ⟨hy, by ring⟩
  | @tail m b _ hedge ih =>
      obtain ⟨hm, ihe⟩ := ih
      have he := ratio_step_edge Q R hcone hedge
      exact ⟨hedge.1, mul_right_cancel₀ hm (by linear_combination Q b * ihe + Q y * he)⟩

/-- **Walks reverse** (the edge relation is symmetric on anisotropic vertices, and every vertex on a walk from an
anisotropic start is anisotropic). `ReflTransGen (ratioEdge Q) y z` with `y` anisotropic ⟹ `z` anisotropic and
`ReflTransGen (ratioEdge Q) z y`. -/
theorem reflTransGen_ratioEdge_symm (Q : QuadraticForm K V) {y z : V} (hy : Q y ≠ 0)
    (h : Relation.ReflTransGen (ratioEdge Q) y z) :
    Q z ≠ 0 ∧ Relation.ReflTransGen (ratioEdge Q) z y := by
  induction h with
  | refl => exact ⟨hy, .refl⟩
  | @tail m z _ hmz ih =>
      obtain ⟨hm, ihpath⟩ := ih
      exact ⟨hmz.1, (Relation.ReflTransGen.single (ratioEdge_symm Q hmz hm)).trans ihpath⟩

/-- **Hub reduction of connectivity.** If every anisotropic vector is reachable from a single anisotropic
reference `r` (`hub`), then any two anisotropic vectors are connected: `y → r` (reverse of `hub y`) then
`r → y'` (`hub y'`). Reduces the open `hconn` to a one-sided `hub` lemma. -/
theorem hconn_of_hub (Q : QuadraticForm K V) {r : V} (hr : Q r ≠ 0)
    (hub : ∀ z, Q z ≠ 0 → Relation.ReflTransGen (ratioEdge Q) r z) :
    ∀ y y', Q y ≠ 0 → Q y' ≠ 0 → Relation.ReflTransGen (ratioEdge Q) y y' :=
  fun y y' hy hy' => ((reflTransGen_ratioEdge_symm Q hr (hub y hy)).2).trans (hub y' hy')

/-- **The connectivity assembly — the hspan-free route to the μ-scalar conclusion.** Reduces the full quadric
Nullstellensatz to a SINGLE structural fact: the isotropic-edge graph on anisotropic vectors is **connected**
(`hconn`, the reflexive-transitive closure of `ratioEdge` joins any two anisotropic vectors). The ratio `R/Q` is
preserved along each edge (`ratio_step`), so connectivity makes it globally constant, and `R v = μ Q v` follows
by a case split on `Q v = 0` (cone) vs `≠ 0` (constancy). No `hspan`, no polar-form finish, no char hypothesis.
Connectivity HOLDS at the `d = 4` elliptic boundary (probe: diameter 3–4 for all `VO^ε_{4,6}(3,5,7)`) — the exact
regime where the old `hspan` was hard — so the delicate obstruction is genuinely gone; only its discharge (graph
connectivity via the `GaussCount` point-count / an explicit walk) remains. -/
theorem nullstellensatz_of_connectivity (Q R : QuadraticForm K V)
    (hcone : ∀ v, Q v = 0 ↔ R v = 0)
    (hEx : ∃ y, Q y ≠ 0)
    (hconn : ∀ y y', Q y ≠ 0 → Q y' ≠ 0 → Relation.ReflTransGen (ratioEdge Q) y y') :
    ∃ μ : Kˣ, ∀ v, R v = (μ : K) * Q v := by
  classical
  have hcone' : ∀ v, Q v = 0 → R v = 0 := fun v h => (hcone v).mp h
  -- the ratio is constant across all anisotropic vectors, by connectivity.
  have const : ∀ y y', Q y ≠ 0 → Q y' ≠ 0 → R y * Q y' = R y' * Q y := fun y y' hy hy' =>
    (ratio_const_of_reflTransGen Q R hcone' hy (hconn y y' hy hy')).2
  -- `μ := R y₀ / Q y₀`; `R v = μ Q v` by cases on `Q v = 0` (cone) vs `≠ 0` (constancy).
  obtain ⟨y0, hy0⟩ := hEx
  have hRy0 : R y0 ≠ 0 := fun h => hy0 ((hcone y0).mpr h)
  refine ⟨Units.mk0 (R y0 * (Q y0)⁻¹) (mul_ne_zero hRy0 (inv_ne_zero hy0)), fun v => ?_⟩
  simp only [Units.val_mk0]
  by_cases hv : Q v = 0
  · rw [(hcone v).mp hv, hv, mul_zero]
  · have hc := const v y0 hv hy0
    rw [show R y0 * (Q y0)⁻¹ * Q v = R y0 * Q v * (Q y0)⁻¹ by ring, ← hc,
      mul_assoc, mul_inv_cancel₀ hy0, mul_one]

/-! ### The assembly — the two structural facts imply the μ-scalar conclusion

`nullstellensatz_of_structural` reduces the full quadric Nullstellensatz to two **purely geometric** facts about the
nondegenerate `Q` (probe-validated for the `VO^ε` families, `nsp2.py`):
- `hspan` — for each anisotropic `y`, the **punctured isotropic cone** `{x | Q x = 0 ∧ polar Q x y ≠ 0}` spans `V`.
- `hlink` — the anisotropic vectors have **`polar`-diameter ≤ 2**: any two are joined through one anisotropic `z` with
  `polar Q y z ≠ 0` and `polar Q z y' ≠ 0` (replaces a general connectivity induction).
Everything else is elementary and proved here. This is the "isolate" capstone: the opaque Nullstellensatz is now
exactly these two finite-geometry facts + `nullstellensatz_core`. -/
theorem nullstellensatz_of_structural [Nontrivial V] (Q R : QuadraticForm K V)
    (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hcone : ∀ v, Q v = 0 ↔ R v = 0)
    (hspan : ∀ y, Q y ≠ 0 →
      Submodule.span K {x | Q x = 0 ∧ QuadraticMap.polar Q x y ≠ 0} = ⊤)
    (hlink : ∀ y y', Q y ≠ 0 → Q y' ≠ 0 →
      ∃ z, Q z ≠ 0 ∧ QuadraticMap.polar Q y z ≠ 0 ∧ QuadraticMap.polar Q z y' ≠ 0) :
    ∃ μ : Kˣ, ∀ v, R v = (μ : K) * Q v := by
  classical
  -- (0) an anisotropic vector exists (else `polarBilin Q = 0`, impossible for a nondegenerate form).
  have hEx : ∃ y, Q y ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hz : QuadraticMap.polarBilin Q = 0 := by
      ext x y
      simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h]
    exact LinearMap.BilinForm.not_nondegenerate_zero K V (hz ▸ hQnd)
  -- (†) the per-anisotropic-`y` identity `Q y · polar R x y = R y · polar Q x y`, for ALL x
  -- (proved on the punctured cone via `nullstellensatz_core`, then extended by linearity over its span).
  have key : ∀ y, Q y ≠ 0 → ∀ x,
      Q y * QuadraticMap.polar R x y = R y * QuadraticMap.polar Q x y := by
    intro y hy x
    have hx : x ∈ Submodule.span K {x | Q x = 0 ∧ QuadraticMap.polar Q x y ≠ 0} := by
      rw [hspan y hy]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨hziso, hzp⟩ := hz
        have hc := nullstellensatz_core Q R (fun v hv => (hcone v).mp hv) hziso (y := y)
        have h0 := (mul_eq_zero.mp hc).resolve_left hzp
        linear_combination -h0
    | zero => simp
    | add a b _ _ pa pb =>
        simp only [QuadraticMap.polar_add_left]
        linear_combination pa + pb
    | smul c a _ pa =>
        simp only [QuadraticMap.polar_smul_left, smul_eq_mul]
        linear_combination c * pa
  -- (step) two `polar`-linked anisotropic vectors have the same ratio `R/Q`.
  have step : ∀ y z, Q y ≠ 0 → Q z ≠ 0 → QuadraticMap.polar Q y z ≠ 0 →
      R y * Q z = R z * Q y := by
    intro y z hy hz hpyz
    have e1 : Q z * QuadraticMap.polar R y z = R z * QuadraticMap.polar Q y z := key z hz y
    have e2 : Q y * QuadraticMap.polar R y z = R y * QuadraticMap.polar Q y z := by
      have h := key y hy z
      rwa [QuadraticMap.polar_comm R z y, QuadraticMap.polar_comm Q z y] at h
    have h3 : (R y * Q z) * QuadraticMap.polar Q y z = (R z * Q y) * QuadraticMap.polar Q y z := by
      linear_combination Q y * e1 - Q z * e2
    exact mul_right_cancel₀ hpyz h3
  -- (const) hence the ratio is constant across ALL anisotropic vectors (via the diameter-≤2 link).
  have const : ∀ y y', Q y ≠ 0 → Q y' ≠ 0 → R y * Q y' = R y' * Q y := by
    intro y y' hy hy'
    obtain ⟨z, hz, hyz, hzy'⟩ := hlink y y' hy hy'
    have s1 : R y * Q z = R z * Q y := step y z hy hz hyz
    have s2 : R z * Q y' = R y' * Q z := step z y' hz hy' hzy'
    have h3 : (R y * Q y') * Q z = (R y' * Q y) * Q z := by
      linear_combination Q y' * s1 + Q y * s2
    exact mul_right_cancel₀ hz h3
  -- (finish) `μ := R y₀ / Q y₀`; `R v = μ Q v` by cases on `Q v = 0` (cone) vs `≠ 0` (constancy).
  obtain ⟨y0, hy0⟩ := hEx
  have hRy0 : R y0 ≠ 0 := fun h => hy0 ((hcone y0).mpr h)
  refine ⟨Units.mk0 (R y0 * (Q y0)⁻¹) (mul_ne_zero hRy0 (inv_ne_zero hy0)), fun v => ?_⟩
  simp only [Units.val_mk0]
  by_cases hv : Q v = 0
  · rw [(hcone v).mp hv, hv, mul_zero]
  · have hc := const v y0 hv hy0
    rw [show R y0 * (Q y0)⁻¹ * Q v = R y0 * Q v * (Q y0)⁻¹ by ring, ← hc,
      mul_assoc, mul_inv_cancel₀ hy0, mul_one]

end Field

end ChainDescent.Nullstellensatz
