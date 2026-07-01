/-
# δ′ dominator-closure on the forms graph — the full-base pinning substrate + the dimensional wall

**What this module builds.** The recovery route's ITEM B (`docs/chain-descent-recovery-route.md` §6) picks the δ′
dominator-closure lead — the forced-triangle route — for the poly crux. The abstract δ′ engine is fully built
(`CascadeAffine.lean` §S-bridge-δ: `DominatorReachable`, `dominatorReachable_of_rank`, the affine forced-triangle
criterion `affineScheme_interNum_eq_one_of_unique`, the seal consumer `separatesAtBoundedBase_of_dominatorClosure`) and
has been *discharged end-to-end* on the 1-dimensional cyclotomic family (`dominatorReachable_G0pow_neg` /
`reachesRigidOrCameron_viaG0powNeg`). This module scopes and lands the **forms-graph** (`VO^ε`) substrate.

**The affine forced-triangle premise, geometrically.** `affineScheme_interNum_eq_one_of_unique` pins `γ` from `α, β`
when `γ` is the unique `u` with `u − α ∼ γ − α` and `β − u ∼ β − γ` (`∼` = the `G₀`-orbit of the difference). For the
**isometry group** `G₀ = GO(Q)`, Witt's theorem makes `∼` exactly *equal `Q`-value*: `x ∼ y ↔ Q x = Q y`. So the δ′
pinning of `γ` by a set of already-reached points `R` reads: `γ` is the unique `u` with `Q (u − r) = Q (γ − r)` for all
`r ∈ R`. This module proves the **full-base** instance: at a base whose span is `⊤`, the exact-`Q` profile pins the
vertex (`spanning_exactQ_determines`) — the geometric core of "the δ′ closure completes from a spanning base."

**★ THE DIMENSIONAL WALL (the scoping finding).** The δ′ *step* (`DominatorReachable.step`) pins `γ` from just **two**
points `α, β` — i.e. **two** scalar `Q`-constraints `Q(u−α)=Q(γ−α)`, `Q(β−u)=Q(β−γ)`. Two quadratic constraints cut out
a codimension-`≤2` subvariety of `V = K^d`, which has `≈ q^{d−2}` points — **not** a singleton once `d ≥ 3`. So the raw
two-point forced triangle *cannot pin* on `VO^ε` (`d ≥ 4`); the closure does not complete from a bounded base in the
scheme's own colours. This is the **same wall** that forced the seal onto the two-round pair form `χ(det G₂)` (a
single relation among the rank-3 SRG colours has intersection number `Θ(q^{d−2})`), and it is exactly why the
successful δ′ discharge (`dominatorReachable_G0pow_neg`) is the **dimension-1** line (where two points *do* pin, by the
cross-ratio) and why the rainbow variant "cannot reach node 4's rank-3 SRG core". `spanning_exactQ_determines` shows
the pinning *does* hold with the **full** `O(d)` base — full-base pinning, not the two-point step.

**Consequence for the route.** On `VO^ε` the δ′ closure needs either (a) the **extension** relations — pinning in
`X_T` after individualizing a base, where each point carries the whole `T`-profile
(`reachesRigidOrCameron_viaExtensionDominatorClosure`, which carries the `hcatch` 1-WL↔fiber catch-up), or (b) a
**multi-point** pinning engine (full-base, as here). Both reduce to the *same* open core as the poly crux: does the
`isoClass`/`Q`-value profile to an `O(d)` base determine the vertex — the WL-orbit defect / cell-discretisation. So δ′
**restructures** the crux as an inductive forced-triangle closure; it does not dodge it. What it *does* buy: the
full-base pinning here is unconditional geometry (reuses `spanning_sameExactGram_determines`), isolating the open
content to the **fusion** step (rank-3 similitude vs. exact `Q`-value) — the 2-round count the seal already handles.

Reuses `ChainDescent.BranchDepth.spanning_sameExactGram_determines` (§1 of `ScratchBranchDepth`). Axiom-clean
`[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchBranchDepth

namespace ChainDescent.DominatorForms

open ChainDescent.Wall QuadraticMap

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  {Q : QuadraticForm K V}

/-- **The polar↔`Q`-value identity.** `polar Q x s = Q x + Q s − Q (x − s)`. The bridge between the exact Gram data
(`polar`, what `spanning_sameExactGram_determines` consumes) and the `Q`-value-of-difference data (what the affine
isometry scheme's relation is). Pure quadratic-map algebra. -/
theorem polar_eq_qSub (x s : V) : QuadraticMap.polar Q x s = Q x + Q s - Q (x - s) := by
  have hn : QuadraticMap.polar Q x (-s) = - QuadraticMap.polar Q x s := QuadraticMap.polar_neg_right Q x s
  simp only [QuadraticMap.polar] at hn ⊢
  rw [QuadraticMap.map_neg, ← sub_eq_add_neg] at hn
  linear_combination hn

/-- **★ Full-base forced-triangle pinning (exact-`Q` form).** At a base `S` whose span is `⊤`, with a nondegenerate
polar form, the **exact `Q`-value profile** pins the vertex: if `Q t = Q t'` and `Q (t − s) = Q (t' − s)` for every
`s ∈ S`, then `t = t'`. This is `spanning_sameExactGram_determines` (§1) re-expressed in the affine isometry scheme's
own relation language (`Q`-value of differences = `GO(Q)`-orbit of difference, by Witt) — the geometric content of "the
δ′ closure completes from a spanning base", via **full-base** pinning. (The two-point δ′ step gives only two of these
constraints; see the module header's dimensional wall.) -/
theorem spanning_exactQ_determines {S : Finset V}
    (hnd : (Q.polarBilin).Nondegenerate)
    (hspan : Submodule.span K (↑S : Set V) = ⊤)
    {t t' : V} (hQ0 : Q t = Q t')
    (hqs : ∀ s ∈ (↑S : Set V), Q (t - s) = Q (t' - s)) : t = t' := by
  refine ChainDescent.BranchDepth.spanning_sameExactGram_determines hnd hspan ⟨hQ0, fun s hs => ?_⟩
  rw [polar_eq_qSub, polar_eq_qSub, hQ0, hqs s hs]

/-- **The two-point premise is a projection of the full-base one.** The δ′ step's data — `Q`-values to two points
`α, β` — is the `S = {α, β}` instance of `spanning_exactQ_determines`'s hypothesis. When `{α, β}` does **not** span
(always, for `d ≥ 3`), the hypothesis `hspan` fails and the pinning conclusion is unavailable — the formal shadow of
the dimensional wall: two points carry two constraints, a spanning base carries `d`. Records that the gap between the
δ′ step and the pinning is exactly *spanning*. -/
theorem twoPoint_insufficient_unless_spans {α β t t' : V}
    (hnd : (Q.polarBilin).Nondegenerate)
    (hspan : Submodule.span K (↑({α, β} : Finset V) : Set V) = ⊤)
    (hQ0 : Q t = Q t')
    (hqs : ∀ s ∈ (↑({α, β} : Finset V) : Set V), Q (t - s) = Q (t' - s)) : t = t' :=
  spanning_exactQ_determines hnd hspan hQ0 hqs

end ChainDescent.DominatorForms
