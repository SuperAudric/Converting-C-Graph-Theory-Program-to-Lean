/-
# Route C — the spanning-base generalization of the orthogonal-form seal (F5 / A3 first brick)

**What this module builds.** Route C (`docs/chain-descent-route-c-plan.md`) recovers the quadratic form `Q` from the
abstract graph and then works with the **isometry** scheme `O(Q)`, whose discretization at a base is the landed
`reachesRigidOrCameron_viaOrthogonalForm` (`CascadeAffine.lean:2704`). But that theorem uses the **literal standard
frame** `{0, e₁, …, e_d}` (`frameBase`) — and Route C, working from an abstract graph, has **no canonical standard
coordinates**: it must individualize an *iso-invariantly chosen* base. So the necessary first brick is to generalize
the seal from the standard frame to **any base whose difference-vectors span `V`**.

**What it proves (both axiom-clean, `lake env lean`, NOT in `build.sh`):**
* `coords_determine_spanning` — the spanning generalization of the landed `coords_determine` (`CascadeAffine.lean:2640`):
  if `Q`'s polar form is nondegenerate and the `Q`-values `Q v`, `Q (v − s)` agree with `v'` on a set `S` that
  **spans** `V`, then `v = v'`. (Same `Q`-value profile ⟹ same polar coordinates on a spanning set ⟹ by
  nondegeneracy, same vector.) Mirrors `coords_determine`'s proof, replacing the `Pi.basisFun` finish with
  `LinearMap.ext_on` on the spanning set.
* `reachesRigidOrCameron_viaOrthogonalForm_spanning` — the spanning generalization of
  `reachesRigidOrCameron_viaOrthogonalForm`: for any base `T ∋ o` whose difference-vectors `{t̄ − ō : t ∈ T}` span
  `V`, the affine isometry scheme discretizes at `T` and seals via `reachesRigidOrCameron_viaSpielman`. Carries NO
  `hSmallAutThin`. The standard-frame theorem is the special case `T = frameBase`, `o = 0`.
* `isometryScheme_refines_similitudeScheme` (**A3, brick 1**) — since `O(Q) ≤ GO(Q)` (`isometry_le_similitude`), the
  isometry scheme (exact-`Q` relations) refines the given **similitude** graph (isotropy-only relations): equal isometry
  relation ⟹ equal similitude relation. The consistency half of the refinement bridge — the recovered form gives
  relations finer than, and consistent with, the given graph. Pure `H ≤ G ⟹` finer orbitals (no Witt / orbit-structure).

**Scope / place in the plan.** The two spanning theorems are the **isometry-scheme** discretization at an arbitrary
spanning base — the back-half Route C rides on once `Q` is recovered (F1 `route_c_f1_probe.py` / `AffineStructureRecovery`
+ A1 `route_c_reconstruct_probe.py` / `QuadraticFormRecovery`, both DONE + confirmed in C#). `isometryScheme_refines_
similitudeScheme` is A3's brick 1.

**F4 (iso-invariance of the recovered form) — equivariance core now LANDED (F4 section below):**
`recoveredForm_colouring_equivariant` + bricks `similitude_colouring_equivariant` / `similitude_conePreserving`. The one
non-elementary link is `ConeSepDeterminesForm` (same isotropic cone ⟹ scalar-multiple form = A1's `vanishDim=1`
uniqueness), named + carried as a classical citation — so **F4 and A1's Lean side unify into one carried fact**, the
equivariance proved around it. Remaining Route-C open items: that classical carry + the meta-poly bootstrapping (F1
consumes `Aut`, whose poly recovery for this residue is the open T0 problem — see the plan's STATUS "OPEN — meta-poly
bootstrapping"). Full pickup: `docs/chain-descent-route-c-plan.md` STATUS + §6a. See §4 for the preexisting-lemma names.
-/
import ChainDescent.CascadeAffine

namespace ChainDescent.RouteC

open QuadraticMap

variable {p d : ℕ} [Fact p.Prime]

/-- **The spanning generalization of `coords_determine`.** With a nondegenerate polar form, the `Q`-value profile at a
base `S` that **spans** `V` determines the vector: if `Q v = Q v'` and `Q (v − s) = Q (v' − s)` for every `s ∈ S`, and
`span S = ⊤`, then `v = v'`. Proof mirrors `coords_determine` (`CascadeAffine.lean:2640`): the `Q`-value equalities give
`polar Q v s = polar Q v' s` (via `polar_eq_of_sub`), so `polarBilin (v − v')` vanishes on the spanning set `S`, hence
everywhere (`LinearMap.ext_on`), hence — by nondegeneracy — `v = v'`. Generalizes the standard-frame `coords_determine`
to an arbitrary spanning base (cf. the abstract `BranchDepth.spanning_sameExactGram_determines`). -/
theorem coords_determine_spanning (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (hQ : (Q.polarBilin).Nondegenerate) {S : Set (Fin d → ZMod p)}
    (hspan : Submodule.span (ZMod p) S = ⊤)
    {v v' : Fin d → ZMod p}
    (h0 : Q v = Q v')
    (hs : ∀ s ∈ S, Q (v - s) = Q (v' - s)) :
    v = v' := by
  have key : ∀ s ∈ S, Q.polarBilin v s = Q.polarBilin v' s := by
    intro s hsS
    rw [polarBilin_apply_apply, polarBilin_apply_apply, ChainDescent.polar_eq_of_sub,
      ChainDescent.polar_eq_of_sub, h0, hs s hsS]
  have hzero : Q.polarBilin (v - v') = 0 := by
    apply LinearMap.ext_on hspan
    intro x hx
    rw [LinearMap.zero_apply, map_sub, LinearMap.sub_apply, key x hx, sub_self]
  have hsep := hQ.1 (v - v') (fun y => by rw [hzero, LinearMap.zero_apply])
  exact sub_eq_zero.mp hsep

/-- **THE SEAL VIA THE ORTHOGONAL FORM AT A SPANNING BASE (Route C back-half, generalizing Stage B.0).**
For any quadratic form `Q` on `F_p^d` with nondegenerate polar form, and any base `T ∋ o` whose difference-vectors
`{t̄ − ō : t ∈ T}` (`t̄ = affineE.symm t`) **span** `V`, the affine scheme of the isometry group `O(Q)` individualizes
to discrete at `T` and seals. Mechanism (depth-1): under `O(Q)` the orbit-of-difference determines `Q(v − t)`, and the
`Q`-values at the spanning base recover the vector (`coords_determine_spanning`). **Carries NO `hSmallAutThin`.**
Generalizes `reachesRigidOrCameron_viaOrthogonalForm` (`CascadeAffine.lean:2704`) off the literal standard frame
`frameBase` — the generalization Route C needs, since an abstract graph has no canonical standard coordinates and must
individualize an iso-invariantly chosen spanning base. Honest scope: `O(Q)` is the *finer* isometry scheme, not the
given rank-3 SRG `VO^ε` (= similitude `GO(Q)`); the A3 refinement bridge (recovered `Q` refines the given graph to this
scheme) is separate (`docs/chain-descent-route-c-plan.md` §4/§6). Axiom-clean. -/
theorem reachesRigidOrCameron_viaOrthogonalForm_spanning
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} {bound : Nat}
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) (hQ : (Q.polarBilin).Nondegenerate)
    {T : Finset (Fin (p ^ d))} {o : Fin (p ^ d)} (ho : o ∈ T)
    (hspan : Submodule.span (ZMod p)
        ((fun t => ChainDescent.affineE.symm t - ChainDescent.affineE.symm o) '' (↑T : Set (Fin (p ^ d)))) = ⊤)
    (hbound : T.card ≤ bound) :
    ((SchemeBlockRecovered (p ^ d)
          (ChainDescent.affineScheme (ChainDescent.isometryGroup Q) (ChainDescent.neg_mem_isometryGroup Q))
        ∨ AbelianConsumed (p ^ d)
          (ChainDescent.affineScheme (ChainDescent.isometryGroup Q) (ChainDescent.neg_mem_isometryGroup Q)))
        ∨ SchemeRecoveredByDepth (p ^ d)
          (ChainDescent.affineScheme (ChainDescent.isometryGroup Q) (ChainDescent.neg_mem_isometryGroup Q)) bound)
      ∨ IsCameronScheme (p ^ d)
          (ChainDescent.affineScheme (ChainDescent.isometryGroup Q) (ChainDescent.neg_mem_isometryGroup Q)) := by
  have hsep : ∀ u u' : Fin (p ^ d),
      (∀ t ∈ T, ∃ g₀ ∈ ChainDescent.isometryGroup Q,
        g₀ (ChainDescent.affineE.symm u' - ChainDescent.affineE.symm t)
          = ChainDescent.affineE.symm u - ChainDescent.affineE.symm t) → u = u' := by
    intro u u' hh
    -- isometry ⟹ Q-value equality at every base vertex
    have hval : ∀ t ∈ T, Q (ChainDescent.affineE.symm u - ChainDescent.affineE.symm t)
        = Q (ChainDescent.affineE.symm u' - ChainDescent.affineE.symm t) := by
      intro t ht
      obtain ⟨g₀, hg, hgeq⟩ := hh t ht
      have hgx := hg (ChainDescent.affineE.symm u' - ChainDescent.affineE.symm t)
      rw [hgeq] at hgx
      exact hgx
    -- centre at o and apply the spanning determiner
    have hc : ChainDescent.affineE.symm u - ChainDescent.affineE.symm o
        = ChainDescent.affineE.symm u' - ChainDescent.affineE.symm o := by
      refine coords_determine_spanning Q hQ hspan (hval o ho) (fun s hsS => ?_)
      obtain ⟨t, htT, rfl⟩ := hsS
      have e1 : (ChainDescent.affineE.symm u - ChainDescent.affineE.symm o)
              - (ChainDescent.affineE.symm t - ChainDescent.affineE.symm o)
            = ChainDescent.affineE.symm u - ChainDescent.affineE.symm t := by abel
      have e2 : (ChainDescent.affineE.symm u' - ChainDescent.affineE.symm o)
              - (ChainDescent.affineE.symm t - ChainDescent.affineE.symm o)
            = ChainDescent.affineE.symm u' - ChainDescent.affineE.symm t := by abel
      rw [e1, e2]
      exact hval t (Finset.mem_coe.mp htT)
    exact ChainDescent.affineE.symm.injective (sub_left_inj.mp hc)
  exact ChainDescent.reachesRigidOrCameron_viaSpielman _
    ⟨T, hbound,
      ChainDescent.discrete_affineScheme_of_jointSeparates
        (ChainDescent.isometryGroup Q) (ChainDescent.neg_mem_isometryGroup Q) hsep⟩

/-! ## A3 — the refinement bridge (recovered `Q` upgrades the similitude graph to the isometry scheme)

The GIVEN forms graph is the **similitude** scheme `affineScheme (similitudeGroup Q)` — its relation records
only the isotropy class of a difference (the `GO(Q)`-orbit). Route C recovers `Q` (F1 + A1, confirmed in C#)
and works with the **isometry** scheme `affineScheme (isometryGroup Q)`, whose relation is the *exact*
`Q`-value of the difference (the `O(Q)`-orbit) — and which the landed
`reachesRigidOrCameron_viaOrthogonalForm_spanning` discretizes at a spanning base. The bridge has two halves:
this brick (the isometry scheme *refines* the given graph — so using the recovered form is consistent, not
fabricated) and F4 (the recovered form is iso-invariant — separate). -/

/-- **A3, brick 1 — the isometry scheme refines the similitude scheme.** Since `O(Q) ≤ GO(Q)`
(`isometry_le_similitude`), the affine orbital scheme of the isometry group is FINER than that of the
similitude group: whenever the isometry scheme assigns two pairs the same relation, so does the similitude
scheme. This is the formal sense in which the recovered form `Q` (whose exact-value-of-difference data IS the
isometry relation) *refines* the given similitude graph (isotropy-only) rather than fabricating structure —
the consistency half of the Route-C bridge. Pure `H ≤ G ⟹` finer orbitals; no Witt / orbit-structure needed.
Axiom-clean. -/
theorem isometryScheme_refines_similitudeScheme
    (Q : QuadraticForm (ZMod p) (Fin d → ZMod p)) {x y x' y' : Fin (p ^ d)}
    (h : (ChainDescent.affineScheme (ChainDescent.isometryGroup Q)
            (ChainDescent.neg_mem_isometryGroup Q)).relOfPair x y
        = (ChainDescent.affineScheme (ChainDescent.isometryGroup Q)
            (ChainDescent.neg_mem_isometryGroup Q)).relOfPair x' y') :
    (ChainDescent.affineScheme (ChainDescent.similitudeGroup Q)
          (ChainDescent.neg_mem_similitudeGroup Q)).relOfPair x y
      = (ChainDescent.affineScheme (ChainDescent.similitudeGroup Q)
          (ChainDescent.neg_mem_similitudeGroup Q)).relOfPair x' y' := by
  rw [ChainDescent.affineScheme_relOfPair_eq_iff (ChainDescent.isometryGroup Q)
        (ChainDescent.neg_mem_isometryGroup Q),
    ChainDescent.orbMk_affine_eq_iff] at h
  rw [ChainDescent.affineScheme_relOfPair_eq_iff (ChainDescent.similitudeGroup Q)
        (ChainDescent.neg_mem_similitudeGroup Q),
    ChainDescent.orbMk_affine_eq_iff]
  obtain ⟨g₀, hg₀, hg⟩ := h
  exact ⟨g₀, ChainDescent.isometry_le_similitude Q hg₀, hg⟩

/-! ## F4 — iso-invariance of the recovered form (the recovered-`Q` colouring is relabeling-equivariant)

The Route-C spine (recover `Q` → isometry scheme refines the graph (A3 brick 1) → discretizes at a
spanning base (`viaOrthogonalForm_spanning`)) yields an iso-invariant discrete colouring **only if** the
recovered `Q` is itself iso-invariant. Concretely: a graph isomorphism between two affine-polar graphs is,
after F1 coordinatization, a linear map `g` carrying the isotropic cone of `Q` onto the cone of `Q'`
(`Q v = 0 ↔ Q' (g v) = 0`) — and F4 must conclude that the recovered-`Q` **difference colouring** is then
carried correspondingly (`Q' (g u − g t) = μ · Q (u − t)`), the `forcedNode_relabel` analog for the form.

**The honest split (this resolves the plan's "only F4 remains" — F4 and A1's Lean side are two faces of
one classical fact).** The chain *graph iso → linear `g` with cone-preservation → `g` is a form similitude
→ colouring equivariant* has exactly one non-elementary link: **cone-preservation ⟹ similitude**, i.e.
"a nondegenerate quadric determines its quadratic form up to a nonzero scalar". That is precisely A1's
finite-geometry content (probe-confirmed `vanishDim = 1`, `route_c_reconstruct_probe.py`) and is carried
here as the scoped named predicate `ConeSepDeterminesForm` — a classical citation, same discipline as
Witt/G3. Everything else (the similitude ⟹ equivariant-colouring identity, and similitude ⟹ cone-preserving)
is elementary linear algebra, proved below axiom-clean. So F4 lands its genuine content (the equivariance)
and names — rather than hides — the one classical carry it shares with A1. -/

/-- **A1 / F4's shared classical carry — a nondegenerate quadric determines its form up to a scalar.**
If `Q` and `R` have the same isotropic cone (`Q v = 0 ↔ R v = 0` for all `v`), then `R` is a nonzero
scalar multiple of `Q`. This is the finite-geometry uniqueness behind A1 (the degree-2 forms vanishing
on the cone are exactly `⟨Q⟩`, `vanishDim = 1`, probe-confirmed for nondegenerate `Q`, `d ≥ 4`); carried
as a citation (it is a classical fact, not re-proved here). Scoped to the two forms in question so it is
**true** (the unrestricted `∀ Q R` form is false for degenerate/low-dim forms — cf. the vacuity trap). -/
def ConeSepDeterminesForm (Q R : QuadraticForm (ZMod p) (Fin d → ZMod p)) : Prop :=
  (∀ v, Q v = 0 ↔ R v = 0) → ∃ μ : (ZMod p)ˣ, ∀ v, R v = (μ : ZMod p) * Q v

/-- **F4 brick 1 — a form similitude carries the difference colouring (equivariance, provable).** If `g`
is a similitude from `Q` to `Q'` (`Q' (g v) = μ · Q v`), then the recovered-`Q` **difference** colouring
transports by the same scalar: `Q' (g u − g t) = μ · Q (u − t)`. This is the exact sense in which the
isometry-scheme colouring (a pair `(u,t)` coloured by `Q`-value-of-difference) is *equivariant* under the
linear part of a graph iso — the load-bearing content of F4. Pure linearity: `g u − g t = g (u − t)`. -/
theorem similitude_colouring_equivariant
    (Q Q' : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)} {μ : ZMod p}
    (hsim : ∀ v, Q' (g v) = μ * Q v) (u t : Fin d → ZMod p) :
    Q' (g u - g t) = μ * Q (u - t) := by
  rw [← map_sub]
  exact hsim (u - t)

/-- **F4 brick 1b — a form similitude preserves the cone (consistency, provable).** If `g` is a
similitude from `Q` to `Q'` with unit factor `μ`, then `g` carries the `Q`-cone to the `Q'`-cone
(`Q' (g v) = 0 ↔ Q v = 0`). The converse (cone-preservation ⟹ similitude) is the carried
`ConeSepDeterminesForm`. Together they say: for nondegenerate forms, "similitude" and "cone-preserving"
coincide — which is why recovering `Q` up to scalar (A1) is well-defined. -/
theorem similitude_conePreserving
    (Q Q' : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)} {μ : (ZMod p)ˣ}
    (hsim : ∀ v, Q' (g v) = (μ : ZMod p) * Q v) (v : Fin d → ZMod p) :
    Q' (g v) = 0 ↔ Q v = 0 := by
  rw [hsim v, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (Units.ne_zero μ)
    · exact h
  · exact fun h => Or.inr h

/-- **F4 — the recovered-`Q` difference colouring is iso-invariant (equivariant under a graph iso's
linear part).** Given the linear part `g` of a graph isomorphism (which carries the `Q`-cone to the
`Q'`-cone: `Q v = 0 ↔ Q' (g v) = 0`) and the classical uniqueness `ConeSepDeterminesForm` (A1's carried
fact), the recovered difference colouring transports with a single global scalar `μ`:
`Q' (g u − g t) = μ · Q (u − t)` for all `u, t`. So canonicalizing via the recovered form produces a
*canonical* (iso-invariant) colouring — the property the poly canonicalization claim needs, and the one
the banked seal does **not** supply (discreteness does not transfer to the coarser similitude scheme).
Composes with A3 brick 1 (`isometryScheme_refines_similitudeScheme`) and `viaOrthogonalForm_spanning` to
give: iso-invariant discrete colouring at a spanning base ⟹ (meta) poly canonical labelling. Axiom-clean;
the only non-elementary input is the named classical carry `ConeSepDeterminesForm`. -/
theorem recoveredForm_colouring_equivariant
    (Q Q' : QuadraticForm (ZMod p) (Fin d → ZMod p))
    {g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)}
    (hcone : ∀ v, Q v = 0 ↔ Q' (g v) = 0)
    (hclassical : ConeSepDeterminesForm Q
      (Q'.comp (g : (Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p)))) :
    ∃ μ : (ZMod p)ˣ, ∀ u t : Fin d → ZMod p, Q' (g u - g t) = (μ : ZMod p) * Q (u - t) := by
  obtain ⟨μ, hμ⟩ := hclassical hcone
  exact ⟨μ, fun u t => similitude_colouring_equivariant Q Q' (fun v => hμ v) u t⟩

end ChainDescent.RouteC
