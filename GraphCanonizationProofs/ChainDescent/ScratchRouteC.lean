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

**Scope / place in the plan.** This is the **isometry-scheme** discretization at an arbitrary spanning base — the
back-half Route C rides on once `Q` is recovered (`route_c_reconstruct_probe.py`, `vanishDim = 1`) and coordinates are
recovered (`route_c_f1_probe.py`, `T = O_p(Aut)`). The remaining Route-C Lean content (A3 refinement bridge:
the *given* similitude graph refined by the recovered `Q` equals this isometry scheme; F4 iso-invariance of the
recovery) is separate. See `docs/chain-descent-route-c-plan.md` §4/§6.
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

end ChainDescent.RouteC
