/-
# Route C — the spanning-base generalization of the orthogonal-form seal (F5 / A3 first brick)

**What this module builds.** Route C (`docs/chain-descent-route-c-plan.md`) recovers the quadratic form `Q` from the
abstract graph and then works with the **isometry** scheme `O(Q)`, whose discretization at a base is the landed
`reachesRigidOrCameron_viaOrthogonalForm` (`CascadeAffine.lean:2704`). But that theorem uses the **literal standard
frame** `{0, e₁, …, e_d}` (`frameBase`) — and Route C, working from an abstract graph, has **no canonical standard
coordinates**: it must individualize an *iso-invariantly chosen* base. So the necessary first brick is to generalize
the seal from the standard frame to **any base whose difference-vectors span `V`**.

**What it proves (all axiom-clean, in `build.sh`; the four Route-C form-family seals live in this module):**
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
non-elementary link is `NondegQuadricDeterminesForm` (same isotropic cone ⟹ scalar-multiple form = A1's `vanishDim=1`
uniqueness; the EXACT scoped classical theorem, `p≠2`/`d≥4`), named + carried as a classical citation (Hirschfeld,
projective Nullstellensatz for a nondegenerate quadric) — so **F4 and A1's Lean side unify into one carried fact**, the
equivariance proved around it. Remaining Route-C open items: that classical carry + the meta-poly bootstrapping (F1
consumes `Aut`, whose poly recovery for this residue is the open T0 problem — see the plan's STATUS "OPEN — meta-poly
bootstrapping"). Full pickup: `docs/chain-descent-route-c-plan.md` STATUS + §6a. See §4 for the preexisting-lemma names.
-/
import ChainDescent.CascadeAffine
import ChainDescent.NullstellensatzHlink

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

/-- **The generic refinement bridge — a smaller linear group gives a finer affine scheme.** For any two
subgroups `H ≤ G` of `GL(V)` (both containing `−1`), the affine orbital scheme of `H` is FINER than that of
`G`: whenever the `H`-scheme assigns two pairs the same relation, so does the `G`-scheme. Pure `H ≤ G ⟹`
finer orbitals — the `H`-orbit of a difference is contained in its `G`-orbit. This is the reusable core of
every Route-C refinement brick (single-form `isometryScheme_refines_similitudeScheme`, multi-form
`multiIsometryScheme_refines_coneScheme`): recovering a *smaller* group refines, never fabricates. Axiom-clean. -/
theorem affineScheme_refines_of_le
    {H G : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))} (hHG : H ≤ G)
    (hnegH : LinearEquiv.neg (ZMod p) ∈ H) (hnegG : LinearEquiv.neg (ZMod p) ∈ G)
    {x y x' y' : Fin (p ^ d)}
    (h : (ChainDescent.affineScheme H hnegH).relOfPair x y
        = (ChainDescent.affineScheme H hnegH).relOfPair x' y') :
    (ChainDescent.affineScheme G hnegG).relOfPair x y
      = (ChainDescent.affineScheme G hnegG).relOfPair x' y' := by
  rw [ChainDescent.affineScheme_relOfPair_eq_iff H hnegH, ChainDescent.orbMk_affine_eq_iff] at h
  rw [ChainDescent.affineScheme_relOfPair_eq_iff G hnegG, ChainDescent.orbMk_affine_eq_iff]
  obtain ⟨g₀, hg₀, hg⟩ := h
  exact ⟨g₀, hHG hg₀, hg⟩

/-- **A3, brick 1 — the isometry scheme refines the similitude scheme.** Since `O(Q) ≤ GO(Q)`
(`isometry_le_similitude`), the affine orbital scheme of the isometry group is FINER than that of the
similitude group: whenever the isometry scheme assigns two pairs the same relation, so does the similitude
scheme. This is the formal sense in which the recovered form `Q` (whose exact-value-of-difference data IS the
isometry relation) *refines* the given similitude graph (isotropy-only) rather than fabricating structure —
the consistency half of the Route-C bridge. A one-line corollary of the generic `affineScheme_refines_of_le`.
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
          (ChainDescent.neg_mem_similitudeGroup Q)).relOfPair x' y' :=
  affineScheme_refines_of_le (ChainDescent.isometry_le_similitude Q)
    (ChainDescent.neg_mem_isometryGroup Q) (ChainDescent.neg_mem_similitudeGroup Q) h

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
here as the **exact scoped** named premise `NondegQuadricDeterminesForm` (`p ≠ 2`, `4 ≤ d`, `Q` nondeg — the
range where it is TRUE; the unrestricted form is false at `d=3,q=3`) — a classical citation, same discipline
as Witt/G3. Everything else (the similitude ⟹ equivariant-colouring identity, and similitude ⟹ cone-preserving)
is elementary linear algebra, proved below axiom-clean. So F4 lands its genuine content (the equivariance)
and names — rather than hides — the one classical carry it shares with A1. -/

/-- **A1 / F4's shared classical carry — a nondegenerate quadric determines its form up to a scalar
(the EXACT, correctly-scoped classical theorem, carried as a citation).** For `p` odd and `d ≥ 4`: any
two quadratic forms `Q`, `R` on `𝔽_p^d` with `Q` nondegenerate and the **same isotropic cone**
(`Q v = 0 ↔ R v = 0`) satisfy `R = μ·Q` for a nonzero scalar `μ`. Equivalently, the degree-2 forms
vanishing on the quadric `Q = 0` are exactly `⟨Q⟩` (`vanishDim = 1`); equivalently, the vanishing ideal
of a nondegenerate quadric is principal.

**Citation, not a Lean proof.** This is classical finite geometry (Hirschfeld, *Projective Geometries
over Finite Fields*, quadrics chapter; the projective Nullstellensatz for a nondegenerate quadric).
Mathlib has no quadric zero-locus result, so — following the project discipline for cited results
(`Theorem41Statement`, `PrimitiveCCClassification`) — it is carried as a **named premise** threaded to
the capstone, NOT proved here.

**The scope is load-bearing and makes it EXACTLY TRUE (not a vacuity trap).** The unrestricted `∀ Q R`
form is FALSE: at `d = 3, q = 3` a nondegenerate conic has only `q+1 = 4` points, which lie on a pencil
of conics (`vanishDim = 2`). The hypotheses `p ≠ 2`, `4 ≤ d`, `Q.polarBilin.Nondegenerate` are exactly
the range where it holds — probe-confirmed `vanishDim = 1` for `d = 4,6,8`, `q = 3,5,7,11`
(`route_c_reconstruct_probe.py`), and covering all affine-polar `VO^ε_{2m}` (`m ≥ 2`). The bounds are
built into the statement as antecedents so a `p = 2` / `d < 4` instance is (correctly) vacuous. -/
def NondegQuadricDeterminesForm (p d : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 4 ≤ d → ∀ (Q R : QuadraticForm (ZMod p) (Fin d → ZMod p)),
    (Q.polarBilin).Nondegenerate → (∀ v, Q v = 0 ↔ R v = 0) →
      ∃ μ : (ZMod p)ˣ, ∀ v, R v = (μ : ZMod p) * Q v

/-- **The Nullstellensatz citation, DISCHARGED (even `d`).** `NondegQuadricDeterminesForm p d` is no longer
an assumption but a theorem: for odd prime `p` and even `4 ≤ d`, a nondegenerate quadric on `(ZMod p)^d` is
determined up to a `(ZMod p)ˣ` scalar by its isotropic cone. Proof = `nondegQuadric_zmod_of_even`
(`ChainDescent.Nullstellensatz`; structural route hspan + hlink + Gauss-sum counting; axiom-clean). Every
Route-C instantiation is even-dimensional (`VO^ε_{2m}`, `m ≥ 2`), so `hev : Even d` is always available; the
`even`-scope is the exact range the structural section count (`sec_aniso`, odd `u^⊥`) covers. -/
theorem nondegQuadricDeterminesForm_of_even (hp : p ≠ 2) (hev : Even d) :
    NondegQuadricDeterminesForm p d :=
  fun _ hd Q R hQnd hcone =>
    ChainDescent.Nullstellensatz.nondegQuadric_zmod_of_even p d hp hev hd Q R hQnd hcone

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
`NondegQuadricDeterminesForm`. Together they say: for nondegenerate forms, "similitude" and "cone-preserving"
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
`Q'`-cone: `Q v = 0 ↔ Q' (g v) = 0`), the nondegeneracy of `Q`, and — for even `d` — the now-**discharged**
quadric Nullstellensatz `nondegQuadricDeterminesForm_of_even` (A1's uniqueness; no longer a premise), the
recovered difference colouring transports with a single global scalar `μ`: `Q' (g u − g t) = μ · Q (u − t)`
for all `u, t`. So canonicalizing via the recovered form produces a *canonical* (iso-invariant) colouring —
the property the poly canonicalization claim needs, and the one the banked seal does **not** supply
(discreteness does not transfer to the coarser similitude scheme). Composes with A3 brick 1
(`isometryScheme_refines_similitudeScheme`) and `viaOrthogonalForm_spanning` to give: iso-invariant
discrete colouring at a spanning base ⟹ (meta) poly canonical labelling. Axiom-clean; the Nullstellensatz
input is now proved outright (`ChainDescent.Nullstellensatz.nondegQuadric_zmod_of_even`), so only the
elementary `hev : Even d` (always available for `VO^ε_{2m}`) is carried. -/
theorem recoveredForm_colouring_equivariant
    (hp : p ≠ 2) (hd : 4 ≤ d) (hev : Even d)
    (Q Q' : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (hQ : (Q.polarBilin).Nondegenerate)
    {g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)}
    (hcone : ∀ v, Q v = 0 ↔ Q' (g v) = 0) :
    ∃ μ : (ZMod p)ˣ, ∀ u t : Fin d → ZMod p, Q' (g u - g t) = (μ : ZMod p) * Q (u - t) := by
  obtain ⟨μ, hμ⟩ := nondegQuadricDeterminesForm_of_even hp hev hp hd Q
    (Q'.comp (g : (Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p))) hQ hcone
  exact ⟨μ, fun u t => similitude_colouring_equivariant Q Q' (fun v => hμ v) u t⟩

/-! ## F4 citation-free — the vanishing-space (`W`) route to partition iso-invariance (`q = p`)

`recoveredForm_colouring_equivariant` above concludes the **single-scalar** identity `Q'(g u − g t) = μ · Q(u − t)`,
which asserts `dim W(Q) = 1` (the degree-2 forms vanishing on `cone(Q)` are exactly `⟨Q⟩`) — the projective
Nullstellensatz, carried as `NondegQuadricDeterminesForm`. But F4's actual job — **iso-invariance of the recovered
colour partition** — needs no dimension count. Colour a pair `(u,t)` by the evaluation `F ↦ F(u−t)` over the whole
degree-2 **vanishing space** `W(Q) = {F | F ≡ 0 on cone(Q)}`, an *intrinsic* invariant of the graph (it is read off
the connection set from the origin). A cone-preserving linear iso `g` induces a canonical linear iso `W(Q') ≅ W(Q)`
by pullback `F' ↦ F'∘g` — needing only cone-preservation + `g` bijective, **NO dimension count** — so the `W`-colour
partition transports. And since `Q ∈ W(Q)`, the `W`-colouring **refines** the `Q`-colouring, so the
`coords_determine` separation still fires. This discharges the F4 iso-invariance object from
`NondegQuadricDeterminesForm` (and `JointVarietyDeterminesFamily`, via the generic core) at `q = p`; the citations
remain needed only for the strictly stronger `|Aut|`-naming statement `Aut = AΓO(Q)` (the C#/meta side — see
`chain-descent-citation-discharge.md` §3.2). The core is generic over an arbitrary "cone" predicate `C`, so it
serves both the single quadric (`C v := Q v = 0`) and the multi-form family (`C v := ∀ k, Qs k v = 0`). -/

/-- **The load-bearing pullback (`W`-transport), generic in the cone predicate.** If `g` carries `cone(C)` to
`cone(C')` (`C v ↔ C' (g v)`), then pulling a form `F'` vanishing on `cone(C')` back by `g` gives a form vanishing
on `cone(C)`: `F' ∈ W(C') ⟹ F'∘g ∈ W(C)`. Elementary (`comp_apply` + the cone equivalence); no dimension count,
no citation. The `≅` half of the vanishing-space transport (the other half is the same lemma at `g.symm`). -/
theorem vanishingForm_transport_gen {C C' : (Fin d → ZMod p) → Prop}
    (g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) (hcone : ∀ v, C v ↔ C' (g v))
    (F' : QuadraticForm (ZMod p) (Fin d → ZMod p)) (hF' : ∀ v, C' v → F' v = 0) :
    ∀ v, C v → (F'.comp (g : (Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p))) v = 0 := by
  intro v hv
  rw [QuadraticMap.comp_apply]
  exact hF' (g v) ((hcone v).mp hv)

/-- **F4 citation-free payoff (generic) — the recovered `W`-colour partition is iso-invariant.** Two source pairs
are indistinguishable by the whole vanishing space `W(C)` **iff** their `g`-images are indistinguishable by `W(C')`.
Proved by pulling each vanishing form across `g` (`vanishingForm_transport_gen`) and its inverse `g.symm` — NO
`NondegQuadricDeterminesForm`, NO dimension count. This is the iso-invariance F4 actually needs (the recovered
colouring is a canonical refinement of the graph); the scalar-`μ` / injective-`Φ` statements
(`recoveredForm_colouring_equivariant`, `recoveredFamily_colouring_equivariant`) are the strictly stronger
`|Aut|`-naming forms that still carry the citation. -/
theorem recoveredForm_partition_isoInvariant_gen {C C' : (Fin d → ZMod p) → Prop}
    (g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) (hcone : ∀ v, C v ↔ C' (g v))
    (u t u' t' : Fin d → ZMod p) :
    (∀ F : QuadraticForm (ZMod p) (Fin d → ZMod p), (∀ v, C v → F v = 0) →
        F (u - t) = F (u' - t')) ↔
      (∀ F' : QuadraticForm (ZMod p) (Fin d → ZMod p), (∀ v, C' v → F' v = 0) →
        F' (g u - g t) = F' (g u' - g t')) := by
  -- the reversed cone equivalence (via g.symm), for the ← direction
  have hcone_rev : ∀ w, C' w ↔ C (g.symm w) := by
    intro w
    have h := (hcone (g.symm w)).symm
    rwa [LinearEquiv.apply_symm_apply] at h
  constructor
  · intro h F' hF'
    have hval : ∀ a b : Fin d → ZMod p,
        (F'.comp (g : (Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p))) (a - b) = F' (g a - g b) := by
      intro a b; rw [QuadraticMap.comp_apply, LinearEquiv.coe_coe, map_sub]
    rw [← hval u t, ← hval u' t']
    exact h _ (vanishingForm_transport_gen g hcone F' hF')
  · intro h F hF
    have hval' : ∀ a b : Fin d → ZMod p,
        (F.comp (g.symm : (Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p))) (g a - g b) = F (a - b) := by
      intro a b
      rw [QuadraticMap.comp_apply, LinearEquiv.coe_coe, map_sub,
        LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rw [← hval' u t, ← hval' u' t']
    exact h _ (vanishingForm_transport_gen g.symm hcone_rev F hF)

/-- **F4 citation-free — single quadric.** The recovered `W(Q)`-colour partition of a nondegenerate affine-polar
graph is iso-invariant under a cone-preserving linear iso `g`, with **no `NondegQuadricDeterminesForm`**. The
`C v := Q v = 0` specialization of `recoveredForm_partition_isoInvariant_gen`. -/
theorem recoveredForm_partition_isoInvariant
    (Q Q' : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
    (hcone : ∀ v, Q v = 0 ↔ Q' (g v) = 0) (u t u' t' : Fin d → ZMod p) :
    (∀ F : QuadraticForm (ZMod p) (Fin d → ZMod p), (∀ v, Q v = 0 → F v = 0) →
        F (u - t) = F (u' - t')) ↔
      (∀ F' : QuadraticForm (ZMod p) (Fin d → ZMod p), (∀ v, Q' v = 0 → F' v = 0) →
        F' (g u - g t) = F' (g u' - g t')) :=
  recoveredForm_partition_isoInvariant_gen (C := fun v => Q v = 0) (C' := fun v => Q' v = 0) g hcone u t u' t'

/-- **The `W`-colouring refines the `Q`-colouring** (so the discharge does not lose separation). Since
`Q ∈ W(Q)` (a form vanishes on its own cone), any two pairs indistinguishable by the whole vanishing space are in
particular `Q`-indistinguishable — hence anything `coords_determine` separates via the `Q`/isometry colouring, the
citation-free `W`-colouring separates too. Trivial (`F := Q`), but it closes the "separation still fires" half. -/
theorem vanishingColour_refines_form (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (u t u' t' : Fin d → ZMod p)
    (h : ∀ F : QuadraticForm (ZMod p) (Fin d → ZMod p), (∀ v, Q v = 0 → F v = 0) →
        F (u - t) = F (u' - t')) :
    Q (u - t) = Q (u' - t') :=
  h Q (fun _ hv => hv)

/-! ## F2 — the `q = pᵉ` semilinear (Frobenius / ΓL) seam

For `q = p` (prime) the whole spine above works over `ZMod p` because the additive structure F1 recovers
*is* the `𝔽_p`-vector space. For `q = pᵉ` (`e > 1`) the vertex set is `𝔽_q^d`, and the crucial new fact is
that a graph isomorphism between two `𝔽_q`-affine-polar graphs is only `𝔽_p`-**semilinear**: by the
fundamental theorem of projective geometry its linear part is `g = M ∘ σ̂`, where `M` is `𝔽_q`-linear and
`σ̂` is the coordinate-wise action of a field automorphism `σ ∈ Gal(𝔽_q/𝔽_p)` (the "Γ" in `AΓO`). So the
recovered form transports up to a scalar **and** a field automorphism: `Q'(g u − g t) = μ · σ(Q(u − t))`.
This section proves that equivariance identity (the semilinear analog of F4), field-generically over `K`.
The recovery of the `𝔽_q`-structure itself is subsumed by the geometric coordinatization (§7a / R1 —
Buekenhout–Shult recovers the projective space *over `𝔽_q`*, field included). -/

section F2
variable {K : Type*} [Field K] [Fintype K] {d : ℕ}
open QuadraticMap

/-- The coordinate-wise action of a field endomorphism `σ` on `V = Fin d → K` — the semilinear part
of a collineation of `AG(d, q)` (`x ↦ σ(x)` in each coordinate). -/
def frobVec (σ : K →+* K) (x : Fin d → K) : Fin d → K := fun i => σ (x i)

omit [Fintype K] in
/-- `σ̂` is additive (it is a ring hom applied coordinate-wise): `σ̂(u − t) = σ̂ u − σ̂ t`. This is what
makes the semilinear equivariance identity go through. -/
theorem frobVec_sub (σ : K →+* K) (u t : Fin d → K) :
    frobVec σ (u - t) = frobVec σ u - frobVec σ t := by
  funext i; simp only [frobVec, Pi.sub_apply, map_sub]

omit [Fintype K] in
/-- **F2 brick 1 — a semi-similitude carries the difference colouring (equivariance, provable).** If
`g = M ∘ σ̂` is a semi-similitude from `Q` to `Q'` (`Q'(M(σ̂ v)) = μ · σ(Q v)`), then the recovered
difference colouring transports by the scalar `μ` **and** the field automorphism `σ`:
`Q'(M(σ̂ u) − M(σ̂ t)) = μ · σ(Q(u − t))`. Pure structure: `M` linear + `σ̂` additive ⟹
`M(σ̂ u) − M(σ̂ t) = M(σ̂(u − t))`. The semilinear analog of `similitude_colouring_equivariant`. -/
theorem semisimilitude_colouring_equivariant
    (Q Q' : QuadraticForm K (Fin d → K))
    (M : (Fin d → K) ≃ₗ[K] (Fin d → K)) (σ : K →+* K) {μ : K}
    (hss : ∀ v, Q' (M (frobVec σ v)) = μ * σ (Q v)) (u t : Fin d → K) :
    Q' (M (frobVec σ u) - M (frobVec σ t)) = μ * σ (Q (u - t)) := by
  rw [← map_sub, ← frobVec_sub]
  exact hss (u - t)

/-- **F2's cited classical fact — a cone-preserving collineation is a semi-similitude (scoped, carried).**
For `p` odd (`(2:K) ≠ 0`) and `d ≥ 4`: a bijective, cone-preserving linear-part-of-a-collineation `g`
between two affine-polar graphs (`Q` nondegenerate) decomposes as `g = M ∘ σ̂` (`M` `K`-linear, `σ` a
field endomorphism) and is a **semi-similitude** `Q'(g v) = μ · σ(Q v)` (`μ ≠ 0`). This is the
**fundamental theorem of projective geometry** (a collineation of `PG(d,q)`, `d ≥ 2`, is a semilinear
map) composed with the semilinear form of the quadric-determines-form uniqueness (§ `NondegQuadric
DeterminesForm`). Classical (Hirschfeld; Artin, *Geometric Algebra*); carried as a premise like
`Theorem41Statement`. The `p ≠ 2`, `d ≥ 4` scope is exactly where it is TRUE (the linear `q = p` case is
the `σ = id` specialization of this). -/
def ConePreservingCollineationIsSemiSimilitude (K : Type*) [Field K] [Fintype K] (d : ℕ) : Prop :=
  (2 : K) ≠ 0 → 4 ≤ d → ∀ (Q Q' : QuadraticForm K (Fin d → K)) (g : (Fin d → K) → (Fin d → K)),
    (Q.polarBilin).Nondegenerate → Function.Bijective g → (∀ v, Q v = 0 ↔ Q' (g v) = 0) →
      ∃ (M : (Fin d → K) ≃ₗ[K] (Fin d → K)) (σ : K →+* K) (μ : K),
        μ ≠ 0 ∧ (∀ v, g v = M (frobVec σ v)) ∧ (∀ v, Q' (g v) = μ * σ (Q v))

/-- **F2 — the recovered form is iso-invariant over `𝔽_q` (equivariant under a graph iso, including the
Frobenius twist).** Given the linear part `g` of a graph isomorphism between two `𝔽_q`-affine-polar
graphs (bijective, cone-preserving), nondegenerate `Q`, and the cited fundamental-theorem fact `hcite`,
the recovered difference colouring transports with a global scalar `μ` **and** a field automorphism `σ`:
`Q'(g u − g t) = μ · σ(Q(u − t))`. This is F4 for `q = pᵉ`: canonicalizing via the recovered form is
iso-invariant even in the presence of field twists (`AΓO` vs `AGO`). The `q = p` prime case
(`recoveredForm_colouring_equivariant`) is the `σ = id` specialization. Axiom-clean; the only
non-elementary input is `hcite`, threaded like `Theorem41Statement`. -/
theorem recoveredForm_colouring_equivariant_semilinear
    (hcite : ConePreservingCollineationIsSemiSimilitude K d) (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d)
    (Q Q' : QuadraticForm K (Fin d → K)) (hQ : (Q.polarBilin).Nondegenerate)
    (g : (Fin d → K) → (Fin d → K)) (hg : Function.Bijective g)
    (hcone : ∀ v, Q v = 0 ↔ Q' (g v) = 0) :
    ∃ (σ : K →+* K) (μ : K), ∀ u t : Fin d → K, Q' (g u - g t) = μ * σ (Q (u - t)) := by
  obtain ⟨M, σ, μ, _hμ, hgM, hss⟩ := hcite h2 hd Q Q' g hQ hg hcone
  refine ⟨σ, μ, fun u t => ?_⟩
  rw [hgM u, hgM t]
  exact semisimilitude_colouring_equivariant Q Q' M σ (fun v => by rw [← hgM v]; exact hss v) u t

end F2

/-! ## F3 — the generic engine interface (`IFormStructure`): 1 engine, N family adapters

The Route-C engine (`affineScheme` + `discrete_affineScheme_of_jointSeparates` + `viaSpielman`) is already
**generic in the linear group `G₀`**. What is family-specific is exactly: (a) the group `G₀ ≤ GL(V)` whose affine
scheme is the (isometry-refined) graph, (b) a bounded base `T`, and (c) the `Separates` certificate — the family's
`coords_determine` analog. `FormAdapter` bundles precisely (a)–(c); `FormAdapter.reachesRigidOrCameron` is the shared
engine theorem. Each family (affine-polar / alternating / half-spin / Suzuki) becomes **one `FormAdapter` instance** —
the Lean realization of the plan's "1 engine + `IFormStructure`×4" (§3 / F3). The affine-polar instance
`affinePolarAdapter` below validates the interface end-to-end and reproduces `reachesRigidOrCameron_viaOrthogonalForm`;
the other families supply only their own `separates` (their `Separates` certificate — the genuine per-family content,
`docs/chain-descent-formsgraph-wldim-plan.md` §11.4: the alternating/half-spin/Suzuki form objects are non-quadratic,
so `separates` is re-instantiated per form, same shape). -/

/-- **The generic Route-C adapter (`IFormStructure`).** A family plugs in its linear group `G₀` (with `−1 ∈ G₀`),
a base `base` of size `≤ bound`, and the `Separates` certificate: the `G₀`-orbit-of-difference profile at `base`
determines the vertex. This is the whole family-specific interface; everything downstream is shared. -/
structure FormAdapter (bound : ℕ) where
  /-- The family's linear group (`O(Q)` for affine-polar; `Sp(B)`-style for alternating; …). -/
  G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
  /-- `−1 ∈ G₀` — the `hneg` input for `affineScheme`. -/
  neg_mem : LinearEquiv.neg (ZMod p) ∈ G₀
  /-- The individualized base (size `≤ bound`). -/
  base : Finset (Fin (p ^ d))
  base_card_le : base.card ≤ bound
  /-- The `Separates` certificate: the `G₀`-orbit-of-difference profile at `base` determines the vertex. -/
  separates : ∀ u u' : Fin (p ^ d),
    (∀ t ∈ base, ∃ g₀ ∈ G₀, g₀ (ChainDescent.affineE.symm u' - ChainDescent.affineE.symm t)
        = ChainDescent.affineE.symm u - ChainDescent.affineE.symm t) → u = u'

/-- **The shared engine theorem — any `FormAdapter` seals.** Its affine scheme individualizes to discrete at the
base and reaches the rigid-or-Cameron disjunction via `viaSpielman`. Family-agnostic: the ONLY input is the adapter,
so writing a new family reduces to constructing its `FormAdapter` (i.e. proving its `separates`). -/
theorem FormAdapter.reachesRigidOrCameron {bound : ℕ}
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} (A : FormAdapter (p := p) (d := d) bound) :
    ((SchemeBlockRecovered (p ^ d) (ChainDescent.affineScheme A.G₀ A.neg_mem)
        ∨ AbelianConsumed (p ^ d) (ChainDescent.affineScheme A.G₀ A.neg_mem))
        ∨ SchemeRecoveredByDepth (p ^ d) (ChainDescent.affineScheme A.G₀ A.neg_mem) bound)
      ∨ IsCameronScheme (p ^ d) (ChainDescent.affineScheme A.G₀ A.neg_mem) :=
  ChainDescent.reachesRigidOrCameron_viaSpielman _
    ⟨A.base, A.base_card_le,
      ChainDescent.discrete_affineScheme_of_jointSeparates A.G₀ A.neg_mem A.separates⟩

/-- **Instance 1 — affine-polar `VO^ε` (validates the interface).** `G₀ = O(Q)`, `base` = the standard frame
`{0, e₁, …, e_d}`, and `separates` = the `coords_determine` certificate. Shows `FormAdapter` is non-vacuous, and
`affinePolarAdapter Q hQ |>.reachesRigidOrCameron` reproduces `reachesRigidOrCameron_viaOrthogonalForm`. -/
noncomputable def affinePolarAdapter (Q : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (hQ : (Q.polarBilin).Nondegenerate) : FormAdapter (p := p) (d := d) (d + 1) where
  G₀ := ChainDescent.isometryGroup Q
  neg_mem := ChainDescent.neg_mem_isometryGroup Q
  base := ChainDescent.frameBase
  base_card_le := ChainDescent.frameBase_card_le
  separates := by
    intro u u' hh
    have h0 : Q (ChainDescent.affineE.symm u) = Q (ChainDescent.affineE.symm u') := by
      obtain ⟨g₀, hg, hgeq⟩ := hh (ChainDescent.affineE 0) (Finset.mem_insert_self _ _)
      rw [Equiv.symm_apply_apply, sub_zero, sub_zero] at hgeq
      have hval := hg (ChainDescent.affineE.symm u')
      rw [hgeq] at hval
      exact hval
    have hi : ∀ i : Fin d, Q (ChainDescent.affineE.symm u - Pi.single i 1)
        = Q (ChainDescent.affineE.symm u' - Pi.single i 1) := by
      intro i
      obtain ⟨g₀, hg, hgeq⟩ := hh (ChainDescent.affineE (Pi.single i 1))
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      rw [Equiv.symm_apply_apply] at hgeq
      have hval := hg (ChainDescent.affineE.symm u' - Pi.single i 1)
      rw [hgeq] at hval
      exact hval
    exact ChainDescent.affineE.symm.injective (ChainDescent.coords_determine Q hQ h0 hi)

/-! ## Alternating forms family (instance 2) — the multi-quadric `separates` core

The alternating forms graph `Alt(n,q)` has vertices `Λ²(𝔽_q^n)` (alternating matrices) and adjacency
`rank(A−B) = 2`. **`n = 4` is affine-polar in disguise:** `Λ²(𝔽_q^4) ≅ 𝔽_q^6` and `rank < 4 ⟺ Pfaffian = 0`, so
`Alt(4,q) = VO⁺₆(q)` with `Q = Pf` (a single nondegenerate quadratic form) — already covered by
`affinePolarAdapter`. **The genuinely-new family is `n ≥ 5`:** `rank ≤ 2` is cut out by a *family* of quadratic
forms (the Plücker / 4×4-sub-Pfaffian relations — 5 of them for `n = 5`), so the connection set is their **joint
cone** (the Grassmann `G(2,n)` cone). Each single Plücker form is degenerate; only *jointly* do their polar forms
separate. So the `separates` certificate for the alternating `FormAdapter` needs the **multi-form** generalization
of `coords_determine`: a family `{Q_k}` whose polar forms have trivial *common* radical determines the vertex from
the joint value-profile. That reusable core is built here (standard frame + spanning base); the remaining
per-family work is identifying `G₀ = Λ²(SL_n)` and wiring the rank-2 graph relations to the Plücker value-profile
(the recovery/refinement step). -/

/-- **Multi-form `coords_determine` (the alternating family's `separates` core).** A *family* of quadratic forms
`Qs : ι → QuadraticForm` whose polar forms **jointly** separate (trivial common radical: `(∀ k, polar_{Q_k} w = 0)
⟹ w = 0`) determines the vector from the joint value-profile at the standard frame: if `Q_k v = Q_k v'` and
`Q_k (v − e_i) = Q_k (v' − e_i)` for all `k` and `i`, then `v = v'`. Generalizes `coords_determine` (`ι = Unit`
case) — each `Q_k` gives `polar_{Q_k}(v−v') = 0`, and joint nondegeneracy across `k` finishes. The Plücker quadrics
of `Alt(n,q)` are individually degenerate but jointly separating, which is exactly this hypothesis. -/
theorem coords_determine_multi {ι : Type*} (Qs : ι → QuadraticForm (ZMod p) (Fin d → ZMod p))
    (hjoint : ∀ w : Fin d → ZMod p, (∀ k, (Qs k).polarBilin w = 0) → w = 0)
    {v v' : Fin d → ZMod p}
    (h0 : ∀ k, Qs k v = Qs k v')
    (hi : ∀ (k : ι) (i : Fin d), Qs k (v - Pi.single i 1) = Qs k (v' - Pi.single i 1)) :
    v = v' := by
  have hzero : ∀ k, (Qs k).polarBilin (v - v') = 0 := by
    intro k
    apply (Pi.basisFun (ZMod p) (Fin d)).ext
    intro i
    have hk : (Qs k).polarBilin v (Pi.single i 1) = (Qs k).polarBilin v' (Pi.single i 1) := by
      rw [polarBilin_apply_apply, polarBilin_apply_apply, ChainDescent.polar_eq_of_sub,
        ChainDescent.polar_eq_of_sub, h0 k, hi k i]
    rw [LinearMap.zero_apply, map_sub, LinearMap.sub_apply, Pi.basisFun_apply, hk, sub_self]
  exact sub_eq_zero.mp (hjoint (v - v') hzero)

/-- **Multi-form `coords_determine` at a spanning base** (the alternating family's `separates` core, Route-C
form). Same as `coords_determine_multi` but the value-profile is taken over any base `S` that **spans** `V`
(Route C individualizes an iso-invariantly chosen spanning base, not the literal frame). Combines the spanning
argument of `coords_determine_spanning` with the joint-radical argument of `coords_determine_multi`. -/
theorem coords_determine_multi_spanning {ι : Type*} (Qs : ι → QuadraticForm (ZMod p) (Fin d → ZMod p))
    (hjoint : ∀ w : Fin d → ZMod p, (∀ k, (Qs k).polarBilin w = 0) → w = 0)
    {S : Set (Fin d → ZMod p)} (hspan : Submodule.span (ZMod p) S = ⊤)
    {v v' : Fin d → ZMod p}
    (h0 : ∀ k, Qs k v = Qs k v')
    (hs : ∀ (k : ι), ∀ s ∈ S, Qs k (v - s) = Qs k (v' - s)) :
    v = v' := by
  have hzero : ∀ k, (Qs k).polarBilin (v - v') = 0 := by
    intro k
    apply LinearMap.ext_on hspan
    intro x hx
    have hk : (Qs k).polarBilin v x = (Qs k).polarBilin v' x := by
      rw [polarBilin_apply_apply, polarBilin_apply_apply, ChainDescent.polar_eq_of_sub,
        ChainDescent.polar_eq_of_sub, h0 k, hs k x hx]
    rw [LinearMap.zero_apply, map_sub, LinearMap.sub_apply, hk, sub_self]
  exact sub_eq_zero.mp (hjoint (v - v') hzero)

/-- **The general multi-quadric `FormAdapter`** — the alternating family's engine hookup. Given a family of
quadratic forms `Qs : ι → QuadraticForm` whose polar forms **jointly** separate (trivial common radical), the
**joint isometry group** `G₀ = ⨅ₖ O(Q_k)` (the maps preserving every `Q_k`) forms a `FormAdapter` at the standard
frame: a `G₀`-element preserves every `Q_k`-value, so the orbit-of-difference profile at the frame gives the joint
`Q_k`-profile, which `coords_determine_multi` inverts. `affinePolarAdapter` is the `ι = Unit` case (a single
nondegenerate `Q`); the alternating `Alt(n≥5,q)` family is this with `Qs =` the Plücker quadrics (individually
degenerate, jointly separating). So the remaining alternating work is exactly: supply the Plücker `Qs` and prove
their joint nondegeneracy `hjoint`. Axiom-clean. -/
noncomputable def multiFormAdapter {ι : Type*} (Qs : ι → QuadraticForm (ZMod p) (Fin d → ZMod p))
    (hjoint : ∀ w : Fin d → ZMod p, (∀ k, (Qs k).polarBilin w = 0) → w = 0) :
    FormAdapter (p := p) (d := d) (d + 1) where
  G₀ := ⨅ k, ChainDescent.isometryGroup (Qs k)
  neg_mem := Subgroup.mem_iInf.mpr (fun k => ChainDescent.neg_mem_isometryGroup (Qs k))
  base := ChainDescent.frameBase
  base_card_le := ChainDescent.frameBase_card_le
  separates := by
    intro u u' hh
    have h0 : ∀ k, Qs k (ChainDescent.affineE.symm u) = Qs k (ChainDescent.affineE.symm u') := by
      intro k
      obtain ⟨g₀, hg, hgeq⟩ := hh (ChainDescent.affineE 0) (Finset.mem_insert_self _ _)
      rw [Equiv.symm_apply_apply, sub_zero, sub_zero] at hgeq
      have hval := (Subgroup.mem_iInf.mp hg k) (ChainDescent.affineE.symm u')
      rw [hgeq] at hval
      exact hval
    have hi : ∀ (k : ι) (i : Fin d), Qs k (ChainDescent.affineE.symm u - Pi.single i 1)
        = Qs k (ChainDescent.affineE.symm u' - Pi.single i 1) := by
      intro k i
      obtain ⟨g₀, hg, hgeq⟩ := hh (ChainDescent.affineE (Pi.single i 1))
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      rw [Equiv.symm_apply_apply] at hgeq
      have hval := (Subgroup.mem_iInf.mp hg k) (ChainDescent.affineE.symm u' - Pi.single i 1)
      rw [hgeq] at hval
      exact hval
    exact ChainDescent.affineE.symm.injective (coords_determine_multi Qs hjoint h0 hi)

/-! ## Multi-quadric bridges — brick-1 (refinement) and F4 (iso-invariance) for the multi-form families

The single-quadratic affine-polar instance carries THREE legs: the seal (`…viaOrthogonalForm_spanning` /
`affinePolarAdapter`, discretizes at a bounded base), **A3 brick 1** (`isometryScheme_refines_similitudeScheme`,
the recovered scheme refines the actual graph) and **F4** (`recoveredForm_colouring_equivariant`, the recovered
colouring is iso-invariant). The multi-quadric families (`multiFormAdapter`: alternating, half-spin) previously
carried only the seal leg. This section supplies the multi-form analogs of the other two, GENERICALLY over the
form family `Qs`, so every multi-quadric family gets all three legs at once (alternating retroactively, half-spin
the moment its spinor quadrics land).

* **brick-1-multi** (`multiIsometryScheme_refines_coneScheme`): the joint-isometry scheme `⨅ₖ O(Q_k)` refines
  the **cone-stabilizer** scheme `jointConeStab Qs` — and the cone stabilizer is a *graph-intrinsic* object
  (the setwise stabilizer of the connection set `{v | ∀k, Q_k v = 0}`, definable from the graph alone), so this
  is genuinely "recovered scheme refines the given graph", cleaner than the single-form case (which refines the
  *form*-defined similitude group). A corollary of the generic `affineScheme_refines_of_le`.
* **F4-multi** (`recoveredFamily_colouring_equivariant`): a graph iso's linear part `g` carries the joint cone
  to the joint cone, hence (via the carried multi-form citation `JointVarietyDeterminesFamily`) transports the
  recovered value-tuple colouring `v ↦ (Q_k v)_k` by a single global INJECTIVE map `Φ` — so the induced
  colour partition is iso-invariant (`recoveredFamily_partition_isoInvariant`). The `Φ` replaces the single-form
  global scalar `μ`; injectivity is the multi-form analog of `μ` being a unit (it "cancels in comparisons"). -/

/-- **The cone stabilizer — the graph-intrinsic linear group of a multi-quadric forms graph.** The setwise
stabilizer of the joint isotropic cone `{v | ∀ k, Q_k v = 0}` (= the connection set / adjacency of the graph):
the linear maps `g` with `(∀ k, Q_k (g v) = 0) ↔ (∀ k, Q_k v = 0)` for all `v`. Definable from the graph alone
(the cone IS the connection set), so its affine scheme is a graph-intrinsic refinement target — the multi-form
analog of `similitudeGroup` (which is *form*-defined). Every joint isometry preserves the cone, so
`⨅ₖ O(Q_k) ≤ jointConeStab` (`iInf_isometryGroup_le_jointConeStab`). -/
def jointConeStab {ι : Type*} (Qs : ι → QuadraticForm (ZMod p) (Fin d → ZMod p)) :
    Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) where
  carrier := {g | ∀ v, (∀ k, Qs k (g v) = 0) ↔ (∀ k, Qs k v = 0)}
  one_mem' := by intro v; rfl
  mul_mem' := by
    intro a b ha hb v
    rw [LinearEquiv.mul_apply, ha (b v), hb v]
  inv_mem' := by
    intro a ha v
    have hav : a (a⁻¹ v) = v := by
      have h := LinearEquiv.mul_apply a a⁻¹ v
      rw [mul_inv_cancel] at h; simpa using h.symm
    have := ha (a⁻¹ v)
    rw [hav] at this
    exact this.symm

/-- `−1 ∈ jointConeStab Qs` — the `hneg` input for the cone-stabilizer scheme. `Q_k (−v) = Q_k v`, so the cone
condition is literally unchanged. -/
theorem neg_mem_jointConeStab {ι : Type*} (Qs : ι → QuadraticForm (ZMod p) (Fin d → ZMod p)) :
    LinearEquiv.neg (ZMod p) ∈ jointConeStab Qs := by
  intro v
  constructor <;> intro h k <;> [skip; skip]
  · have := h k; rwa [LinearEquiv.neg_apply, QuadraticMap.map_neg] at this
  · rw [LinearEquiv.neg_apply, QuadraticMap.map_neg]; exact h k

/-- **The joint isometry group is contained in the cone stabilizer.** A `g` preserving every `Q_k`-value
exactly (`g ∈ ⨅ₖ O(Q_k)`) certainly preserves the joint cone setwise, so `⨅ₖ O(Q_k) ≤ jointConeStab Qs`.
This is what lets `affineScheme_refines_of_le` fire: the recovered joint-isometry scheme refines the
graph-intrinsic cone-stabilizer scheme. -/
theorem iInf_isometryGroup_le_jointConeStab {ι : Type*}
    (Qs : ι → QuadraticForm (ZMod p) (Fin d → ZMod p)) :
    (⨅ k, ChainDescent.isometryGroup (Qs k)) ≤ jointConeStab Qs := by
  intro g hg v
  have hval : ∀ k, Qs k (g v) = Qs k v := fun k => (Subgroup.mem_iInf.mp hg k) v
  constructor <;> intro h k
  · rw [← hval k]; exact h k
  · rw [hval k]; exact h k

/-- **brick-1-multi — the joint-isometry scheme refines the cone-stabilizer (graph-intrinsic) scheme.** The
multi-form analog of `isometryScheme_refines_similitudeScheme`: the recovered joint-isometry scheme
`affineScheme (⨅ₖ O(Q_k))` is finer than the scheme of the cone stabilizer `jointConeStab Qs` — and the latter
is defined from the connection set alone, so this says the recovered structure refines the *actual graph*, not a
form-defined artefact. A corollary of `affineScheme_refines_of_le` via `iInf_isometryGroup_le_jointConeStab`.
Axiom-clean. -/
theorem multiIsometryScheme_refines_coneScheme {ι : Type*}
    (Qs : ι → QuadraticForm (ZMod p) (Fin d → ZMod p))
    (hneg₀ : LinearEquiv.neg (ZMod p) ∈ ⨅ k, ChainDescent.isometryGroup (Qs k))
    {x y x' y' : Fin (p ^ d)}
    (h : (ChainDescent.affineScheme (⨅ k, ChainDescent.isometryGroup (Qs k)) hneg₀).relOfPair x y
        = (ChainDescent.affineScheme (⨅ k, ChainDescent.isometryGroup (Qs k)) hneg₀).relOfPair x' y') :
    (ChainDescent.affineScheme (jointConeStab Qs) (neg_mem_jointConeStab Qs)).relOfPair x y
      = (ChainDescent.affineScheme (jointConeStab Qs) (neg_mem_jointConeStab Qs)).relOfPair x' y' :=
  affineScheme_refines_of_le (iInf_isometryGroup_le_jointConeStab Qs) hneg₀
    (neg_mem_jointConeStab Qs) h

/-- **F4-multi brick — a family semi-similitude carries the value-tuple colouring (equivariance, provable).**
If a graph iso's linear part `g` transports the recovered value-tuple colouring by a global map `Φ`
(`(Q'_k (g v))_k = Φ ((Q_k v)_k)` for all `v`), then it transports the **difference** colouring by the same
`Φ`: `(Q'_k (g u − g t))_k = Φ ((Q_k (u − t))_k)`. Pure linearity — `g u − g t = g (u − t)` — with `Φ`
completely arbitrary. The multi-form analog of `similitude_colouring_equivariant` (there `Φ = (μ · ·)`). -/
theorem multiSimilitude_colouring_equivariant {ι : Type*}
    (Qs Qs' : ι → QuadraticForm (ZMod p) (Fin d → ZMod p))
    (g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) (Φ : (ι → ZMod p) → (ι → ZMod p))
    (hsim : ∀ v, (fun k => Qs' k (g v)) = Φ (fun k => Qs k v)) (u t : Fin d → ZMod p) :
    (fun k => Qs' k (g u - g t)) = Φ (fun k => Qs k (u - t)) := by
  have h := hsim (u - t)
  simp only [map_sub] at h
  exact h

/-- **F4-multi's cited classical fact — the joint variety determines its quadric family up to an invertible
recombination (scoped, carried).** For a jointly-nondegenerate family `Qs` (trivial common polar radical) and a
graph iso's linear part `g` preserving the joint cone (`(∀ k, Q_k v = 0) ↔ (∀ k, Q'_k (g v) = 0)`), the pulled-
back family `{Q'_k ∘ g}` and `{Q_k}` span the same space of degree-2 forms (the degree-2 part of the vanishing
ideal of the cone), so the value-tuple transports by a global **injective** linear map `Φ`. This is the
multi-form analog of `NondegQuadricDeterminesForm`: there the vanishing space is `⟨Q⟩` (`Φ = ` scalar); here it
is `span {Q_k}` (`Φ = ` the change-of-basis, injective because the family is independent — true for the Plücker
quadrics of `Alt(5,q)` and the D₅ spinor quadrics). Classical projective algebraic geometry (the ideal of the
Grassmann / spinor variety is generated by the Plücker / spinor quadrics — projective normality); carried as a
premise like `Theorem41Statement`. NOT proved here. -/
def JointVarietyDeterminesFamily (p d : ℕ) (ι : Type*) [Fact p.Prime] : Prop :=
  ∀ (Qs Qs' : ι → QuadraticForm (ZMod p) (Fin d → ZMod p))
    (g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)),
    (∀ w : Fin d → ZMod p, (∀ k, (Qs k).polarBilin w = 0) → w = 0) →
    (∀ v, (∀ k, Qs k v = 0) ↔ (∀ k, Qs' k (g v) = 0)) →
      ∃ Φ : (ι → ZMod p) → (ι → ZMod p),
        Function.Injective Φ ∧ ∀ v, (fun k => Qs' k (g v)) = Φ (fun k => Qs k v)

/-- **F4-multi — the recovered family colouring is iso-invariant (equivariant under a graph iso's linear
part).** Given the linear part `g` of a graph iso between two multi-quadric forms graphs (joint-cone-preserving),
joint nondegeneracy, and the cited `JointVarietyDeterminesFamily` (`hcite`), the recovered value-tuple
**difference** colouring transports by a single global injective `Φ`:
`(Q'_k (g u − g t))_k = Φ ((Q_k (u − t))_k)`. So canonicalizing via the recovered family produces a canonical
(iso-invariant) colouring — the multi-form completion of F4, previously present only for the single-quadratic
affine-polar instance. Composes with `multiIsometryScheme_refines_coneScheme` and `FormAdapter.reachesRigidOrCameron`
to give: iso-invariant discrete colouring at a bounded base ⟹ (meta) poly canonical labelling, for every
multi-quadric family. Axiom-clean; the only non-elementary input is `hcite`. -/
theorem recoveredFamily_colouring_equivariant {ι : Type*}
    (hcite : JointVarietyDeterminesFamily p d ι)
    (Qs Qs' : ι → QuadraticForm (ZMod p) (Fin d → ZMod p))
    (g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
    (hjoint : ∀ w : Fin d → ZMod p, (∀ k, (Qs k).polarBilin w = 0) → w = 0)
    (hcone : ∀ v, (∀ k, Qs k v = 0) ↔ (∀ k, Qs' k (g v) = 0)) :
    ∃ Φ : (ι → ZMod p) → (ι → ZMod p), Function.Injective Φ ∧
      ∀ u t : Fin d → ZMod p, (fun k => Qs' k (g u - g t)) = Φ (fun k => Qs k (u - t)) := by
  obtain ⟨Φ, hΦinj, hΦ⟩ := hcite Qs Qs' g hjoint hcone
  exact ⟨Φ, hΦinj, fun u t => multiSimilitude_colouring_equivariant Qs Qs' g Φ hΦ u t⟩

/-- **F4-multi payoff — the recovered colour partition is iso-invariant.** From the equivariance
(`recoveredFamily_colouring_equivariant`) with an INJECTIVE `Φ`: two pairs get the same recovered colour in the
source graph **iff** their `g`-images get the same recovered colour in the target — the exact "the global
ambiguity cancels in comparisons" statement (here injectivity of `Φ` plays the role the single-form scalar `μ`
being a unit played). This is what makes the recovered-form colouring usable as an iso-invariant refinement.
Axiom-clean. -/
theorem recoveredFamily_partition_isoInvariant {ι : Type*}
    {Φ : (ι → ZMod p) → (ι → ZMod p)} (hΦinj : Function.Injective Φ)
    {Qs Qs' : ι → QuadraticForm (ZMod p) (Fin d → ZMod p)}
    {g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)}
    (hΦ : ∀ u t : Fin d → ZMod p, (fun k => Qs' k (g u - g t)) = Φ (fun k => Qs k (u - t)))
    (u t u' t' : Fin d → ZMod p) :
    ((fun k => Qs k (u - t)) = fun k => Qs k (u' - t')) ↔
      ((fun k => Qs' k (g u - g t)) = fun k => Qs' k (g u' - g t')) := by
  rw [hΦ u t, hΦ u' t']
  constructor
  · intro h; rw [h]
  · intro h; exact hΦinj h

/-- **F4-multi citation-free — the recovered joint-`W` colour partition is iso-invariant, with NO
`JointVarietyDeterminesFamily`.** The multi-form sibling of `recoveredForm_partition_isoInvariant`: colour a pair by
the whole degree-2 space vanishing on the **joint** cone `{v | ∀ k, Qs k v = 0}`, and the partition transports under
a joint-cone-preserving linear iso `g`. The `C v := ∀ k, Qs k v = 0` specialization of the generic
`recoveredForm_partition_isoInvariant_gen` — the elementary vanishing-space route (`chain-descent-citation-discharge.md`
§3.2), discharging the F4-multi iso-invariance object from the projective-normality citation at `q = p`. The injective-`Φ`
statement `recoveredFamily_colouring_equivariant` remains the strictly stronger `|Aut|`-naming form that carries the
citation. -/
theorem recoveredFamily_partition_isoInvariant_vanishing {ι : Type*}
    (Qs Qs' : ι → QuadraticForm (ZMod p) (Fin d → ZMod p))
    (g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))
    (hcone : ∀ v, (∀ k, Qs k v = 0) ↔ (∀ k, Qs' k (g v) = 0)) (u t u' t' : Fin d → ZMod p) :
    (∀ F : QuadraticForm (ZMod p) (Fin d → ZMod p), (∀ v, (∀ k, Qs k v = 0) → F v = 0) →
        F (u - t) = F (u' - t')) ↔
      (∀ F' : QuadraticForm (ZMod p) (Fin d → ZMod p), (∀ v, (∀ k, Qs' k v = 0) → F' v = 0) →
        F' (g u - g t) = F' (g u' - g t')) :=
  recoveredForm_partition_isoInvariant_gen (C := fun v => ∀ k, Qs k v = 0)
    (C' := fun v => ∀ k, Qs' k v = 0) g hcone u t u' t'

/-! ### The concrete alternating instance `Alt(5,q)` — the Plücker quadrics + the sealed adapter

`Alt(5,q)` has vertex space `Λ²(𝔽_q^5) ≅ 𝔽_q^10`. Index the 10 Plücker coordinates (pairs `{i<j} ⊆ Fin 5`) as
`Fin 10`: `0:(0,1) 1:(0,2) 2:(0,3) 3:(0,4) 4:(1,2) 5:(1,3) 6:(1,4) 7:(2,3) 8:(2,4) 9:(3,4)`. The rank `≤ 2`
(decomposable) locus is cut out by the **5 sub-Pfaffians** `Pf_k` (delete index `k`), each a quadratic form on
`𝔽_q^10`. They are individually degenerate but **jointly nondegenerate** (`plucker_hjoint`: `Pf₀` forces
coords `4..9 = 0`, `Pf₁` forces `1,2,3`, `Pf₂` forces `0`), so `multiFormAdapter` assembles them into a sealed
`FormAdapter` — the first concrete non-quadratic (multi-form) Route-C family. All axiom-clean. -/

/-- **Reusable primitive — the polar of a product-of-linear-forms.** `polar (linMulLin f g) x y =
f x · g y + f y · g x`. The building block for the polar of any "Clifford-term-sum" quadric (Plücker
sub-Pfaffians, D₅ spinor quadrics): each such form is a sum of `linMulLin (proj a) (proj b)` terms. -/
theorem polar_linMulLin (f g : (Fin d → ZMod p) →ₗ[ZMod p] ZMod p) (x y : Fin d → ZMod p) :
    QuadraticMap.polar (QuadraticMap.linMulLin f g) x y = f x * g y + f y * g x := by
  simp only [QuadraticMap.polar, QuadraticMap.linMulLin_apply, map_add]; ring

namespace Plucker
open QuadraticMap

/-- The `i`-th Plücker coordinate projection on `𝔽_p^10`. -/
noncomputable def pc (i : Fin 10) : (Fin 10 → ZMod p) →ₗ[ZMod p] ZMod p := LinearMap.proj i

/-- Sub-Pfaffian deleting index 0 (`= x₄x₉ − x₅x₈ + x₆x₇`). -/
noncomputable def Pf0 : QuadraticForm (ZMod p) (Fin 10 → ZMod p) :=
  linMulLin (pc 4) (pc 9) - linMulLin (pc 5) (pc 8) + linMulLin (pc 6) (pc 7)
/-- Sub-Pfaffian deleting index 1 (`= x₁x₉ − x₂x₈ + x₃x₇`). -/
noncomputable def Pf1 : QuadraticForm (ZMod p) (Fin 10 → ZMod p) :=
  linMulLin (pc 1) (pc 9) - linMulLin (pc 2) (pc 8) + linMulLin (pc 3) (pc 7)
/-- Sub-Pfaffian deleting index 2 (`= x₀x₉ − x₂x₆ + x₃x₅`). -/
noncomputable def Pf2 : QuadraticForm (ZMod p) (Fin 10 → ZMod p) :=
  linMulLin (pc 0) (pc 9) - linMulLin (pc 2) (pc 6) + linMulLin (pc 3) (pc 5)
/-- Sub-Pfaffian deleting index 3 (`= x₀x₈ − x₁x₆ + x₃x₄`). -/
noncomputable def Pf3 : QuadraticForm (ZMod p) (Fin 10 → ZMod p) :=
  linMulLin (pc 0) (pc 8) - linMulLin (pc 1) (pc 6) + linMulLin (pc 3) (pc 4)
/-- Sub-Pfaffian deleting index 4 (`= x₀x₇ − x₁x₅ + x₂x₄`). -/
noncomputable def Pf4 : QuadraticForm (ZMod p) (Fin 10 → ZMod p) :=
  linMulLin (pc 0) (pc 7) - linMulLin (pc 1) (pc 5) + linMulLin (pc 2) (pc 4)

/-- The family of 5 Plücker quadrics (the connection set of `Alt(5,q)` is their joint cone). -/
noncomputable def pluckerForms : Fin 5 → QuadraticForm (ZMod p) (Fin 10 → ZMod p)
  | 0 => Pf0 | 1 => Pf1 | 2 => Pf2 | 3 => Pf3 | 4 => Pf4

theorem Pf0_polar (x y : Fin 10 → ZMod p) : polar Pf0 x y =
    x 4 * y 9 + y 4 * x 9 - (x 5 * y 8 + y 5 * x 8) + (x 6 * y 7 + y 6 * x 7) := by
  simp only [polar, Pf0, QuadraticMap.add_apply, QuadraticMap.sub_apply, linMulLin_apply, pc,
    LinearMap.proj_apply, Pi.add_apply]; ring
theorem Pf1_polar (x y : Fin 10 → ZMod p) : polar Pf1 x y =
    x 1 * y 9 + y 1 * x 9 - (x 2 * y 8 + y 2 * x 8) + (x 3 * y 7 + y 3 * x 7) := by
  simp only [polar, Pf1, QuadraticMap.add_apply, QuadraticMap.sub_apply, linMulLin_apply, pc,
    LinearMap.proj_apply, Pi.add_apply]; ring
theorem Pf2_polar (x y : Fin 10 → ZMod p) : polar Pf2 x y =
    x 0 * y 9 + y 0 * x 9 - (x 2 * y 6 + y 2 * x 6) + (x 3 * y 5 + y 3 * x 5) := by
  simp only [polar, Pf2, QuadraticMap.add_apply, QuadraticMap.sub_apply, linMulLin_apply, pc,
    LinearMap.proj_apply, Pi.add_apply]; ring

/-- **The Plücker quadrics are jointly nondegenerate** (their polar forms have trivial common radical): if
`polar_{Pf_k} w = 0` for every `k`, then `w = 0`. Only `Pf₀,Pf₁,Pf₂` are needed — `Pf₀` isolates coords `4..9`,
`Pf₁` isolates `1,2,3`, `Pf₂` isolates `0` — but all 5 are in the family (extra forms only shrink the radical).
This `hjoint` is the sole geometric input the alternating adapter needs. -/
theorem plucker_hjoint (w : Fin 10 → ZMod p)
    (h : ∀ k, (pluckerForms k).polarBilin w = 0) : w = 0 := by
  have h0 : Pf0.polarBilin w = 0 := h 0
  have h1 : Pf1.polarBilin w = 0 := h 1
  have h2 : Pf2.polarBilin w = 0 := h 2
  have w0 : w 0 = 0 := by
    have e := LinearMap.congr_fun h2 (Pi.single (9 : Fin 10) 1)
    rw [polarBilin_apply_apply, Pf2_polar, LinearMap.zero_apply] at e; simpa using e
  have w1 : w 1 = 0 := by
    have e := LinearMap.congr_fun h1 (Pi.single (9 : Fin 10) 1)
    rw [polarBilin_apply_apply, Pf1_polar, LinearMap.zero_apply] at e; simpa using e
  have w2 : w 2 = 0 := by
    have e := LinearMap.congr_fun h1 (Pi.single (8 : Fin 10) 1)
    rw [polarBilin_apply_apply, Pf1_polar, LinearMap.zero_apply] at e; simpa using e
  have w3 : w 3 = 0 := by
    have e := LinearMap.congr_fun h1 (Pi.single (7 : Fin 10) 1)
    rw [polarBilin_apply_apply, Pf1_polar, LinearMap.zero_apply] at e; simpa using e
  have w4 : w 4 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (9 : Fin 10) 1)
    rw [polarBilin_apply_apply, Pf0_polar, LinearMap.zero_apply] at e; simpa using e
  have w5 : w 5 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (8 : Fin 10) 1)
    rw [polarBilin_apply_apply, Pf0_polar, LinearMap.zero_apply] at e; simpa using e
  have w6 : w 6 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (7 : Fin 10) 1)
    rw [polarBilin_apply_apply, Pf0_polar, LinearMap.zero_apply] at e; simpa using e
  have w7 : w 7 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (6 : Fin 10) 1)
    rw [polarBilin_apply_apply, Pf0_polar, LinearMap.zero_apply] at e; simpa using e
  have w8 : w 8 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (5 : Fin 10) 1)
    rw [polarBilin_apply_apply, Pf0_polar, LinearMap.zero_apply] at e; simpa using e
  have w9 : w 9 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (4 : Fin 10) 1)
    rw [polarBilin_apply_apply, Pf0_polar, LinearMap.zero_apply] at e; simpa using e
  funext c; fin_cases c <;> assumption

/-- **`Alt(5,q)` as a sealed `FormAdapter`** — the first concrete non-quadratic Route-C family. Assembles the
Plücker quadrics via `multiFormAdapter`; `G₀ = ⨅ₖ O(Pf_k)` is the joint isometry group. -/
noncomputable def alternatingAdapter : FormAdapter (p := p) (d := 10) (10 + 1) :=
  multiFormAdapter pluckerForms plucker_hjoint

/-- **`Alt(5,q)` reaches the rigid-or-Cameron disjunction** — the alternating family sealed, via the shared
engine. The whole chain (Plücker forms → `hjoint` → `multiFormAdapter` → `FormAdapter.reachesRigidOrCameron`)
is axiom-clean. -/
theorem reachesRigidOrCameron_alternating
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} :
    ((SchemeBlockRecovered (p ^ 10)
          (ChainDescent.affineScheme alternatingAdapter.G₀ alternatingAdapter.neg_mem)
        ∨ AbelianConsumed (p ^ 10)
          (ChainDescent.affineScheme alternatingAdapter.G₀ alternatingAdapter.neg_mem))
        ∨ SchemeRecoveredByDepth (p ^ 10)
          (ChainDescent.affineScheme alternatingAdapter.G₀ alternatingAdapter.neg_mem) (10 + 1))
      ∨ IsCameronScheme (p ^ 10)
          (ChainDescent.affineScheme alternatingAdapter.G₀ alternatingAdapter.neg_mem) :=
  alternatingAdapter.reachesRigidOrCameron

/-- **`Alt(5,q)` brick-1 (concrete) — the recovered joint-isometry scheme refines the cone-stabilizer scheme.**
The generic `multiIsometryScheme_refines_coneScheme` fired on the actual Plücker family: the recovered scheme
`affineScheme alternatingAdapter.G₀` (= `⨅ₖ O(Pf_k)`) refines the graph-intrinsic cone-stabilizer scheme of
`pluckerForms`. Confirms the multi-quadric refinement bridge is applicable to `Alt(5,q)`, giving it the same
refinement leg the affine-polar instance has. Axiom-clean. -/
theorem alternating_refines_coneScheme {x y x' y' : Fin (p ^ 10)}
    (h : (ChainDescent.affineScheme alternatingAdapter.G₀ alternatingAdapter.neg_mem).relOfPair x y
        = (ChainDescent.affineScheme alternatingAdapter.G₀ alternatingAdapter.neg_mem).relOfPair x' y') :
    (ChainDescent.affineScheme (jointConeStab pluckerForms)
          (neg_mem_jointConeStab pluckerForms)).relOfPair x y
      = (ChainDescent.affineScheme (jointConeStab pluckerForms)
          (neg_mem_jointConeStab pluckerForms)).relOfPair x' y' :=
  multiIsometryScheme_refines_coneScheme pluckerForms alternatingAdapter.neg_mem h

end Plucker

/-! ## Half-spin family (instance 3) — scoping + the reduction target

The half-spin graph is the **D₅ half-spin** action: `Spin₁₀(q)` on the 16-dimensional half-spin (spinor)
module `V = 𝔽_q^16`, a rank-3 group. The connection set is the cone of **pure spinors** (the highest-weight
orbit = the spinor variety `S₅ ⊂ P^15`), cut out by **10 quadratic equations** (matching the 10-dim vector
representation of D₅). So half-spin is — like alternating — a **MULTI-QUADRIC family**, and reuses the SAME
engine: `multiFormAdapter` + `coords_determine_multi` (both landed, axiom-clean). **No new engine is needed.**

`halfSpin_reduction` below makes the target concrete: it commits the D₅ dimensions (module `Fin 16`, family
`Fin 10`) and shows that supplying the 10 spinor quadrics `Qs` with joint nondegeneracy `hjoint` **seals the
family** via the shared engine. So the entire remaining half-spin work is exactly: **define the 10 D₅ spinor
quadrics on `𝔽_p^16` (the even-subset / Clifford model — a careful representation-theoretic derivation, do NOT
template blindly) and prove their `hjoint`.** The polar of each (a sum of `linMulLin` terms) is computed via
`polar_linMulLin` + the `simp only [polar, add_apply, sub_apply, linMulLin_apply, proj_apply]; ring` pattern
(as in `§Plucker`), and `hjoint` by the coordinate-isolation pattern of `plucker_hjoint`. -/

namespace HalfSpin

/-- **Half-spin reduction (instance 3 target).** Committing the D₅ dimensions: any family of 10 quadratic
forms `Qs` on `𝔽_p^16` (the half-spin module) with joint nondegeneracy `hjoint` is **sealed** — its affine
scheme (`G₀ = ⨅ₖ O(Q_k)`) reaches the rigid-or-Cameron disjunction, via `multiFormAdapter` + the shared engine.
So the only remaining half-spin content is constructing the 10 D₅ spinor quadrics and proving `hjoint`. -/
theorem halfSpin_reduction
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop}
    (Qs : Fin 10 → QuadraticForm (ZMod p) (Fin 16 → ZMod p))
    (hjoint : ∀ w : Fin 16 → ZMod p, (∀ k, (Qs k).polarBilin w = 0) → w = 0) :
    ((SchemeBlockRecovered (p ^ 16)
          (ChainDescent.affineScheme (multiFormAdapter Qs hjoint).G₀ (multiFormAdapter Qs hjoint).neg_mem)
        ∨ AbelianConsumed (p ^ 16)
          (ChainDescent.affineScheme (multiFormAdapter Qs hjoint).G₀ (multiFormAdapter Qs hjoint).neg_mem))
        ∨ SchemeRecoveredByDepth (p ^ 16)
          (ChainDescent.affineScheme (multiFormAdapter Qs hjoint).G₀ (multiFormAdapter Qs hjoint).neg_mem)
          (16 + 1))
      ∨ IsCameronScheme (p ^ 16)
          (ChainDescent.affineScheme (multiFormAdapter Qs hjoint).G₀ (multiFormAdapter Qs hjoint).neg_mem) :=
  (multiFormAdapter Qs hjoint).reachesRigidOrCameron

/-! ### The concrete half-spin instance — the 10 D₅ spinor quadrics + the sealed adapter

The 10 quadratic equations of the pure-spinor cone (`= 0` on the spinor variety `S₅`) were found and validated
by `route_c_halfspin_probe.py` (2026-07-03): generate genuine pure spinors via the char-free big-cell Pfaffian
formula and fit the degree-2 vanishing ideal — **dim `= 10`** exactly (q=3,5,7,11), **EXACT `𝔽₂` zero-locus count
`= 2296 = 1+(q−1)∏₁⁴(qⁱ+1)`** (the forms cut *precisely* the cone), **joint polar radical `= 0`** (this `hjoint`),
and it holds already from the 5 "quadruple" forms `S0..S4`. Index the 16 half-spin coords (even subsets of
`{1..5}`) as `Fin 16`: `0:∅`; pairs `1:12 2:13 3:23 4:14 5:24 6:34 7:15 8:25 9:35 10:45`; quadruples
`11:1234 12:1235 13:1245 14:1345 15:2345`. Each form is a 4-term `linMulLin` sum (like the Plücker `Pf`); the
signs below are the probe's forms negated (irrelevant: `O(Q)=O(−Q)`, and the cone/radical are sign-blind), chosen
so each starts with a `+` term. `S0..S4` are the quadruple relations `x_∅·x_{ijkl} = Pf(pairs)`; `S5..S9` the
pair×quadruple relations (needed so the joint cone models the graph, not for `hjoint`). All axiom-clean. -/

open QuadraticMap

/-- The `i`-th half-spin coordinate projection on `𝔽_p^16`. -/
noncomputable def sc (i : Fin 16) : (Fin 16 → ZMod p) →ₗ[ZMod p] ZMod p := LinearMap.proj i

/-- Quadruple form for `1234` (`x_∅x_{1234} = Pf`). -/
noncomputable def S0 : QuadraticForm (ZMod p) (Fin 16 → ZMod p) :=
  linMulLin (sc 0) (sc 11) - linMulLin (sc 1) (sc 6) + linMulLin (sc 2) (sc 5) - linMulLin (sc 3) (sc 4)
/-- Quadruple form for `1235`. -/
noncomputable def S1 : QuadraticForm (ZMod p) (Fin 16 → ZMod p) :=
  linMulLin (sc 0) (sc 12) - linMulLin (sc 1) (sc 9) + linMulLin (sc 2) (sc 8) - linMulLin (sc 3) (sc 7)
/-- Quadruple form for `1245`. -/
noncomputable def S2 : QuadraticForm (ZMod p) (Fin 16 → ZMod p) :=
  linMulLin (sc 0) (sc 13) - linMulLin (sc 1) (sc 10) + linMulLin (sc 4) (sc 8) - linMulLin (sc 5) (sc 7)
/-- Quadruple form for `1345`. -/
noncomputable def S3 : QuadraticForm (ZMod p) (Fin 16 → ZMod p) :=
  linMulLin (sc 0) (sc 14) - linMulLin (sc 2) (sc 10) + linMulLin (sc 4) (sc 9) - linMulLin (sc 6) (sc 7)
/-- Quadruple form for `2345`. -/
noncomputable def S4 : QuadraticForm (ZMod p) (Fin 16 → ZMod p) :=
  linMulLin (sc 0) (sc 15) - linMulLin (sc 3) (sc 10) + linMulLin (sc 5) (sc 9) - linMulLin (sc 6) (sc 8)
/-- Pair×quadruple form 5. -/
noncomputable def S5 : QuadraticForm (ZMod p) (Fin 16 → ZMod p) :=
  linMulLin (sc 1) (sc 14) - linMulLin (sc 2) (sc 13) + linMulLin (sc 4) (sc 12) - linMulLin (sc 7) (sc 11)
/-- Pair×quadruple form 6. -/
noncomputable def S6 : QuadraticForm (ZMod p) (Fin 16 → ZMod p) :=
  linMulLin (sc 1) (sc 15) - linMulLin (sc 3) (sc 13) + linMulLin (sc 5) (sc 12) - linMulLin (sc 8) (sc 11)
/-- Pair×quadruple form 7. -/
noncomputable def S7 : QuadraticForm (ZMod p) (Fin 16 → ZMod p) :=
  linMulLin (sc 2) (sc 15) - linMulLin (sc 3) (sc 14) + linMulLin (sc 6) (sc 12) - linMulLin (sc 9) (sc 11)
/-- Pair×quadruple form 8. -/
noncomputable def S8 : QuadraticForm (ZMod p) (Fin 16 → ZMod p) :=
  linMulLin (sc 4) (sc 15) - linMulLin (sc 5) (sc 14) + linMulLin (sc 6) (sc 13) - linMulLin (sc 10) (sc 11)
/-- Pair×quadruple form 9. -/
noncomputable def S9 : QuadraticForm (ZMod p) (Fin 16 → ZMod p) :=
  linMulLin (sc 7) (sc 15) - linMulLin (sc 8) (sc 14) + linMulLin (sc 9) (sc 13) - linMulLin (sc 10) (sc 12)

/-- The family of 10 D₅ spinor quadrics (their joint cone = the pure-spinor cone = the half-spin connection set). -/
noncomputable def spinorForms : Fin 10 → QuadraticForm (ZMod p) (Fin 16 → ZMod p)
  | 0 => S0 | 1 => S1 | 2 => S2 | 3 => S3 | 4 => S4
  | 5 => S5 | 6 => S6 | 7 => S7 | 8 => S8 | 9 => S9

theorem S0_polar (x y : Fin 16 → ZMod p) : polar S0 x y =
    x 0 * y 11 + y 0 * x 11 - (x 1 * y 6 + y 1 * x 6) + (x 2 * y 5 + y 2 * x 5) - (x 3 * y 4 + y 3 * x 4) := by
  simp only [polar, S0, QuadraticMap.add_apply, QuadraticMap.sub_apply, linMulLin_apply, sc,
    LinearMap.proj_apply, Pi.add_apply]; ring
theorem S1_polar (x y : Fin 16 → ZMod p) : polar S1 x y =
    x 0 * y 12 + y 0 * x 12 - (x 1 * y 9 + y 1 * x 9) + (x 2 * y 8 + y 2 * x 8) - (x 3 * y 7 + y 3 * x 7) := by
  simp only [polar, S1, QuadraticMap.add_apply, QuadraticMap.sub_apply, linMulLin_apply, sc,
    LinearMap.proj_apply, Pi.add_apply]; ring
theorem S2_polar (x y : Fin 16 → ZMod p) : polar S2 x y =
    x 0 * y 13 + y 0 * x 13 - (x 1 * y 10 + y 1 * x 10) + (x 4 * y 8 + y 4 * x 8) - (x 5 * y 7 + y 5 * x 7) := by
  simp only [polar, S2, QuadraticMap.add_apply, QuadraticMap.sub_apply, linMulLin_apply, sc,
    LinearMap.proj_apply, Pi.add_apply]; ring
theorem S3_polar (x y : Fin 16 → ZMod p) : polar S3 x y =
    x 0 * y 14 + y 0 * x 14 - (x 2 * y 10 + y 2 * x 10) + (x 4 * y 9 + y 4 * x 9) - (x 6 * y 7 + y 6 * x 7) := by
  simp only [polar, S3, QuadraticMap.add_apply, QuadraticMap.sub_apply, linMulLin_apply, sc,
    LinearMap.proj_apply, Pi.add_apply]; ring
theorem S4_polar (x y : Fin 16 → ZMod p) : polar S4 x y =
    x 0 * y 15 + y 0 * x 15 - (x 3 * y 10 + y 3 * x 10) + (x 5 * y 9 + y 5 * x 9) - (x 6 * y 8 + y 6 * x 8) := by
  simp only [polar, S4, QuadraticMap.add_apply, QuadraticMap.sub_apply, linMulLin_apply, sc,
    LinearMap.proj_apply, Pi.add_apply]; ring

/-- **The 10 spinor quadrics are jointly nondegenerate** (trivial common polar radical) — the `hjoint` the
half-spin adapter needs. Provable from the 5 quadruple forms `S0..S4` alone (probe-confirmed: their polar radical
is already `0`): each `S_a` isolates coord `∅` (via `e_{quad}`), its own quadruple (via `e_∅`), and 6 pair coords,
and the 5 together cover all 16. Mirrors `plucker_hjoint`. Axiom-clean. -/
theorem spinor_hjoint (w : Fin 16 → ZMod p)
    (h : ∀ k, (spinorForms k).polarBilin w = 0) : w = 0 := by
  have h0 : S0.polarBilin w = 0 := h 0
  have h1 : S1.polarBilin w = 0 := h 1
  have h2 : S2.polarBilin w = 0 := h 2
  have h3 : S3.polarBilin w = 0 := h 3
  have h4 : S4.polarBilin w = 0 := h 4
  have w0 : w 0 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (11 : Fin 16) 1)
    rw [polarBilin_apply_apply, S0_polar, LinearMap.zero_apply] at e; simpa using e
  have w1 : w 1 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (6 : Fin 16) 1)
    rw [polarBilin_apply_apply, S0_polar, LinearMap.zero_apply] at e; simpa using e
  have w2 : w 2 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (5 : Fin 16) 1)
    rw [polarBilin_apply_apply, S0_polar, LinearMap.zero_apply] at e; simpa using e
  have w3 : w 3 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (4 : Fin 16) 1)
    rw [polarBilin_apply_apply, S0_polar, LinearMap.zero_apply] at e; simpa using e
  have w4 : w 4 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (3 : Fin 16) 1)
    rw [polarBilin_apply_apply, S0_polar, LinearMap.zero_apply] at e; simpa using e
  have w5 : w 5 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (2 : Fin 16) 1)
    rw [polarBilin_apply_apply, S0_polar, LinearMap.zero_apply] at e; simpa using e
  have w6 : w 6 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (1 : Fin 16) 1)
    rw [polarBilin_apply_apply, S0_polar, LinearMap.zero_apply] at e; simpa using e
  have w7 : w 7 = 0 := by
    have e := LinearMap.congr_fun h1 (Pi.single (3 : Fin 16) 1)
    rw [polarBilin_apply_apply, S1_polar, LinearMap.zero_apply] at e; simpa using e
  have w8 : w 8 = 0 := by
    have e := LinearMap.congr_fun h1 (Pi.single (2 : Fin 16) 1)
    rw [polarBilin_apply_apply, S1_polar, LinearMap.zero_apply] at e; simpa using e
  have w9 : w 9 = 0 := by
    have e := LinearMap.congr_fun h1 (Pi.single (1 : Fin 16) 1)
    rw [polarBilin_apply_apply, S1_polar, LinearMap.zero_apply] at e; simpa using e
  have w10 : w 10 = 0 := by
    have e := LinearMap.congr_fun h2 (Pi.single (1 : Fin 16) 1)
    rw [polarBilin_apply_apply, S2_polar, LinearMap.zero_apply] at e; simpa using e
  have w11 : w 11 = 0 := by
    have e := LinearMap.congr_fun h0 (Pi.single (0 : Fin 16) 1)
    rw [polarBilin_apply_apply, S0_polar, LinearMap.zero_apply] at e; simpa using e
  have w12 : w 12 = 0 := by
    have e := LinearMap.congr_fun h1 (Pi.single (0 : Fin 16) 1)
    rw [polarBilin_apply_apply, S1_polar, LinearMap.zero_apply] at e; simpa using e
  have w13 : w 13 = 0 := by
    have e := LinearMap.congr_fun h2 (Pi.single (0 : Fin 16) 1)
    rw [polarBilin_apply_apply, S2_polar, LinearMap.zero_apply] at e; simpa using e
  have w14 : w 14 = 0 := by
    have e := LinearMap.congr_fun h3 (Pi.single (0 : Fin 16) 1)
    rw [polarBilin_apply_apply, S3_polar, LinearMap.zero_apply] at e; simpa using e
  have w15 : w 15 = 0 := by
    have e := LinearMap.congr_fun h4 (Pi.single (0 : Fin 16) 1)
    rw [polarBilin_apply_apply, S4_polar, LinearMap.zero_apply] at e; simpa using e
  funext c; fin_cases c <;> assumption

/-- **The D₅ half-spin family as a sealed `FormAdapter`.** Assembles the 10 spinor quadrics via
`multiFormAdapter`; `G₀ = ⨅ₖ O(S_k)` is their joint isometry group. -/
noncomputable def spinAdapter : FormAdapter (p := p) (d := 16) (16 + 1) :=
  multiFormAdapter spinorForms spinor_hjoint

/-- **Half-spin reaches the rigid-or-Cameron disjunction** — instance 3 SEALED, via the shared engine. The whole
chain (10 validated spinor quadrics → `spinor_hjoint` → `multiFormAdapter` → `FormAdapter.reachesRigidOrCameron`)
is axiom-clean. With the generic multi-quadric bridges (`multiIsometryScheme_refines_coneScheme`,
`recoveredFamily_colouring_equivariant`), half-spin is at full instance-1 parity. -/
theorem reachesRigidOrCameron_halfSpin
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} :
    ((SchemeBlockRecovered (p ^ 16)
          (ChainDescent.affineScheme spinAdapter.G₀ spinAdapter.neg_mem)
        ∨ AbelianConsumed (p ^ 16)
          (ChainDescent.affineScheme spinAdapter.G₀ spinAdapter.neg_mem))
        ∨ SchemeRecoveredByDepth (p ^ 16)
          (ChainDescent.affineScheme spinAdapter.G₀ spinAdapter.neg_mem) (16 + 1))
      ∨ IsCameronScheme (p ^ 16)
          (ChainDescent.affineScheme spinAdapter.G₀ spinAdapter.neg_mem) :=
  spinAdapter.reachesRigidOrCameron

/-- **Half-spin brick-1 (concrete)** — the recovered joint-isometry scheme refines the graph-intrinsic
cone-stabilizer scheme of the spinor forms. The generic `multiIsometryScheme_refines_coneScheme` on the real
`spinorForms` family, giving half-spin the refinement leg (parity with alternating / affine-polar). Axiom-clean. -/
theorem halfSpin_refines_coneScheme {x y x' y' : Fin (p ^ 16)}
    (h : (ChainDescent.affineScheme spinAdapter.G₀ spinAdapter.neg_mem).relOfPair x y
        = (ChainDescent.affineScheme spinAdapter.G₀ spinAdapter.neg_mem).relOfPair x' y') :
    (ChainDescent.affineScheme (jointConeStab spinorForms)
          (neg_mem_jointConeStab spinorForms)).relOfPair x y
      = (ChainDescent.affineScheme (jointConeStab spinorForms)
          (neg_mem_jointConeStab spinorForms)).relOfPair x' y' :=
  multiIsometryScheme_refines_coneScheme spinorForms spinAdapter.neg_mem h

end HalfSpin

/-! ## Suzuki–Tits family (instance 4) — the σ-twisted ovoid forms (rederivation)

The Suzuki–Tits graph `VSz(q)` (`q = 2^{2e+1}`) is the Cayley graph on `GF(q)^4` whose connection set is the
cone over the **Tits ovoid** `O = {(1,a,b, ab + a^{σ+2} + b^σ)} ∪ {(0,0,0,1)}`, where `σ` is the **Tits
endomorphism** (`σ∘σ = Frobenius = (·)²`). Unlike the other three families the ovoid is **not** cut by quadratic
forms, and (de-risk `route_c_suzuki_probe.py`, q=8) **not** by any single σ-twisted form either — but its cone IS
the **joint** zero locus of a **5-dim family of σ-twisted type-(1,2) forms** `σ(xₐ)·x_b·x_c` (validated: joint
zero = cone EXACTLY, |·|=456; and the joint value-profile separates at base `4 ≤ d+1` ⟹ poly, the
`coords_determine_multi` mechanism). So Suzuki is the **σ-twisted sibling of alternating/half-spin**.

This section **rederives the 5 forms in Lean** (canonical, representation-independent: all-unit coefficients) over
an abstract char-2 commutative ring `K` with a Tits endomorphism `σ`, and proves the core fact that they cut the
cone: each `SF_k` (i) **vanishes on the affine ovoid** `(1, a, b, ovoidC a b)` [via `σ` a ring hom + `σ∘σ=(·)²`],
(ii) **vanishes at infinity** `(0,0,0,1)`, and (iii) is **σ-twisted homogeneous** (`SF_k(λx) = σλ·λ²·SF_k(x)`), so
by (i)+(ii)+(iii) it vanishes on the whole cone. All axiom-clean. `SF0` = the single derived form
`x₃x₀^{σ+1}+x₁x₂x₀^σ+x₁^{σ+2}+x₂^σx₀²`; `SF1..SF4` trim its spurious zeros. The remaining Suzuki work (the σ-twisted
`coords_determine_multi` = `separates`, and the `GF(q)^4 ↔ 𝔽₂^d` module bridge to the char-2-ready engine) is the
next step; here the forms themselves are landed and proven to model the connection set. -/

namespace Suzuki

variable {K : Type*} [CommRing K] [CharP K 2] (σ : K →+* K)

/-- The 4th ovoid coordinate: `c = a·b + a^{σ+2} + b^σ = a·b + σa·a² + σb` (affine chart `x₀=1`). -/
def ovoidC (a b : K) : K := a * b + σ a * a ^ 2 + σ b

/-- Suzuki σ-twisted form 0 (= the single derived `F`; `x₃x₀^{σ+1}+x₁x₂x₀^σ+x₁^{σ+2}+x₂^σx₀²`). -/
def SF0 (x0 x1 x2 x3 : K) : K :=
  σ x0 * x0 * x3 + σ x0 * x1 * x2 + σ x1 * x1 ^ 2 + σ x2 * x0 ^ 2
/-- Suzuki σ-twisted form 1. -/
def SF1 (x0 x1 x2 x3 : K) : K :=
  σ x0 * x2 ^ 2 + σ x1 * x0 * x3 + σ x1 * x1 * x2 + σ x3 * x0 ^ 2
/-- Suzuki σ-twisted form 2. -/
def SF2 (x0 x1 x2 x3 : K) : K :=
  σ x0 * x2 * x3 + σ x1 * x1 * x3 + σ x2 * x0 * x2 + σ x3 * x0 * x1
/-- Suzuki σ-twisted form 3. -/
def SF3 (x0 x1 x2 x3 : K) : K :=
  σ x0 * x3 ^ 2 + σ x2 * x0 * x3 + σ x2 * x1 * x2 + σ x3 * x1 ^ 2
/-- Suzuki σ-twisted form 4. -/
def SF4 (x0 x1 x2 x3 : K) : K :=
  σ x1 * x3 ^ 2 + σ x2 * x2 ^ 2 + σ x3 * x0 * x3 + σ x3 * x1 * x2

/-- The 5 forms as a family (`ι = Fin 5`), for the eventual joint-value adapter. -/
def suzukiForms (x0 x1 x2 x3 : K) : Fin 5 → K
  | 0 => SF0 σ x0 x1 x2 x3 | 1 => SF1 σ x0 x1 x2 x3 | 2 => SF2 σ x0 x1 x2 x3
  | 3 => SF3 σ x0 x1 x2 x3 | 4 => SF4 σ x0 x1 x2 x3

/-- `(4 : K) = 0` in char 2 (`4 = 2·2`, `2 = 0`) — clears the `·4` coefficients `ring_nf` produces when four
equal monomials collect. -/
theorem four_eq_zero : (4 : K) = 0 := by
  rw [show (4 : K) = 2 * 2 from by norm_num, CharTwo.two_eq_zero, zero_mul]

/-- `SF0` vanishes on the affine ovoid (needs no `σ∘σ` — `SF0` is linear in `x₃`). -/
theorem SF0_ovoid (a b : K) : SF0 σ 1 a b (ovoidC σ a b) = 0 := by
  simp only [SF0, ovoidC, map_one, one_mul, mul_one]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

theorem SF1_ovoid (hσ : ∀ x : K, σ (σ x) = x ^ 2) (a b : K) :
    SF1 σ 1 a b (ovoidC σ a b) = 0 := by
  simp only [SF1, ovoidC, map_one, one_mul, mul_one, map_add, map_mul, map_pow, hσ]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

theorem SF2_ovoid (hσ : ∀ x : K, σ (σ x) = x ^ 2) (a b : K) :
    SF2 σ 1 a b (ovoidC σ a b) = 0 := by
  simp only [SF2, ovoidC, map_one, one_mul, mul_one, map_add, map_mul, map_pow, hσ]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

theorem SF3_ovoid (hσ : ∀ x : K, σ (σ x) = x ^ 2) (a b : K) :
    SF3 σ 1 a b (ovoidC σ a b) = 0 := by
  simp only [SF3, ovoidC, map_one, one_mul, mul_one, map_add, map_mul, map_pow, hσ]
  ring_nf
  simp only [CharTwo.two_eq_zero, four_eq_zero, mul_zero, add_zero]

theorem SF4_ovoid (hσ : ∀ x : K, σ (σ x) = x ^ 2) (a b : K) :
    SF4 σ 1 a b (ovoidC σ a b) = 0 := by
  simp only [SF4, ovoidC, mul_one, map_add, map_mul, map_pow, hσ]
  ring_nf
  simp only [CharTwo.two_eq_zero, four_eq_zero, mul_zero, add_zero]

/-- All 5 forms vanish on the affine ovoid (packaged over `Fin 5`). -/
theorem suzukiForms_ovoid (hσ : ∀ x : K, σ (σ x) = x ^ 2) (a b : K) (k : Fin 5) :
    suzukiForms σ 1 a b (ovoidC σ a b) k = 0 := by
  fin_cases k
  · exact SF0_ovoid σ a b
  · exact SF1_ovoid σ hσ a b
  · exact SF2_ovoid σ hσ a b
  · exact SF3_ovoid σ hσ a b
  · exact SF4_ovoid σ hσ a b

omit [CharP K 2] in
/-- All 5 forms vanish at the point at infinity `(0,0,0,1)`. -/
theorem suzukiForms_infty (k : Fin 5) : suzukiForms σ 0 0 0 1 k = 0 := by
  fin_cases k <;> simp [suzukiForms, SF0, SF1, SF2, SF3, SF4, map_zero]

omit [CharP K 2] in
/-- **σ-twisted homogeneity** — `SF_k(λ·x) = σλ·λ²·SF_k(x)`, so `{SF_k=0}` is a cone (and vanishing on the
ovoid + at infinity ⟹ vanishing on the whole connection set). Pure ring identity via `σ` multiplicative. -/
theorem suzukiForms_homog (l x0 x1 x2 x3 : K) (k : Fin 5) :
    suzukiForms σ (l * x0) (l * x1) (l * x2) (l * x3) k
      = σ l * l ^ 2 * suzukiForms σ x0 x1 x2 x3 k := by
  fin_cases k <;>
    simp only [suzukiForms, SF0, SF1, SF2, SF3, SF4, map_mul] <;> ring

/-! ### The σ-twisted `separates` (instance 4) — the value-profile determiner, PROVED citation-free

`separates` for Suzuki is the σ-twisted analog of `coords_determine_multi`: the joint `F_k`-value profile
determines the vertex. **It is PROVED outright (no citation, no `hσ`, no field-size hypothesis).** The earlier
draft carried it as a scoped citation `SuzukiFormsDetermine` — true for `GF(2^{2e+1})` but requiring the deep
`Sz(q)` 2-transitivity, because the *first-order* frame `{0, eⱼ}` gives only nonlinear, large-`q`-only recovery
(that frame IS injective for q=8/q=32 — verified `route_c_suzuki_determine_probe.py` — so the citation was
correct, just heavy). The discharge (§ recovery identities above) instead uses the enlarged base
`{0, eᵢ, eⱼ, eᵢ+eⱼ}`: each coordinate is a **second discrete derivative** of one σ-form, which in char 2 collapses
to a bare coordinate (`Dᵢ Dⱼ SF_k = x_·`, σ-terms and constants cancel). So the determiner is elementary char-2
algebra, valid over ANY `CharP K 2` ring. Base grows `4+1 → 8` (still `O(d²)`, poly). This makes instance 4 a
fully unconditional seal, on par with `affinePolarAdapter` (which still carries `NondegQuadricDeterminesForm`). -/

/-- The Suzuki form family as a function of a vector `v : Fin 4 → K`. -/
def SFv (v : Fin 4 → K) (k : Fin 5) : K := suzukiForms σ (v 0) (v 1) (v 2) (v 3) k

/-- A map preserves the σ-twisted Suzuki forms (the joint-isometry condition): `F_k(g w) = F_k(w)` for all
`w, k`. The joint σ-form isometry group is `{g : PreservesForms σ g}`; its orbit-of-difference relation is the
Route-C isometry-scheme colouring. -/
def PreservesForms (g : (Fin 4 → K) → (Fin 4 → K)) : Prop := ∀ w k, SFv σ (g w) k = SFv σ w k

/-! #### The recovery identities — a citation-free discharge of `separates`

The joint-value determiner is **provable outright** (no `Sz(q)` citation, no `hσ`, no field-size hypothesis) once
the base is enlarged from the first-order frame `{0, eⱼ}` to include **pairwise sums** `{0, eᵢ, eⱼ, eᵢ+eⱼ}`. The
reason: each coordinate is a **second discrete derivative** of one σ-form, `Dᵢ Dⱼ SF_k(v) := SF_k(v) + SF_k(v−eᵢ)
+ SF_k(v−eⱼ) + SF_k(v−eᵢ−eⱼ)`, and in char 2 the σ-terms and constants of that alternating sum **cancel**,
collapsing it to a bare coordinate. E.g. `D₀ D₁ SF0 = x₂` (verified by hand and over `GF(8)`/`GF(32)`,
`route_c_suzuki_determine_probe.py`). So `separates` follows from **formal char-2 ring identities**, valid over any
`CharP K 2` ring with `σ` a ring hom — replacing the old scoped citation `SuzukiFormsDetermine` (which was true but
required the deep `Sz(q)` 2-transitivity because the first-order frame gives only nonlinear, large-`q`-only
recovery). The base grows `4+1 → 8` (still `O(d²)`, poly). The four identities, one per coordinate:

* `x₂ = D₀D₁ SF0`,  `x₃ = D₀D₁ SF1`,  `x₀ = D₁D₃ SF1`,  `x₁ = D₂D₃ SF4`.  -/

/-- Recovery of `x₂` — the 2nd discrete derivative `D₀D₁ SF0` collapses to `x₂` (σ-terms cancel in char 2). -/
theorem SF0_recover (x0 x1 x2 x3 : K) :
    SF0 σ x0 x1 x2 x3 + SF0 σ (x0 - 1) x1 x2 x3 + SF0 σ x0 (x1 - 1) x2 x3
      + SF0 σ (x0 - 1) (x1 - 1) x2 x3 = x2 := by
  simp only [SF0, map_sub, map_one]; ring_nf
  simp only [CharTwo.two_eq_zero, four_eq_zero, mul_zero, sub_zero]
  abel

/-- Recovery of `x₃` — `D₀D₁ SF1 = x₃`. -/
theorem SF1_recover_x3 (x0 x1 x2 x3 : K) :
    SF1 σ x0 x1 x2 x3 + SF1 σ (x0 - 1) x1 x2 x3 + SF1 σ x0 (x1 - 1) x2 x3
      + SF1 σ (x0 - 1) (x1 - 1) x2 x3 = x3 := by
  simp only [SF1, map_sub, map_one]; ring_nf
  simp only [CharTwo.two_eq_zero, four_eq_zero, mul_zero, sub_zero]
  abel

/-- Recovery of `x₀` — `D₁D₃ SF1 = x₀`. -/
theorem SF1_recover_x0 (x0 x1 x2 x3 : K) :
    SF1 σ x0 x1 x2 x3 + SF1 σ x0 (x1 - 1) x2 x3 + SF1 σ x0 x1 x2 (x3 - 1)
      + SF1 σ x0 (x1 - 1) x2 (x3 - 1) = x0 := by
  simp only [SF1, map_sub, map_one]; ring_nf
  simp only [CharTwo.two_eq_zero, four_eq_zero, mul_zero, sub_zero]
  abel

/-- Recovery of `x₁` — `D₂D₃ SF4 = x₁`. -/
theorem SF4_recover_x1 (x0 x1 x2 x3 : K) :
    SF4 σ x0 x1 x2 x3 + SF4 σ x0 x1 (x2 - 1) x3 + SF4 σ x0 x1 x2 (x3 - 1)
      + SF4 σ x0 x1 (x2 - 1) (x3 - 1) = x1 := by
  simp only [SF4, map_sub, map_one]; ring_nf
  simp only [CharTwo.two_eq_zero, four_eq_zero, mul_zero, sub_zero]
  abel

omit [CharP K 2] in
/-- A form-preserving map that carries `b` to `a` equalizes the form-values: `F_k a = F_k b`. The provable
"orbit ⟹ equal-values" half (the σ-twisted analog of "an isometry preserves the `Q`-value of a difference"). -/
theorem preservesForms_eq {g : (Fin 4 → K) → (Fin 4 → K)} (hg : PreservesForms σ g)
    {a b : Fin 4 → K} (hgab : g b = a) (k : Fin 5) : SFv σ a k = SFv σ b k := by
  rw [← hgab]; exact hg b k

/-- `SFv`-level recovery of `x₂` (`D₀D₁ SF0`), lifting `SF0_recover` through the coordinate evaluation. -/
theorem recover_x2 (v : Fin 4 → K) :
    SFv σ v 0 + SFv σ (v - Pi.single 0 1) 0 + SFv σ (v - Pi.single 1 1) 0
      + SFv σ (v - Pi.single 0 1 - Pi.single 1 1) 0 = v 2 := by
  simp only [SFv, suzukiForms, Pi.sub_apply, Pi.single_apply, Fin.reduceEq, if_true, if_false, sub_zero]
  exact SF0_recover σ (v 0) (v 1) (v 2) (v 3)

/-- `SFv`-level recovery of `x₃` (`D₀D₁ SF1`). -/
theorem recover_x3 (v : Fin 4 → K) :
    SFv σ v 1 + SFv σ (v - Pi.single 0 1) 1 + SFv σ (v - Pi.single 1 1) 1
      + SFv σ (v - Pi.single 0 1 - Pi.single 1 1) 1 = v 3 := by
  simp only [SFv, suzukiForms, Pi.sub_apply, Pi.single_apply, Fin.reduceEq, if_true, if_false, sub_zero]
  exact SF1_recover_x3 σ (v 0) (v 1) (v 2) (v 3)

/-- `SFv`-level recovery of `x₀` (`D₁D₃ SF1`). -/
theorem recover_x0 (v : Fin 4 → K) :
    SFv σ v 1 + SFv σ (v - Pi.single 1 1) 1 + SFv σ (v - Pi.single 3 1) 1
      + SFv σ (v - Pi.single 1 1 - Pi.single 3 1) 1 = v 0 := by
  simp only [SFv, suzukiForms, Pi.sub_apply, Pi.single_apply, Fin.reduceEq, if_true, if_false, sub_zero]
  exact SF1_recover_x0 σ (v 0) (v 1) (v 2) (v 3)

/-- `SFv`-level recovery of `x₁` (`D₂D₃ SF4`). -/
theorem recover_x1 (v : Fin 4 → K) :
    SFv σ v 4 + SFv σ (v - Pi.single 2 1) 4 + SFv σ (v - Pi.single 3 1) 4
      + SFv σ (v - Pi.single 2 1 - Pi.single 3 1) 4 = v 1 := by
  simp only [SFv, suzukiForms, Pi.sub_apply, Pi.single_apply, Fin.reduceEq, if_true, if_false, sub_zero]
  exact SF4_recover_x1 σ (v 0) (v 1) (v 2) (v 3)

/-- **The σ-twisted `separates` determiner (instance 4) — PROVED, no citation.** If `v` and `v'` have equal
joint `F_k`-values at the enlarged base `{0, e₀, e₁, e₂, e₃, e₀+e₁, e₁+e₃, e₂+e₃}`, then `v = v'`. Each coordinate
is read off by one recovery identity (a 2nd discrete derivative), so this is elementary char-2 algebra — the
σ-twisted analog of `coords_determine_multi`, but with **no** scoped citation, **no** `hσ`, and **no** field-size
hypothesis (it holds over any `CharP K 2` ring). Replaces the old carried `SuzukiFormsDetermine`. -/
theorem suzukiForms_determine {v v' : Fin 4 → K}
    (h0 : ∀ k, SFv σ v k = SFv σ v' k)
    (he0 : ∀ k, SFv σ (v - Pi.single 0 1) k = SFv σ (v' - Pi.single 0 1) k)
    (he1 : ∀ k, SFv σ (v - Pi.single 1 1) k = SFv σ (v' - Pi.single 1 1) k)
    (he2 : ∀ k, SFv σ (v - Pi.single 2 1) k = SFv σ (v' - Pi.single 2 1) k)
    (he3 : ∀ k, SFv σ (v - Pi.single 3 1) k = SFv σ (v' - Pi.single 3 1) k)
    (he01 : ∀ k, SFv σ (v - Pi.single 0 1 - Pi.single 1 1) k
        = SFv σ (v' - Pi.single 0 1 - Pi.single 1 1) k)
    (he13 : ∀ k, SFv σ (v - Pi.single 1 1 - Pi.single 3 1) k
        = SFv σ (v' - Pi.single 1 1 - Pi.single 3 1) k)
    (he23 : ∀ k, SFv σ (v - Pi.single 2 1 - Pi.single 3 1) k
        = SFv σ (v' - Pi.single 2 1 - Pi.single 3 1) k) :
    v = v' := by
  funext i
  fin_cases i
  · show v 0 = v' 0
    rw [← recover_x0 σ v, h0 1, he1 1, he3 1, he13 1]; exact recover_x0 σ v'
  · show v 1 = v' 1
    rw [← recover_x1 σ v, h0 4, he2 4, he3 4, he23 4]; exact recover_x1 σ v'
  · show v 2 = v' 2
    rw [← recover_x2 σ v, h0 0, he0 0, he1 0, he01 0]; exact recover_x2 σ v'
  · show v 3 = v' 3
    rw [← recover_x3 σ v, h0 1, he0 1, he1 1, he01 1]; exact recover_x3 σ v'

/-! ### The module bridge + the Suzuki adapter (instance 4 seal)

The engine works over the standard `𝔽₂`-space `Fin D → ZMod 2` (`D = 4·dim_{𝔽₂} K`). Bridge the Suzuki data over
`GF(q)^4 = Fin 4 → K` to it via an **additive** iso `Ψ : (Fin D → ZMod 2) ≃+ (Fin 4 → K)` (no `ZMod 2`-module
structure on `K` needed — `PreservesForms` is a function condition, and `Ψ` additive is all the difference-transport
uses). Define the forms in `𝔽₂`-coordinates (`SFbar := SFv ∘ Ψ`), so the joint-isometry group `suzukiG₀` is a clean
subgroup of `(Fin D → ZMod 2) ≃ₗ[ZMod 2] …`. `neg_mem` is free (char 2). `separates` transports the engine's
orbit-profile at the enlarged base (`Ψ`-images of `suzukiBaseVecs`) back through `Ψ` to the PROVED determiner
`suzukiForms_determine`. The result is a `FormAdapter`, sealed by the shared engine →
`reachesRigidOrCameron_suzuki` (citation-free). -/

variable {D : ℕ} (Ψ : (Fin D → ZMod 2) ≃+ (Fin 4 → K))

/-- The Suzuki forms in `𝔽₂`-coordinates via `Ψ`. -/
def SFbar (w : Fin D → ZMod 2) (k : Fin 5) : K := SFv σ (Ψ w) k

/-- **The transported Suzuki joint-isometry group** — the `𝔽₂`-linear autos of `Fin D → ZMod 2` preserving every
`SFbar`. A clean subgroup (the `SFbar`-preservation composes directly; no conjugation gymnastics). -/
def suzukiG₀ : Subgroup ((Fin D → ZMod 2) ≃ₗ[ZMod 2] (Fin D → ZMod 2)) where
  carrier := {g | ∀ w k, SFbar σ Ψ (g w) k = SFbar σ Ψ w k}
  one_mem' := by intro w k; rfl
  mul_mem' := by
    intro a b ha hb w k
    rw [LinearEquiv.mul_apply, ha (b w) k, hb w k]
  inv_mem' := by
    intro a ha w k
    have hx : a (a⁻¹ w) = w := by
      have h := LinearEquiv.mul_apply a a⁻¹ w
      rw [mul_inv_cancel] at h; simpa using h.symm
    have := ha (a⁻¹ w) k
    rw [hx] at this
    exact this.symm

omit [CharP K 2] in
/-- `g ∈ suzukiG₀` ⟹ the `Ψ`-conjugate `w ↦ Ψ(g(Ψ.symm w))` preserves the `K`-forms (`PreservesForms`). The
link from the standard-space isometry to the `K`-side determiner (`base_sfv_eq` / `suzukiForms_determine`). -/
theorem preservesForms_of_mem_G₀ {g : (Fin D → ZMod 2) ≃ₗ[ZMod 2] (Fin D → ZMod 2)}
    (hg : g ∈ suzukiG₀ σ Ψ) : PreservesForms σ (fun v => Ψ (g (Ψ.symm v))) := by
  intro v k
  have := hg (Ψ.symm v) k
  simp only [SFbar, Ψ.apply_symm_apply] at this
  exact this

/-- `-1 ∈ suzukiG₀` — free in char 2 (`Ψ(-w) = -Ψw = Ψw`, so `neg` preserves every `SFbar`). -/
theorem neg_mem_suzukiG₀ : LinearEquiv.neg (ZMod 2) ∈ suzukiG₀ σ Ψ := by
  intro w k
  have h : Ψ (LinearEquiv.neg (ZMod 2) w) = Ψ w := by
    rw [LinearEquiv.neg_apply, map_neg]
    funext i; rw [Pi.neg_apply]; exact CharTwo.neg_eq _
  simp only [SFbar, h]

/-- The base vectors on the `K`-side — the enlarged base `{0, e₀, e₁, e₂, e₃, e₀+e₁, e₁+e₃, e₂+e₃}` (8 points)
whose pairwise sums power the second-derivative recovery. -/
def suzukiBaseVecs : List (Fin 4 → K) :=
  [0, Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1,
   Pi.single 0 1 + Pi.single 1 1, Pi.single 1 1 + Pi.single 3 1, Pi.single 2 1 + Pi.single 3 1]

/-- The individualized base — `Ψ`-images of `suzukiBaseVecs`, transported to `Fin (2^D)` (`≤ 8` points). -/
noncomputable def suzukiBase : Finset (Fin (2 ^ D)) :=
  (suzukiBaseVecs.map (fun b => ChainDescent.affineE (Ψ.symm b))).toFinset

omit [CharP K 2] in
theorem suzukiBase_card_le : (suzukiBase Ψ).card ≤ 8 := by
  unfold suzukiBase
  refine le_trans (List.toFinset_card_le _) ?_
  simp [suzukiBaseVecs]

omit [CharP K 2] in
/-- **The per-base-vector transport.** A `G₀`-orbit witness at the base point `Ψ`-image of `b` gives equality of
the σ-form values of the two vertices' differences by `b` (via `preservesForms_of_mem_G₀` + `preservesForms_eq`). -/
theorem base_sfv_eq {u u' : Fin (2 ^ D)} (b : Fin 4 → K)
    (hb : ∃ g₀ ∈ suzukiG₀ σ Ψ,
       g₀ (ChainDescent.affineE.symm u' - Ψ.symm b) = ChainDescent.affineE.symm u - Ψ.symm b) (k) :
    SFv σ (Ψ (ChainDescent.affineE.symm u) - b) k = SFv σ (Ψ (ChainDescent.affineE.symm u') - b) k := by
  obtain ⟨g, hg, hgeq⟩ := hb
  apply preservesForms_eq σ (preservesForms_of_mem_G₀ σ Ψ hg)
  show Ψ (g (Ψ.symm (Ψ (ChainDescent.affineE.symm u') - b))) = Ψ (ChainDescent.affineE.symm u) - b
  rw [map_sub, Ψ.symm_apply_apply, hgeq, map_sub, Ψ.apply_symm_apply]

/-- **The Suzuki family as a `FormAdapter`** (instance 4). `G₀ = suzukiG₀`, base = the enlarged frame images
(`≤ 8`), `separates` = the transport of the engine orbit-profile to the PROVED determiner `suzukiForms_determine`
(the second-derivative recovery). **No citation, no `hσ`, no field-size hypothesis.** -/
noncomputable def suzukiAdapter :
    FormAdapter (p := 2) (d := D) 8 where
  G₀ := suzukiG₀ σ Ψ
  neg_mem := neg_mem_suzukiG₀ σ Ψ
  base := suzukiBase Ψ
  base_card_le := suzukiBase_card_le Ψ
  separates := by
    intro u u' hh
    have key : ∀ b : Fin 4 → K, b ∈ suzukiBaseVecs → ∀ k,
        SFv σ (Ψ (ChainDescent.affineE.symm u) - b) k = SFv σ (Ψ (ChainDescent.affineE.symm u') - b) k := by
      intro b hb k
      apply base_sfv_eq σ Ψ b _ k
      obtain ⟨g, hg, hgeq⟩ := hh (ChainDescent.affineE (Ψ.symm b))
        (List.mem_toFinset.mpr (List.mem_map_of_mem hb))
      rw [Equiv.symm_apply_apply] at hgeq
      exact ⟨g, hg, hgeq⟩
    have hvv' : Ψ (ChainDescent.affineE.symm u) = Ψ (ChainDescent.affineE.symm u') := by
      refine suzukiForms_determine σ
        (fun k => by have h := key 0 (by simp [suzukiBaseVecs]) k; rwa [sub_zero, sub_zero] at h)
        (fun k => key (Pi.single 0 1) (by simp [suzukiBaseVecs]) k)
        (fun k => key (Pi.single 1 1) (by simp [suzukiBaseVecs]) k)
        (fun k => key (Pi.single 2 1) (by simp [suzukiBaseVecs]) k)
        (fun k => key (Pi.single 3 1) (by simp [suzukiBaseVecs]) k)
        (fun k => ?_) (fun k => ?_) (fun k => ?_)
      · have h := key (Pi.single 0 1 + Pi.single 1 1) (by simp [suzukiBaseVecs]) k
        rwa [sub_add_eq_sub_sub, sub_add_eq_sub_sub] at h
      · have h := key (Pi.single 1 1 + Pi.single 3 1) (by simp [suzukiBaseVecs]) k
        rwa [sub_add_eq_sub_sub, sub_add_eq_sub_sub] at h
      · have h := key (Pi.single 2 1 + Pi.single 3 1) (by simp [suzukiBaseVecs]) k
        rwa [sub_add_eq_sub_sub, sub_add_eq_sub_sub] at h
    exact ChainDescent.affineE.symm.injective (Ψ.injective hvv')

/-- **Suzuki reaches the rigid-or-Cameron disjunction** (instance 4 SEALED, **citation-free**). The σ-twisted
multi-form family, bridged to the char-2-ready engine and sealed by the shared `FormAdapter.reachesRigidOrCameron`.
The determiner `suzukiForms_determine` is proved outright (second-derivative recovery), so — unlike the earlier
draft — this carries **no `SuzukiFormsDetermine` citation and no `hσ`**. -/
theorem reachesRigidOrCameron_suzuki
    {IsCameronScheme : ∀ (m : Nat), SchurianScheme m → Prop} :
    ((SchemeBlockRecovered (2 ^ D)
          (ChainDescent.affineScheme (suzukiAdapter σ Ψ).G₀ (suzukiAdapter σ Ψ).neg_mem)
        ∨ AbelianConsumed (2 ^ D)
          (ChainDescent.affineScheme (suzukiAdapter σ Ψ).G₀ (suzukiAdapter σ Ψ).neg_mem))
        ∨ SchemeRecoveredByDepth (2 ^ D)
          (ChainDescent.affineScheme (suzukiAdapter σ Ψ).G₀ (suzukiAdapter σ Ψ).neg_mem) 8)
      ∨ IsCameronScheme (2 ^ D)
          (ChainDescent.affineScheme (suzukiAdapter σ Ψ).G₀ (suzukiAdapter σ Ψ).neg_mem) :=
  (suzukiAdapter σ Ψ).reachesRigidOrCameron

end Suzuki

end ChainDescent.RouteC
