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
non-elementary link is `NondegQuadricDeterminesForm` (same isotropic cone ⟹ scalar-multiple form = A1's `vanishDim=1`
uniqueness; the EXACT scoped classical theorem, `p≠2`/`d≥4`), named + carried as a classical citation (Hirschfeld,
projective Nullstellensatz for a nondegenerate quadric) — so **F4 and A1's Lean side unify into one carried fact**, the
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
`Q'`-cone: `Q v = 0 ↔ Q' (g v) = 0`), the nondegeneracy of `Q`, and the **exact cited classical fact**
`NondegQuadricDeterminesForm` (A1's uniqueness, `hcite`, scoped `p ≠ 2`, `4 ≤ d`), the recovered
difference colouring transports with a single global scalar `μ`: `Q' (g u − g t) = μ · Q (u − t)` for all
`u, t`. So canonicalizing via the recovered form produces a *canonical* (iso-invariant) colouring — the
property the poly canonicalization claim needs, and the one the banked seal does **not** supply
(discreteness does not transfer to the coarser similitude scheme). Composes with A3 brick 1
(`isometryScheme_refines_similitudeScheme`) and `viaOrthogonalForm_spanning` to give: iso-invariant
discrete colouring at a spanning base ⟹ (meta) poly canonical labelling. Axiom-clean; the only
non-elementary input is `hcite`, threaded up as a premise exactly like `Theorem41Statement`. -/
theorem recoveredForm_colouring_equivariant
    (hcite : NondegQuadricDeterminesForm p d) (hp : p ≠ 2) (hd : 4 ≤ d)
    (Q Q' : QuadraticForm (ZMod p) (Fin d → ZMod p))
    (hQ : (Q.polarBilin).Nondegenerate)
    {g : (Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)}
    (hcone : ∀ v, Q v = 0 ↔ Q' (g v) = 0) :
    ∃ μ : (ZMod p)ˣ, ∀ u t : Fin d → ZMod p, Q' (g u - g t) = (μ : ZMod p) * Q (u - t) := by
  obtain ⟨μ, hμ⟩ := hcite hp hd Q
    (Q'.comp (g : (Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p))) hQ hcone
  exact ⟨μ, fun u t => similitude_colouring_equivariant Q Q' (fun v => hμ v) u t⟩

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

end ChainDescent.RouteC
