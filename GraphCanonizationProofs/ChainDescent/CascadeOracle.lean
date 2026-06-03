import ChainDescent
import ChainDescent.CFI
import ChainDescent.Scheme
import Mathlib.GroupTheory.Perm.Support

/-!
# §C — A-priori cascade oracle: interface and soundness

The Lean contract for the **a-priori cascade oracle**
(`docs/chain-descent-cascade-oracle.md`), paralleling the linear-oracle interface
of §15.8 (`LinearOracleSpec` / `LeafTwistSpec`). As there, the *discovery*
algorithm — the lockstep single-path recursion — lives on the C# side (built +
measured 2026-05-28); the Lean side supplies the interface and the spec it must
meet. The plan is `docs/chain-descent-cascade-oracle-lean-brief.md`.

This file is **Phase A** (soundness / validity), depending only on the core
`ChainDescent` development:

* `CascadeOracleSpec` — the interface type. Unlike `LinearOracleSpec` it is **not**
  leaf-gated: the cascade oracle harvests at *internal* target cells, so it takes a
  `SpineChain` at any level `k` (the committed path `D = chain.D`) and two candidate
  representatives `v w`, returning an optional verified automorphism.
* `CascadeOracleSpec.some_isAut` — subtype-level soundness (automatic).
* `CascadeOracleSpec.OrbitMapSpec` — the validity predicate (the `LeafTwistSpec`
  analogue): a returned merge witnesses an `Aut_D` orbit relation `OrbitPartition`.
  This is the soundness anchor that justifies pruning.
* `CascadeOracleSpec.merged_sameCell` — a certified merge never crosses 1-WL cells.

Completeness on the cascade class (CFI / schemes) is **Phase B** — wiring
`OrbitMapSpec` to `theorem_1_HOR_at_depth` and its axiom-free specialisations
(`theorem_1_HOR_cfi_oddDeg`, `theorem_2_HOR_concrete_rank_two_J_singleton`),
appended later. **Phase C** isolates the residual obligations: verdict
iso-invariance is *discharged conditionally* (`verdictIsoInvariant_of_complete` —
it follows from soundness + completeness + recoverability, so it is not
independent), and the localisation obligation is *sharpened* to its single open
implication (`orbitRecoverableAt_iff_cellsAreOrbits` / `CellsAreOrbits`). The hard
half of localisation (cells-are-orbits at the recursion's nodes) and general-class
completeness (`GI ∈ P`, not expected) remain genuinely open — stated, not assumed.

**P-invariance seam.** `OrbitPartition` requires the witness to preserve `P`
(not just `adj`); `OrbitMapSpec` therefore requires it too. This mirrors the
`hP_invariant` hypothesis of `theorem_2_HOR_concrete_rank_two_J_singleton` — a
known seam, discharged operationally (the descent builds `P` only from path
individualisations, which a path-fixing automorphism preserves).
-/

namespace ChainDescent

/-! ## §C.0 — Real-stays-real (the deferred-decisions foundation)

The scheduling layer above the oracles (`docs/chain-descent-deferred-decisions.md`)
defers *real* decisions and consumes symmetry first. Its soundness foundation is
**real-stays-real**: a pair with no path-fixing automorphism swapping it never
acquires one under further individualisation. In `OrbitPartition` terms this is
pure monotonicity in the fixed set `S` — proved here. -/

namespace OrbitPartition

/-- **Orbit monotonicity in the fixed set.** Fixing *more* vertices only *shrinks*
an orbit: if `v, w` are `Aut_{S'}`-orbit-equivalent and `S ⊆ S'`, they are
`Aut_S`-orbit-equivalent too — the same witness `π`, whose pointwise-fixing of the
larger `S'` implies pointwise-fixing of `S`. Pure stabilizer monotonicity; no
warm-refinement or cascade content. -/
theorem mono {n : Nat} {adj : AdjMatrix n} {P : PMatrix n} {S S' : Finset (Fin n)}
    {v w : Fin n} (hsub : S ⊆ S') (h : OrbitPartition adj P S' v w) :
    OrbitPartition adj P S v w := by
  obtain ⟨π, hπ, hP, hπS', hvw⟩ := h
  exact ⟨π, hπ, hP, fun x hx => hπS' x (hsub hx), hvw⟩

/-- **Real-stays-real** (`docs/chain-descent-deferred-decisions.md` §2),
the contrapositive of `mono`: a *real* decision at `S` — no orbit relation, i.e. no
path-fixing automorphism swaps `v, w` — persists to every larger fixed set
`S' ⊇ S`. So deferring a real decision is free: it is still real when Phase 2
reaches it. -/
theorem real_stays_real {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {S S' : Finset (Fin n)} {v w : Fin n} (hsub : S ⊆ S')
    (h : ¬ OrbitPartition adj P S v w) : ¬ OrbitPartition adj P S' v w :=
  fun h' => h (mono hsub h')

end OrbitPartition

/-! ## §C.0.1 — The support backbone

When does an individualization remove a symmetry from the **pointwise stabilizer**?
`OrbitPartition.mono` says fixing *more* shrinks orbits, but the sharp statement is in
terms of the permutation's **support** `π.support = {x | π x ≠ x}`: an automorphism `π`
lies in `Aut_S` exactly when `S` avoids `supp(π)`
(`π ∈ Aut_S ⟺ Disjoint S π.support`). Two consequences:

* `orbitPartition_of_support_disjoint` — a `P`-preserving automorphism `π` with
  `π v = w` witnesses `OrbitPartition … S v w` at **every** `S` disjoint from its
  support. (The `FixesPointwise` conjunct of `OrbitPartition` *is* support-disjointness.)
* `exists_orbit_witness_of_aut` — so the orbit pair `(v, π v)` stays available all the
  way down to `S = (π.support)ᶜ`, of size `n − |supp π|`. This is the **availability
  depth** behind the support-grading: a symmetry of support `s` is a *within-cell* orbit
  witness for any individualization of `≤ n − s` vertices — fixed-point-free symmetries
  (e.g. rotations, `s = n`) only at the root, transpositions (`s = 2`) down to depth
  `n − 2` (the twin end).

**Caveat — this is the clean-harvest *window*, not a deadline.** `S ∩ supp(π) ≠ ∅`
removes `π` from the *pointwise stabilizer* `Aut_S`, but `π` is **not destroyed** — it
relocates to the stabilizer-chain transversal (a coset representative relating
branches), still a member of `Aut(adj)`, harvested cross-branch instead of within-cell.
`Aut(adj)` is graph-intrinsic; no individualization/ordering decision can remove a graph
automorphism (a decision ordering `(a,b)` consumes only the symmetries with `π a = b` —
those for which `(a,b)` is a *projected pair*; every `π` with `π a ≠ b` maps the decision
to a parallel one and survives intact). So the real open obligation (1b) is *discovery* —
the oracle recognizing each orbit/transversal so it prunes rather than branches — not a
race against destruction. Fully modelling the transversal relocation needs the
stabilizer-chain group object (tractable-buildout Part A), not yet built. -/

/-- **Support-disjoint orbit witness.** A `P`-preserving automorphism `π` whose support
is disjoint from the individualized set `S` (equivalently: `π` fixes `S` pointwise)
and which sends `v` to `w` puts `v, w` in the same `Aut_S` orbit. The
support-disjointness *is* the `FixesPointwise` conjunct, made explicit — `S` meeting
`supp(π)` removes `π` from the pointwise stabilizer `Aut_S` (relocating it to the
stabilizer-chain transversal, *not* destroying it; see §C.0.1). -/
theorem orbitPartition_of_support_disjoint {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {S : Finset (Fin n)} {π : Equiv.Perm (Fin n)} {v w : Fin n}
    (hπ : IsAut π adj) (hP : ∀ x u, P (π x) (π u) = P x u)
    (hdisj : Disjoint S π.support) (hvw : π v = w) :
    OrbitPartition adj P S v w := by
  refine ⟨π, hπ, hP, fun s hs => ?_, hvw⟩
  have hns : s ∉ π.support := Finset.disjoint_left.mp hdisj hs
  rw [Equiv.Perm.mem_support, not_not] at hns
  exact hns

/-- **Availability depth.** An automorphism `π` of support `s = |supp π|` keeps its
orbit pair `(v, π v)` alive for the individualization of *any* set avoiding `supp π`,
in particular the full complement `(π.support)ᶜ` of size `n − s`. So a symmetry of
support `s` is certifiable up to depth `n − s` — the support-graded bound. (Whether
the canonical descent actually certifies it by then is obligation 1b.) -/
theorem exists_orbit_witness_of_aut {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {π : Equiv.Perm (Fin n)} {v w : Fin n}
    (hπ : IsAut π adj) (hP : ∀ x u, P (π x) (π u) = P x u) (hvw : π v = w) :
    ∃ S : Finset (Fin n), S.card = n - π.support.card ∧ OrbitPartition adj P S v w :=
  ⟨(π.support)ᶜ, by rw [Finset.card_compl, Fintype.card_fin],
    orbitPartition_of_support_disjoint hπ hP disjoint_compl_left hvw⟩

/-- **Cascade-oracle interface type.** Given a node — a `SpineChain` at level `k`,
whose accumulated `chain.D` is the committed individualisation path — and two
candidate representatives `v w`, return either `none` (no orbit map certified) or a
verified automorphism `π` of `adj` (bundled with its `IsAut` proof).

Parallel to `LinearOracleSpec` (§15.8) but **internal-node**, not leaf-gated: the
cascade oracle harvests *before* branching at a target cell, so there is no
`chain.IsLeaf` argument. The implementation is the C# lockstep single-path
recursion; the Lean side is the interface + spec. -/
def CascadeOracleSpec {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) : Type :=
  ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → (v w : Fin n) →
    Option { π : Equiv.Perm (Fin n) // IsAut π adj }

namespace CascadeOracleSpec

variable {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
  {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}

/-- **Soundness (subtype-level).** When the oracle returns `some result`, the
returned permutation is an automorphism — automatic from the bundled subtype
(mirrors `LinearOracleSpec.some_isAut`). -/
theorem some_isAut (oracle : CascadeOracleSpec adj P₀ χι₀ sel)
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (v w : Fin n)
    {result : { π : Equiv.Perm (Fin n) // IsAut π adj }}
    (_ : oracle chain v w = some result) :
    IsAut result.val adj :=
  result.property

/-- **Cascade-orbit validity** (the `LeafTwistSpec` analogue). When the oracle
merges `v` and `w` (returns `some`), they lie in the same `Aut_D` orbit: there is
an automorphism of `adj` preserving `chain.P`, fixing `chain.D` pointwise, and
sending `v` to `w` (`OrbitPartition`). This is the soundness anchor that justifies
pruning `w`'s branch as isomorphic to `v`'s.

Like `LeafTwistSpec`, this *constrains* the oracle (it is the spec the discharge
must meet); the C# verification gate establishes it operationally. -/
def OrbitMapSpec (oracle : CascadeOracleSpec adj P₀ χι₀ sel) : Prop :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (v w : Fin n)
    (result : { π : Equiv.Perm (Fin n) // IsAut π adj }),
    oracle chain v w = some result →
    OrbitPartition adj chain.P chain.D v w

/-- A valid cascade oracle never merges across 1-WL cells: a certified merge of
`v, w` forces them into the same `warmRefine` cell (under the individualisation of
the committed path `chain.D`). Immediate from `OrbitPartition.subset_warmRefine` —
the merge is consistent with the partition the descent branches on. -/
theorem merged_sameCell {oracle : CascadeOracleSpec adj P₀ χι₀ sel}
    (hvalid : OrbitMapSpec oracle)
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (v w : Fin n)
    (result : { π : Equiv.Perm (Fin n) // IsAut π adj })
    (h : oracle chain v w = some result) :
    warmRefine adj chain.P (individualizedColouring n chain.D) v =
      warmRefine adj chain.P (individualizedColouring n chain.D) w :=
  OrbitPartition.subset_warmRefine (hvalid chain v w result h)

end CascadeOracleSpec

/-! ## §C.2 — Phase B: completeness on the cascade class

The soundness side (Phase A) is class-blind. Completeness — that the oracle
returns *one representative per orbit*, missing no merge — is realizable exactly
where the **orbit relation coincides with the 1-WL cell relation**, because the
cell relation is refinement-computable (polynomial). That coincidence is the
content of the orbit-recovery theorems, here re-exported in oracle vocabulary
(`OrbitRecoverableAt`) and instantiated for CFI and schemes.

**Scope (honest).** `theorem_1_HOR_at_depth` characterises orbits at the
*discretizing* depth `S` (`|S| ≤ k`); the actual oracle acts at *intermediate*
nodes `D ⊊ S`, where cells are coarser than orbits (the genuine-decision case).
Bridging the per-node intermediate behaviour to the cascade-depth recoverability
is the localisation obligation (Phase C / open). What Phase B establishes:
the characterisation (`certifies_iff_orbit`), the foundation that completeness
reduces to refinement at recoverable nodes (`complete_of_cellComplete_recoverable`),
and the axiom-free recoverability instances for CFI and rank-≤2 schemes. -/

/-- **Orbit recoverable at `S`** (oracle vocabulary for the orbit-recovery
squeeze). The `Aut_S`-orbit relation equals the 1-WL cell relation under the
individualisation of `S`. Where this holds, refinement — polynomial — computes
the orbit partition, so a complete cascade oracle is realizable. This is exactly
the conclusion of `theorem_1_HOR_at_depth` and its specialisations. -/
def OrbitRecoverableAt {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (S : Finset (Fin n)) : Prop :=
  ∀ v w, OrbitPartition adj P S v w ↔
    warmRefine adj P (individualizedColouring n S) v =
      warmRefine adj P (individualizedColouring n S) w

/-- **General foundation.** On the cascade class, orbits are recoverable at some
depth `≤ k`. Direct re-export of `theorem_1_HOR_at_depth`. -/
theorem orbitRecoverable_of_cascade {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {k : Nat} (h : CascadesAt adj P k) :
    ∃ S : Finset (Fin n), S.card ≤ k ∧
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      OrbitRecoverableAt adj P S := by
  obtain ⟨S, hcard, hd, hiff⟩ := theorem_1_HOR_at_depth h
  exact ⟨S, hcard, hd, hiff⟩

/-- **CFI instance** (axiom-free, OddDegree). Orbits are recoverable at depth
`≤ cfi_depth_bound h`, via `theorem_1_HOR_cfi_oddDeg`. -/
theorem orbitRecoverable_cfi {n : Nat} {adj : AdjMatrix n}
    (h : IsCFI' adj) (h_odd : h.OddDegree) (P : PMatrix n) :
    ∃ S : Finset (Fin n), S.card ≤ cfi_depth_bound h ∧
      Discrete (warmRefine adj P (individualizedColouring n S)) ∧
      OrbitRecoverableAt adj P S := by
  obtain ⟨S, hcard, hd, hiff⟩ := IsCFI'.theorem_1_HOR_cfi_oddDeg h h_odd P
  exact ⟨S, hcard, hd, hiff⟩

/-- **Scheme instance** (axiom-free, rank 2 / `|J| = 1`). Orbits are recoverable at
depth 1 (the singleton `{v}`), via `theorem_2_HOR_concrete_rank_two_J_singleton`.
Unlike the CFI case the cells here are *not* singletons — depth-1 individualisation
recovers the non-trivial `Aut_v`-orbit = cell partition. -/
theorem orbitRecoverable_scheme {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph' adj) (hrank : h.G.scheme.rank = 2)
    (hJ : h.G.toSchemeGraph.J.card = 1) (P : PMatrix n) (v : Fin n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj →
      ∀ x u, P (π x) (π u) = P x u) :
    OrbitRecoverableAt adj P {v} :=
  theorem_2_HOR_concrete_rank_two_J_singleton h hrank hJ P v hP_invariant

/-- **Cells-are-orbits** — the *non-trivial* half of `OrbitRecoverableAt`: every
same-cell pair is a genuine `Aut_S` orbit pair (1-WL cells are no coarser than
orbits). The other half — orbits refine cells — is unconditional
(`OrbitPartition.subset_warmRefine`), so this predicate is *equivalent* to
`OrbitRecoverableAt` (`orbitRecoverableAt_iff_cellsAreOrbits`) while naming exactly
the open content of the localisation obligation. It holds at cascade / discretizing
depth (`orbitRecoverable_cfi` / `_scheme`) and **fails at generic intermediate
nodes**, where 1-WL leaves genuine decisions unresolved (cells strictly coarser
than orbits). -/
def CellsAreOrbits {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (S : Finset (Fin n)) : Prop :=
  ∀ v w, warmRefine adj P (individualizedColouring n S) v =
            warmRefine adj P (individualizedColouring n S) w →
         OrbitPartition adj P S v w

/-- **`OrbitRecoverableAt` decomposes into a free half and the open half.** The
`OrbitPartition → same-cell` direction is unconditional (`subset_warmRefine`), so
recoverability **is** `CellsAreOrbits` — pinning the localisation obligation to a
single implication (cells-no-coarser-than-orbits) rather than an iff. -/
theorem orbitRecoverableAt_iff_cellsAreOrbits {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {S : Finset (Fin n)} :
    OrbitRecoverableAt adj P S ↔ CellsAreOrbits adj P S := by
  constructor
  · intro h v w hcell; exact (h v w).mpr hcell
  · intro h v w; exact ⟨fun ho => OrbitPartition.subset_warmRefine ho, h v w⟩

/-- **Cells-are-orbits is automatic at discretizing depth** — the recursion-bottom
anchor, and the reason localisation is *not* GI-hard. When `warmRefine` at `S` is
`Discrete`, both the cell relation and the `Aut_S`-orbit relation collapse to vertex
equality (`orbit_iff_eq_of_discrete_warmRefine`, Fact B), so `CellsAreOrbits` holds
for free. The cascade oracle's recursion deepens each node to discreteness, where
this applies; the content left is reaching discreteness at *bounded* depth (the
cascade property, proved below) and the recursion's reconstruction — never the
coincidence itself. -/
theorem cellsAreOrbits_of_discrete {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {S : Finset (Fin n)}
    (hd : Discrete (warmRefine adj P (individualizedColouring n S))) :
    CellsAreOrbits adj P S :=
  fun v w hcell => (orbit_iff_eq_of_discrete_warmRefine hd v w).mpr (hd v w hcell)

/-! ### §C.2 — Leg (a): the colour-match candidate *is* the orbit automorphism

The cascade oracle harvests by constructing a candidate `t` that matches one branch's
refined colours to the other's (`docs/chain-descent-cascade-oracle.md` §4.2), then
verifying `t ∈ Aut`. **Leg (a) of the harvest-window argument** is that this verification
*succeeds whenever a genuine orbit automorphism exists* — i.e. the construction is
complete, not just sound. The lemma below is the mechanical core: at a **discrete**
footprint, any permutation `t` realising the colour-match `χ₂ ∘ t = χ₁` (where
`χᵢ = warmRefine …`) **equals** the orbit automorphism `g`, hence is itself an
automorphism. No σ-coherence, no cycle construction, no rank rebasing (so no conjugation
gap): the witness is forced by `warmRefine_transport` (equivariance) + injectivity.

The transport hypothesis `hχ : ∀ v, χ₂ (g v) = χ₁ v` is what couples the two branches;
discharging it for a concrete individualization is the downstream obligation (it needs a
*uniform* fresh colour on the explored representative — the index-based
`individualizedColouring` gives the swapped pair `r₁, r₂` distinct colours and breaks
`hχ` at exactly that pair). Here it is taken as given, isolating the linchpin. -/

/-- **Leg (a) linchpin — the colour-match candidate equals the orbit automorphism.**
If `g ∈ Aut(adj)` carries the branch-1 configuration `(P, χ₁)` onto the branch-2
configuration `(P, χ₂)` (`hP`, `hχ`), the branch-2 refinement is `Discrete`, and `t`
realises the colour-match `warmRefine … χ₂ (t v) = warmRefine … χ₁ v`, then `t = g`.
Forced by `warmRefine_transport` + injectivity at the discrete footprint. -/
theorem colourMatch_eq_aut {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {g t : Equiv.Perm (Fin n)} {χ₁ χ₂ : Colouring n}
    (hg : IsAut g adj) (hP : ∀ v u, P (g v) (g u) = P v u)
    (hχ : ∀ v, χ₂ (g v) = χ₁ v)
    (hdisc : Discrete (warmRefine adj P χ₂))
    (ht : ∀ v, warmRefine adj P χ₂ (t v) = warmRefine adj P χ₁ v) :
    t = g := by
  have htrans : ∀ v, warmRefine adj P χ₂ (g v) = warmRefine adj P χ₁ v :=
    fun v => warmRefine_transport hg hP hχ v
  refine Equiv.ext (fun v => hdisc (t v) (g v) ?_)
  rw [ht v, htrans v]

/-- **Leg (a) deliverable — the colour-match candidate verifies.** Under the same
hypotheses, the constructed candidate `t` is an automorphism of `adj` (it equals `g`).
This is exactly "the harvest's verification step succeeds whenever the orbit pair is
genuine" — the completeness half the cascade oracle needs, given a discrete footprint. -/
theorem colourMatch_isAut {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {g t : Equiv.Perm (Fin n)} {χ₁ χ₂ : Colouring n}
    (hg : IsAut g adj) (hP : ∀ v u, P (g v) (g u) = P v u)
    (hχ : ∀ v, χ₂ (g v) = χ₁ v)
    (hdisc : Discrete (warmRefine adj P χ₂))
    (ht : ∀ v, warmRefine adj P χ₂ (t v) = warmRefine adj P χ₁ v) :
    IsAut t adj := by
  rw [colourMatch_eq_aut hg hP hχ hdisc ht]; exact hg

/-- **Uniform-colour individualization of an explored representative.** Individualize the
committed set `S` by index (`individualizedColouring`) **plus** an explored rep `r` with a
single *uniform* fresh colour `n+1` (distinct from every index colour `{1,…,n}` and the
background `0`). The uniform colour on `r` is exactly what makes the orbit automorphism
transport branch-`r₁` onto branch-`r₂`: the index-based colouring would hand `r₁` and `r₂`
*distinct* colours and break the transport hypothesis at the swapped pair. -/
def indivWithRep (n : Nat) (S : Finset (Fin n)) (r : Fin n) : Colouring n :=
  fun v => if v = r then n + 1 else individualizedColouring n S v

/-- **The transport hypothesis, discharged for `indivWithRep`.** An orbit automorphism `g`
that fixes the committed set `S` pointwise and sends `r₁ ↦ r₂` (with `r₂ ∉ S`) carries the
branch-`r₁` colouring onto the branch-`r₂` colouring: `χ₂ (g v) = χ₁ v` for every `v`. This
is the `hχ` that `colourMatch_eq_aut` consumes, now proved rather than assumed. -/
theorem indivWithRep_transport {n : Nat} {S : Finset (Fin n)} {g : Equiv.Perm (Fin n)}
    {r₁ r₂ : Fin n} (hgS : FixesPointwise g S) (hgr : g r₁ = r₂) (hr₂S : r₂ ∉ S) (v : Fin n) :
    indivWithRep n S r₂ (g v) = indivWithRep n S r₁ v := by
  unfold indivWithRep individualizedColouring
  by_cases hv1 : v = r₁
  · subst hv1; rw [hgr]; simp
  · rw [if_neg hv1]
    by_cases hvS : v ∈ S
    · have hgv : g v = v := hgS v hvS
      have hvr2 : v ≠ r₂ := fun h => hr₂S (h ▸ hvS)
      rw [hgv, if_neg hvr2, if_pos hvS]
    · have hgvS : g v ∉ S := hgS.complement hvS
      have hgvr2 : g v ≠ r₂ := by rw [← hgr]; exact fun h => hv1 (g.injective h)
      rw [if_neg hgvr2, if_neg hgvS, if_neg hvS]

/-- **Leg (a), grounded — the harvest's candidate verifies at a discrete footprint.**
Combining the linchpin with the discharged transport: given a genuine orbit automorphism
`g` (fixes the committed path `S`, `g r₁ = r₂`, `r₂ ∉ S`), a **discrete** branch-`r₂`
footprint, and any colour-match permutation `t`, the candidate `t` is an automorphism of
`adj`. No σ-coherence, no cycle, no rank rebasing. The remaining input — *discreteness of
the footprint within a bounded depth* — is what the recursion (orbit recovery) supplies. -/
theorem harvest_isAut_of_discrete {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {g t : Equiv.Perm (Fin n)} {S : Finset (Fin n)} {r₁ r₂ : Fin n}
    (hg : IsAut g adj) (hP : ∀ v u, P (g v) (g u) = P v u)
    (hgS : FixesPointwise g S) (hgr : g r₁ = r₂) (hr₂S : r₂ ∉ S)
    (hdisc : Discrete (warmRefine adj P (indivWithRep n S r₂)))
    (ht : ∀ v, warmRefine adj P (indivWithRep n S r₂) (t v)
             = warmRefine adj P (indivWithRep n S r₁) v) :
    IsAut t adj :=
  colourMatch_isAut hg hP (indivWithRep_transport hgS hgr hr₂S) hdisc ht

/-- **The colour-match relation** (the cascade harvest's construction, cascade-oracle §4.2):
`t` matches branch-`w`'s refined colours to branch-`v`'s — `warmRefine χ_w ∘ t = warmRefine χ_v`
with `χ_v = indivWithRep D v`, `χ_w = indivWithRep D w`. The harvest builds `t` this way and verifies
`IsAut t`; the two bricks below pin it at a discrete footprint (it *exists* and is *unique*, = `g`). -/
def IsColourMatch {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) (D : Finset (Fin n))
    (v w : Fin n) (t : Equiv.Perm (Fin n)) : Prop :=
  ∀ x, warmRefine adj P (indivWithRep n D w) (t x) = warmRefine adj P (indivWithRep n D v) x

/-- **Completeness brick — the orbit automorphism IS a colour-match.** An `Aut_D` witness `g`
(`IsAut`, `P`-preserving, fixes `D`, `g v = w`, `w ∉ D`) satisfies `IsColourMatch` — directly by
`warmRefine_transport` ∘ `indivWithRep_transport`. So at a recoverable node, where a same-cell pair
has such a `g`, the colour-match construction is non-empty: leg-(a)'s *completeness* direction, the
key to discharging `CellComplete`. -/
theorem colourMatch_complete {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {D : Finset (Fin n)} {v w : Fin n} {g : Equiv.Perm (Fin n)}
    (hg : IsAut g adj) (hgP : ∀ x u, P (g x) (g u) = P x u)
    (hgD : FixesPointwise g D) (hgvw : g v = w) (hwD : w ∉ D) :
    IsColourMatch adj P D v w g :=
  fun x => warmRefine_transport hg hgP (indivWithRep_transport hgD hgvw hwD) x

/-- **Uniqueness brick — at a discrete footprint every colour-match equals the orbit
automorphism.** `colourMatch_eq_aut` restated against `IsColourMatch`: given a genuine `g` and a
discrete branch-`w` footprint, any `IsColourMatch` `t` satisfies `t = g`. Combined with
`colourMatch_complete`, the colour-match candidate at a discrete recoverable node *exists and is
unique*, and it is the orbit automorphism — the harvest both fires (completeness) and pins the unique
verified map. -/
theorem colourMatch_unique {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {D : Finset (Fin n)} {v w : Fin n} {g t : Equiv.Perm (Fin n)}
    (hg : IsAut g adj) (hgP : ∀ x u, P (g x) (g u) = P x u)
    (hgD : FixesPointwise g D) (hgvw : g v = w) (hwD : w ∉ D)
    (hdisc : Discrete (warmRefine adj P (indivWithRep n D w)))
    (ht : IsColourMatch adj P D v w t) :
    t = g :=
  colourMatch_eq_aut hg hgP (indivWithRep_transport hgD hgvw hwD) hdisc ht

/-! #### §C.2 — the colour-model firing (legs A+B unified; the de-classing of Leg B)

The linear oracle (Leg B, hidden-abelian) originally fired in the **order model** — a twist
relabels `canonAdj σ` to `canonAdj (flip)` (`RealizableFlip`) — which forces the σ-cell-coherence
that `cell_split_uniform_false` proves false. The two lemmas below fire **in the colour model**
instead, straight from orbit recovery: where `CellsAreOrbits` holds, the orbit automorphism *is* a
verifying colour-match (it exists), and at a discrete footprint *any* colour-match verifies (it is
unique and `= g`). This is the **same** harvest both oracles use, so Leg B's firing folds into Leg
A's — no order `σ`, no `ConfigSwap`, no σ-coherence. The class-specificity that remains is only the
**depth** at which the footprint becomes discrete/recoverable (the exposure depth — `tw(H)` for CFI,
depth-1 for schemes), and the concrete construction of `t` (the open M-B `colourMatchPerm`). Pruning
soundness is inherited semantically from `OrbitPartition` (a certified orbit pair ⟹ the branches are
`Aut`-equivalent), not from the retired `RealizableFlip`. -/

/-- **The firing certificate exists at a recoverable node.** Where `CellsAreOrbits` holds, a
same-cell decision pair `(r₁, r₂)` (with `r₂ ∉ S`) has a verifying colour-match — namely the orbit
automorphism `g` itself (`colourMatch_complete`). So the harvest's construction target is non-empty
without any order/σ data; this is the completeness (existence) half of the fold, and it needs no
discreteness. -/
theorem colourMatch_exists_of_cellsAreOrbits {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {S : Finset (Fin n)} {r₁ r₂ : Fin n}
    (hco : CellsAreOrbits adj P S)
    (hcell : warmRefine adj P (individualizedColouring n S) r₁
           = warmRefine adj P (individualizedColouring n S) r₂)
    (hr₂S : r₂ ∉ S) :
    ∃ t : Equiv.Perm (Fin n), IsAut t adj ∧ IsColourMatch adj P S r₁ r₂ t := by
  obtain ⟨g, hg, hgP, hgS, hgr⟩ := hco r₁ r₂ hcell
  exact ⟨g, hg, colourMatch_complete hg hgP hgS hgr hr₂S⟩

/-- **The harvest fires at a recoverable + discrete footprint.** Where `CellsAreOrbits` holds and the
branch-`r₂` footprint is `Discrete`, *any* constructed colour-match `t` for the decision pair verifies
as an automorphism (`harvest_isAut_of_discrete`, fed the orbit automorphism from `CellsAreOrbits`).
This is Leg B's firing in the colour model — order-free and class-agnostic; the only remaining input
is discreteness within a bounded depth (the exposure-depth witness, "B's core"). -/
theorem harvest_fires_of_cellsAreOrbits_discrete {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {S : Finset (Fin n)} {r₁ r₂ : Fin n} {t : Equiv.Perm (Fin n)}
    (hco : CellsAreOrbits adj P S)
    (hcell : warmRefine adj P (individualizedColouring n S) r₁
           = warmRefine adj P (individualizedColouring n S) r₂)
    (hr₂S : r₂ ∉ S)
    (hdisc : Discrete (warmRefine adj P (indivWithRep n S r₂)))
    (ht : IsColourMatch adj P S r₁ r₂ t) :
    IsAut t adj := by
  obtain ⟨g, hg, hgP, hgS, hgr⟩ := hco r₁ r₂ hcell
  exact harvest_isAut_of_discrete hg hgP hgS hgr hr₂S hdisc ht

/-- **General-singleton round-1 match.** If `s` is a `χ`-singleton (uniquely
coloured) and `a, b` (both `≠ s`) get the same colour after one `refineStep`, they
share adjacency and `P`-relation to `s`. The arbitrary-singleton generalisation of
`Scheme.refineStep_round1_pair_eq` (which fixes the singleton to be the individualized
vertex); the same witness-tuple argument. -/
private theorem refineStep_singleton_pair_eq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    {χ : Colouring n} {s a b : Fin n} (hsing : ∀ u, u ≠ s → χ u ≠ χ s)
    (has : a ≠ s) (hbs : b ≠ s)
    (h : refineStep adj P χ a = refineStep adj P χ b) :
    adj.adj a s = adj.adj b s ∧ P a s = P b s := by
  have hsig : signature adj P χ a = signature adj P χ b :=
    ((refineStep_iff adj P χ a b).mp h).2
  have hin : (χ s, adj.adj a s, P a s) ∈ signature adj P χ a := by
    unfold signature
    refine Multiset.mem_map.mpr ⟨s, ?_, rfl⟩
    rw [Finset.mem_val, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun heq => has heq.symm⟩
  have hinb : (χ s, adj.adj a s, P a s) ∈ signature adj P χ b := hsig ▸ hin
  unfold signature at hinb
  obtain ⟨s', hmem, heq⟩ := Multiset.mem_map.mp hinb
  rw [Finset.mem_val, Finset.mem_filter] at hmem
  have hχ : χ s' = χ s := ((Prod.mk.injEq _ _ _ _).mp heq).1
  have hrest := (Prod.mk.injEq _ _ _ _).mp ((Prod.mk.injEq _ _ _ _).mp heq).2
  have hs' : s' = s := by by_contra hne; exact hsing s' hne hχ
  subst hs'
  exact ⟨hrest.1.symm, hrest.2.symm⟩

/-- **A twin pair's transposition is an automorphism.** If `v, w` are adjacency-twins
(`adj v s = adj w s` for every other `s`) of a simple graph (`hsymm` symmetric, `hloop`
loopless), the transposition `(v w)` preserves every edge — `IsAut (Equiv.swap v w) adj`.
The `adj`-only half of the twin swap witness; extracted so the linear oracle can build a
`ConfigSwap` from the same twin hypothesis (`LinearOracle.configSwap_of_twin`). -/
theorem isAut_swap_of_twin {n : Nat} {adj : AdjMatrix n} {v w : Fin n}
    (hsymm : ∀ a b, adj.adj a b = adj.adj b a)
    (hloop : ∀ a, adj.adj a a = 0)
    (htwin : ∀ s, s ≠ v → s ≠ w → adj.adj v s = adj.adj w s) :
    IsAut (Equiv.swap v w) adj := by
  intro a b
  rcases eq_or_ne a v with ha | hav
  · rw [ha]
    rcases eq_or_ne b v with hb | hbv
    · rw [hb, Equiv.swap_apply_left, hloop, hloop]
    · rcases eq_or_ne b w with hb | hbw
      · rw [hb, Equiv.swap_apply_left, Equiv.swap_apply_right]; exact hsymm w v
      · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hbv hbw]
        exact (htwin b hbv hbw).symm
  · rcases eq_or_ne a w with ha | haw
    · rw [ha]
      rcases eq_or_ne b v with hb | hbv
      · rw [hb, Equiv.swap_apply_right, Equiv.swap_apply_left]; exact hsymm v w
      · rcases eq_or_ne b w with hb | hbw
        · rw [hb, Equiv.swap_apply_right, hloop, hloop]
        · rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hbv hbw]
          exact htwin b hbv hbw
    · rw [Equiv.swap_apply_of_ne_of_ne hav haw]
      rcases eq_or_ne b v with hb | hbv
      · rw [hb, Equiv.swap_apply_left, hsymm a w, hsymm a v]
        exact (htwin a hav haw).symm
      · rcases eq_or_ne b w with hb | hbw
        · rw [hb, Equiv.swap_apply_right, hsymm a v, hsymm a w]
          exact htwin a hav haw
        · rw [Equiv.swap_apply_of_ne_of_ne hbv hbw]

/-- **Transposition orbit witness from a twin pair** — the support-grading's
reconstruction mechanism, isolated from any depth bound. If `v, w` are an
*order-undecided twin pair* outside the individualized set `S` — identical adjacency
and `P`-relation to every *other* vertex (`htwin`) and `unknown` between themselves
(`hund`) — then the transposition `(v w)` is a `P`-preserving automorphism fixing `S`
pointwise, witnessing `OrbitPartition adj P S v w`.

This is the core of the twin endpoint extracted so it applies at **any** support: it
needs only that `v, w` be twins, *not* that the omitted set `Sᶜ` be small. The
`Sᶜ.card ≤ 2` and `twin-cells` lemmas both consume it, differing only in how they
*establish* the twin condition. The simple-graph / partial-order hypotheses (`hsymm`,
`hloop`, `hanti`) transport the twin condition across the subject/object sides. The
`adj`-only half is `isAut_swap_of_twin` (reused by the linear oracle). -/
theorem orbitPartition_swap_of_twin {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {S : Finset (Fin n)} {v w : Fin n}
    (hsymm : ∀ a b, adj.adj a b = adj.adj b a)
    (hloop : ∀ a, adj.adj a a = 0)
    (hanti : ∀ a b, P a b = POE.neg (P b a))
    (hvS : v ∉ S) (hwS : w ∉ S)
    (htwin : ∀ s, s ≠ v → s ≠ w → adj.adj v s = adj.adj w s ∧ P v s = P w s)
    (hund : P v w = POE.unknown) :
    OrbitPartition adj P S v w := by
  -- `P` collapses to `unknown` exactly where the swap could break antisymmetry.
  have keyP : ∀ e : POE, e = POE.neg e → e = POE.unknown := by
    intro e he
    cases e with
    | less => exact absurd he (by decide)
    | unknown => rfl
    | greater => exact absurd he (by decide)
  have hPvw : P v w = POE.unknown := hund
  have hPwv : P w v = POE.unknown := by rw [hanti w v, hPvw]; rfl
  have hPdiag : ∀ a, P a a = POE.unknown := fun a => keyP _ (hanti a a)
  -- The transposition `(v w)` is the orbit witness.
  refine ⟨Equiv.swap v w, isAut_swap_of_twin hsymm hloop (fun s h1 h2 => (htwin s h1 h2).1),
    ?_, ?_, ?_⟩
  · -- `P`-preservation. Same case structure; antisymmetry handles the subject-flip.
    intro x u
    rcases eq_or_ne x v with hx | hxv
    · rw [hx]
      rcases eq_or_ne u v with hu | huv
      · rw [hu, Equiv.swap_apply_left, hPdiag, hPdiag]
      · rcases eq_or_ne u w with hu | huw
        · rw [hu, Equiv.swap_apply_left, Equiv.swap_apply_right, hPwv, hPvw]
        · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne huv huw]
          exact ((htwin u huv huw).2).symm
    · rcases eq_or_ne x w with hx | hxw
      · rw [hx]
        rcases eq_or_ne u v with hu | huv
        · rw [hu, Equiv.swap_apply_right, Equiv.swap_apply_left, hPvw, hPwv]
        · rcases eq_or_ne u w with hu | huw
          · rw [hu, Equiv.swap_apply_right, hPdiag, hPdiag]
          · rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne huv huw]
            exact (htwin u huv huw).2
      · rw [Equiv.swap_apply_of_ne_of_ne hxv hxw]
        rcases eq_or_ne u v with hu | huv
        · rw [hu, Equiv.swap_apply_left, hanti x w, hanti x v, (htwin x hxv hxw).2]
        · rcases eq_or_ne u w with hu | huw
          · rw [hu, Equiv.swap_apply_right, hanti x v, hanti x w, (htwin x hxv hxw).2]
          · rw [Equiv.swap_apply_of_ne_of_ne huv huw]
  · -- FixesPointwise
    intro s hs
    have hsv : s ≠ v := fun h => hvS (h ▸ hs)
    have hsw : s ≠ w := fun h => hwS (h ▸ hs)
    exact Equiv.swap_apply_of_ne_of_ne hsv hsw
  · -- maps `v` to `w`
    exact Equiv.swap_apply_left v w

/-- **Twin endpoint of the support-grading** (the `s = 2` end). When the individualized
set omits at most two vertices (`Sᶜ.card ≤ 2`, i.e. `|S| ≥ n − 2`), `CellsAreOrbits`
holds: the only possible non-singleton 1-WL cell is the omitted pair `{v, w}`, a
same-cell pair is necessarily a **twin pair** (identical adjacency/`P` to every
individualized vertex), and the transposition `(v w)` is then a `P`-preserving
automorphism fixing `S` pointwise — the `OrbitPartition` witness. Together with
`cellsAreOrbits_of_discrete` (the discrete end) this pins both ends of the support
spectrum (`exists_orbit_witness_of_aut`): full-support symmetries are certifiable at
the root, support-2 transpositions down to depth `n − 2`.

The hypotheses are the simple-graph / partial-order setting that CFI and scheme graphs
satisfy: `adj` symmetric and loopless, `P` antisymmetric (needed because a same-cell
pair only constrains the *subject* side of adjacency/`P` to each singleton; symmetry /
antisymmetry transport it to the other side). -/
theorem cellsAreOrbits_of_compl_card_le_two {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {S : Finset (Fin n)}
    (hsymm : ∀ a b, adj.adj a b = adj.adj b a)
    (hloop : ∀ a, adj.adj a a = 0)
    (hanti : ∀ a b, P a b = POE.neg (P b a))
    (hcard : Sᶜ.card ≤ 2) :
    CellsAreOrbits adj P S := by
  intro v w hcell
  by_cases hvw : v = w
  · subst hvw; exact OrbitPartition.refl v
  set χ := individualizedColouring n S with hχ
  have hcol : χ v = χ w := warmRefine_refines adj P χ hcell
  -- A vertex sharing a distinct vertex's colour is outside S.
  have hnotS : ∀ x y : Fin n, x ≠ y → χ x = χ y → x ∉ S := by
    intro x y hxy heq hxS
    have hx : χ x = x.val + 1 := by rw [hχ]; simp [individualizedColouring, hxS]
    rw [hx] at heq
    by_cases hyS : y ∈ S
    · have hy : χ y = y.val + 1 := by rw [hχ]; simp [individualizedColouring, hyS]
      rw [hy] at heq; exact hxy (Fin.ext (Nat.succ_injective heq))
    · have hy : χ y = 0 := by rw [hχ]; simp [individualizedColouring, hyS]
      rw [hy] at heq; exact Nat.succ_ne_zero _ heq
  have hvS : v ∉ S := hnotS v w hvw hcol
  have hwS : w ∉ S := hnotS w v (Ne.symm hvw) hcol.symm
  -- Hence `Sᶜ = {v, w}`.
  have hsub : ({v, w} : Finset (Fin n)) ⊆ Sᶜ := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · subst h; exact Finset.mem_compl.mpr hvS
    · rw [Finset.mem_singleton] at h; subst h; exact Finset.mem_compl.mpr hwS
  have hcard2 : ({v, w} : Finset (Fin n)).card = 2 := by
    rw [Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr hvw),
      Finset.card_singleton]
  have hSc : Sᶜ = ({v, w} : Finset (Fin n)) :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hcard2]; exact hcard)).symm
  have hmemS : ∀ s, s ≠ v → s ≠ w → s ∈ S := by
    intro s hsv hsw
    by_contra hsS
    have hmem : s ∈ Sᶜ := Finset.mem_compl.mpr hsS
    rw [hSc] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact hsv h
    · exact hsw (Finset.mem_singleton.mp h)
  -- Reduce the same-cell hypothesis to round 1.
  have hn1 : 1 ≤ n := by have := v.isLt; omega
  have hround : refineStep adj P χ v = refineStep adj P χ w := by
    have h1 := warmRefine_eq_iter_eq adj P χ 1 hn1 hcell
    simpa [Function.iterate_one] using h1
  -- Twin facts: matching adjacency / `P` to every individualized vertex.
  have htwin : ∀ s, s ≠ v → s ≠ w → adj.adj v s = adj.adj w s ∧ P v s = P w s := by
    intro s hsv hsw
    have hsS := hmemS s hsv hsw
    have hsing : ∀ u, u ≠ s → χ u ≠ χ s := by
      intro u hus heq
      have hcs : χ s = s.val + 1 := by rw [hχ]; simp [individualizedColouring, hsS]
      rw [hcs] at heq
      by_cases huS : u ∈ S
      · have hcu : χ u = u.val + 1 := by rw [hχ]; simp [individualizedColouring, huS]
        rw [hcu] at heq; exact hus (Fin.ext (Nat.succ_injective heq))
      · have hcu : χ u = 0 := by rw [hχ]; simp [individualizedColouring, huS]
        rw [hcu] at heq; exact Nat.succ_ne_zero _ heq.symm
    exact refineStep_singleton_pair_eq adj P hsing (Ne.symm hsv) (Ne.symm hsw) hround
  -- Cross-pair fact: same cell forces `P v w = P w v`, hence (with antisymmetry) unknown.
  have hcross : P v w = P w v := by
    have hsig : signature adj P χ v = signature adj P χ w :=
      ((refineStep_iff adj P χ v w).mp hround).2
    have hin : (χ w, adj.adj v w, P v w) ∈ signature adj P χ v := by
      unfold signature
      refine Multiset.mem_map.mpr ⟨w, ?_, rfl⟩
      rw [Finset.mem_val, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun heq => hvw heq.symm⟩
    have hinw : (χ w, adj.adj v w, P v w) ∈ signature adj P χ w := hsig ▸ hin
    unfold signature at hinw
    obtain ⟨u, hmem, heq⟩ := Multiset.mem_map.mp hinw
    rw [Finset.mem_val, Finset.mem_filter] at hmem
    have hχu : χ u = χ w := ((Prod.mk.injEq _ _ _ _).mp heq).1
    have hcw0 : χ w = 0 := by rw [hχ]; simp [individualizedColouring, hwS]
    have huv : u = v := by
      have huS : u ∉ S := by
        intro huin
        have hcu : χ u = u.val + 1 := by rw [hχ]; simp [individualizedColouring, huin]
        rw [hcu, hcw0] at hχu; exact Nat.succ_ne_zero _ hχu
      have hmemc : u ∈ Sᶜ := Finset.mem_compl.mpr huS
      rw [hSc] at hmemc
      rcases Finset.mem_insert.mp hmemc with h | h
      · exact h
      · exact absurd (Finset.mem_singleton.mp h) hmem.2
    subst huv
    have hrest := (Prod.mk.injEq _ _ _ _).mp ((Prod.mk.injEq _ _ _ _).mp heq).2
    exact hrest.2.symm
  -- `v, w` are order-undecided (their `P`-relation collapses to `unknown` by
  -- antisymmetry + the cross-pair fact), so they are a twin pair: the extracted
  -- swap witness (`orbitPartition_swap_of_twin`) finishes.
  have hund : P v w = POE.unknown := by
    have hh := hanti v w
    rw [← hcross] at hh
    cases hpv : P v w with
    | less => rw [hpv] at hh; exact absurd hh (by decide)
    | unknown => rfl
    | greater => rw [hpv] at hh; exact absurd hh (by decide)
  exact orbitPartition_swap_of_twin hsymm hloop hanti hvS hwS htwin hund

/-- **Twin-cells: cells-are-orbits at ARBITRARY support** — the twin-reconstructible
slice of the localisation obligation (1b). When *every* same-cell distinct pair is an
**order-undecided twin pair** (`unknown` between themselves, identical adjacency/`P` to
every other vertex), `CellsAreOrbits adj P S` holds — for **any** `S`, with no bound on
`|Sᶜ|`. The witness is the transposition (`orbitPartition_swap_of_twin`), exactly as in
the `Sᶜ.card ≤ 2` endpoint; the difference is purely that the twin condition is now a
*hypothesis on the partition* rather than forced by a small omitted set.

**Why this is the right slice of 1b.** The support-grading proved its two extremes
(`cellsAreOrbits_of_discrete`, support 0; `cellsAreOrbits_of_compl_card_le_two`,
support ≤ 2) but the general-support *middle* cannot hold unconditionally — at a
generic intermediate node a same-cell pair can be a genuine decision (1-WL blind, no
swap automorphism). This lemma closes the case when same-cell pairs are *twins*: the
orbit is recovered by a transposition at any depth.

**Scope (corrected 2026-05-31).** Twin classes are the **genuine-twin / module** abelian
regime — vertices with identical neighbourhoods, whose `Z₂` symmetry *is* a transposition.
This is **not** CFI: `CFI(H)` has *no* twins (`CFI.cfi_triangle_no_twins`; each endpoint
has a unique bridge partner, each subset vertex's neighbourhood encodes its subset), so
CFI's `Z₂` is a global gadget-flip involution, *not* a transposition. The twin slice and
CFI are therefore **complementary** abelian classes; CFI completeness routes through the
*general* orbit recovery (`theorem_1_HOR_cfi_oddDeg`) plus the general (non-transposition)
gadget twist, not this lemma. What this lemma adds is the support-grading *middle* for the
twin/module class (any support, no `|Sᶜ|` bound); the non-twin same-cell case — including
all of CFI's residual cells — stays open (the genuine-decision / general-orbit content). -/
theorem cellsAreOrbits_of_twin_cells {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {S : Finset (Fin n)}
    (hsymm : ∀ a b, adj.adj a b = adj.adj b a)
    (hloop : ∀ a, adj.adj a a = 0)
    (hanti : ∀ a b, P a b = POE.neg (P b a))
    (htwins : ∀ v w : Fin n,
      warmRefine adj P (individualizedColouring n S) v =
          warmRefine adj P (individualizedColouring n S) w →
        v ≠ w →
        P v w = POE.unknown ∧
          (∀ s, s ≠ v → s ≠ w → adj.adj v s = adj.adj w s ∧ P v s = P w s)) :
    CellsAreOrbits adj P S := by
  intro v w hcell
  by_cases hvw : v = w
  · subst hvw; exact OrbitPartition.refl v
  set χ := individualizedColouring n S with hχ
  have hcol : χ v = χ w := warmRefine_refines adj P χ hcell
  -- A vertex sharing a distinct vertex's colour is outside `S` (the general
  -- individualized-colouring argument; not specific to a small `Sᶜ`).
  have hnotS : ∀ x y : Fin n, x ≠ y → χ x = χ y → x ∉ S := by
    intro x y hxy heq hxS
    have hx : χ x = x.val + 1 := by rw [hχ]; simp [individualizedColouring, hxS]
    rw [hx] at heq
    by_cases hyS : y ∈ S
    · have hy : χ y = y.val + 1 := by rw [hχ]; simp [individualizedColouring, hyS]
      rw [hy] at heq; exact hxy (Fin.ext (Nat.succ_injective heq))
    · have hy : χ y = 0 := by rw [hχ]; simp [individualizedColouring, hyS]
      rw [hy] at heq; exact Nat.succ_ne_zero _ heq
  have hvS : v ∉ S := hnotS v w hvw hcol
  have hwS : w ∉ S := hnotS w v (Ne.symm hvw) hcol.symm
  obtain ⟨hund, htwin⟩ := htwins v w hcell hvw
  exact orbitPartition_swap_of_twin hsymm hloop hanti hvS hwS htwin hund

/-- **Twin-cells ⟹ orbit-recoverable at arbitrary support** — the oracle-vocabulary
form of `cellsAreOrbits_of_twin_cells`, via `orbitRecoverableAt_iff_cellsAreOrbits`.
Where the 1-WL cells are twin classes, refinement (polynomial) computes the
`Aut_S`-orbit partition with *no* depth bound — so a complete cascade oracle is
realisable on the twin regime at any node, not only near discreteness. This is the
within-the-wall-boundary half of the localisation obligation, discharged. -/
theorem orbitRecoverableAt_of_twin_cells {n : Nat} {adj : AdjMatrix n}
    {P : PMatrix n} {S : Finset (Fin n)}
    (hsymm : ∀ a b, adj.adj a b = adj.adj b a)
    (hloop : ∀ a, adj.adj a a = 0)
    (hanti : ∀ a b, P a b = POE.neg (P b a))
    (htwins : ∀ v w : Fin n,
      warmRefine adj P (individualizedColouring n S) v =
          warmRefine adj P (individualizedColouring n S) w →
        v ≠ w →
        P v w = POE.unknown ∧
          (∀ s, s ≠ v → s ≠ w → adj.adj v s = adj.adj w s ∧ P v s = P w s)) :
    OrbitRecoverableAt adj P S :=
  orbitRecoverableAt_iff_cellsAreOrbits.mpr
    (cellsAreOrbits_of_twin_cells hsymm hloop hanti htwins)

/-- **Orbit-recoverable by depth `bound`** — the oracle-contract statement of
"there is a (polynomially bounded) depth at which 1-WL cells coincide with orbits",
i.e. cascade-class membership. The *bound* carries all the content: the unbounded
form `∃ S, CellsAreOrbits adj P S` is **vacuous** (`recoverableByDepth_univ` — take
`S = univ`, where warm refinement is discrete, via `cellsAreOrbits_of_discrete`).
The cascade class realises it at a polynomial bound (`recoverableByDepth_of_cascade`),
CFI(OddDegree) at `cfi_depth_bound` (≤ baseSize), rank-≤2 schemes at depth 1. -/
def RecoverableByDepth {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (bound : Nat) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ bound ∧ CellsAreOrbits adj P S

/-- **Cascade-class foundation.** A graph cascading at depth `k` is orbit-recoverable
by depth `k`: refinement computes orbits at a set of size `≤ k`. Re-export of
`theorem_1_HOR_at_depth` through the `CellsAreOrbits` decomposition. -/
theorem recoverableByDepth_of_cascade {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {k : Nat} (h : CascadesAt adj P k) : RecoverableByDepth adj P k := by
  obtain ⟨S, hcard, _, hrec⟩ := orbitRecoverable_of_cascade h
  exact ⟨S, hcard, orbitRecoverableAt_iff_cellsAreOrbits.mp hrec⟩

/-- **CFI instance** (axiom-free, OddDegree): recoverable by depth `cfi_depth_bound h`
(≤ `baseSize` ≤ `n / 6`), via `theorem_1_HOR_cfi_oddDeg`. -/
theorem recoverableByDepth_cfi {n : Nat} {adj : AdjMatrix n}
    (h : IsCFI' adj) (h_odd : h.OddDegree) (P : PMatrix n) :
    RecoverableByDepth adj P (cfi_depth_bound h) := by
  obtain ⟨S, hcard, _, hrec⟩ := orbitRecoverable_cfi h h_odd P
  exact ⟨S, hcard, orbitRecoverableAt_iff_cellsAreOrbits.mp hrec⟩

/-- **Scheme instance** (axiom-free, rank 2 / `|J| = 1`): recoverable by depth 1 —
and *non-trivially*, the depth-1 cells are not singletons, so this is genuine
recoverability at the very node the oracle acts on (unlike CFI's deep discretizing
set). Via `theorem_2_HOR_concrete_rank_two_J_singleton`. -/
theorem recoverableByDepth_scheme {n : Nat} {adj : AdjMatrix n}
    (h : IsSchurianSchemeGraph' adj) (hrank : h.G.scheme.rank = 2)
    (hJ : h.G.toSchemeGraph.J.card = 1) (P : PMatrix n) (v : Fin n)
    (hP_invariant : ∀ {π : Equiv.Perm (Fin n)}, IsAut π adj →
      ∀ x u, P (π x) (π u) = P x u) :
    RecoverableByDepth adj P 1 :=
  ⟨{v}, (Finset.card_singleton v).le,
    orbitRecoverableAt_iff_cellsAreOrbits.mp
      (orbitRecoverable_scheme h hrank hJ P v hP_invariant)⟩

/-- **The unbounded form is vacuous.** Every graph is orbit-recoverable by depth `n`
(individualize everything: warm refinement is then discrete and cells = orbits =
singletons). So "∃ a depth where cells are orbits" alone says nothing — only the
*polynomial bound* (above) is cascade-class content. This is the oracle-contract
mirror of `cascadesAt_univ` / `theorem_1_HOR_at_n`. -/
theorem recoverableByDepth_univ {n : Nat} {adj : AdjMatrix n} {P : PMatrix n} :
    RecoverableByDepth adj P n :=
  recoverableByDepth_of_cascade (cascadesAt_univ adj P)

namespace CascadeOracleSpec

variable {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
  {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}

/-- **Completeness.** The oracle certifies *every* genuine orbit pair at a node
(returns `some`). With `OrbitMapSpec` (Phase A) this gives the oracle computes the
`Aut_D`-orbit relation exactly. The polynomial collapse of the descent rests on
this: only genuine (false-symmetry) decisions survive as branches. -/
def CascadeComplete (oracle : CascadeOracleSpec adj P₀ χι₀ sel) : Prop :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (v w : Fin n),
    OrbitPartition adj chain.P chain.D v w →
    ∃ result : { π : Equiv.Perm (Fin n) // IsAut π adj }, oracle chain v w = some result

/-- **Exact orbit computation.** A sound (`OrbitMapSpec`) and complete
(`CascadeComplete`) cascade oracle returns `some` for `v, w` **iff** they lie in
the same `Aut_D` orbit. The two halves combine to pin the oracle to the orbit
relation. -/
theorem certifies_iff_orbit {oracle : CascadeOracleSpec adj P₀ χι₀ sel}
    (hsound : OrbitMapSpec oracle) (hcomplete : CascadeComplete oracle)
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (v w : Fin n) :
    (∃ result : { π : Equiv.Perm (Fin n) // IsAut π adj },
        oracle chain v w = some result) ↔
      OrbitPartition adj chain.P chain.D v w := by
  constructor
  · rintro ⟨result, h⟩
    exact hsound chain v w result h
  · intro h
    exact hcomplete chain v w h

/-- **Cell-completeness.** The oracle certifies every pair sharing a 1-WL cell.
This is the *refinement-decidable* completeness — refinement computes the cell
relation in polynomial time. -/
def CellComplete (oracle : CascadeOracleSpec adj P₀ χι₀ sel) : Prop :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (v w : Fin n),
    warmRefine adj chain.P (individualizedColouring n chain.D) v =
        warmRefine adj chain.P (individualizedColouring n chain.D) w →
    ∃ result : { π : Equiv.Perm (Fin n) // IsAut π adj }, oracle chain v w = some result

/-- **The completeness payoff.** At an *orbit-recoverable* node — one where the
orbit relation equals the cell relation (the cascade class, by
`orbitRecoverable_cfi` / `_scheme`) — cell-completeness (refinement-decidable)
suffices for orbit-completeness. So on the cascade class the genuinely hard
"certify every orbit map" reduces to the polynomial "certify every same-cell
pair". (The remaining obligation is that the node's `chain.D` is itself a
recoverable cascade-depth set — the localisation, open.) -/
theorem complete_of_cellComplete_recoverable
    {oracle : CascadeOracleSpec adj P₀ χι₀ sel} (hcell : CellComplete oracle)
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k)
    (hrec : OrbitRecoverableAt adj chain.P chain.D)
    (v w : Fin n) (horb : OrbitPartition adj chain.P chain.D v w) :
    ∃ result : { π : Equiv.Perm (Fin n) // IsAut π adj }, oracle chain v w = some result :=
  hcell chain v w ((hrec v w).mp horb)

/-! ### §C.3 — Phase C: the open obligations

Phase A proved soundness (class-blind); Phase B proved the realizability reduction
(completeness reduces to refinement at orbit-recoverable nodes). What remains is
isolated here — partly **discharged conditionally** (obligation 3, and the
sharpening of obligation 1), partly genuinely **open** (the hard half of 1, and 2),
all without `sorry` or new axioms:

1. **Localisation** — that the oracle is cell-complete and its nodes are
   orbit-recoverable at the depth the recursion reaches.
   `cascadeComplete_of_localization` proves these *suffice* for `CascadeComplete`;
   `orbitRecoverableAt_iff_cellsAreOrbits` sharpens node-recoverability to its single
   non-trivial half `CellsAreOrbits` (the orbits-refine-cells half is unconditional).
   **This obligation splits cleanly, and crucially it is *not* GI ∈ P:**
   * **(1a) bounded-depth recoverability — PROVED on the cascade class.** "There is a
     polynomially bounded depth where cells = orbits" is `RecoverableByDepth`; it holds
     for CFI(OddDegree) (`recoverableByDepth_cfi`, depth ≤ baseSize) and rank-≤2 schemes
     (`recoverableByDepth_scheme`, depth 1 — and there *non-trivially*, at the very node
     the oracle acts on). At any discretizing depth it is automatic
     (`cellsAreOrbits_of_discrete`). The *unbounded* form is vacuous
     (`recoverableByDepth_univ`), so the polynomial bound is the entire content — and it
     is discharged.
   * **(1b) intermediate-to-deep bridging — OPEN, but cascade-class-specific.** Recovery
     holds at the bounded depth `S` of (1a), whereas the oracle acts at a shallower node
     `D ⊊ S` whose cells are coarser than orbits (the genuine-decision case). The
     recursion bridges `D` to `S`; that bridging (the lockstep reconstruction, which the
     C# confirms through CFI(K7)) plus the
     `chain.χι ↔ individualizedColouring n chain.D` partition correspondence is the
     remaining work. It is construction-correctness on the cascade class, **not** the
     general isomorphism problem.

2. **General-class completeness** — that the cascade class is *all* graphs. **This** is
   the `GI ∈ P` obligation (and the only one): the project's honest position is that it
   is **not** expected to hold in general (the non-abelian wall / hidden Johnson), so it
   is recorded as a conjecture, not a target. The proved cascade-class instances are
   CFI(OddDegree) and rank-≤2 schemes (`recoverableByDepth_cfi` / `_scheme`).

3. **Verdict iso-invariance** — `VerdictIsoInvariant` below (strategy §15 gap 2).
   **Discharged conditionally (this phase):** `verdictIsoInvariant_of_complete` proves
   it is *not* an independent obligation — a sound (`OrbitMapSpec`) and complete
   (`CascadeComplete`) oracle at orbit-recoverable nodes is automatically
   verdict-iso-invariant, because its verdict equals the orbit relation
   (`certifies_iff_orbit`), which there equals the iso-invariant cell relation. So
   obligation 3 ⊆ obligation 1: closing localisation closes iso-invariance for free. -/

/-- **Verdict iso-invariance** (strategy §15 gap 2). The oracle's merge decision
depends only on the iso-invariant 1-WL partition, not the raw labelling:
cell-equivalent pairs get the same answer. A concrete, partition-determined form of
the obligation; the full statement (transporting a `SpineChain` along a relabelling)
is itself open work, as for `LinearOracleSpec`. **Derivable** under soundness +
completeness + recoverability — see `verdictIsoInvariant_of_complete`. -/
def VerdictIsoInvariant (oracle : CascadeOracleSpec adj P₀ χι₀ sel) : Prop :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (v w v' w' : Fin n),
    warmRefine adj chain.P (individualizedColouring n chain.D) v =
        warmRefine adj chain.P (individualizedColouring n chain.D) v' →
    warmRefine adj chain.P (individualizedColouring n chain.D) w =
        warmRefine adj chain.P (individualizedColouring n chain.D) w' →
    ((∃ r : { π : Equiv.Perm (Fin n) // IsAut π adj }, oracle chain v w = some r) ↔
      (∃ r : { π : Equiv.Perm (Fin n) // IsAut π adj }, oracle chain v' w' = some r))

/-- **Capstone (provable).** The localisation obligation, made precise as a
*sufficient* condition: if the oracle is cell-complete and every node is
orbit-recoverable, then it is `CascadeComplete`. Discharging the two hypotheses on
the cascade class is the open work (obligation 1 above) — this theorem shows they
are exactly what is missing. -/
theorem cascadeComplete_of_localization {oracle : CascadeOracleSpec adj P₀ χι₀ sel}
    (hcell : CellComplete oracle)
    (hrecAll : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k),
      OrbitRecoverableAt adj chain.P chain.D) :
    CascadeComplete oracle := by
  intro k chain v w horb
  exact complete_of_cellComplete_recoverable hcell chain (hrecAll chain) v w horb

/-- **Capstone (provable), sharpened.** The localisation capstone over the *open
half* of recoverability: cell-completeness plus `CellsAreOrbits` at every node gives
`CascadeComplete`. Identical strength to `cascadeComplete_of_localization` (via
`orbitRecoverableAt_iff_cellsAreOrbits`) but states the hypothesis as the single
implication that is the genuine open content. -/
theorem cascadeComplete_of_cellsAreOrbits {oracle : CascadeOracleSpec adj P₀ χι₀ sel}
    (hcell : CellComplete oracle)
    (hcellOrbAll : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k),
      CellsAreOrbits adj chain.P chain.D) :
    CascadeComplete oracle :=
  cascadeComplete_of_localization hcell
    (fun chain => orbitRecoverableAt_iff_cellsAreOrbits.mpr (hcellOrbAll chain))

/-- **Verdict iso-invariance is derivable** (Phase C obligation 3, discharged
conditionally). A sound (`OrbitMapSpec`) and complete (`CascadeComplete`) oracle at
orbit-recoverable nodes is automatically `VerdictIsoInvariant`: by
`certifies_iff_orbit` its verdict on `(v, w)` is exactly `OrbitPartition`, and at a
recoverable node that equals the iso-invariant cell relation, which is preserved
under the cell-equivalences `v ~ v'`, `w ~ w'`. So iso-invariance is **not** an
independent obligation — it follows from localisation (obligation 1) for free. -/
theorem verdictIsoInvariant_of_complete {oracle : CascadeOracleSpec adj P₀ χι₀ sel}
    (hsound : OrbitMapSpec oracle) (hcomplete : CascadeComplete oracle)
    (hrecAll : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k),
      OrbitRecoverableAt adj chain.P chain.D) :
    VerdictIsoInvariant oracle := by
  intro k chain v w v' w' hvv' hww'
  rw [certifies_iff_orbit hsound hcomplete chain v w,
      certifies_iff_orbit hsound hcomplete chain v' w',
      (hrecAll chain) v w, (hrecAll chain) v' w', hvv', hww']

/-- **Capstone (provable).** Assembling the program: a sound oracle that is complete
returns `some` for `v, w` iff they share an `Aut_D` orbit — it computes the orbit
relation exactly. Soundness (`OrbitMapSpec`) is discharged (Phase A); completeness
(`CascadeComplete`) is the localisation obligation (Phase C, obligation 1). Restates
`certifies_iff_orbit` as the program-level correctness conditional on the one open
hypothesis. -/
theorem computes_orbits_of_complete {oracle : CascadeOracleSpec adj P₀ χι₀ sel}
    (hsound : OrbitMapSpec oracle) (hcomplete : CascadeComplete oracle)
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (v w : Fin n) :
    (∃ result : { π : Equiv.Perm (Fin n) // IsAut π adj },
        oracle chain v w = some result) ↔
      OrbitPartition adj chain.P chain.D v w :=
  certifies_iff_orbit hsound hcomplete chain v w

end CascadeOracleSpec

/-! ### §C.4 — M-B: the concrete colour-match oracle (`colourMatchPerm` / `matchOracle`)

The shared open construction that fires *both* oracles
([declassing §9](../../docs/chain-descent-declassing.md),
[cascade-oracle §2.6](../../docs/chain-descent-cascade-oracle.md)). `colourMatchPerm` is the explicit
`Equiv.Perm` built from the two *discrete* branch colourings as the rank composition
`(rankPerm χ_w)⁻¹ * (rankPerm χ_v)`; `matchOracle` **constructs** it and then **verifies**
`IsAut ∧ P-preserving ∧ fixes D ∧ v ↦ w` (construct-and-check — *not* the existential shortcut, so
soundness *derives* the orbit witness from the constructed perm, and completeness genuinely uses
`colourMatchPerm = g` via `vertexRank_comp`). Soundness (`OrbitMapSpec`) is **unconditional**;
completeness reduces to the two named-open hypotheses (one-step discretizing depth = M-C / "B's core";
`CellsAreOrbits` = localisation). -/

/-- The rank-composition identity behind `colourMatchPerm = g`: if `g` value-matches the two
colourings (`χ₂ ∘ g = χ₁`), then `(rankPerm χ₂)⁻¹ * rankPerm χ₁ = g` — pure `vertexRank` reindexing
(`vertexRank_comp`), no graph structure. -/
theorem rankPerm_inv_mul_eq_of_match {n : Nat} {χ₁ χ₂ : Colouring n} {g : Equiv.Perm (Fin n)}
    (h₁ : Discrete χ₁) (h₂ : Discrete χ₂) (hmatch : ∀ x, χ₂ (g x) = χ₁ x) :
    (Colouring.rankPerm χ₂ h₂)⁻¹ * Colouring.rankPerm χ₁ h₁ = g := by
  have hcomp : Colouring.rankPerm χ₁ h₁ = Colouring.rankPerm χ₂ h₂ * g := by
    ext v
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Colouring.rankPerm_apply]
    have hfun : (fun x => χ₂ (g x)) = χ₁ := funext hmatch
    rw [← hfun]
    exact congrArg _ (vertexRank_comp χ₂ g v)
  rw [hcomp, inv_mul_cancel_left]

/-- **M-B — the colour-match permutation.** The explicit `Equiv.Perm` matching branch-`v`'s discrete
refined colouring to branch-`w`'s, as the rank composition `(rankPerm χ_w)⁻¹ * (rankPerm χ_v)`
(`χ_r = warmRefine adj P (indivWithRep n D r)`). Always a well-defined permutation given the two
discreteness proofs; equal to the orbit automorphism at a recoverable node
(`colourMatchPerm_eq_of_orbit`). -/
noncomputable def colourMatchPerm {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (D : Finset (Fin n)) (v w : Fin n)
    (hv : Discrete (warmRefine adj P (indivWithRep n D v)))
    (hw : Discrete (warmRefine adj P (indivWithRep n D w))) : Equiv.Perm (Fin n) :=
  (Colouring.rankPerm (warmRefine adj P (indivWithRep n D w)) hw)⁻¹ *
    Colouring.rankPerm (warmRefine adj P (indivWithRep n D v)) hv

/-- **`colourMatchPerm` is the orbit automorphism, at a recoverable node.** An `Aut_D` witness `g`
(`g v = w`, `w ∉ D`) value-matches the two branch colourings (`colourMatch_complete`), so the
rank-composition `colourMatchPerm` equals it. The completeness linchpin — built from the colours,
not assumed. -/
theorem colourMatchPerm_eq_of_orbit {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {D : Finset (Fin n)} {v w : Fin n} {g : Equiv.Perm (Fin n)}
    (hv : Discrete (warmRefine adj P (indivWithRep n D v)))
    (hw : Discrete (warmRefine adj P (indivWithRep n D w)))
    (hg : IsAut g adj) (hgP : ∀ x u, P (g x) (g u) = P x u)
    (hgD : FixesPointwise g D) (hgvw : g v = w) (hwD : w ∉ D) :
    colourMatchPerm adj P D v w hv hw = g :=
  rankPerm_inv_mul_eq_of_match hv hw (colourMatch_complete hg hgP hgD hgvw hwD)

open Classical in
/-- **M-B — the colour-match cascade oracle.** Construct `colourMatchPerm` from the two branch
colourings (when both footprints are discrete), then return it **iff** it verifies as an `Aut_D`
orbit map (`IsAut ∧ P-preserving ∧ fixes D ∧ v ↦ w`). Construct-and-check: *not* the existential
shortcut, so soundness derives the orbit witness from the constructed perm rather than assuming it. -/
noncomputable def matchOracle {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) :
    CascadeOracleSpec adj P₀ χι₀ sel :=
  fun {k} chain v w =>
    if hv : Discrete (warmRefine adj chain.P (indivWithRep n chain.D v)) then
      if hw : Discrete (warmRefine adj chain.P (indivWithRep n chain.D w)) then
        if hchk : IsAut (colourMatchPerm adj chain.P chain.D v w hv hw) adj
            ∧ (∀ x u, chain.P (colourMatchPerm adj chain.P chain.D v w hv hw x)
                              (colourMatchPerm adj chain.P chain.D v w hv hw u) = chain.P x u)
            ∧ FixesPointwise (colourMatchPerm adj chain.P chain.D v w hv hw) chain.D
            ∧ colourMatchPerm adj chain.P chain.D v w hv hw v = w then
          some ⟨colourMatchPerm adj chain.P chain.D v w hv hw, hchk.1⟩
        else none
      else none
    else none

/-- **The oracle fires once the constructed perm passes the checks.** A reusable evaluation lemma:
given the discreteness proofs and the four verification facts about `colourMatchPerm`, `matchOracle`
returns `some`. The engine of the completeness proof. -/
theorem matchOracle_fires {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) {v w : Fin n}
    (hv : Discrete (warmRefine adj chain.P (indivWithRep n chain.D v)))
    (hw : Discrete (warmRefine adj chain.P (indivWithRep n chain.D w)))
    (hAut : IsAut (colourMatchPerm adj chain.P chain.D v w hv hw) adj)
    (hP : ∀ x u, chain.P (colourMatchPerm adj chain.P chain.D v w hv hw x)
                         (colourMatchPerm adj chain.P chain.D v w hv hw u) = chain.P x u)
    (hFix : FixesPointwise (colourMatchPerm adj chain.P chain.D v w hv hw) chain.D)
    (hvw : colourMatchPerm adj chain.P chain.D v w hv hw v = w) :
    ∃ result, matchOracle adj P₀ χι₀ sel chain v w = some result := by
  have hchk : IsAut (colourMatchPerm adj chain.P chain.D v w hv hw) adj
      ∧ (∀ x u, chain.P (colourMatchPerm adj chain.P chain.D v w hv hw x)
                        (colourMatchPerm adj chain.P chain.D v w hv hw u) = chain.P x u)
      ∧ FixesPointwise (colourMatchPerm adj chain.P chain.D v w hv hw) chain.D
      ∧ colourMatchPerm adj chain.P chain.D v w hv hw v = w := ⟨hAut, hP, hFix, hvw⟩
  refine ⟨⟨colourMatchPerm adj chain.P chain.D v w hv hw, hAut⟩, ?_⟩
  simp only [matchOracle]
  rw [dif_pos hv, dif_pos hw, dif_pos hchk]

/-- **M-B soundness — `OrbitMapSpec`, unconditional.** When `matchOracle` fires, its four checks
*are* the `OrbitPartition` witness conditions, so the returned perm certifies a genuine `Aut_D` orbit
pair. No discreteness or recoverability hypothesis. -/
theorem matchOracle_orbitMapSpec {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n)) :
    CascadeOracleSpec.OrbitMapSpec (matchOracle adj P₀ χι₀ sel) := by
  intro _k chain v w _result heq
  simp only [matchOracle] at heq
  split_ifs at heq with hv hw hchk
  exact ⟨colourMatchPerm adj chain.P chain.D v w hv hw,
    hchk.1, hchk.2.1, hchk.2.2.1, hchk.2.2.2⟩

/-- **M-B completeness — `CellComplete` on the discretizing recoverable class.** Conditional on the
two named-open hypotheses: every node one-step-discretizing (`hdisc`, = the exposure-depth witness /
M-C / "B's core") and `CellsAreOrbits` at every node (`hco`, = localisation). At a same-cell pair the
orbit automorphism `g` exists (`hco`), `colourMatchPerm = g` (`colourMatchPerm_eq_of_orbit`), so the
checks pass and the oracle fires. The `w ∈ D` edge case collapses to `v = w` (where
`colourMatchPerm = 1`). -/
theorem matchOracle_cellComplete {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    (hdisc : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (r : Fin n),
       Discrete (warmRefine adj chain.P (indivWithRep n chain.D r)))
    (hco : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k),
       CellsAreOrbits adj chain.P chain.D) :
    CascadeOracleSpec.CellComplete (matchOracle adj P₀ χι₀ sel) := by
  intro k chain v w hcell
  have hv := hdisc chain v
  have hw := hdisc chain w
  have hinit : individualizedColouring n chain.D v = individualizedColouring n chain.D w :=
    warmRefine_refines adj chain.P (individualizedColouring n chain.D) hcell
  by_cases hwD : w ∈ chain.D
  · have hvw : v = w := (individualizedColouring_eq_iff_of_mem chain.D hwD).mp hinit
    subst hvw
    have hid : colourMatchPerm adj chain.P chain.D v v hv hw = 1 := by
      simp only [colourMatchPerm]
      exact inv_mul_cancel _
    refine matchOracle_fires chain hv hw ?_ ?_ ?_ ?_
    · rw [hid]; exact fun _ _ => rfl
    · rw [hid]; exact fun _ _ => rfl
    · rw [hid]; exact fun _ _ => rfl
    · rw [hid]; rfl
  · obtain ⟨g, hg, hgP, hgD, hgvw⟩ := hco chain v w hcell
    have hcmp : colourMatchPerm adj chain.P chain.D v w hv hw = g :=
      colourMatchPerm_eq_of_orbit hv hw hg hgP hgD hgvw hwD
    refine matchOracle_fires chain hv hw ?_ ?_ ?_ ?_
    · rw [hcmp]; exact hg
    · rw [hcmp]; exact hgP
    · rw [hcmp]; exact hgD
    · rw [hcmp]; exact hgvw

/-- **M-B capstone — `CascadeComplete`.** The construct-and-check `matchOracle` computes the orbit
relation exactly, reduced to the two named-open hypotheses (discretizing depth + `CellsAreOrbits`).
Soundness (`matchOracle_orbitMapSpec`) is already unconditional; this supplies completeness. -/
theorem matchOracle_cascadeComplete {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    (hdisc : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (r : Fin n),
       Discrete (warmRefine adj chain.P (indivWithRep n chain.D r)))
    (hco : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k),
       CellsAreOrbits adj chain.P chain.D) :
    CascadeOracleSpec.CascadeComplete (matchOracle adj P₀ χι₀ sel) :=
  CascadeOracleSpec.cascadeComplete_of_cellsAreOrbits
    (matchOracle_cellComplete hdisc hco) hco

/-- **M-B — flag iso-invariance, free.** With soundness (unconditional) and completeness (under the
two hypotheses), `verdictIsoInvariant_of_complete` gives the oracle's verdict as a function of the
iso-invariant 1-WL partition — discharging strategy §15 gap 2 for `matchOracle` on the recoverable
class. -/
theorem matchOracle_verdictIsoInvariant {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    (hdisc : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (r : Fin n),
       Discrete (warmRefine adj chain.P (indivWithRep n chain.D r)))
    (hco : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k),
       CellsAreOrbits adj chain.P chain.D) :
    CascadeOracleSpec.VerdictIsoInvariant (matchOracle adj P₀ χι₀ sel) :=
  CascadeOracleSpec.verdictIsoInvariant_of_complete
    (matchOracle_orbitMapSpec adj P₀ χι₀ sel)
    (matchOracle_cascadeComplete hdisc hco)
    (fun chain => orbitRecoverableAt_iff_cellsAreOrbits.mpr (hco chain))

/-! ### §C.4b — the depth-witness bridge (single-rep): `hdisc` ⟸ indexed-recovery discreteness

The feasibility probe (`docs/Archive/ChainDescent/cfi.lean`) established, and this section formalizes,
that the single-rep footprint `indivWithRep D r` has the **same partition** as the *indexed*
`individualizedColouring (insert r D)` — `r` is marked by a globally-unique colour either way (`n+1`
vs `r.val+1`), and the two colourings agree off `r`. Hence M-B's depth witness
`hdisc` (`Discrete (warmRefine … (indivWithRep D r))`) follows from discreteness of the *indexed*
colouring `individualizedColouring (insert r D)` — i.e. from the `RecoverableByDepth` / discretizing-depth
framework that `recoverableByDepth_cfi` / `_scheme` populate, **class-agnostically**.

**Asymmetry the probe also pinned (why this is single-rep only).** The multi-step *uniform*
`indivWithSet D R` (the whole set `R` one block colour `n+1`) is strictly **coarser** than the indexed
`individualizedColouring (D ∪ R)` whenever `|R| ≥ 2`, so it has **no** such bridge — uniform marking of a
≥2 set genuinely loses resolution. Concretely (probe): for CFI(K4) the indexed seeds discretize at the
empty commit while the uniform-block seeds do not. This is exactly why M-D's `hdiscSet` is strictly harder
than M-B's `hdisc`, and why the single rep is the discretizing-mode harvest's natural unit. -/

/-- Discreteness transfers across `samePartition` (both directions are the same partition). -/
theorem discrete_of_samePartition {n : Nat} {χ₁ χ₂ : Colouring n}
    (h : samePartition χ₁ χ₂) (hd : Discrete χ₁) : Discrete χ₂ :=
  fun i j hij => hd i j ((h i j).mpr hij)

/-- `warmRefine` respects `samePartition` (specialization of `warmRefine_agree_off'`, `D = ∅`). -/
theorem warmRefine_samePartition {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    {χ χ' : Colouring n} (h : samePartition χ χ') :
    samePartition (warmRefine adj P χ) (warmRefine adj P χ') :=
  warmRefine_agree_off' adj P P χ χ' ∅ h (fun _ _ _ => rfl)
    (fun x hx => absurd hx (by simp))

/-- **Same partition: single-rep footprint = indexed `insert`.** For `r ∉ D`, `indivWithRep n D r` and
`individualizedColouring n (insert r D)` induce the same partition: they agree off `r`, and at `r` each
assigns a colour distinct from every other vertex's. -/
theorem samePartition_indivWithRep_insert {n : Nat} (D : Finset (Fin n)) (r : Fin n) (hr : r ∉ D) :
    samePartition (indivWithRep n D r) (individualizedColouring n (insert r D)) := by
  -- off `r`, the two colourings are literally equal
  have hoff : ∀ v, v ≠ r → indivWithRep n D r v = individualizedColouring n (insert r D) v := by
    intro v hv
    rw [indivWithRep, if_neg hv]
    by_cases hvD : v ∈ D
    · rw [individualizedColouring, if_pos hvD, individualizedColouring,
          if_pos (Finset.mem_insert_of_mem hvD)]
    · rw [individualizedColouring, if_neg hvD, individualizedColouring,
          if_neg (by simp [Finset.mem_insert, hv, hvD])]
  -- `r`'s colour is globally unique under `indivWithRep` (it is `n+1`, others are `≤ n` or `0`)
  have huA : ∀ v, v ≠ r → indivWithRep n D r v ≠ indivWithRep n D r r := by
    intro v hv
    have hrr : indivWithRep n D r r = n + 1 := by rw [indivWithRep, if_pos rfl]
    have hle : indivWithRep n D r v ≤ n := by
      rw [indivWithRep, if_neg hv, individualizedColouring]
      split
      · exact v.is_lt
      · exact Nat.zero_le n
    rw [hrr]; omega
  -- `r`'s colour is globally unique under the indexed colouring (it is `r.val+1`)
  have huB : ∀ v, v ≠ r → individualizedColouring n (insert r D) v
      ≠ individualizedColouring n (insert r D) r := by
    intro v hv
    have hrr : individualizedColouring n (insert r D) r = r.val + 1 := by
      rw [individualizedColouring, if_pos (Finset.mem_insert_self r D)]
    rw [hrr, individualizedColouring]
    by_cases hvD : v ∈ D
    · rw [if_pos (Finset.mem_insert_of_mem hvD)]; intro h; exact hv (Fin.ext (by omega))
    · rw [if_neg (by simp [Finset.mem_insert, hv, hvD])]; omega
  intro i j
  by_cases hi : i = r <;> by_cases hj : j = r
  · subst hi; subst hj; exact ⟨fun _ => rfl, fun _ => rfl⟩
  · subst hi
    exact ⟨fun h => absurd h.symm (huA j hj), fun h => absurd h.symm (huB j hj)⟩
  · subst hj
    exact ⟨fun h => absurd h (huA i hi), fun h => absurd h (huB i hi)⟩
  · rw [hoff i hi, hoff j hj]

/-- **The M-B depth-witness bridge.** `hdisc` for rep `r` (discreteness of the single-rep footprint)
follows from discreteness of the *indexed* `individualizedColouring (insert r D)`. This connects M-B's
depth witness to the `RecoverableByDepth` / discretizing-depth framework (class-agnostic); the per-class
CFI / scheme recovery theorems supply the indexed discreteness as witnesses. -/
theorem discrete_indivWithRep_of_discrete_insert {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (D : Finset (Fin n)) (r : Fin n) (hr : r ∉ D)
    (hd : Discrete (warmRefine adj P (individualizedColouring n (insert r D)))) :
    Discrete (warmRefine adj P (indivWithRep n D r)) :=
  discrete_of_samePartition
    (warmRefine_samePartition adj P (samePartition_indivWithRep_insert D r hr).symm) hd

/-! ### §C.5 — M-C: multi-step depth (`indivWithSet`)

`indivWithRep` (M-B) marks a single explored rep; CFI's `tw(H)` depth needs a *sequence* of explored
vertices before the footprint discretizes. `indivWithSet` marks an arbitrary explored *set* `R`,
**uniformly** — the only transport-compatible choice: an orbit automorphism *moves* `R` (`R₂ = g(R₁) ≠
R₁`), so distinct/index colours would break `χ₂ ∘ g = χ₁` on `R`, and a `g`-dependent distinct
colouring is unavailable to an oracle that does not know `g`. The harvest bricks lift verbatim
(`colourMatch_eq_aut` / `colourMatch_isAut` are already *colouring-generic*; only the **transport**
specializes), so the colour-match candidate equals the orbit automorphism at a *set*-discretized
footprint. `indivWithRep` is the singleton case.

**Scope.** M-C delivers the depth-correct *ingredients* (colouring + transport + lifted bricks + the
multi-step `colourMatchPermSet`). The multi-step *oracle* `matchOracleSet` and the **lockstep** argument
that branch-`w`'s independently chosen exploration set equals `(branch-`v`'s).image g` are **M-D**. -/

/-- **Multi-step uniform individualization.** Individualize the committed set `S` by index, plus an
explored *set* `R` with a single uniform fresh colour `n+1`. Generalizes `indivWithRep` (the `R = {r}`
case). Uniform on `R` is forced by transport (an orbit automorphism moves `R`, so only a colour
constant on `R` satisfies `χ₂ ∘ g = χ₁`). -/
def indivWithSet (n : Nat) (S R : Finset (Fin n)) : Colouring n :=
  fun v => if v ∈ R then n + 1 else individualizedColouring n S v

/-- `indivWithRep` is the singleton case of `indivWithSet`. -/
theorem indivWithRep_eq_indivWithSet {n : Nat} (S : Finset (Fin n)) (r : Fin n) :
    indivWithRep n S r = indivWithSet n S {r} := by
  funext v; simp only [indivWithRep, indivWithSet, Finset.mem_singleton]

/-- **The multi-step transport hypothesis.** An orbit automorphism `g` fixing the committed set `S`
and mapping the explored set `R₁` onto `R₂ = R₁.image g` carries the branch-`R₁` colouring onto the
branch-`R₂` colouring (`χ₂ ∘ g = χ₁`). The `indivWithRep_transport` generalization — uniform colour on
`R` is exactly what makes it hold on the moved set. -/
theorem indivWithSet_transport {n : Nat} {S R₁ R₂ : Finset (Fin n)} {g : Equiv.Perm (Fin n)}
    (hgS : FixesPointwise g S) (hR : R₂ = R₁.image g) (v : Fin n) :
    indivWithSet n S R₂ (g v) = indivWithSet n S R₁ v := by
  unfold indivWithSet
  by_cases hv : v ∈ R₁
  · have hgv : g v ∈ R₂ := by rw [hR]; exact Finset.mem_image_of_mem g hv
    rw [if_pos hgv, if_pos hv]
  · have hgv : g v ∉ R₂ := by
      rw [hR, Finset.mem_image]
      rintro ⟨u, hu, hgu⟩
      exact hv ((g.injective hgu) ▸ hu)
    rw [if_neg hgv, if_neg hv]
    by_cases hvS : v ∈ S
    · rw [hgS v hvS]
    · have hgvS : g v ∉ S := hgS.complement hvS
      simp only [individualizedColouring, if_neg hgvS, if_neg hvS]

/-- **The multi-step colour-match relation.** `t` matches branch-`R₂`'s refined colours to
branch-`R₁`'s. The `IsColourMatch` generalization. -/
def IsColourMatchSet {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) (S R₁ R₂ : Finset (Fin n))
    (t : Equiv.Perm (Fin n)) : Prop :=
  ∀ x, warmRefine adj P (indivWithSet n S R₂) (t x) = warmRefine adj P (indivWithSet n S R₁) x

/-- **Multi-step completeness brick.** The orbit automorphism `g` (fixing `S`, `R₂ = R₁.image g`) *is* a
colour-match — via `warmRefine_transport ∘ indivWithSet_transport`. -/
theorem colourMatchSet_complete {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {S R₁ R₂ : Finset (Fin n)} {g : Equiv.Perm (Fin n)}
    (hg : IsAut g adj) (hgP : ∀ x u, P (g x) (g u) = P x u)
    (hgS : FixesPointwise g S) (hR : R₂ = R₁.image g) :
    IsColourMatchSet adj P S R₁ R₂ g :=
  fun x => warmRefine_transport hg hgP (indivWithSet_transport hgS hR) x

/-- **Multi-step uniqueness brick.** At a discrete branch-`R₂` footprint, any colour-match equals the
orbit automorphism `g` — via the colouring-generic `colourMatch_eq_aut`. The `colourMatch_unique`
generalization. -/
theorem colourMatchSet_unique {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {S R₁ R₂ : Finset (Fin n)} {g t : Equiv.Perm (Fin n)}
    (hg : IsAut g adj) (hgP : ∀ x u, P (g x) (g u) = P x u)
    (hgS : FixesPointwise g S) (hR : R₂ = R₁.image g)
    (hdisc : Discrete (warmRefine adj P (indivWithSet n S R₂)))
    (ht : IsColourMatchSet adj P S R₁ R₂ t) :
    t = g :=
  colourMatch_eq_aut hg hgP (indivWithSet_transport hgS hR) hdisc ht

/-- **Multi-step harvest brick.** At a discrete branch-`R₂` footprint, any colour-match candidate
verifies as an automorphism (it equals `g`). The `harvest_isAut_of_discrete` generalization: the
harvest now fires at a footprint discretized by an explored *set* (a sequence), not just one rep. -/
theorem harvestSet_isAut_of_discrete {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {S R₁ R₂ : Finset (Fin n)} {g t : Equiv.Perm (Fin n)}
    (hg : IsAut g adj) (hgP : ∀ x u, P (g x) (g u) = P x u)
    (hgS : FixesPointwise g S) (hR : R₂ = R₁.image g)
    (hdisc : Discrete (warmRefine adj P (indivWithSet n S R₂)))
    (ht : IsColourMatchSet adj P S R₁ R₂ t) :
    IsAut t adj :=
  colourMatch_isAut hg hgP (indivWithSet_transport hgS hR) hdisc ht

/-- **M-C — the multi-step colour-match permutation.** The rank composition for set footprints;
`colourMatchPerm` (M-B) is the `R₁ = {v}`, `R₂ = {w}` case. -/
noncomputable def colourMatchPermSet {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (S R₁ R₂ : Finset (Fin n))
    (h₁ : Discrete (warmRefine adj P (indivWithSet n S R₁)))
    (h₂ : Discrete (warmRefine adj P (indivWithSet n S R₂))) : Equiv.Perm (Fin n) :=
  (Colouring.rankPerm (warmRefine adj P (indivWithSet n S R₂)) h₂)⁻¹ *
    Colouring.rankPerm (warmRefine adj P (indivWithSet n S R₁)) h₁

/-- **`colourMatchPermSet` is the orbit automorphism, at a recoverable set-footprint.** Same proof
shape as `colourMatchPerm_eq_of_orbit` (`rankPerm_inv_mul_eq_of_match` ← `vertexRank_comp` +
`colourMatchSet_complete`), now over an explored set. -/
theorem colourMatchPermSet_eq_of_orbit {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {S R₁ R₂ : Finset (Fin n)} {g : Equiv.Perm (Fin n)}
    (h₁ : Discrete (warmRefine adj P (indivWithSet n S R₁)))
    (h₂ : Discrete (warmRefine adj P (indivWithSet n S R₂)))
    (hg : IsAut g adj) (hgP : ∀ x u, P (g x) (g u) = P x u)
    (hgS : FixesPointwise g S) (hR : R₂ = R₁.image g) :
    colourMatchPermSet adj P S R₁ R₂ h₁ h₂ = g :=
  rankPerm_inv_mul_eq_of_match h₁ h₂ (colourMatchSet_complete hg hgP hgS hR)

/-- **The multi-step firing certificate exists.** Where `CellsAreOrbits` gives the orbit automorphism
`g` for a same-cell pair `(v, w)`, then for *any* exploration set `R₁` the partner `R₂ = R₁.image g`
exists, contains `w` whenever `v ∈ R₁`, and `g` is a colour-match between them. The multi-step analogue
of `colourMatch_exists_of_cellsAreOrbits`; the open piece (M-D) is that the oracle's independently
chosen branch-`w` set *is* this `R₁.image g` (lockstep). -/
theorem colourMatchSet_exists_of_cellsAreOrbits {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {S : Finset (Fin n)} {v w : Fin n} (R₁ : Finset (Fin n))
    (hco : CellsAreOrbits adj P S)
    (hcell : warmRefine adj P (individualizedColouring n S) v
           = warmRefine adj P (individualizedColouring n S) w) :
    ∃ g : Equiv.Perm (Fin n), IsAut g adj ∧ (∀ x u, P (g x) (g u) = P x u)
      ∧ FixesPointwise g S ∧ g v = w ∧ IsColourMatchSet adj P S R₁ (R₁.image g) g := by
  obtain ⟨g, hg, hgP, hgS, hgvw⟩ := hco v w hcell
  exact ⟨g, hg, hgP, hgS, hgvw, colourMatchSet_complete hg hgP hgS rfl⟩

/-! ### §C.6 — M-D: the multi-step oracle (`matchOracleSet`) + the lockstep

M-C lifted the harvest bricks to an explored *set* `R`, leaving open the *oracle* that threads the set
and the **lockstep** correspondence — that branch-`w`'s independently chosen exploration set is the
`g`-image of branch-`v`'s (`R₂ = R₁.image g`). `matchOracleSet` is the multi-step `matchOracle`,
parameterized by an exploration-set selector `expand`. Soundness is **unconditional** (as M-B);
completeness reduces to set-footprint discreteness + `CellsAreOrbits` + **`LockstepExpand expand`** (the
equivariance of `expand`). The lockstep is *not assumed in general*: it is **discharged** for the
canonical iso-invariant rule `forcedExpand` (in `Cascade.lean`, via Leg A's `movedSet_image`). -/

open Classical in
/-- **M-D — the multi-step colour-match oracle.** Like `matchOracle` but individualizes a whole
explored *set* `expand chain r` (per the selector) on top of the committed path. Construct
`colourMatchPermSet`, return it **iff** it verifies `IsAut ∧ P-preserving ∧ fixes D ∧ v ↦ w`. -/
noncomputable def matchOracleSet {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n))
    (expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → Finset (Fin n)) :
    CascadeOracleSpec adj P₀ χι₀ sel :=
  fun {k} chain v w =>
    if hv : Discrete (warmRefine adj chain.P (indivWithSet n chain.D (expand chain v))) then
      if hw : Discrete (warmRefine adj chain.P (indivWithSet n chain.D (expand chain w))) then
        if hchk :
            IsAut (colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw) adj
            ∧ (∀ x u, chain.P (colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw x)
                              (colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw u)
                       = chain.P x u)
            ∧ FixesPointwise (colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw) chain.D
            ∧ colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw v = w then
          some ⟨colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw, hchk.1⟩
        else none
      else none
    else none

/-- Evaluation lemma: given discreteness + the four verification facts about `colourMatchPermSet`,
`matchOracleSet` fires. The engine of the completeness proof. -/
theorem matchOracleSet_fires {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → Finset (Fin n)}
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) {v w : Fin n}
    (hv : Discrete (warmRefine adj chain.P (indivWithSet n chain.D (expand chain v))))
    (hw : Discrete (warmRefine adj chain.P (indivWithSet n chain.D (expand chain w))))
    (hAut : IsAut (colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw) adj)
    (hP : ∀ x u, chain.P (colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw x)
                         (colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw u)
                  = chain.P x u)
    (hFix : FixesPointwise (colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw) chain.D)
    (hvw : colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw v = w) :
    ∃ result, matchOracleSet adj P₀ χι₀ sel expand chain v w = some result := by
  have hchk :
      IsAut (colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw) adj
      ∧ (∀ x u, chain.P (colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw x)
                        (colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw u)
                 = chain.P x u)
      ∧ FixesPointwise (colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw) chain.D
      ∧ colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw v = w :=
    ⟨hAut, hP, hFix, hvw⟩
  refine ⟨⟨colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw, hAut⟩, ?_⟩
  simp only [matchOracleSet]
  rw [dif_pos hv, dif_pos hw, dif_pos hchk]

/-- **M-D soundness — `OrbitMapSpec`, unconditional.** As for `matchOracle`: when it fires, the four
checks *are* the `OrbitPartition` witness. No discreteness/recoverability/lockstep hypothesis. -/
theorem matchOracleSet_orbitMapSpec {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n))
    (expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → Finset (Fin n)) :
    CascadeOracleSpec.OrbitMapSpec (matchOracleSet adj P₀ χι₀ sel expand) := by
  intro _k chain v w _result heq
  simp only [matchOracleSet] at heq
  split_ifs at heq with hv hw hchk
  exact ⟨colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw,
    hchk.1, hchk.2.1, hchk.2.2.1, hchk.2.2.2⟩

/-- **The lockstep correspondence** (the genuinely new M-D content, stated as a property of the
exploration rule): `expand` is *equivariant* — any `P`-preserving automorphism `g` fixing the committed
path carries one branch's exploration set onto the other's. With `g v = w` this gives
`expand chain w = (expand chain v).image g`, exactly the `R₂ = R₁.image g` the harvest needs. Discharged
for the canonical rule by `lockstepExpand_forcedExpand` (`Cascade.lean`). -/
def LockstepExpand {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)}
    (expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → Finset (Fin n)) : Prop :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (g : Equiv.Perm (Fin n)) (v : Fin n),
    IsAut g adj → (∀ x u, chain.P (g x) (g u) = chain.P x u) → FixesPointwise g chain.D →
    expand chain (g v) = (expand chain v).image g

/-- **M-D completeness — `CellComplete`.** Conditional on three named-open hypotheses: set-footprint
discreteness (`hdiscSet`, = the multi-step depth witness / "B's core"), `CellsAreOrbits` (`hco`, =
localisation), and `LockstepExpand` (`hlock` — *discharged* for `forcedExpand`). At a same-cell pair the
orbit automorphism `g` exists (`hco`); the lockstep supplies `R₂ = R₁.image g`, so
`colourMatchPermSet = g` and the oracle fires. The `w ∈ D` edge case collapses to `v = w` (identity). -/
theorem matchOracleSet_cellComplete {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → Finset (Fin n)}
    (hdiscSet : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (r : Fin n),
       Discrete (warmRefine adj chain.P (indivWithSet n chain.D (expand chain r))))
    (hco : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k),
       CellsAreOrbits adj chain.P chain.D)
    (hlock : LockstepExpand expand) :
    CascadeOracleSpec.CellComplete (matchOracleSet adj P₀ χι₀ sel expand) := by
  intro k chain v w hcell
  have hv := hdiscSet chain v
  have hw := hdiscSet chain w
  have hinit : individualizedColouring n chain.D v = individualizedColouring n chain.D w :=
    warmRefine_refines adj chain.P (individualizedColouring n chain.D) hcell
  by_cases hwD : w ∈ chain.D
  · have hvw : v = w := (individualizedColouring_eq_iff_of_mem chain.D hwD).mp hinit
    subst hvw
    have hid : colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain v) hv hw = 1 := by
      simp only [colourMatchPermSet]
      exact inv_mul_cancel _
    refine matchOracleSet_fires chain hv hw ?_ ?_ ?_ ?_
    · rw [hid]; exact fun _ _ => rfl
    · rw [hid]; exact fun _ _ => rfl
    · rw [hid]; exact fun _ _ => rfl
    · rw [hid]; rfl
  · obtain ⟨g, hg, hgP, hgD, hgvw⟩ := hco chain v w hcell
    have hR : expand chain w = (expand chain v).image g := by
      have h := hlock chain g v hg hgP hgD
      rwa [hgvw] at h
    have hcmps : colourMatchPermSet adj chain.P chain.D (expand chain v) (expand chain w) hv hw = g :=
      colourMatchPermSet_eq_of_orbit hv hw hg hgP hgD hR
    refine matchOracleSet_fires chain hv hw ?_ ?_ ?_ ?_
    · rw [hcmps]; exact hg
    · rw [hcmps]; exact hgP
    · rw [hcmps]; exact hgD
    · rw [hcmps]; exact hgvw

/-- **M-D capstone — `CascadeComplete`.** The multi-step oracle computes the orbit relation exactly,
reduced to the three named-open hypotheses (the lockstep being discharged for `forcedExpand`). -/
theorem matchOracleSet_cascadeComplete {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → Finset (Fin n)}
    (hdiscSet : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (r : Fin n),
       Discrete (warmRefine adj chain.P (indivWithSet n chain.D (expand chain r))))
    (hco : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k),
       CellsAreOrbits adj chain.P chain.D)
    (hlock : LockstepExpand expand) :
    CascadeOracleSpec.CascadeComplete (matchOracleSet adj P₀ χι₀ sel expand) :=
  CascadeOracleSpec.cascadeComplete_of_cellsAreOrbits
    (matchOracleSet_cellComplete hdiscSet hco hlock) hco

/-- **M-D — flag iso-invariance, free.** As for `matchOracle`. -/
theorem matchOracleSet_verdictIsoInvariant {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → Finset (Fin n)}
    (hdiscSet : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (r : Fin n),
       Discrete (warmRefine adj chain.P (indivWithSet n chain.D (expand chain r))))
    (hco : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k),
       CellsAreOrbits adj chain.P chain.D)
    (hlock : LockstepExpand expand) :
    CascadeOracleSpec.VerdictIsoInvariant (matchOracleSet adj P₀ χι₀ sel expand) :=
  CascadeOracleSpec.verdictIsoInvariant_of_complete
    (matchOracleSet_orbitMapSpec adj P₀ χι₀ sel expand)
    (matchOracleSet_cascadeComplete hdiscSet hco hlock)
    (fun chain => orbitRecoverableAt_iff_cellsAreOrbits.mpr (hco chain))

/-! ### §C.7 — Honest completeness: fire at the deepened node, propagate via `mono`

`matchOracle_cascadeComplete` discharges `CascadeComplete` from two hypotheses quantified over
**every** node: `hdisc` (the single-rep footprint `indivWithRep chain.D r` is discrete) and `hco`
(`CellsAreOrbits chain.D`). For CFI **both are false at shallow nodes** — one rep does not discretize
until depth ≈ `tw(H)`, and cells stay strictly coarser than orbits until then (the Rook3×3 gap,
orbit-recovery §7.2). So the ∀-node form is *not* what the cascade class provides; it demands the
oracle fire exactly where it provably cannot construct `colourMatchPerm`.

This section restates completeness in the shape the descent realizes (the §C.0.1 support window made
operational), in two pieces:

* **Fire at the deepened node, `hco`-free.** `matchOracle` is *construct-and-check*, so a genuine
  `Aut_D` orbit pair `(v, w)` already makes `colourMatchPerm = g` (`colourMatchPerm_eq_of_orbit`) and
  the checks pass — the orbit witness is consumed *directly*. `hco` was only the cell→orbit bridge of
  `complete_of_cellComplete_recoverable`; feeding the orbit pair directly bypasses it. The only input
  left is discreteness, taken in the **indexed** `RecoverableByDepth` form (`individualizedColouring
  (insert · chain.D)` discretizes — what `recoverableByDepth_cfi`/`_scheme` supply) and bridged to the
  footprint by §C.4b. This is `matchOracle_fires_of_insertDiscrete`.
* **Propagate via `mono`.** A merge certified at the (deep) node holds at every **shallower** committed
  set `S ⊆ chain.D` with the same `chain.P`: the returned automorphism fixes `chain.D ⊇ S` pointwise,
  so `OrbitPartition.mono` reuses it as an `Aut_S` witness. This is `matchOracle_orbit_of_fire_mono` —
  the "fire deep, prune shallow" step, justifying an ancestor target-cell decision by a certification
  harvested after deepening.

What stays open is then the single honest obligation (1b), no longer two false ones: the descent must
**reach** such a deepened node while keeping `(v, w)` an orbit pair — i.e. extend `chain.D` into
`(supp g)ᶜ` up to discreteness. `exists_orbit_witness_of_aut` shows the room exists (the pair stays
available down to depth `n − |supp g|`); that the *canonical* descent lands there is the cascade-class
construction-correctness still owed, and is not `GI ∈ P`. -/

/-- **Honest per-node firing (`hco`-free).** At a node where individualizing the committed path plus
the query rep discretizes — the indexed `RecoverableByDepth` form (`recoverableByDepth_cfi`/`_scheme`),
bridged to the footprint by §C.4b — `matchOracle` fires on **any genuine `Aut_D` orbit pair** `(v, w)`
with `v, w ∉ chain.D`. The orbit witness `g` is consumed directly (`colourMatchPerm = g`), so no
`CellsAreOrbits` hypothesis is needed: this is the construct-and-check completeness the descent
actually invokes, at the depth the recursion reaches (not the unsatisfiable ∀-node `hdisc`/`hco`). -/
theorem matchOracle_fires_of_insertDiscrete {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) {v w : Fin n}
    (hvD : v ∉ chain.D) (hwD : w ∉ chain.D)
    (hinsv : Discrete (warmRefine adj chain.P (individualizedColouring n (insert v chain.D))))
    (hinsw : Discrete (warmRefine adj chain.P (individualizedColouring n (insert w chain.D))))
    (horb : OrbitPartition adj chain.P chain.D v w) :
    ∃ result, matchOracle adj P₀ χι₀ sel chain v w = some result := by
  have hv := discrete_indivWithRep_of_discrete_insert adj chain.P chain.D v hvD hinsv
  have hw := discrete_indivWithRep_of_discrete_insert adj chain.P chain.D w hwD hinsw
  obtain ⟨g, hg, hgP, hgD, hgvw⟩ := horb
  have hcmp : colourMatchPerm adj chain.P chain.D v w hv hw = g :=
    colourMatchPerm_eq_of_orbit hv hw hg hgP hgD hgvw hwD
  refine matchOracle_fires chain hv hw ?_ ?_ ?_ ?_
  · rw [hcmp]; exact hg
  · rw [hcmp]; exact hgP
  · rw [hcmp]; exact hgD
  · rw [hcmp]; exact hgvw

/-- **Propagate the certification via `mono`.** A merge `matchOracle` certifies at a node holds at
every **shallower** committed set `S ⊆ chain.D` (same `chain.P`): the returned automorphism fixes
`chain.D ⊇ S` pointwise, so it witnesses the `Aut_S` orbit pair too (`OrbitPartition.mono`). The
"fire deep, prune shallow" step — a decision at an ancestor target cell justified by a certification
harvested after deepening. Together with `matchOracle_fires_of_insertDiscrete` this is the honest
form of the localisation discharge: fire where the footprint discretizes, reuse upward by `mono`. -/
theorem matchOracle_orbit_of_fire_mono {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) {v w : Fin n}
    {S : Finset (Fin n)} (hS : S ⊆ chain.D)
    {result : { π : Equiv.Perm (Fin n) // IsAut π adj }}
    (hfire : matchOracle adj P₀ χι₀ sel chain v w = some result) :
    OrbitPartition adj chain.P S v w :=
  OrbitPartition.mono hS
    (matchOracle_orbitMapSpec adj P₀ χι₀ sel chain v w result hfire)

/-- **Exact orbit decider at the discretizing depth (`hco`-free).** Combining unconditional soundness
(`matchOracle_orbitMapSpec`) with `matchOracle_fires_of_insertDiscrete`: at a node where committing the
path plus the query rep discretizes (`hinsv`/`hinsw`), `matchOracle` fires on `(v, w)` **iff** they are
a genuine `Aut_{chain.D}` orbit pair. No `CellsAreOrbits`/localisation assumption — at the discretizing
depth the construct-and-check oracle *is* the path-fixing-orbit relation exactly.

**Read the limits precisely.** (1) This is an iff *only under the discreteness hypotheses* — i.e. at a
node one individualization from a leaf. The depth at which they become satisfiable is the cascade depth
(`tw(H)` for CFI); for the wall / IR-blind-spot it is *not* polynomial, and there this lemma simply does
not apply (its hypotheses are unmet — that unreachability, not non-firing, is the Cameron/flag signal).
(2) The relation decided is `Aut_{chain.D}` — the **path-fixing** stabilizer, not `Aut(adj)`. Non-firing
means no automorphism *fixing the committed path* swaps `v, w`; a global symmetry that *moves* the path
is not destroyed, only relocated to the stabilizer-chain transversal (§C.0.1), to be harvested
cross-branch. So non-firing is a genuine **local** decision at this node, not a verdict of global
rigidity. -/
theorem matchOracle_certifies_iff_orbit_of_insertDiscrete {n : Nat} {adj : AdjMatrix n}
    {P₀ : PMatrix n} {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) {v w : Fin n}
    (hvD : v ∉ chain.D) (hwD : w ∉ chain.D)
    (hinsv : Discrete (warmRefine adj chain.P (individualizedColouring n (insert v chain.D))))
    (hinsw : Discrete (warmRefine adj chain.P (individualizedColouring n (insert w chain.D)))) :
    (∃ result, matchOracle adj P₀ χι₀ sel chain v w = some result)
      ↔ OrbitPartition adj chain.P chain.D v w := by
  constructor
  · rintro ⟨result, h⟩
    exact matchOracle_orbitMapSpec adj P₀ χι₀ sel chain v w result h
  · exact matchOracle_fires_of_insertDiscrete chain hvD hwD hinsv hinsw

/-! ### §C.8 — Leg 1 (A1): the level-coloured exploration sequence and its depth-witness bridge

The multi-step depth witness `hdiscSet` (M-D, §C.6) is stated for `indivWithSet`, which colours the
explored set **uniformly** — too coarse to discretize shallowly (the probe: CFI(K4) indexed seeds
discretize at the empty commit, uniform-block seeds do not), and with **no** §C.4b-style bridge to the
*indexed* `RecoverableByDepth` framework (uniform marking of a ≥2 set is strictly coarser than indexing
it). Uniform was forced by transport, because the orbit automorphism *moves* the set.

Leg 1 replaces the uniform set with a **level-coloured sequence**: thread the explored vertices as an
ordered list `rs`, colouring the `i`-th by its **position** `n+1+i` (not its vertex index). Position
colours are globally distinct, so — exactly as for one rep in §C.4b — the sequence footprint has the
**same partition** as the *indexed* `individualizedColouring (S ∪ rs.toFinset)`, and discreteness
transfers (`discrete_indivWithSeq_of_discrete_union`). So `hdiscSeq ⟸ recoverableByDepth` — the depth
witness, in the indexed form already proved for CFI/schemes. (A2 — transport under `g`, which needs the
position colouring rather than the vertex index — is the level-wise lockstep, deferred.)

This is A1: the bridge half. It is unconditional (no `Nodup`/disjointness), because position-colours and
index-colours induce the same partition regardless. -/

/-- **Level-coloured exploration sequence.** The committed set `S` by index (`individualizedColouring`)
plus the `i`-th element of the list `rs` by its *position* colour `n+1+i` (via `rs.idxOf`). The position
colouring — not the vertex index — is what will transport under the orbit automorphism in A2 (an index
colouring breaks `χ₂ ∘ g = χ₁` on the moved set, exactly as the §C.4b note explains for a single rep). -/
def indivWithSeq (n : Nat) (S : Finset (Fin n)) (rs : List (Fin n)) : Colouring n :=
  fun v => if v ∈ rs then n + 1 + rs.idxOf v else individualizedColouring n S v

/-- `indivWithRep` (M-B) is the singleton-sequence case (`n+1+0 = n+1`). -/
theorem indivWithRep_eq_indivWithSeq_singleton {n : Nat} (S : Finset (Fin n)) (r : Fin n) :
    indivWithRep n S r = indivWithSeq n S [r] := by
  funext v
  simp only [indivWithRep, indivWithSeq, List.mem_singleton]
  by_cases h : v = r
  · subst h; simp [List.idxOf_cons_self]
  · simp [h]

/-- **Same partition: level-coloured sequence = indexed union.** `indivWithSeq n S rs` and the *indexed*
`individualizedColouring n (S ∪ rs.toFinset)` induce the same partition: each `rs`-vertex gets a globally
unique colour either way (positions are distinct via `List.idxOf_inj`, and `≥ n+1 >` every index/
background colour `≤ n`), and off `rs` the two colourings agree. The sequence generalization of
`samePartition_indivWithRep_insert`; unconditional. -/
theorem samePartition_indivWithSeq {n : Nat} (S : Finset (Fin n)) (rs : List (Fin n)) :
    samePartition (indivWithSeq n S rs) (individualizedColouring n (S ∪ rs.toFinset)) := by
  -- off `rs`, the two colourings are literally equal
  have hoff : ∀ v, v ∉ rs → indivWithSeq n S rs v = individualizedColouring n (S ∪ rs.toFinset) v := by
    intro v hv
    rw [indivWithSeq, if_neg hv]
    by_cases hvS : v ∈ S
    · rw [individualizedColouring, if_pos hvS, individualizedColouring,
          if_pos (Finset.mem_union_left _ hvS)]
    · rw [individualizedColouring, if_neg hvS, individualizedColouring,
          if_neg (by simp [Finset.mem_union, hvS, List.mem_toFinset, hv])]
  -- an `rs`-vertex's colour is globally unique under `indivWithSeq`
  have huSeq : ∀ v, v ∈ rs → ∀ w, w ≠ v →
      indivWithSeq n S rs w ≠ indivWithSeq n S rs v := by
    intro v hv w hwv
    have hvc : indivWithSeq n S rs v = n + 1 + rs.idxOf v := by simp only [indivWithSeq, if_pos hv]
    by_cases hw : w ∈ rs
    · have hwc : indivWithSeq n S rs w = n + 1 + rs.idxOf w := by simp only [indivWithSeq, if_pos hw]
      rw [hvc, hwc]
      intro h
      have : rs.idxOf w = rs.idxOf v := by omega
      exact hwv ((List.idxOf_inj hw).mp this)
    · have hwc : indivWithSeq n S rs w = individualizedColouring n S w := by
        simp only [indivWithSeq, if_neg hw]
      have hle : individualizedColouring n S w ≤ n := by
        rw [individualizedColouring]; split
        · exact w.is_lt
        · exact Nat.zero_le n
      rw [hvc, hwc]; omega
  -- an `rs`-vertex's colour is globally unique under the indexed union colouring
  have huIdx : ∀ v, v ∈ rs → ∀ w, w ≠ v →
      individualizedColouring n (S ∪ rs.toFinset) w
        ≠ individualizedColouring n (S ∪ rs.toFinset) v := by
    intro v hv w hwv
    have hvU : v ∈ S ∪ rs.toFinset := Finset.mem_union_right _ (List.mem_toFinset.mpr hv)
    have hvc : individualizedColouring n (S ∪ rs.toFinset) v = v.val + 1 := by
      rw [individualizedColouring, if_pos hvU]
    rw [hvc, individualizedColouring]
    split
    · intro h; exact hwv (Fin.ext (by omega))
    · omega
  intro i j
  by_cases hi : i ∈ rs
  · by_cases hj : j ∈ rs
    · have hic : indivWithSeq n S rs i = n + 1 + rs.idxOf i := by simp only [indivWithSeq, if_pos hi]
      have hjc : indivWithSeq n S rs j = n + 1 + rs.idxOf j := by simp only [indivWithSeq, if_pos hj]
      have hiU : individualizedColouring n (S ∪ rs.toFinset) i = i.val + 1 := by
        rw [individualizedColouring, if_pos (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))]
      have hjU : individualizedColouring n (S ∪ rs.toFinset) j = j.val + 1 := by
        rw [individualizedColouring, if_pos (Finset.mem_union_right _ (List.mem_toFinset.mpr hj))]
      rw [hic, hjc, hiU, hjU]
      constructor
      · intro h
        have hidx : rs.idxOf i = rs.idxOf j := by omega
        rw [(List.idxOf_inj hi).mp hidx]
      · intro h; rw [Fin.ext (show i.val = j.val by omega)]
    · have hji : j ≠ i := by rintro rfl; exact hj hi
      exact ⟨fun h => absurd h.symm (huSeq i hi j hji),
             fun h => absurd h.symm (huIdx i hi j hji)⟩
  · by_cases hj : j ∈ rs
    · have hij : i ≠ j := by rintro rfl; exact hi hj
      exact ⟨fun h => absurd h (huSeq j hj i hij),
             fun h => absurd h (huIdx j hj i hij)⟩
    · rw [hoff i hi, hoff j hj]

/-- **The Leg-1 depth-witness bridge (sequence).** Discreteness of the level-coloured sequence footprint
`indivWithSeq n S rs` *follows* from discreteness of the **indexed** `individualizedColouring n (S ∪
rs.toFinset)` — the `RecoverableByDepth` / discretizing-depth shape that `recoverableByDepth_cfi` /
`_scheme` populate. The sequence generalization of `discrete_indivWithRep_of_discrete_insert`: it
converts the multi-step depth witness from the unreducible *uniform* form into the indexed form already
proved on the cascade class. (Transport — A2 — is separate; this is the discreteness half.) -/
theorem discrete_indivWithSeq_of_discrete_union {n : Nat} (adj : AdjMatrix n) (P : PMatrix n)
    (S : Finset (Fin n)) (rs : List (Fin n))
    (hd : Discrete (warmRefine adj P (individualizedColouring n (S ∪ rs.toFinset)))) :
    Discrete (warmRefine adj P (indivWithSeq n S rs)) :=
  discrete_of_samePartition
    (warmRefine_samePartition adj P (samePartition_indivWithSeq S rs).symm) hd

/-! #### §C.8 — Leg 1 (A2a): transport for the level-coloured sequence, and the lifted harvest core

The discreteness half (A1, above) is order-blind. The **transport** half is what the position
colouring is *for*: an orbit automorphism `g` moves the explored set, and only a colour that tracks
*position* (not vertex index) survives the move. The position colouring transports because **`map`
preserves position under an injective function** — a pure list fact (`idxOf_map_of_injective`); off the
sequence it is the existing `individualizedColouring` invariance. Given transport, the M-C harvest
bricks lift verbatim (they are colouring-generic), so the level-coloured harvest *fires* at a footprint
that is **both** discretized (A1 ⟸ `recoverableByDepth`) **and** transport-correct. The remaining piece
(A2b) is the equivariant *ordering* of the exploration — the `LockstepExpand` analogue for sequences —
which needs the incremental recursive exploration, not a static sort. -/

/-- **Position is preserved by `map` under an injection.** `(l.map g).idxOf (g a) = l.idxOf a` for a
permutation `g`. The pure-list core of sequence transport: `g` sends the `i`-th element of `l` to the
`i`-th element of `l.map g`, so position colours match across the two branches. -/
theorem idxOf_map_of_injective {n : Nat} (g : Equiv.Perm (Fin n)) (a : Fin n) :
    ∀ l : List (Fin n), (l.map g).idxOf (g a) = l.idxOf a
  | [] => by simp
  | x :: xs => by
    rw [List.map_cons]
    by_cases hxa : x = a
    · subst hxa; rw [List.idxOf_cons_self, List.idxOf_cons_self]
    · have hgx : g x ≠ g a := fun h => hxa (g.injective h)
      rw [List.idxOf_cons_ne (xs.map g) hgx, List.idxOf_cons_ne xs hxa,
          idxOf_map_of_injective g a xs]

/-- **Sequence transport.** An orbit automorphism `g` fixing the committed set `S`, with branch-`w`'s
sequence `rs₂` the `g`-image of branch-`v`'s `rs₁` (`rs₂ = rs₁.map g`), carries the branch-`v` level
colouring onto the branch-`w` one (`χ₂ ∘ g = χ₁`). On the sequence it is `idxOf_map_of_injective`
(position preserved); off it, the `individualizedColouring` invariance (`g` fixes `S`, moves its
complement to its complement). The `indivWithSet_transport` analogue — now position-, not uniform-,
based, so it composes with the A1 discreteness bridge. -/
theorem indivWithSeq_transport {n : Nat} {S : Finset (Fin n)} {rs₁ rs₂ : List (Fin n)}
    {g : Equiv.Perm (Fin n)} (hgS : FixesPointwise g S) (hrs : rs₂ = rs₁.map g) (v : Fin n) :
    indivWithSeq n S rs₂ (g v) = indivWithSeq n S rs₁ v := by
  unfold indivWithSeq
  by_cases hv : v ∈ rs₁
  · have hgv : g v ∈ rs₂ := by rw [hrs]; exact List.mem_map_of_mem hv
    rw [if_pos hgv, if_pos hv, hrs, idxOf_map_of_injective g v rs₁]
  · have hgv : g v ∉ rs₂ := by
      rw [hrs, List.mem_map]
      rintro ⟨u, hu, hgu⟩
      exact hv ((g.injective hgu) ▸ hu)
    rw [if_neg hgv, if_neg hv]
    by_cases hvS : v ∈ S
    · rw [hgS v hvS]
    · have hgvS : g v ∉ S := hgS.complement hvS
      simp only [individualizedColouring, if_neg hgvS, if_neg hvS]

/-- **The sequence colour-match relation** (`IsColourMatch` / `IsColourMatchSet` analogue). -/
def IsColourMatchSeq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n))
    (rs₁ rs₂ : List (Fin n)) (t : Equiv.Perm (Fin n)) : Prop :=
  ∀ x, warmRefine adj P (indivWithSeq n S rs₂) (t x) = warmRefine adj P (indivWithSeq n S rs₁) x

/-- **Sequence completeness brick.** The orbit automorphism `g` (fixing `S`, `rs₂ = rs₁.map g`) *is* a
colour-match — `warmRefine_transport ∘ indivWithSeq_transport`. The `colourMatchSet_complete` analogue. -/
theorem colourMatchSeq_complete {n : Nat} {adj : AdjMatrix n} {P : PMatrix n} {S : Finset (Fin n)}
    {rs₁ rs₂ : List (Fin n)} {g : Equiv.Perm (Fin n)}
    (hg : IsAut g adj) (hgP : ∀ x u, P (g x) (g u) = P x u)
    (hgS : FixesPointwise g S) (hrs : rs₂ = rs₁.map g) :
    IsColourMatchSeq adj P S rs₁ rs₂ g :=
  fun x => warmRefine_transport hg hgP (indivWithSeq_transport hgS hrs) x

/-- **The sequence colour-match permutation.** The rank composition for level-coloured footprints;
`colourMatchPermSet` (M-C) with the uniform set replaced by the level-coloured sequence. -/
noncomputable def colourMatchPermSeq {n : Nat} (adj : AdjMatrix n) (P : PMatrix n) (S : Finset (Fin n))
    (rs₁ rs₂ : List (Fin n))
    (h₁ : Discrete (warmRefine adj P (indivWithSeq n S rs₁)))
    (h₂ : Discrete (warmRefine adj P (indivWithSeq n S rs₂))) : Equiv.Perm (Fin n) :=
  (Colouring.rankPerm (warmRefine adj P (indivWithSeq n S rs₂)) h₂)⁻¹ *
    Colouring.rankPerm (warmRefine adj P (indivWithSeq n S rs₁)) h₁

/-- **`colourMatchPermSeq` is the orbit automorphism, at a recoverable level-coloured footprint.** Same
shape as `colourMatchPermSet_eq_of_orbit` (`rankPerm_inv_mul_eq_of_match` ← `vertexRank_comp` +
`colourMatchSeq_complete`), now over a level-coloured sequence whose discreteness is A1-reducible. -/
theorem colourMatchPermSeq_eq_of_orbit {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {S : Finset (Fin n)} {rs₁ rs₂ : List (Fin n)} {g : Equiv.Perm (Fin n)}
    (h₁ : Discrete (warmRefine adj P (indivWithSeq n S rs₁)))
    (h₂ : Discrete (warmRefine adj P (indivWithSeq n S rs₂)))
    (hg : IsAut g adj) (hgP : ∀ x u, P (g x) (g u) = P x u)
    (hgS : FixesPointwise g S) (hrs : rs₂ = rs₁.map g) :
    colourMatchPermSeq adj P S rs₁ rs₂ h₁ h₂ = g :=
  rankPerm_inv_mul_eq_of_match h₁ h₂ (colourMatchSeq_complete hg hgP hgS hrs)

/-- **The level-coloured firing certificate exists.** Where `CellsAreOrbits` gives the orbit
automorphism `g` for a same-cell pair `(v, w)`, then for *any* exploration sequence `rs₁` the partner
`rs₂ = rs₁.map g` and `g` is a colour-match between them. The `colourMatchSet_exists_of_cellsAreOrbits`
analogue, now at a level-coloured (hence A1-reducible) footprint. The open piece (A2b) is that the
oracle's branch-`w` sequence *is* this `rs₁.map g` (the level-wise lockstep). -/
theorem colourMatchSeq_exists_of_cellsAreOrbits {n : Nat} {adj : AdjMatrix n} {P : PMatrix n}
    {S : Finset (Fin n)} {v w : Fin n} (rs₁ : List (Fin n))
    (hco : CellsAreOrbits adj P S)
    (hcell : warmRefine adj P (individualizedColouring n S) v
           = warmRefine adj P (individualizedColouring n S) w) :
    ∃ g : Equiv.Perm (Fin n), IsAut g adj ∧ (∀ x u, P (g x) (g u) = P x u)
      ∧ FixesPointwise g S ∧ g v = w ∧ IsColourMatchSeq adj P S rs₁ (rs₁.map g) g := by
  obtain ⟨g, hg, hgP, hgS, hgvw⟩ := hco v w hcell
  exact ⟨g, hg, hgP, hgS, hgvw, colourMatchSeq_complete hg hgP hgS rfl⟩

/-! #### §C.8 — Leg 1: the multi-step sequence oracle (`matchOracleSeq`)

`matchOracleSeq` is the level-coloured twin of the M-D `matchOracleSet`: same construct-and-check, but
it individualizes the *ordered sequence* `expand chain r` via `indivWithSeq` (rather than the uniform
`indivWithSet`). The payoff is that its depth witness `hdiscSeq` is **A1-reducible**
(`discrete_indivWithSeq_of_discrete_union` ⟸ `recoverableByDepth`), where `matchOracleSet`'s `hdiscSet`
was not. Soundness is unconditional; completeness reduces to `hdiscSeq` + `hco` + `LockstepExpandSeq`
(the *sequence* lockstep `expand chain (g v) = (expand chain v).map g`). The single remaining open piece
(A2b) is discharging `LockstepExpandSeq` for the canonical recursive exploration. -/

open Classical in
/-- **The multi-step sequence colour-match oracle.** Like `matchOracleSet` but individualizes the
ordered sequence `expand chain r` (per the selector) via `indivWithSeq`. Construct `colourMatchPermSeq`,
return it **iff** it verifies `IsAut ∧ P-preserving ∧ fixes D ∧ v ↦ w`. -/
noncomputable def matchOracleSeq {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n))
    (expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → List (Fin n)) :
    CascadeOracleSpec adj P₀ χι₀ sel :=
  fun {k} chain v w =>
    if hv : Discrete (warmRefine adj chain.P (indivWithSeq n chain.D (expand chain v))) then
      if hw : Discrete (warmRefine adj chain.P (indivWithSeq n chain.D (expand chain w))) then
        if hchk :
            IsAut (colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw) adj
            ∧ (∀ x u, chain.P (colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw x)
                              (colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw u)
                       = chain.P x u)
            ∧ FixesPointwise (colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw) chain.D
            ∧ colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw v = w then
          some ⟨colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw, hchk.1⟩
        else none
      else none
    else none

/-- Evaluation lemma: discreteness + the four checks on `colourMatchPermSeq` ⟹ `matchOracleSeq` fires. -/
theorem matchOracleSeq_fires {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → List (Fin n)}
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) {v w : Fin n}
    (hv : Discrete (warmRefine adj chain.P (indivWithSeq n chain.D (expand chain v))))
    (hw : Discrete (warmRefine adj chain.P (indivWithSeq n chain.D (expand chain w))))
    (hAut : IsAut (colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw) adj)
    (hP : ∀ x u, chain.P (colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw x)
                         (colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw u)
                  = chain.P x u)
    (hFix : FixesPointwise (colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw) chain.D)
    (hvw : colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw v = w) :
    ∃ result, matchOracleSeq adj P₀ χι₀ sel expand chain v w = some result := by
  have hchk :
      IsAut (colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw) adj
      ∧ (∀ x u, chain.P (colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw x)
                        (colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw u)
                 = chain.P x u)
      ∧ FixesPointwise (colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw) chain.D
      ∧ colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw v = w :=
    ⟨hAut, hP, hFix, hvw⟩
  refine ⟨⟨colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw, hAut⟩, ?_⟩
  simp only [matchOracleSeq]
  rw [dif_pos hv, dif_pos hw, dif_pos hchk]

/-- **M-D (sequence) soundness — `OrbitMapSpec`, unconditional.** As for `matchOracleSet`. -/
theorem matchOracleSeq_orbitMapSpec {n : Nat} (adj : AdjMatrix n) (P₀ : PMatrix n)
    (χι₀ : Colouring n) (sel : Colouring n → Finset (Fin n))
    (expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → List (Fin n)) :
    CascadeOracleSpec.OrbitMapSpec (matchOracleSeq adj P₀ χι₀ sel expand) := by
  intro _k chain v w _result heq
  simp only [matchOracleSeq] at heq
  split_ifs at heq with hv hw hchk
  exact ⟨colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw,
    hchk.1, hchk.2.1, hchk.2.2.1, hchk.2.2.2⟩

/-- **The sequence lockstep correspondence.** The `LockstepExpand` analogue for an ordered selector:
any `P`-preserving automorphism `g` fixing the committed path carries one branch's exploration
*sequence* onto the other's, **as an ordered list** — `expand chain (g v) = (expand chain v).map g`
(`map`, not `image`). This is strictly stronger than the set lockstep, and is the genuinely new content
(A2b): discharging it needs the canonical recursive exploration (per-level forced-node equivariance),
not a static sort. -/
def LockstepExpandSeq {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n} {χι₀ : Colouring n}
    {sel : Colouring n → Finset (Fin n)}
    (expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → List (Fin n)) : Prop :=
  ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (g : Equiv.Perm (Fin n)) (v : Fin n),
    IsAut g adj → (∀ x u, chain.P (g x) (g u) = chain.P x u) → FixesPointwise g chain.D →
    expand chain (g v) = (expand chain v).map g

/-- **M-D (sequence) completeness — `CellComplete`.** Reduced to the three hypotheses: sequence-footprint
discreteness `hdiscSeq` (now A1-reducible via `discrete_indivWithSeq_of_discrete_union`), `CellsAreOrbits`
(`hco`), and `LockstepExpandSeq` (`hlock`). At a same-cell pair the orbit automorphism `g` exists; the
lockstep supplies `rs₂ = rs₁.map g`, so `colourMatchPermSeq = g` and the oracle fires. -/
theorem matchOracleSeq_cellComplete {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → List (Fin n)}
    (hdiscSeq : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (r : Fin n),
       Discrete (warmRefine adj chain.P (indivWithSeq n chain.D (expand chain r))))
    (hco : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k),
       CellsAreOrbits adj chain.P chain.D)
    (hlock : LockstepExpandSeq expand) :
    CascadeOracleSpec.CellComplete (matchOracleSeq adj P₀ χι₀ sel expand) := by
  intro k chain v w hcell
  have hv := hdiscSeq chain v
  have hw := hdiscSeq chain w
  have hinit : individualizedColouring n chain.D v = individualizedColouring n chain.D w :=
    warmRefine_refines adj chain.P (individualizedColouring n chain.D) hcell
  by_cases hwD : w ∈ chain.D
  · have hvw : v = w := (individualizedColouring_eq_iff_of_mem chain.D hwD).mp hinit
    subst hvw
    have hid : colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain v) hv hw = 1 := by
      simp only [colourMatchPermSeq]
      exact inv_mul_cancel _
    refine matchOracleSeq_fires chain hv hw ?_ ?_ ?_ ?_
    · rw [hid]; exact fun _ _ => rfl
    · rw [hid]; exact fun _ _ => rfl
    · rw [hid]; exact fun _ _ => rfl
    · rw [hid]; rfl
  · obtain ⟨g, hg, hgP, hgD, hgvw⟩ := hco chain v w hcell
    have hR : expand chain w = (expand chain v).map g := by
      have h := hlock chain g v hg hgP hgD
      rwa [hgvw] at h
    have hcmps : colourMatchPermSeq adj chain.P chain.D (expand chain v) (expand chain w) hv hw = g :=
      colourMatchPermSeq_eq_of_orbit hv hw hg hgP hgD hR
    refine matchOracleSeq_fires chain hv hw ?_ ?_ ?_ ?_
    · rw [hcmps]; exact hg
    · rw [hcmps]; exact hgP
    · rw [hcmps]; exact hgD
    · rw [hcmps]; exact hgvw

/-- **M-D (sequence) capstone — `CascadeComplete`.** The sequence oracle computes the orbit relation
exactly, reduced to `hdiscSeq` (A1-reducible) + `hco` + `LockstepExpandSeq`. -/
theorem matchOracleSeq_cascadeComplete {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → List (Fin n)}
    (hdiscSeq : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (r : Fin n),
       Discrete (warmRefine adj chain.P (indivWithSeq n chain.D (expand chain r))))
    (hco : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k),
       CellsAreOrbits adj chain.P chain.D)
    (hlock : LockstepExpandSeq expand) :
    CascadeOracleSpec.CascadeComplete (matchOracleSeq adj P₀ χι₀ sel expand) :=
  CascadeOracleSpec.cascadeComplete_of_cellsAreOrbits
    (matchOracleSeq_cellComplete hdiscSeq hco hlock) hco

/-- **M-D (sequence) — flag iso-invariance, free** (via `verdictIsoInvariant_of_complete`). -/
theorem matchOracleSeq_verdictIsoInvariant {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → List (Fin n)}
    (hdiscSeq : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (r : Fin n),
       Discrete (warmRefine adj chain.P (indivWithSeq n chain.D (expand chain r))))
    (hco : ∀ {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k),
       CellsAreOrbits adj chain.P chain.D)
    (hlock : LockstepExpandSeq expand) :
    CascadeOracleSpec.VerdictIsoInvariant (matchOracleSeq adj P₀ χι₀ sel expand) :=
  CascadeOracleSpec.verdictIsoInvariant_of_complete
    (matchOracleSeq_orbitMapSpec adj P₀ χι₀ sel expand)
    (matchOracleSeq_cascadeComplete hdiscSeq hco hlock)
    (fun chain => orbitRecoverableAt_iff_cellsAreOrbits.mpr (hco chain))

/-! #### §C.8 — Leg 1: the discretizing-oracle limit (conservation of obstruction)

`matchOracleSeq` trades `matchOracleSet`'s unreducible uniform depth witness for an A1-reducible one,
but the obstruction is **conserved, not removed** — it relocates from `hdiscSet` (false) to
`LockstepExpandSeq` (also false in the regime it is needed). The theorem below makes this precise: the
two completeness hypotheses of `matchOracleSeq` are **jointly satisfiable only in the single-rep
regime**.

The argument (no `Classical`, no new axioms): take any path-fixing `P`-preserving automorphism `g` that
*fixes* `v` (`g ∈ stab_{Aut_D}(v)`). The lockstep at `g` reads `expand chain v = (expand chain v).map g`,
forcing `g` to fix every explored vertex pointwise; the level-footprint discreteness (via the A1
`samePartition` bridge to the indexed footprint) then forces `g = 1` by Fact B
(`aut_trivial_of_discrete_warmRefine`). So `stab_{Aut_D}(v)` is trivial — i.e. **one rep already kills
the residual**. For genuine multi-step CFI (`tw ≥ 2`, nontrivial residual after one rep) the two
hypotheses are therefore *incompatible*: the multi-step moved orbit **cannot** be harvested within-cell
by the discretizing colour-match, and belongs to the cross-branch (stabilizer-chain / Schreier–Sims)
harvest. This bounds the discretizing oracle's reach to exactly the single-rep / `stab(v)=1` case
(`matchOracle`, §C.7); it is the conserved core behind all three colourings (uniform / indexed /
position) being stuck. -/

/-- A list equal to its own image under `g` is fixed pointwise by `g`. -/
theorem fixedPointwise_of_map_self {n : Nat} {g : Equiv.Perm (Fin n)} :
    ∀ (l : List (Fin n)), l.map g = l → ∀ x ∈ l, g x = x
  | [], _, x, hx => by simp at hx
  | y :: ys, h, x, hx => by
    rw [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact h.1
    · exact fixedPointwise_of_map_self ys h.2 x hmem

/-- **The discretizing-oracle limit.** If the sequence lockstep holds and rep `v`'s level-coloured
footprint discretizes, then every path-fixing `P`-preserving automorphism fixing `v` is the identity:
`stab_{Aut_{chain.D}}(v)` is trivial. Hence `LockstepExpandSeq` and `hdiscSeq` hold *together* only
where one rep already kills the residual — for genuine multi-step they are incompatible, and the moved
orbit must be harvested cross-branch (Schreier–Sims / Part A), not by the within-cell discretizing
colour-match. The honest boundary of Leg 1 (conservation of obstruction). -/
theorem lockstep_disc_imp_stab_trivial {n : Nat} {adj : AdjMatrix n} {P₀ : PMatrix n}
    {χι₀ : Colouring n} {sel : Colouring n → Finset (Fin n)}
    {expand : ∀ {k : Nat}, SpineChain adj P₀ χι₀ sel k → Fin n → List (Fin n)}
    (hlock : LockstepExpandSeq expand)
    {k : Nat} (chain : SpineChain adj P₀ χι₀ sel k) (v : Fin n)
    (hdisc : Discrete (warmRefine adj chain.P (indivWithSeq n chain.D (expand chain v))))
    {g : Equiv.Perm (Fin n)} (hg : IsAut g adj)
    (hgP : ∀ x u, chain.P (g x) (g u) = chain.P x u)
    (hgD : FixesPointwise g chain.D) (hgv : g v = v) :
    g = Equiv.refl (Fin n) := by
  -- 1. lockstep at `g` (which fixes `v`): `expand chain v` is fixed setwise/ordered by `g`
  have hmap : (expand chain v).map g = expand chain v := by
    have h := hlock chain g v hg hgP hgD
    rw [hgv] at h
    exact h.symm
  -- 2-3. `g` fixes `chain.D ∪ (expand chain v)` pointwise
  have hfixS : FixesPointwise g (chain.D ∪ (expand chain v).toFinset) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxD | hxR
    · exact hgD x hxD
    · exact fixedPointwise_of_map_self (expand chain v) hmap x (List.mem_toFinset.mp hxR)
  -- 4. discreteness of the indexed union footprint (A1 `samePartition` bridge)
  have hdiscU : Discrete (warmRefine adj chain.P
      (individualizedColouring n (chain.D ∪ (expand chain v).toFinset))) :=
    discrete_of_samePartition
      (warmRefine_samePartition adj chain.P (samePartition_indivWithSeq chain.D (expand chain v)))
      hdisc
  -- 5. Fact B: a discrete footprint trivializes the path-fixing residual
  exact aut_trivial_of_discrete_warmRefine hdiscU hg hgP hfixS

end ChainDescent
