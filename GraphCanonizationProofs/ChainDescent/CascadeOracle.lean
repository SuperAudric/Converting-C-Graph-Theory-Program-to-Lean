import ChainDescent
import ChainDescent.CFI
import ChainDescent.Scheme

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

1. **Localisation** — that the descent's nodes are orbit-recoverable at the depth
   the recursion reaches, and the oracle is cell-complete (refinement certifies every
   same-cell pair). `cascadeComplete_of_localization` proves these two *suffice* for
   `CascadeComplete`. **Sharpened (this phase):** `orbitRecoverableAt_iff_cellsAreOrbits`
   shows the node-recoverability hypothesis is equivalent to its non-trivial half
   `CellsAreOrbits` — the trivial half (orbits refine cells) is unconditional, so the
   open obligation is *exactly* "1-WL cells are no coarser than orbits" at the node.
   That single implication is *false at generic intermediate nodes* (cells coarser
   than orbits, where genuine decisions live) and true at cascade/discretizing depth;
   `cascadeComplete_of_cellsAreOrbits` restates the capstone over it. Discharging it
   on the cascade class is the remaining open content (the construction-correctness
   the C# confirms through CFI(K7), plus the
   `chain.χι ↔ individualizedColouring n chain.D` partition correspondence).

2. **General-class completeness** — that the cascade class is *all* graphs. This is
   `GI ∈ P`; the project's honest position is that it is **not** expected to hold in
   general (the non-abelian wall / hidden Johnson), so it is recorded as a conjecture,
   not a target. The proved instances are CFI(OddDegree) and rank-≤2 schemes
   (`orbitRecoverable_cfi` / `_scheme`).

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

end ChainDescent
