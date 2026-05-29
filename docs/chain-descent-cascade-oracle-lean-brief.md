# Chain descent — a-priori cascade oracle Lean brief (temporary)

> **Temporary doc — archive after the discharge.** Grounds the Lean
> discharge of the a-priori cascade oracle (the C# side is built + measured,
> [cascade-oracle.md §8.1](./chain-descent-cascade-oracle.md)) in the actual
> `GraphCanonizationProofs` source, with a milestone order tagged by
> proof-defensibility. Parallels the C# build brief
> ([chain-descent-cascade-oracle-build-brief.md](./chain-descent-cascade-oracle-build-brief.md)).

**Purpose.** Supply the Lean *contract* for the cascade oracle and discharge
it on the subclasses where orbit recovery is already proved. Per the standing
decision (user, 2026-05-28): *the proof program is the priority.* The headline
that shapes this brief:

> The two load-bearing pieces **already exist and are axiom-free** — the
> soundness target (`OrbitPartition`) and the completeness engine
> (`theorem_1_HOR_at_depth` + its CFI/scheme specialisations). So the discharge
> is mostly **interface + wiring**, not new deep proof. The old §8.2 estimate
> (~1700–2200 lines) is revised sharply down (~400–700).

Like the linear oracle, the Lean spec is **declarative, not a port** of the C#
algorithm: `LinearOracleSpec` records *"the discovery algorithm lives in C#; the
Lean side supplies the interface and the spec."* The C# lockstep recursion is the
constructive witness; Lean states the existential.

---

## 1. What the Lean already gives us

All in `namespace ChainDescent` ([ChainDescent.lean](../GraphCanonizationProofs/ChainDescent.lean)):

- **`OrbitPartition adj P S v w`** (3471) — `∃ π, IsAut π adj ∧ (π preserves P) ∧
  FixesPointwise π S ∧ π v = w`. A verified path-fixing automorphism carrying
  `r₁ ↦ rⱼ` **is** an `OrbitPartition` witness. Equivalence relation (`refl`/`symm`/
  `trans`), with the trivial direction `subset_warmRefine` (orbits ⊆ 1-WL cells).
- **`theorem_1_HOR_at_depth`** (3732) — if `CascadesAt adj P k`, then `∃ S`,
  `|S| ≤ k`, `warmRefine` discrete, and `∀ v w, OrbitPartition adj P S v w ↔
  cells-coincide`. The `↔` *is* completeness (cells = orbits). Axiom-free.
  - **`theorem_1_HOR_cfi_oddDeg`** (CFI.lean) — same shape, depth ≤ `cfi_depth_bound`,
    conditional only on `OddDegree`. Axiom-free.
  - **`theorem_2_HOR_concrete_rank_two_J_singleton`** (Scheme.lean) — depth 1,
    conditional on rank=2 ∧ |J|=1 ∧ a `hP_invariant` hypothesis. Axiom-free.
    (Use this, **not** the abstract `theorem_2_HOR`, which is axiomatic.)
- **`orbit_iff_eq_of_discrete_warmRefine`** (3638) — at discrete depth,
  `OrbitPartition adj P S v w ↔ v = w`. Fact B.
- **Interface precedent** — `LinearOracleSpec` (3242), `some_isAut` (3265),
  `LeafTwistSpec` (3279) in §15.8. The shape to parallel.
- **Substrate** — `SpineChain` (2275; fields `D`, `P`, `χι`), `IsAut` (2871),
  `FixesPointwise` (3340), `individualizedColouring` (3334),
  `warmRefine_invariant_of_isAut` (3446).

---

## 2. Proof-defensibility map (the spine)

| Property | Bucket | Basis |
|---|---|---|
| **Soundness** — a returned merge is a real `Aut_D` orbit map (`OrbitPartition`) | **PROOF-BACKED** | The validity predicate `OrbitMapSpec`; mirrors `LeafTwistSpec`. Class-blind, unconditional. |
| **Merges respect cells** — merged `v,w` share a 1-WL cell | **PROOF-BACKED** | `OrbitPartition.subset_warmRefine`. |
| **Completeness on OddDegree CFI** — cells = orbits ⇒ one rep per orbit covers | **PROOF TARGET** | `theorem_1_HOR_cfi_oddDeg` (axiom-free) + a localisation bridge. |
| **Completeness on rank-≤2 schemes** | **PROOF TARGET** | `theorem_2_HOR_concrete_rank_two_J_singleton` (axiom-free) + bridge. |
| **Completeness on the general cascade class** | **CONJECTURAL** | Tier-3 open content. |
| **Verdict iso-invariance** — output labelling-independent (lockstep cell-id seq) | **UNDISCHARGED** | strategy §15 gap 2; shared with the linear oracle. |

**Headline:** soundness is unconditional and class-blind; completeness is
*already defensible* on exactly the subclasses where orbit recovery is proved,
because those theorems exist and are axiom-free.

---

## 3. Phase A — interface + soundness/validity  [PROOF-BACKED] — **BUILT**

File `ChainDescent/CascadeOracle.lean`, §C. Builds clean, axiom-clean (only
`refineStep`/`refineStep_iff` + Lean foundationals). Deliverables:

1. **`CascadeOracleSpec`** — interface `Type`, parallel to `LinearOracleSpec` but
   **not leaf-gated** (the cascade oracle harvests at internal target cells):
   given a chain at level `k` (the committed path `D = chain.D`) and two candidate
   reps `v w`, return `Option { π // IsAut π adj }`.
2. **`CascadeOracleSpec.some_isAut`** — subtype-level soundness (automatic).
3. **`CascadeOracleSpec.OrbitMapSpec`** (validity, the `LeafTwistSpec` analogue):
   `oracle chain v w = some result → OrbitPartition adj chain.P chain.D v w`. This
   is the soundness anchor that justifies pruning.
4. **`merged_sameCell`** — corollary via `subset_warmRefine`: a certified merge
   forces `v,w` into the same `warmRefine adj chain.P (individualizedColouring n
   chain.D)` cell. (Internal consistency; never merge across cells.)

Phase A is self-contained (core `ChainDescent` only) and compiles independently of
CFI/Scheme.

---

## 4. Phase B — completeness on the proven subclasses  [PROOF TARGET] — **BUILT**

Imports `ChainDescent.CFI` and `ChainDescent.Scheme`. **A design refinement found
while building** (recorded so the plan stays honest): `theorem_1_HOR_at_depth`
characterises orbits at the *discretizing* depth `S` (where, being discrete, orbits
collapse to `v = w`); the oracle acts at *intermediate* nodes `D ⊊ S`, where cells
are coarser than orbits. So "a complete oracle exists" is either vacuous (decide
`OrbitPartition` directly — exponential) or needs the localisation `D = S`. Phase B
therefore proves the *realizability reduction*, not a blanket existence claim.
Delivered (all axiom-clean — only `refineStep`/`refineStep_iff` + Lean foundationals):

1. **`CascadeComplete`** — the oracle certifies every `OrbitPartition` pair at a node.
2. **`certifies_iff_orbit`** — `OrbitMapSpec` + `CascadeComplete` ⟹ the oracle returns
   `some` **iff** `OrbitPartition` (computes the orbit relation exactly).
3. **`OrbitRecoverableAt`** + **`orbitRecoverable_of_cascade`** / **`_cfi`** / **`_scheme`**
   — the orbit-recovery squeeze in oracle vocabulary, wired to `theorem_1_HOR_at_depth`
   / `theorem_1_HOR_cfi_oddDeg` / `theorem_2_HOR_concrete_rank_two_J_singleton`.
   (Scheme instance confirmed *not* to pull `schurian_scheme_profile_exists`.)
4. **`complete_of_cellComplete_recoverable`** (the payoff) — at an orbit-recoverable
   node, *cell*-completeness (refinement-decidable, polynomial) ⟹ orbit-completeness.
   So on the cascade class the hard "certify every orbit map" reduces to the easy
   "certify every same-cell pair".

**Residual (→ Phase C / open):** the **localisation** — that an intermediate node's
`chain.D` is itself a recoverable cascade-depth set — and the `chain.χι` ↔
`individualizedColouring n chain.D` partition correspondence. These are the genuine
remaining connecting work; Phase B isolates them precisely rather than closing them.

---

## 5. Phase C — explicitly open  [stated, not proven] (~50 lines)

Named `Prop`s with no `sorry`, recorded as the residual obligations:
- **General-class completeness** (Tier-3 conjecture).
- **Verdict iso-invariance** (§15 gap 2) — the lockstep cell-id sequence's
  labelling-independence; multi-level version of the linear oracle's obligation.

---

## 6. Modeling decisions / risks to settle (the real content)

1. **P-invariance seam (settle first — gates Phase A's validity).** `OrbitPartition`
   requires `π` to preserve `P`; the C# `IsAutomorphism` only checks `adj`. The scheme
   theorem already takes `hP_invariant : ∀ π, IsAut π adj → π preserves P` as a
   hypothesis — so this is a *known seam*. Options: (a) carry `hP_invariant` on the
   spec, discharged because the descent builds `P` only from path individualisations,
   which a path-fixing automorphism preserves; (b) prove the bridge lemma
   "path-fixing `adj`-auto ⇒ preserves the individualisation `P`". Decide before
   writing `OrbitMapSpec`.
2. **Per-node vs global discreteness.** `theorem_1_HOR_at_depth` is about *global*
   discreteness at `S`; the oracle acts per-node on one cell, deepening just enough.
   Phase B needs a localisation: either state completeness globally (the oracle's
   merges across the descent realise the depth-`k` discretisation) or per-cell with a
   bridge lemma. This is the main Phase-B design choice.
3. **Interface shape — internal node, not leaf.** `LinearOracleSpec` is `IsLeaf`-gated;
   the cascade oracle is internal-node + target-cell. The `(chain, v, w)` pairwise form
   (Phase A) captures this without a cell argument (the cell is implicit: `v,w` share a
   cell by `subset_warmRefine`).
4. **Existential, not constructive.** Follow the `LinearOracleSpec` precedent — the
   discovery algorithm (lockstep recursion) is out of scope; Lean states the
   existential, the C# is the constructive witness. This revises the old §8.2
   "constructive discharge of ∃S" wording.

---

## 7. File placement + build order

- `ChainDescent/CascadeOracle.lean` — Phase A (`import ChainDescent`), then Phase B
  appended (add `import ChainDescent.CFI`, `import ChainDescent.Scheme`), Phase C `Prop`s.
- Add `ChainDescent.CascadeOracle` to `lakefile.toml` `defaultTargets` and a `[[lean_lib]]`.
- Build order: **Phase A first** (cleanest, class-blind, mirrors §15.8) → **Phase B**
  (wiring the axiom-free theorems; settle risk #2) → **Phase C** (honest scoping).
  Settle risk #1 (P-invariance) before Phase A's `OrbitMapSpec`.

---

## 8. Done criteria

- Phase A compiles, no `sorry`/axioms; `CascadeOracleSpec` + `some_isAut` +
  `OrbitMapSpec` + `merged_sameCell` mirror §15.8 and connect to `OrbitPartition`.
- Phase B: a complete-and-valid cascade oracle proven to exist on OddDegree CFI and
  rank-≤2 schemes, wired to the axiom-free orbit-recovery theorems.
- Phase C: general completeness and verdict iso-invariance stated as named open
  obligations, no `sorry`.
- Then fold the Lean status back into [cascade-oracle.md §8.2](./chain-descent-cascade-oracle.md)
  and archive this brief.

---

## 9. Cross-references

- [`chain-descent-cascade-oracle.md`](./chain-descent-cascade-oracle.md) §2.5
  (no Lean spec yet), §8.2 (the skeleton this brief replaces).
- [`chain-descent-cascade-oracle-build-brief.md`](./chain-descent-cascade-oracle-build-brief.md) —
  the C# brief this parallels; §1 proof-defensibility map.
- [`ChainDescent.lean`](../GraphCanonizationProofs/ChainDescent.lean) §15.8
  (`LinearOracleSpec`/`LeafTwistSpec`), `OrbitPartition`, `theorem_1_HOR_at_depth`.
- [CFI.lean](../GraphCanonizationProofs/ChainDescent/CFI.lean)
  (`theorem_1_HOR_cfi_oddDeg`), [Scheme.lean](../GraphCanonizationProofs/ChainDescent/Scheme.lean)
  (`theorem_2_HOR_concrete_rank_two_J_singleton`).
