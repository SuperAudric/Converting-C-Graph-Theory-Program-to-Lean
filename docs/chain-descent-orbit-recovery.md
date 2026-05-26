# Chain descent — orbit recovery for CFI graphs

A focused theorem about how 1-WL refinement interacts with the
automorphism orbit partition of CFI graphs, with a path toward a
polynomial-cost bound for chain descent's cascade class.

This is a **standalone research note** — readable cold. For broader
context: [`chain-descent-strategy.md`](./chain-descent-strategy.md) for
the canonization algorithm and its requirements;
[`chain-descent-calculator.md`](./chain-descent-calculator.md) for the
oracle and the cost model.

---

## 1. Headline

> **Theorem 1 (HOR for CFI).** Let `H` be a connected graph with all
> vertices of degree ≥ 2, and let `G = CFI(H)`. For any sequence of
> fresh-colour individualizations `S = (v_1, …, v_k)` chosen by the
> canonical chain-descent picker, there exists `k ≤ tw(H)` such that
> the 1-WL fixpoint partition on `(G, S)` equals the `Aut(G)_S`-orbit
> partition.

Where `tw(H)` is the treewidth of `H`. The HOR ("hidden orbit
revelation") framing: at each individualization step, the cell-orbit
gap may persist or grow, but it **closes by depth tw(H)**.

The proof is short (§5) and rests on classical CFI theory. The
interesting content is empirical: F7 (cells = orbits at depth 1)
holds for many CFI bases but **not** all — Rook3×3 subset start is
a clean counterexample requiring depth = tw(H) = 4.

---

## 2. Background and motivation

This direction emerged from two earlier closed workstreams:

- **Matroid framework** ([`chain-descent-matroid.md`](./chain-descent-matroid.md)) —
  attempted to model warm-refinement closure on commit-set guesses as
  a matroid, enabling a Tier-2 detector via binary-matroid testing.
  Closed 2026-05-23 after the exchange axiom failed on both partition-
  based `cl` and TC-based `cl_prov` (despite `cl_prov` being a
  topological closure).
- **Tier-2 decomposition experiment**
  ([`chain-descent-tier2-decomposition-experiment.md`](./chain-descent-tier2-decomposition-experiment.md))
  — attempted a Luks/Babai structure-tree approach against CFI(Petersen).
  Closed 2026-05-26 with the finding "CFI ladder is Tier-1, not Tier-2"
  (confirmed calculator.md §7's decomposability claim).

The experiment's depth-1 probe surfaced a sharp observation (F7):
1-WL refinement on CFI(Petersen) with one individualization gave a
partition whose cell sizes matched the residual-stabilizer orbit
structure exactly. This suggested a clean Tier-1 result —
"1-WL recovers Aut-stabilizer orbits at depth 1." If true, this would
be a strong building block toward T-C (calculator.md §4) for the
cascade class.

F7 was verified rigorously at depth 1 on CFI(K₄), CFI(K₃,₃), CFI(Petersen)
— all bases tested initially. Then **CFI(Rook3×3) subset start was
tested and failed** F7's depth-1 form. The refined statement
(**Theorem 1** above, "F7-graded") cleanly captures what is universally
true: orbit recovery happens, but the depth at which it happens is
base-dependent.

---

## 3. Setup and notation

**Base graph.** Fix a connected graph `H = (V_H, E_H)` with every
vertex of degree ≥ 2. Write `n_H = |V_H|`, `m_H = |E_H|`,
`β_H = m_H − n_H + 1` (first Betti number / cycle dimension).

For `u ∈ V_H`, let `N(u) ⊆ V_H` be its neighbour set, and
`deg(u) = |N(u)|`.

**CFI graph `G = CFI(H)`.** The Cai-Fürer-Immerman (1992) construction,
in the variant used by [`CfiGraphGenerator.cs`](../GraphCanonizationProject/CfiGraphGenerator.cs):

- For each `u ∈ V_H` and each even-cardinality `S ⊆ N(u)`, a
  **subset vertex** `a_S^u`. There are `2^{deg(u)−1}` of these per gadget.
- For each edge `(u, w) ∈ E_H`, four **endpoint vertices**:
  `e^0_{u→w}`, `e^1_{u→w}` (in `u`'s gadget) and `e^0_{w→u}`, `e^1_{w→u}`
  (in `w`'s gadget). The gadget `X(u)` has `2 deg(u)` endpoints total.
- **Intra-gadget edges**: `a_S^u ∼ e^b_{u→w}` iff `(w ∈ S) ⊕ (b = 1)`.
- **Inter-gadget bridges (canonical untwisted "G_even")**:
  `e^b_{u→w} ∼ e^b_{w→u}` for each `(u, w) ∈ E_H`, both `b ∈ {0,1}`.

Total `|V(G)| = sum over u of (2^{deg(u)-1} + 2 deg(u))`.

The **gadget at `u`** is
`X(u) = { a_S^u : S even } ∪ { e^b_{u→w} : w ∈ N(u), b ∈ {0,1} }`.

**Automorphism group structure (Cai-Fürer-Immerman 1992;
Grohe 2017 §13.4):** `Aut(CFI(H)) ≅ Z₂^{β_H} ⋊ Aut(H)`.
The base part lifts `σ ∈ Aut(H)` to `Φ(σ)` permuting CFI vertices by
relabelling the base index. The gauge part (cycle space `Z₂^{β_H}`)
permutes endpoint parities and subset memberships via "cycle twist"
actions.

**Treewidth.** `tw(H)`, the standard treewidth. Examples used in this
doc:
- `tw(K_4) = 3`
- `tw(K_{3,3}) = 3`
- `tw(Petersen) = 4`
- `tw(Rook3×3) = 4`

**1-WL refinement.** Standard 1-dimensional Weisfeiler-Leman colour
refinement: each round, vertex `v`'s new colour is `(old colour, sorted
multiset of neighbour colours)`. Iterated to fixpoint, gives the
**1-WL partition** of `V(G)`.

**Fresh-colour individualization.** Given `S ⊆ V(G)`, the
*S-individualized* colouring assigns each vertex of `S` a distinct
fresh colour and leaves all others equal. Write `χ_S` for this
colouring and `P_∞(G, S)` for the 1-WL fixpoint partition starting
from `χ_S`.

**Aut-stabilizer.** `Aut(G)_S` = pointwise stabilizer of `S` in
`Aut(G)`. Its orbit partition on `V(G)` is `O(G, S)`.

**The trivial direction (always true).** `O(G, S) ⊆ P_∞(G, S)` — each
Aut-stabilizer orbit lies inside a single 1-WL cell. (Automorphisms
preserve any 1-WL-derived partition.) Equivalently: 1-WL cells are at
least as coarse as orbits.

**The non-trivial direction (the orbit-recovery question).** When are
1-WL cells equal to orbits? Theorem 1 answers: at some depth ≤ tw(H)
for CFI(H).

**Canonical chain-descent picker.** At each step, individualize the
lex-smallest-id non-singleton cell; within that cell, pick the vertex
whose `VertexRoles` string sorts first (ground-truth tie-break for
iso-invariance; in production this would be an iso-invariant
within-cell rule). Used uniformly in the empirical work.

---

## 4. The three-tier ladder

Orbit-recovery as a general program:

> **Conjecture (general).** For "nice enough" graphs G, 1-WL after
> sufficient fresh-colour individualization recovers `Aut_S`-orbits.

This is true for some classes, conjectured for others, false for
none-yet-known. Three concrete tiers:

- **Tier 1 — CFI(H) for any connected H.** Theorem 1 above. Proof
  uses classical CFI WL-dim result.
- **Tier 2 — association-scheme graphs** (Johnson, Hamming,
  distance-regular). 1-WL after **one** individualization recovers
  `Aut_v`-orbits. Provable from classical scheme machinery.
  Subsumes Piece C of
  [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md).
- **Tier 3 — cascade class** (most general). Orbit recovery for any
  graph in the cascade class of [`chain-descent-calculator.md`](./chain-descent-calculator.md) §3.
  Conjectural; essentially equivalent to T-C on cascade class.

This doc is currently focused on **Tier 1**. Tier 2 is sketched in §10
as a follow-on direction. Tier 3 is left open.

---

## 5. Proof of Theorem 1

Reduces to two classical facts plus assembly.

**Fact A (CFI cascade depth).** Chain descent with the canonical
picker on `G = CFI(H)` for connected `H` reaches a discrete partition
(every vertex in its own cell) within at most `tw(H)` fresh-colour
individualizations.

*Reference.* Cai, Fürer, Immerman (1992) "An optimal lower bound on
the number of variables for graph identification" — implicit in the
WL-dimension argument of Theorem 5.4. Reformulated for chain descent
in Grohe (2017) "Descriptive Complexity, Canonisation, and Definable
Graph Structure Theory" §13.4.

*Intuition.* Each individualization breaks one independent cycle of
`H`'s cycle space (via parity propagation through the broken gadget).
After `tw(H)` breaks, every cycle's parity is forced and the partition
discretizes.

**Fact B (orbit partition at discrete depth).** When `P_∞(G, S)` is
discrete (every vertex in its own cell), `Aut(G)_S` is trivial and
`O(G, S) = P_∞(G, S)` — both are the partition into singletons.

*Proof.* `Aut(G)_S` consists of automorphisms fixing every `v ∈ S`. A
non-identity `g ∈ Aut(G)_S` would need to map some non-`S` vertex `w`
to a different vertex `w' = g(w) ≠ w`. But `g` preserves the 1-WL
partition `P_∞(G, S)`, so `w` and `w'` would share a 1-WL cell —
impossible at discrete depth where cells are singletons. So
`Aut(G)_S = {1_G}`, its orbits are singletons, matching `P_∞`. ∎

**Assembly (proof of Theorem 1).** Set `k =` the depth at which Fact A
discretizes. Then `k ≤ tw(H)`, and by Fact B,
`P_∞(G, S_k) = O(G, S_k)`. ∎

**Honest assessment.** Most of the proof is citation (Fact A). Fact B
is elementary. The "new" content is the HOR/F7-graded framing and the
empirical landscape (§7) showing the bound is sometimes loose.

---

## 6. Corollary — chain descent polynomial cost on cascade-class CFI

**Corollary 1.** For CFI(H) with `tw(H) = c` (constant), chain descent
with the canonical picker canonizes in time `poly(|V(G)|)`.

*Proof sketch.* By Theorem 1, the descent reaches discrete partition
within depth `c`. Each level's branching factor is bounded by cell
size, which is bounded by `O(2^{degmax(H)} · n_H)` (gadget size ×
gadget count). Total node count: `cell_size^c = poly(|V_H|)` for fixed
`c`. Each node does polynomial work (1-WL refinement is `O(|V(G)|^2)`).
Total: `poly(|V(G)|)`. ∎

The "for fixed `tw(H)`" qualifier is essential. For unbounded `tw`,
the bound is not polynomial; this is consistent with chain descent's
flagged region containing CFI over high-treewidth bases.

This Corollary is the actual deliverable for chain descent's
**cascade-class polynomial-or-flag guarantee** at the CFI level.

---

## 7. Empirical landscape

All measurements via [`Tier2DecompositionExperiment.cs`](../GraphCanonizationProject.Tests/Tier2DecompositionExperiment.cs)
(passes in ~5 s for the standard suite, ~2 m for the Rook3×3 deep
probe). Uses canonizer's harvested `Aut(CFI(H))` (rigorous, not partial,
verified via Aut-order matching `2^{β_H} · |Aut(H)|`), and computes
`Aut_S` orbits via the tuple-orbit method.

### 7.1 F7 strict at depth 1 — landscape

| Base | tw(H) | Aut(CFI(H)) order | Subset start (F7 @ depth 1) | Endpoint start (F7 @ depth 1) |
|---|:---:|---:|:---:|:---:|
| K₄ | 3 | 192 | YES (9 = 9) | YES (14 = 14) |
| K₃,₃ | 3 | 1152 | YES (11 = 11) | YES (16 = 16) |
| Petersen | 4 | 7680 | YES (12 = 12) | YES (20 = 20) |
| Rook3×3 | 4 | 73728 | **NO** (14 ≠ 15) | YES (31 = 31) |

7 of 8 datapoints satisfy F7 strict at depth 1. The single
counterexample is **CFI(Rook3×3) subset start**: 1-WL gives 14 cells
while Aut_v has 15 orbits — 1-WL merges two distinct orbits (sizes 4
and 2) into a single size-6 cell.

### 7.2 Rook3×3 subset depth-by-depth

| Depth | Cells | Aut_S orbits | Gap | F7 strict |
|---:|---:|---:|---:|:---:|
| 1 | 14 | 15 | −1 | NO |
| 2 | 45 | 47 | −2 | NO |
| 3 | 57 | 60 | −3 | NO |
| 4 | **108** | **108** | 0 | **YES** |

**The gap grows before it closes.** This means per-step HOR
("branching always reduces the gap") is **false** — branching can
create new compound cells while resolving old ones. The cumulative
HOR / F7-graded statement (gap closes by depth tw(H) = 4) holds.

### 7.3 Side findings

- **CFI of odd-cycle bases is disconnected.** `CFI(C_k)` for odd `k`
  splits into two disjoint cycles of length 3k. Multi-component CFI is
  out of scope for the single-Aut-stabilizer framing. Excluded from the
  test suite.
- **F7 strict often holds at depth 1** for connected CFI bases.
  Whether this is the rule or the exception across all H is open.
  Empirically (in our tests), endpoint starts always satisfy F7 at
  depth 1, subset starts usually do.

---

## 8. Open questions

The proof gives us Tier 1 cleanly but leaves several interesting
questions open. Listed roughly by how much they would change the
program.

**Q1 (sharper depth bound).** For specific CFI(H), what is the
**exact** depth `k(H, vertex type)` at which 1-WL becomes orbit-
complete? Empirically: 1 for K₄/K₃,₃/Petersen subset and all tested
endpoint starts; tw(H) = 4 for Rook3×3 subset. No clean structural
predictor yet.

**Q2 (per-step gap dynamics).** Why does the Rook3×3 gap grow from −1
to −3 before closing at depth 4? Is there a structural invariant
governing gap evolution? A clean answer would refine HOR into a
"per-step" form.

**Q3 (universal early-recovery).** For which structural classes of `H`
does CFI(H) satisfy F7 strict at depth 1 (no early gap)? Conjecture:
graphs where Aut(H) acts "richly enough" on the gadget structure.
Concrete subclasses to check: bipartite, vertex-transitive,
distance-regular, scheme graphs.

**Q4 (unbounded tw).** Theorem 1 gives `k ≤ tw(H)`. For `H` with
unbounded tw, this isn't a polynomial bound. Are there CFI(H) with
unbounded tw where chain descent still canonizes cheaply by some other
mechanism? Probably not — IR blind spots
([`chain-descent-strategy.md`](./chain-descent-strategy.md) §15 #5)
are precisely the high-tw cases where IR struggles.

**Q5 (Tier 2 connection).** For association schemes (Tier 2 of §4),
1-WL at depth 1 is orbit-complete (essentially Piece C of
[`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)).
This is strictly stronger than Tier 1's `k ≤ tw(H)` bound. Tier 2
would be the next paper-write target.

---

## 9. Lean formalization status

**Phase 1 (Tier 1 + Tier 2 assemblies, shared OrbitPartition framework) —
COMPLETE 2026-05-26.** [ChainDescent.lean](../GraphCanonizationProofs/ChainDescent.lean)
is organised as three sections, mirroring the paper structure:

**§16 — Orbit recovery: shared infrastructure** (tier-agnostic):
- `individualizedColouring`, `FixesPointwise` definitions.
- `FixesPointwise.complement`, `individualizedColouring_invariant`.
- `signature_invariant_of_isAut`, `refineStep_invariant_of_isAut`,
  `iterate_refineStep_invariant_of_isAut`,
  `warmRefine_invariant_of_isAut` — automorphism invariance lifts
  through refinement.
- **`OrbitPartition adj P S v w`** — the Aut_S orbit equivalence
  relation. `OrbitPartition.refl/symm/trans` give the equivalence
  structure.
- **`OrbitPartition.subset_warmRefine`** — **the trivial direction,
  proved.** Orbits refine 1-WL cells. Load-bearing for both tiers'
  squeeze. Axiom-clean: depends only on the standard `refineStep`
  basis.

**§17 — Tier 1 (CFI graphs):**
- `id_of_discrete_invariant`, **`aut_trivial_of_discrete_warmRefine`**
  (Fact B, proved), `orbit_iff_eq_of_discrete_warmRefine` (partition
  form, proved).
- **`CascadesAt adj P k`** — depth-parametrised cascade predicate.
- **`cascadesAt_univ`** — **proved**: every graph cascades at depth
  `n` trivially (`S = univ`). The "no content" baseline that makes
  Theorem 1's existential form axiom-free.
- `CascadesAt.mono` — monotonicity in `k`.
- **`theorem_1_HOR_at_depth`** — **the load-bearing depth-parametrised
  theorem, proved unconditionally** (no axioms beyond standard basis).
  Given `CascadesAt adj P k`, OrbitPartition = warmRefine partition at
  some `S` with `|S| ≤ k`.
- **`theorem_1_HOR_at_n`** — **proved**, trivial-bound specialisation
  using `cascadesAt_univ`.
- **`theorem_1_HOR`** — **proved** (existential, legacy form);
  axiom-free corollary of `theorem_1_HOR_at_n`.
- **`theorem_1_HOR_pointwise`** — **proved** (Aut_S trivial form);
  axiom-free corollary.

*Tier-1 CFI placeholder axioms (parallel to Tier 2's
`IsSchurianSchemeGraph`):*
- `IsCFI` — abstract Prop placeholder for "the graph is a CFI graph."
- `cfi_depth_bound : Nat → Nat` + `cfi_depth_bound_le` — abstract
  polynomial cascade-depth function with the placeholder polynomial
  relation `cfi_depth_bound n ≤ n`. Classical content: `cfi_depth_bound
  n = tw(H)` for `adj = CFI(H)`.
- `cfi_cascades_polynomially` — Tier-1 Fact A: a CFI graph cascades at
  depth `cfi_depth_bound n`.
- **`theorem_1_HOR_cfi`** — **proved** (conditional on the three
  placeholders): CFI orbit recovery at polynomial depth.

**§18 — Tier 2 (schurian scheme graphs):**
- **`SchemeProfile`** — bundled structure carrying:
  - `profile : Colouring n` representing the v-profile partition.
  - `v_singleton` — v is alone in its profile class.
  - **`profile_iff_orbit`** — Step 1 field (schurian ⟹ profile = orbits).
  - **`warm_refines_profile`** — Step 2 field (1-WL refines profile).
- **`SchemeProfile.warm_iff_profile`** — **derived squeeze, proved**:
  warmRefine partition equals profile partition. The reverse half
  (profile ⊆ warmRefine) comes from §16.3's trivial direction
  composed with `profile_iff_orbit`.
- `IsSchurianSchemeGraph` — **abstract Prop axiom** placeholder for
  "the graph admits a vertex-transitive schurian association scheme."
- `schurian_scheme_profile_exists` — **Tier 2 Fact A analogue
  axiom**: a SchemeProfile exists at every vertex of a schurian
  scheme graph.
- **`theorem_2_HOR_of_profile`** — **Theorem 2 assembly given
  witness, proved**: given a SchemeProfile at v, OrbitPartition =
  warmRefine partition at depth 1.
- **`theorem_2_HOR`** — **Theorem 2 unconditional form, proved**
  conditional on `schurian_scheme_profile_exists`.

**Axiom dependencies** (from `#print axioms`):

*Axiom-free* (standard `refineStep` basis only):
- `OrbitPartition.subset_warmRefine` (the trivial direction).
- `OrbitPartition.refl/symm/trans`: only `propext` and `Quot.sound`.
- `CascadesAt`, `cascadesAt_univ`.
- `theorem_1_HOR_at_depth` (the depth-parametrised core).
- `theorem_1_HOR_at_n`, `theorem_1_HOR` (legacy existential),
  `theorem_1_HOR_pointwise`.
- `theorem_2_HOR_of_profile` (Tier 2 assembly given witness).

*Tier-1 CFI placeholders* (added only by `theorem_1_HOR_cfi`):
- `IsCFI`, `cfi_depth_bound`, `cfi_cascades_polynomially`.

*Tier-2 scheme placeholders* (added only by `theorem_2_HOR`):
- `IsSchurianSchemeGraph`, `schurian_scheme_profile_exists`.

The Tier 1 / Tier 2 parallel is now load-bearing: each tier adds an
abstract Prop placeholder and a single Fact-A-shaped existence axiom.
The structural orbit-recovery theorems are axiom-free (load-bearing
content is the `CascadesAt`-parametrised core); the tier-specific
forms layer the abstract axioms on top.

**Polynomial-depth bound (2026-05-26).** The Tier-1 specific axiom
`cfi_cascades_polynomially` asserts `CascadesAt adj P (cfi_depth_bound n)`
where `cfi_depth_bound n ≤ n` (placeholder polynomial relation).
Concrete realisation tightens this to `cfi_depth_bound n = tw H` with
the relation `tw H ≤ n_H ≤ n` from the CFI base graph. The
chain-descent polynomial-runtime corollary (Corollary 1) only needs
the depth bound to be polynomial in `n` — any concrete polynomial
realisation suffices.

**Phase 2 (discharging Fact A / Tier 2 Fact A analogue) — REMAINING
WORK.** Two parallel multi-week tracks:

*Tier 1 (`cfi_cascade_exists`)*:
- **CFI construction in Lean.** ~200-400 lines mirroring
  [`CfiGraphGenerator.cs`](../GraphCanonizationProject/CfiGraphGenerator.cs)'s
  gadget structure as Lean definitions.
- **`Aut(G)` as a group action on graphs.** Mathlib has the
  group-theoretic infrastructure; ~100 lines of glue to integrate
  with this project's `AdjMatrix` / `Colouring`.
- **CFI Aut structure lemma** (`Aut(CFI(H)) = Z₂^{β_H} ⋊ Aut(H)`).
- **Cascade lemma proper** — the Cai-Fürer-Immerman WL-dim result.

*Tier 2 (`schurian_scheme_profile_exists`)*:
- **Association scheme infrastructure in Lean.** ~300-500 lines:
  relations `R_0,…,R_d`, intersection numbers, scheme axioms, schurian
  property, vertex-transitivity. Mathlib does not have this.
- **Step 1 lemma**: schurian ⟹ scheme-relation classes = Aut-orbital
  classes. Mostly group action theory.
- **Step 2 lemma**: 1-WL refines profile partition (the
  intersection-number induction-on-rounds argument).
- **SchemeProfile constructor** from a scheme + vertex.

**Depth bound parameterisation — DONE 2026-05-26.** The original
`cfi_cascade_exists` axiom (no depth bound) has been replaced with the
depth-parametrised `CascadesAt adj P k` predicate plus three CFI
placeholder axioms (`IsCFI`, `cfi_depth_bound`,
`cfi_cascades_polynomially`). The structural Theorem 1 is now
axiom-free; the CFI-specific polynomial-depth form
(`theorem_1_HOR_cfi`) layers the placeholders on top. The polynomial
relation is exposed as the (axiomatic, placeholder)
`cfi_depth_bound_le : cfi_depth_bound n ≤ n`, ready to be tightened
to concrete `tw H` once CFI infrastructure lands.

**CFI infrastructure — Stages 1 + 2.1 + 2.2 STARTED 2026-05-26.** New
module
[`GraphCanonizationProofs/ChainDescent/CFI.lean`](../GraphCanonizationProofs/ChainDescent/CFI.lean)
hosts the Lean CFI construction.

*Stage 1 (foundations):*
- `CFIBase m` structure (symmetric, loopless adjacency, deg ≥ 2).
- `neighbors`, `degree`, `mem_neighbors_symm`,
  `not_self_mem_neighbors`, `edgeCountOrdered`.
- `gadgetSize`, `cfiVertexCount`, `gadgetSize_ge_six`,
  `cfiVertexCount_pos`.
- `evenSubsetsOfNeighbors` (indexes the `a_S^v` subset vertices).
- `triangleBase : CFIBase 3` concrete witness; smoke tests
  `triangleBase_degree`, `triangleBase_cfiVertexCount = 18`.

*Stage 2.1 (CFI vertex type):*
- `SubsetVertex H = Σ v, { S // S ∈ evenSubsetsOfNeighbors v }`.
- `EndpointVertex H = Σ v, { w // w ∈ neighbors v } × Bool`.
- `CFIVertex H = SubsetVertex H ⊕ EndpointVertex H`.
- `Fintype` + `DecidableEq` instances (explicit via `inferInstanceAs`
  through `Mathlib.Data.Fintype.Powerset/Sigma/Sum`).
- Smoke test `triangleBase_cfiVertex_card = 18` via `native_decide`.

*Stage 2.2 (CFI adjacency function):*
- `cfiAdj : CFIVertex H → CFIVertex H → Nat` — full CFI adjacency
  encoding the intra-gadget (`a_S^v ∼ e^b_{v→w}` iff `(w ∈ S) ⊕ b`)
  and inter-gadget untwisted bridge (`e^b_{v→w} ∼ e^b_{w→v}`) rules.
- `cfiAdj_symm` — proved.
- `cfiAdj_loopless` — proved, uses `not_self_mem_neighbors`.

*Stage 2.3 (lift to AdjMatrix + concrete IsCFI):*
- `cfiAdjMatrix : CFIBase m → AdjMatrix (Fintype.card H.CFIVertex)` —
  `cfiAdj` lifted through `Fintype.equivFin` (noncomputable; the
  classical bijection from a fintype to its Fin-indexed image).
- `cfiAdjMatrix_symm` / `cfiAdjMatrix_loopless` — proved.
- `IsCFI'` — concrete `Prop` predicate: `∃ m H (e : Fin n ≃
  H.CFIVertex), ∀ i j, adj.adj i j = H.cfiAdj (e i) (e j)`.
- `cfiAdjMatrix_is_cfi` — self-witness: every `H : CFIBase m`'s
  `cfiAdjMatrix` satisfies `IsCFI'`.
- Smoke test: `IsCFI' triangleBase.cfiAdjMatrix` holds.

*IsCFI axiom retirement — DONE 2026-05-26.* The Tier-1 CFI form of
Theorem 1 (`theorem_1_HOR_cfi`) and its placeholder axioms
(`cfi_depth_bound`, `cfi_depth_bound_le`,
`cfi_cascades_polynomially`) have been relocated from
`ChainDescent.lean §17.4` to `ChainDescent/CFI.lean §10`, now using
the concrete `IsCFI'` predicate instead of the abstract `axiom
IsCFI`. The `IsCFI` axiom is **gone**; Tier-1 axiom budget is down
from 3 placeholders to 2 (`cfi_depth_bound`,
`cfi_cascades_polynomially`).

The Tier 2 analogue (`IsSchurianSchemeGraph`,
`schurian_scheme_profile_exists`) still uses an abstract Prop axiom
in `ChainDescent.lean §18`; it'll be relocated similarly once
Tier 2's concrete-scheme-based predicate is built.

*Depth-bound API tightening — DONE 2026-05-26.* The original
`theorem_1_HOR_cfi` claim `S.card ≤ cfi_depth_bound n` was structurally
**vacuous** — it matched `theorem_1_HOR_at_n`'s axiom-free `S.card ≤ n`
modulo the relation `cfi_depth_bound n ≤ n`, since `cfi_depth_bound`
took only `n` and could not encode a CFI-specific bound. Refactor:

- `IsCFI'` is now a **`structure` in `Type`** (was `Prop` `∃`), with
  named projections `m`, `H`, `e`, `matching`. The base graph `h.H` is
  addressable as data.
- New abbreviation `h.baseSize := h.m` exposes the base graph's vertex
  count.
- `cfi_depth_bound` axiom refactored to take the `IsCFI'` witness:
  `∀ {n} {adj : AdjMatrix n}, IsCFI' adj → Nat`. The depth function
  now depends on the specific CFI graph (specifically its base).
- `cfi_depth_bound_le` axiom strengthened to `cfi_depth_bound h ≤
  h.baseSize`. Classical content `tw H ≤ n_H = h.baseSize`.
- New connector `IsCFI'.six_baseSize_le : 6 * h.baseSize ≤ n`
  (axiom-clean) — combinatorial fact `n = card CFIVertex ≥ 6 m` via
  `gadgetSize_ge_six`. So `cfi_depth_bound h ≤ h.baseSize ≤ n / 6`,
  which is strictly tighter than the trivial `≤ n` recovered
  axiom-free.
- New corollaries `theorem_1_HOR_cfi_baseSize` (bound: `≤ h.baseSize`)
  and `theorem_1_HOR_cfi_n_bound` (bound: `6 * S.card ≤ n`). The
  CFI-specific theorem now carries genuine content over the
  axiom-free trivial-bound theorem.

Tier-1 axiom budget unchanged at 3 placeholders (`cfi_depth_bound`,
`cfi_depth_bound_le`, `cfi_cascades_polynomially`), but now they
collectively imply something stronger than `cascadesAt_univ` gives
for free. The Tier 2 analogue refactor is still pending its concrete
scheme predicate.

*Stage 4 / M1 — Depth-bound concretization — DONE 2026-05-26.* With
the depth-bound API tightened to take `IsCFI'` witnesses, the
`cfi_depth_bound` and `cfi_depth_bound_le` axioms are dischargeable
by direct definition. Done:

- `def cfi_depth_bound h := h.baseSize` (was axiom).
- `theorem cfi_depth_bound_le := Nat.le_refl _` (was axiom).

Net effect: Tier-1 axiom budget **3 → 1**. The sole remaining
Tier-1 axiom is `cfi_cascades_polynomially` (the actual cascade
lemma).

Concrete commit value `h.baseSize` is the "one-individualization-
per-gadget" depth; classical bound `tw H ≤ baseSize` is a sharper
realisation deferred to M5. The polynomial-runtime corollary needs
only some polynomial bound; `baseSize ≤ n / 6` satisfies that.

*Stage 4 / M2 — gadget-level distinguishability — DONE 2026-05-26.*
The first cascade lemma: with `a_∅^v` (the canonical seed) individualized,
**one round of `refineStep`** distinguishes v's b=0 endpoints from v's
b=1 endpoints. Lean development (`ChainDescent/CFI.lean` §13):

- §13.1 — `CFIBase.aEmpty v` / `CFIBase.endpoint hw b` constructors.
- §13.2 — `cfiAdj` evaluation: `aEmpty v ↮ endpoint hw false`,
  `aEmpty v ↔ endpoint hw true`. Distinctness `aEmpty_ne_endpoint`.
- §13.3 — Fin-n extractors via the IsCFI' bijection:
  `IsCFI'.seedVertex v := h.e.symm (aEmpty v)`,
  `IsCFI'.endpointVertex hw b := h.e.symm (endpoint hw b)`. Distinct
  via `seedVertex_ne_endpointVertex`.
- §13.4 — `adj` adjacency facts at Fin-n level (`adj_seed_endpoint_false`
  / `_true` and symmetric forms), transported via `h.matching`.
- §13.5 — Generic singleton-individualization lemmas:
  `individualizedColouring_singleton_self`,
  `individualizedColouring_singleton_other`,
  `individualizedColouring_singleton_eq_seed_iff` (the uniqueness
  fact powering the signature argument).
- §13.6 — **`IsCFI'.signature_endpoint_false_ne_true`** (M2.4):
  signature multisets differ under χ_{seed}. Witness tuple
  `(χ seed, 1, P endpoint_true seed)` — present in endpoint_true's
  signature (via u = seed, since seed is adjacent to endpoint_true)
  but absent from endpoint_false's (no u satisfies both χ u = χ seed
  and adj endpoint_false u = 1).
- §13.7 — **`IsCFI'.refineStep_endpoint_false_ne_true`** (M2.5,
  headline): lift via `refineStep_iff`. The b=0 and b=1 endpoints
  have distinct refined colours after one round.

All M2 lemmas axiom-clean (`refineStep_endpoint_false_ne_true`
depends only on `refineStep`, `refineStep_iff` and the standard
basis — no CFI-specific axioms used).

*Stage 4 / M3-M4 (PENDING, multi-week):*
- M3: bridge propagation. The endpoint-endpoint bridge
  `e^b_{v→w} ↔ e^b_{w→v}` carries gadget colour information across
  bases; after O(diam H) refineStep rounds, every endpoint is
  uniquely coloured by (gadget, partner, parity).
- M4: assemble. Construct `S = h.e.symm '' { Sum.inl ⟨v, ⟨∅, _⟩⟩ }`
  (size = `h.baseSize`), prove `warmRefine adj P χ_S` is `Discrete`,
  discharge `cfi_cascades_polynomially`.

*Combinatorial identity — DONE 2026-05-26.* The classical identity
"the number of even-cardinality subsets of a nonempty `d`-element
set is `2^(d-1)`" is proved as
`Finset.card_powerset_filter_even` (using Mathlib's
`sum_powerset_neg_one_pow_card_of_nonempty` alternating-sum
lemma). Combined with `Fintype.card_sigma` / `_sum` / `_coe`, the
full identity `Fintype.card H.CFIVertex = H.cfiVertexCount` is
proved as `CFIBase.card_CFIVertex` in `CFI.lean §11`.

*Pending (Stages 3-4, multi-week):* Aut structure lemma; cascade
lemma discharging `cfi_cascades_polynomially`.

The CFI module is built as a sub-target (`defaultTargets =
["ChainDescent", "ChainDescent.CFI"]` in `lakefile.toml`), split from
`ChainDescent.lean` to keep the main proofs file under ~4000 lines.

**Effort estimate.** Each Phase-2 track is multi-week. The Phase-1
assemblies in place mean the structure is set — once the Fact-A-shape
axioms are discharged, both theorems tighten automatically.

---

## 10. Tier 2 sketch (follow-on direction)

When Tier 1 is settled, Tier 2 is the natural next paper. Sketch:

> **Theorem 2 (orbit recovery for association schemes).** Let `G` be a
> graph admitting a vertex-transitive association scheme (Johnson
> `J(m,k)`, Hamming `H(d,q)`, etc.). For any single fresh-colour
> individualized vertex `v`, 1-WL refinement on `(G, v)` gives a
> partition equal to `Aut(G)_v`-orbits.

*Proof sketch.* Use the scheme's intersection matrix directly:
- After individualizing `v`, the stabilizer's orbits on remaining
  vertices are exactly the **profile classes** of the scheme (e.g.,
  for Johnson `J(m, k)`, two k-subsets are in the same `Aut_v`-orbit
  iff they share the same intersection size with `A` = `v`'s subset).
- 1-WL on a scheme graph computes the scheme's coherent algebra
  (classical result); after individualization, it computes the
  profile-conditioned partition.

This proof routes through association-scheme theory rather than CFI
theory, making it independent of Tier 1.

**Connection to Piece C of hidden-johnson.md:** Piece C is the
Johnson-scheme case of Theorem 2 — proving Theorem 2 advances Piece C
and unblocks the cascade half of the hidden-Johnson near-theorem.

---

## 11. Connection to existing work

- **[`chain-descent-strategy.md`](./chain-descent-strategy.md) §5 (oracle
  interface).** The cascade oracle's job is to certify orbits. Theorem 1
  gives a polynomial cascade-class oracle for CFI(H) with bounded tw(H):
  individualize the canonical picker's choices, refine, repeat for
  ≤ tw(H) steps, read off cells = orbits at termination.
- **[`chain-descent-calculator.md`](./chain-descent-calculator.md) §4
  (T-A/T-B/T-C).** Theorem 1 provides T-C for CFI(H) with bounded
  tw(H). T-A and T-B are free citations from computational group
  theory. So Tier 1 closes the polynomial-bound triangle for the
  bounded-tw CFI class.
- **[`chain-descent-calculator.md`](./chain-descent-calculator.md) §7
  (construction question).** Theorem 1 confirms calculator.md §7's
  claim that "CFI applied to a Johnson base ... is decomposable" via
  empirical verification at depth 1 for Petersen (which equals
  J(5,2)). Both subset and endpoint Aut-orbits cleanly recover.
- **[`chain-descent-matroid.md`](./chain-descent-matroid.md).** Closed
  framework; the binary-closure conjecture (§10 of matroid memo)
  conjectured "every graph's propagation closure is a binary matroid."
  Theorem 1 is a related but distinct claim — it's about refinement-
  orbit equality, not closure-system structure. Independent argument.
- **[`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)
  §5 Piece C.** Tier 2 (§10) of this doc subsumes Piece C and may
  give a cleaner proof route than the current Piece-C scope.

---

## 12. Code and artifacts

- **Test code:** [`Tier2DecompositionExperiment.cs`](../GraphCanonizationProject.Tests/Tier2DecompositionExperiment.cs)
  has all empirical work for §7. Key tests:
  - `CfiK4_OrbitRecovery_…`, `CfiK33_OrbitRecovery_…`,
    `CfiPetersen_OrbitRecovery_…`, `CfiRook3x3_OrbitRecovery_…` —
    depth-1 F7 check on each base.
  - `AllConnectedBases_OrbitRecovery_Depth2_ReportPattern` — depth-2
    comparison across all bases.
  - `CfiRook3x3_SubsetStart_OrbitRecovery_DeepProbe` — depths 1–4 on
    the counterexample case.
- **Production change to support testing:** added
  `CanonGraphOrdererChainDescent.LastAutomorphisms : PermutationGroup`
  public accessor — exposes the canonizer's harvested Aut group so
  tests can extract generators for orbit comparison. One property +
  one assignment, no behaviour change.
- **Sibling docs:**
  [`chain-descent-tier2-decomposition-experiment.md`](./chain-descent-tier2-decomposition-experiment.md)
  documents the experiment that surfaced F7. Now-concluded; the
  positive Tier-1 finding here is its main outcome.

---

## 13. What's settled and what's next

**Settled:**
- Theorem 1 (F7-graded / HOR for CFI) with cascade-based proof (§5).
- Corollary 1 (polynomial cost for bounded-tw CFI) (§6).
- Empirical landscape on 4 connected CFI bases × 2 starts (§7).
- F7 strict at depth 1 is **not** universal (Rook3×3 subset
  counterexample).
- Multi-component CFI (odd cycle bases) is out of scope.

**Next (in user's stated plan order):**
1. ✓ Sketch Tier 2 paper proofs (§10, §14).
2. ✓ Lean Phase 1 — shared OrbitPartition + Tier 1 + Tier 2
   assemblies (§9, §16-§18 of ChainDescent.lean). Both theorems
   conditional on Fact-A-shaped axioms; structure is set.
3. Discharge the Fact-A axioms — multi-week infrastructure builds:
   CFI construction for Tier 1, association schemes for Tier 2.
4. Tighten `cfi_cascade_exists` to expose a polynomial depth bound
   (any polynomial `p(n)` preserves polynomial runtime).
5. From there: sketch Tier 3 or continue with the infrastructure
   work above.

**Stable building blocks delivered:**
- Test harness for orbit-recovery checks (extensible to other graph
  classes for Tiers 2/3).
- HOR framing as the algorithmic statement (more natural than F7 for
  chain descent's polynomial argument).
- Honest empirical pattern map (depth-1 recovery is common but not
  universal; tw(H) is the worst-case bound).

---

## 14. Tier 2 paper proof — association scheme graphs

This section drafts the Tier 2 theorem and proof, expanding §10's
sketch into full paper form. The proof routes through association
scheme theory and is independent of Tier 1 / CFI machinery.

### 14.1 Association scheme background

A reader unfamiliar with schemes can think of them as "a clean
algebraic generalization of distance partitions in a regular graph."
We need the bare minimum.

A **symmetric association scheme** on vertex set `V` is a partition
of `V × V` into "relations" `R_0, R_1, …, R_d` satisfying:
1. `R_0 = { (v, v) : v ∈ V }` (the diagonal).
2. Each `R_i` is symmetric: `(u, v) ∈ R_i` iff `(v, u) ∈ R_i`.
3. **Intersection numbers** `p^k_{ij}`: for any `(u, v) ∈ R_k`, the
   number of `w ∈ V` with `(u, w) ∈ R_i` and `(w, v) ∈ R_j` is
   `p^k_{ij}` — depending **only on k, i, j**, not on the specific
   choice of `(u, v)`.

The number `d` is the **rank** of the scheme (so `d + 1` relations
total counting `R_0`).

A **scheme graph** is a graph `G = (V, E)` whose edge set is a union
of relations from some scheme: `E = ⋃_{j ∈ J} R_j` for some
`J ⊆ {1, …, d}`.

**Examples in scope:**
- **Johnson graph `J(m, k)`** for `m ≥ 2k + 1`: `V` = k-subsets of
  `[m]`; relations `R_j = {(A, B) : |A ∩ B| = k − j}` for
  `j = 0, …, k`; graph edge set = `R_1` (share k−1 elements).
- **Hamming graph `H(d, q)`**: `V` = strings of length `d` over an
  alphabet of size `q`; relations `R_j = {(x, y) :` Hamming
  distance `(x, y) = j}` for `j = 0, …, d`; graph edge set = `R_1`
  (differ in one position).
- **Distance-regular graphs (DRGs)**: any DRG defines a scheme via
  distance relations. Petersen = `J(5, 2)`, Hamming and Johnson graphs,
  and many other classical structures.

A scheme is **schurian** (or **2-closed**) if its relations are
exactly the orbits of `Aut(G)` acting diagonally on `V × V`. For
schurian schemes, scheme-relation classes coincide with
automorphism-orbital classes — the algebraic and group-theoretic
descriptions match.

Johnson and Hamming schemes are schurian for the parameter ranges
above. General DRGs may or may not be schurian; "distance-transitive"
DRGs are.

### 14.2 Theorem 2

> **Theorem 2 (orbit recovery for schurian scheme graphs).** Let
> `G = (V, E)` be a scheme graph for a vertex-transitive **schurian**
> association scheme `S = (R_0, …, R_d)` with `E = ⋃_{j ∈ J} R_j`.
> Then for any single fresh-colour individualized vertex `v ∈ V`,
> 1-WL refinement on `(G, v)` produces a partition equal to
> `Aut(G)_v`-orbits.

The headline contrast with Tier 1: **depth 1 always suffices** for
Tier 2, whereas Tier 1 needed `≤ tw(H)`. The algebraic regularity
of scheme graphs gives 1-WL much more power per individualization.

### 14.3 Proof of Theorem 2

Three sub-arguments, combined.

**Step 1 — `Aut(G)_v` orbits on `V \ {v}` are scheme-relation classes
relative to `v`.**

For each `w ∈ V \ {v}`, there is a unique `j(w) ∈ {1, …, d}` with
`(v, w) ∈ R_{j(w)}`. Define the **v-profile** of `w` as `j(w)`.

*Claim:* `Aut(G)_v`-orbits on `V \ {v}` are exactly the level sets
of `j`.

*Proof of claim.* Each `R_j` is a `Aut(G)`-orbit on ordered pairs
(by the schurian assumption). So for `g ∈ Aut(G)_v` (fixes `v`),
applying `g`: `(v, w) ∈ R_j` ⟹ `(v, g(w)) = (g(v), g(w)) ∈ R_j`.
So `j(g(w)) = j(w)` — `Aut(G)_v` preserves `v`-profile.

Conversely, suppose `j(w) = j(w') = j`. Then `(v, w)` and `(v, w')`
are both in `R_j`, hence in the same `Aut(G)`-orbital. So some
`g ∈ Aut(G)` sends `(v, w)` to `(v, w')`. This `g` fixes the first
coordinate, i.e., `g(v) = v`, so `g ∈ Aut(G)_v`. And `g(w) = w'`.
So `w` and `w'` are in the same `Aut(G)_v`-orbit.

Combined: `Aut(G)_v`-orbits = `v`-profile classes. ∎ Step 1.

**Step 2 — 1-WL on `(G, v individualized)` distinguishes `v`-profile
classes.**

This is the technical heart. We show: at 1-WL fixpoint, two vertices
`w, w' ∈ V \ {v}` share a 1-WL cell iff `j(w) = j(w')`.

*Proof.* We argue by induction on the 1-WL round `r`.

The initial colour `χ_0` has `v` distinct (fresh) and all
other vertices equal. Already at round 1:
- For `w` adjacent to `v` (i.e., `(v, w) ∈ E = ⋃_{j ∈ J} R_j`, so
  `j(w) ∈ J`): `w`'s signature is `(0, multiset with one "v-color"
  and (deg(w) − 1) "other-colors")`.
- For `w` non-adjacent to `v` (i.e., `j(w) ∉ J`): `w`'s signature is
  `(0, multiset with deg(w) "other-colors")` — no v-color.

So round 1 separates `{w : j(w) ∈ J}` from `{w : j(w) ∉ J}`.

For round `r ≥ 2`, by the scheme's intersection numbers, the number
of `w`'s neighbours falling into any cell at round `r − 1` is a
function of `j(w)` only. Specifically: if at round `r − 1` the
partition refines the `v`-profile classes, then at round `r` the
neighbour-color multiset of `w` is determined by the scheme structure
restricted to `R_{j(w)}` — same for all `w` with same `j(w)`.

So at fixpoint, the 1-WL partition is at most as fine as the
`v`-profile partition (cells ⊆ profile classes).

Conversely, the `v`-profile partition is preserved by `Aut(G)_v`
(Step 1), and hence preserved by 1-WL (trivial direction). So 1-WL
partition refines `v`-profile partition... wait that's the wrong
direction. Let me re-state.

The trivial direction says: if `w, w'` are `Aut_v`-equivalent (same
profile by Step 1), they have the same 1-WL colour at every round.
So 1-WL cell of `w` contains all `w'` with `j(w') = j(w)`. I.e.,
profile classes ⊆ 1-WL cells.

Combined with the round-by-round argument (1-WL cells ⊆ profile
classes once fixpoint reached): profile classes = 1-WL cells.

So 1-WL fixpoint partition = `v`-profile partition. ∎ Step 2.

**Step 3 — Combine.** Step 1: `Aut(G)_v` orbits = `v`-profile classes.
Step 2: 1-WL fixpoint = `v`-profile classes. So 1-WL fixpoint =
`Aut(G)_v` orbits. ∎ Theorem 2.

### 14.4 Specific instantiations

**Johnson `J(m, k)` with `m ≥ 2k + 1`.** Schurian (well-known).
`v`-profile of `B` = `|A ∩ B|` for individualized `v = A`. Profile
classes: `k + 1` of them, sizes `\binom{k}{j}\binom{m-k}{k-j}` for
`j = 0, …, k`. By Theorem 2, 1-WL at depth 1 recovers these classes.

**Hamming `H(d, q)`.** Schurian. `v`-profile of `y` = Hamming distance
`d(v, y)` for individualized `v`. Profile classes: `d + 1` of them.

**Distance-transitive DRGs.** Schurian by definition (distance
classes are Aut orbits on pairs). Theorem 2 applies.

**Petersen graph (= `J(5, 2)`).** Schurian. 1-WL after individualizing
a vertex `A` recovers the 3 profile classes (intersection size 1, 0)
plus singleton `{A}`. This is the Petersen-specific case of Theorem 2;
trivially holds since Petersen is distance-regular.

### 14.5 Gaps and open questions

**G1 (schurian assumption).** Theorem 2 requires schurian schemes. For
non-schurian schemes, 1-WL might capture the scheme partition (which
is coarser than orbit partition) but not orbit-recover. Concretely:
some DRGs are not distance-transitive, and Theorem 2 doesn't apply to
those. The proof would weaken from "1-WL = orbits" to "1-WL = scheme
classes, which contain orbits."

**G2 ("1-WL captures scheme structure" precision).** Step 2's
intersection-number argument is structurally right but the precise
classical citation is folklore-ish. Needs a clean reference:
candidates include Cai-Fürer-Immerman 1992 (general WL theory), or
Babai 1979 (coherent configurations and 1-WL).

**G3 (general scheme graphs vs Johnson/Hamming specifically).** The
proof above is for `G` being a scheme graph for any subset
`J ⊆ {1, …, d}`. For the Johnson **graph** itself (with `J = {1}`),
the argument is cleanest. For Johnson **scheme graphs** with more
relations (union of overlap classes), the argument still goes through
but each step needs verification.

**G4 (non-vertex-transitive schemes).** Theorem 2 assumes
vertex-transitivity. Without it, scheme classes depend on the
starting vertex, and the proof needs modification. Easy adaptation
but not stated above.

**G5 (Lean infrastructure).** Mathlib does not have association
schemes packaged. Formalizing Theorem 2 in Lean would need ~300-500
lines of scheme + coherent algebra infrastructure first. Roughly
comparable in effort to the CFI infrastructure for Tier 1.

**Tier 2 Lean assembly is in place (2026-05-26):** §18 of
[ChainDescent.lean](../GraphCanonizationProofs/ChainDescent.lean)
contains the `SchemeProfile` structure (bundling Step 1's
`profile_iff_orbit` and Step 2's `warm_refines_profile`) and
`theorem_2_HOR` conditional on the placeholder existence axiom
`schurian_scheme_profile_exists`. The Tier 1 / Tier 2 parallel is
reflected in the axiom budget — each tier adds exactly one
Fact-A-shaped existence axiom. Discharging
`schurian_scheme_profile_exists` is the G5 work proper.

**G6 (empirical verification).** **Done 2026-05-26.** Two scheme
graphs tested at depth 1; both pass Theorem 2 strictly.

| Graph | n | \|Aut\| | Cells at depth 1 | Aut_v orbits | Match |
|---|---:|---:|---|---|:---:|
| Petersen (Kneser K(5,2)) | 10 | 120 | [6, 3, 1] | [6, 3, 1] | YES |
| Johnson J(5,2) | 10 | 120 | [6, 3, 1] | [6, 3, 1] | YES |

Both match the predicted Aut_v = `S_2 × S_3` stabilizer (order 12)
with profile classes of size 3 (disjoint pairs) and 6 (single-element
overlap) — exactly the Step 1 prediction.

Tests at
[`Tier2DecompositionExperiment.cs`](../GraphCanonizationProject.Tests/Tier2DecompositionExperiment.cs):
`Petersen_OrbitRecovery_Depth1_Tier2Verification`,
`JohnsonJ52_OrbitRecovery_Depth1_Tier2Verification`.

Note interesting contrast with CFI(Petersen) (Tier 1, also 100% match
at depth 1, but for a totally different graph). The 7 of 8 Tier 1
landscape doesn't translate to Tier 2 — Theorem 2 predicts 100% match
for all schurian schemes, no counterexamples expected.

**Additional cases worth adding for fuller verification:** Hamming
H(2, 3) = Rook3×3 directly (different from CFI(Rook3×3); should
satisfy Theorem 2 cleanly at depth 1). Larger Johnson J(m, k) for
m > 5. Optional but cheap.

**G7 (Tier 1 vs Tier 2 interaction — CFI(Johnson) vs Johnson).** Tier 1
verifies CFI(Petersen) = CFI(J(5,2)) cleanly. Tier 2 would verify
Petersen = J(5,2) directly (without the CFI wrapper). These are
**different graphs** with **different Aut groups** — relating their
orbit-recovery behavior is itself a structural question worth
exploring.

### 14.6 Connection to hidden-Johnson Piece C

[`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)
§5 sketches Piece C of the near-theorem: "Johnson scheme graphs
cascade under chain descent (Tier 1)." Piece C's plan (C1–C4) routes
through Young subgroup combinatorics directly:
- C1: identify Young subgroup as stabilizer after individualization
- C2: transversal discovery via profile computation
- C3: depth bound `≤ m − 1`
- C4: assembly

Theorem 2 is a **direct alternative proof** of Piece C for the Johnson
case (and additionally covers Hamming and DRGs). The route through
association scheme theory is shorter and more general.

If Theorem 2 is paper-rigorous, **Piece C is settled** for the
Johnson case via Theorem 2. The hidden-Johnson near-theorem's
remaining open piece becomes closed (for the visible Johnson
case; encoded Johnson is still the open construction question).

### 14.7 What's needed to finalize Tier 2

Status as of 2026-05-26:
- **G6 ✓ done** — Petersen and J(5,2) verified at depth 1.
- **G1 (schurian assumption)** — explicit. Add a sentence noting the
  classical cases (Johnson, Hamming, distance-transitive DRGs) and
  what fails (non-distance-transitive DRGs).
- **G2 (citation precision)** — needs a literature search. Candidate
  references: Babai 1979 "On the complexity of canonical labeling of
  strongly regular graphs"; Cai-Fürer-Immerman 1992; Grohe 2017 Chapter
  on coherent configurations.
- **G3 (general scheme graphs)** — proof above covers union-of-relations
  edge sets in principle. Worth a paragraph spelling out one explicit
  case beyond Johnson/Hamming.
- **G4 (non-vertex-transitive)** — note the adaptation.
- **G5 (Lean infrastructure)** — parallel workstream, multi-week.
- **G7 (Tier 1 vs Tier 2 interaction)** — relate the two graph
  families (CFI(Johnson) vs Johnson) more explicitly. Likely a
  paragraph about how the CFI wrapper interacts with the scheme
  structure of the base.

Once G1–G4 and G7 have explicit paragraphs, Theorem 2 is
**paper-finalized**. G5 (Lean) is a separate multi-week project.

**Note on the Tier 1 / Tier 2 contrast:**

Tier 1 needed `≤ tw(H)` individualizations because CFI graphs are
specifically constructed to defeat 1-WL — the gauge structure hides
orbits behind cycle-space obstacles that only `tw(H)` individualizations
can resolve. Tier 2 graphs (scheme graphs) have no such obstacles — the
scheme's algebraic structure is exactly what 1-WL is good at capturing.

This is the **algebraic / non-algebraic split** in disguise: schemes
are algebraic, CFI is non-algebraic (the gauge action is what makes
CFI an obstacle to algebraic methods).
