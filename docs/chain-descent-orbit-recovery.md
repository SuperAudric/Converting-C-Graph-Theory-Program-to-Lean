# Chain descent — orbit recovery for CFI and scheme graphs (witness theorems)

> **WITNESS LAYER, not the strategy** (read [`chain-descent-declassing.md`](./chain-descent-declassing.md)
> for the current approach). This is the trimmed doc: two concrete, correct
> **witness theorems** — Theorem 1 (CFI cascade depth ≤ tw(H), §5–§6) and Theorem 2
> (schurian scheme graphs, §14.1–§14.4) — that populate the abstract predicates
> (`CascadesAt`, `EdgeGenerates`, `VisiblyRecoverable`) discharged class-agnostically
> by `theorem_2_HOR_of_edgeGenerates` / `theorem_2_HOR_of_pPolynomial` (the whole
> metric / distance-regular family — cycles, Johnson, Hamming, all DRGs — in one
> theorem). The project **no longer recovers orbits class-by-class**; these are
> *examples*, not a queue.
>
> **The full 1778-line research log** (the §4 tier ladder narrative, §8 open
> questions, the §9 Lean formalization phase log, §10/§13 "what's next", §14.5/§14.7
> finalization gaps) was moved to
> [`Archive/ChainDescent/chain-descent-orbit-recovery-v1.md`](./Archive/ChainDescent/chain-descent-orbit-recovery-v1.md).
> Section numbers here are kept stable (so §14.1/§14.3 citations still resolve);
> the gaps in numbering mark the archived sections.

A focused theorem about how 1-WL refinement interacts with the
automorphism orbit partition of CFI graphs, with a path toward a
polynomial-cost bound for chain descent's cascade class.

This is a **standalone research note** — readable cold. For broader
context: [`chain-descent-strategy.md`](./chain-descent-strategy.md) for
the canonization algorithm and its requirements;
[`chain-descent-calculator.md`](./chain-descent-calculator.md) for the
oracle and the cost model.

---

## 0. How to read this doc (witness layer — a reading map)

Two witness theorems and their setup. Read:

- **§1, §3** — headline statement + setup/notation.
- **§5–§6** — Theorem 1 (CFI cascade depth ≤ tw(H)) and the polynomial-cost corollary.
- **§14.1–§14.4** — Theorem 2 (schurian scheme graphs), its proof, and instantiations
  (Johnson, Hamming, DRGs, Petersen).
- **§4** — the (historical) three-tier ladder these witnesses sat in; kept for context,
  banner inside.
- **§11–§12** — connections and code/artifact pointers.

These are *examples* populating the abstract predicates discharged class-agnostically
in [`chain-descent-declassing.md`](./chain-descent-declassing.md); they are **not** a
proof-obligation queue. The multi-step hidden-abelian case is *not* harvested within-cell
(proved: `lockstep_disc_imp_stab_trivial`) — it goes through the cross-branch
stabilizer-chain object, [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md).
The full historical research log is archived (see the banner above).

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

> **Where this sits now — leg A of the seal, and a *witness* (2026-06-02).** Orbit recovery is the
> backbone of the cascade oracle's completeness ([exhaustive-obstruction §0.5](./chain-descent-exhaustive-obstruction.md)),
> but the **harvest argument is now proved class-agnostically** — `colourMatch_eq_aut` /
> `harvest_isAut_of_discrete`
> ([`CascadeOracle.lean`](../GraphCanonizationProofs/ChainDescent/CascadeOracle.lean) §C.2): at a
> discrete footprint the colour-match candidate equals the orbit automorphism (`warmRefine_transport`).
> So **Theorem 1 (CFI) and Theorem 2 (schemes) below are not the recovery *plan*; they are
> *witnesses*** that a graph *has* a poly-depth harvest window (populating the abstract `CascadesAt` /
> D1 predicate). The only genuinely class-specific quantity is that window's **depth**, and only for
> the *hidden-abelian* (leg-B) case — there it is the *concealment* structure (CFI's `tw(H)`
> cycle-space, **substrate-conditional**). For *visible* symmetry (leg A) the depth is `base(g)`,
> seal-characterizable. The un-recovered boundary is therefore a **named property of the residual**
> (¬D1 — half of the leg-C / Cameron fingerprint), *not* a class restriction. Full statement:
> [harvest-window §2.4](./chain-descent-harvest-window.md); the current approach in full:
> [chain-descent-declassing.md](./chain-descent-declassing.md).

---

## 2. Background and motivation

This direction emerged from two earlier closed workstreams:

- **Matroid framework** ([`chain-descent-matroid.md`](./Archive/ChainDescent/chain-descent-matroid.md)) —
  attempted to model warm-refinement closure on commit-set guesses as
  a matroid, enabling a Tier-2 detector via binary-matroid testing.
  Closed 2026-05-23 after the exchange axiom failed on both partition-
  based `cl` and TC-based `cl_prov` (despite `cl_prov` being a
  topological closure).
- **Tier-2 decomposition experiment**
  ([`chain-descent-tier2-decomposition-experiment.md`](./Archive/ChainDescent/chain-descent-tier2-decomposition-experiment.md))
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

> ⚠️ **Historical framing.** The tier-by-tier ladder below was the *per-class*
> program. It is **superseded** by de-classing: each tier is now a correct
> *instantiation* of the abstract predicates, not an active research direction.
> Read it for how the witnesses sit relative to one another, not as a plan —
> [`chain-descent-declassing.md`](./chain-descent-declassing.md).

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
  Paper-first plan in [`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
  (decomposability framing, plus a visibility/no-hidden-symmetry
  alternate framing for inversion arguments). Tier 3a — cascade
  composition (Tier 1 + Tier 2 layers add their depths) — scoped in
  [`chain-descent-tier3a-cascade-composition.md`](./chain-descent-tier3a-cascade-composition.md)
  as the paper-tractable stepping stone.

**These tiers are the witness layer, not the live program.** The de-classing turn
([`chain-descent-declassing.md`](./chain-descent-declassing.md)) replaced the tier-by-tier ladder
with one class-agnostic reduction: the metric / distance-regular family (Tier 2's schemes and more)
is now a **single** theorem (`theorem_2_HOR_of_pPolynomial`), and Tier 1 / Tier 3 are subsumed as
*witnesses* populating the abstract `CascadesAt` predicate. Everything from §5 on is the historical
per-class proof development — correct and load-bearing **as witnesses** (and a candidate for archival
once fully subsumed), **not** an open proof-obligation queue. Read its "remaining work" / "next paper"
phrasings as the record of how the witnesses were built, not as the current plan.

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

This Corollary is the **CFI witness** of the cascade-class guarantee — not the deliverable itself.
The deliverable is the class-agnostic harvest ([declassing §6](./chain-descent-declassing.md)); this
is its bounded-`tw(H)` CFI instance. The cascade oracle's single-path recursion in fact removes the
*fixed-`tw`* restriction ([cascade-oracle §4.6](./chain-descent-cascade-oracle.md)), replacing the
`cell_size^{tw}` **product** with a `tw · n²` **sum**.

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

> **§8 (open questions), §9 (the Lean formalization phase log, ~760 lines), and
> §10 (Tier 2 follow-on sketch) are archived** in
> [`Archive/ChainDescent/chain-descent-orbit-recovery-v1.md`](./Archive/ChainDescent/chain-descent-orbit-recovery-v1.md).
> They are the historical development record; for *what is now proved* see
> [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md), and
> for the current plan [`chain-descent-declassing.md`](./chain-descent-declassing.md).

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
- **[`chain-descent-matroid.md`](./Archive/ChainDescent/chain-descent-matroid.md).** Closed
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
  [`chain-descent-tier2-decomposition-experiment.md`](./Archive/ChainDescent/chain-descent-tier2-decomposition-experiment.md)
  documents the experiment that surfaced F7. Now-concluded; the
  positive Tier-1 finding here is its main outcome.

---

> **§13 ("what's settled and what's next") is archived** — its "next" items were
> the per-class roadmap, superseded by de-classing. See
> [`Archive/ChainDescent/chain-descent-orbit-recovery-v1.md`](./Archive/ChainDescent/chain-descent-orbit-recovery-v1.md).

## 14. Tier 2 paper proof — association scheme graphs

This section drafts the Tier 2 theorem and proof in full paper form (the
historical §10 sketch is archived). The proof routes through association
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

---

> **§14.5 (gaps and open questions), §14.6 (hidden-Johnson Piece C bridge), and
> §14.7 (what's needed to finalize Tier 2) are archived** in
> [`Archive/ChainDescent/chain-descent-orbit-recovery-v1.md`](./Archive/ChainDescent/chain-descent-orbit-recovery-v1.md).
> Theorem 2 is now subsumed by the class-agnostic `theorem_2_HOR_of_pPolynomial`
> ([`chain-descent-declassing.md`](./chain-descent-declassing.md)); the Johnson/wall
> question lives in [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md).

