# Chain descent — orbit recovery for CFI graphs (ARCHIVED v1 — full research log)

> **ARCHIVED 2026-06-04.** This is the complete 1778-line chronological
> orbit-recovery research log. The **live witness theorems** (Theorem 1 — CFI
> cascade depth ≤ tw(H), §5–§6; Theorem 2 — schurian scheme graphs, §14.1–§14.4)
> were kept in the trimmed live doc
> [`docs/chain-descent-orbit-recovery.md`](../../chain-descent-orbit-recovery.md).
> Everything historical — the §4 tier ladder, §8 open questions, the §9 Lean
> formalization phase log, §10/§13 "what's next", §14.5/§14.7 finalization gaps —
> was removed from the live doc and preserved here. None of it is an open
> proof-obligation queue; the current approach is
> [`chain-descent-declassing.md`](../../chain-descent-declassing.md). Note: links
> below are relative to the original `docs/` location and may not resolve from here.

> **⚠️ Read [`chain-descent-declassing.md`](./chain-descent-declassing.md) first (2026-06-02) —
> this doc is the WITNESS LAYER, not the strategy.** Its tier-1 / tier-2 / rank-by-rank /
> OddDegree-CFI proofs are correct and load-bearing *as examples*, but the project **no longer
> recovers orbits class-by-class** (there are unboundedly many classes — that ladder stalls). The
> per-class results are now **witnesses** populating abstract predicates (`CascadesAt`,
> `EdgeGenerates`, `VisiblyRecoverable`) that the general theorems `theorem_2_HOR_of_edgeGenerates`
> / `theorem_2_HOR_of_pPolynomial` discharge for whole structural families — *the entire metric /
> distance-regular class (cycles, Johnson, Hamming, all DRGs) in one theorem*. Do **not** read the
> tier ladder or the §9 "remaining work" lists below as an open proof-obligation queue; read the
> de-classing doc for the current approach in full.

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

This doc is **the witness layer**, written as a chronological research/development
record. After the de-classing turn ([`chain-descent-declassing.md`](./chain-descent-declassing.md))
its per-class results are *examples populating abstract predicates*, **not** a plan. So
read selectively:

- **Live as witnesses (the lasting content).** §5–§6 (Theorem 1: CFI cascade depth
  ≤ tw(H), and the polynomial-cost corollary) and §14.2–§14.3 (Theorem 2 for schurian
  scheme graphs). These are the concrete facts that the general theorems
  `theorem_2_HOR_of_edgeGenerates` / `theorem_2_HOR_of_pPolynomial` and the abstract
  `CascadesAt` / `EdgeGenerates` / `VisiblyRecoverable` predicates are *witnessed by*.
- **Historical development record (read only for "how the witnesses were built").** §9
  (the multi-week CFI cascade M-phase grind and the Tier-2 rank ladder), §8 (open
  questions), §13 ("what's next"), §14.5/§14.7 (Tier-2 finalization gaps). Their
  "remaining work" / "next paper" / "open" phrasings are **superseded** — the metric/DRG
  family is now *one* theorem, and per-class recovery is the witness layer, not a queue.
- **Where the current plan actually lives.** Recovery + firing:
  [`chain-descent-declassing.md`](./chain-descent-declassing.md) (§6 the unified harvest,
  §9 the live frontier). The multi-step hidden-abelian case is *not* harvested within-cell
  (proved: `lockstep_disc_imp_stab_trivial`); it goes through the cross-branch
  stabilizer-chain object, [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md).

Nothing below is wrong; it is just *witness-level*, not *strategy-level*. When a section
says "open" or "next paper," cross-check the STATUS block of the doc it points to before
treating it as live.

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

## 8. Open questions

> **Witness-layer caveat (read §0).** These were open *within the per-class program*.
> The program itself was superseded by de-classing: Q5 (Tier-2 = depth-1) is **subsumed**
> (the metric/DRG family is one theorem, `theorem_2_HOR_of_pPolynomial`); Q1–Q4 (exact
> depth, gap dynamics, early-recovery classes, unbounded-tw) are **research curiosities
> about the witnesses**, not blockers for the current plan. The live frontier is
> [`chain-descent-declassing.md`](./chain-descent-declassing.md) §9.

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
This is strictly stronger than Tier 1's `k ≤ tw(H)` bound. *(Historical: Tier 2 was the next
paper-write target; it has since been **subsumed** — the metric/DRG family, schemes included, is one
theorem `theorem_2_HOR_of_pPolynomial`. See [declassing §3](./chain-descent-declassing.md).)*

---

## 9. Lean formalization status

> **Currency note.** This section is dated 2026-05-26. Tier-2 was since extended
> (2026-05-29) with the depth-2 / depth-3 layers and the relation-isolation
> bootstrap (`Depth2Det`, `theorem_2_HOR_concrete_intersectionSeparates`,
> `RelIsolatedAt`/`relIsolatedAt_succ`, `theorem_2_HOR_concrete_of_isolation`,
> `theorem_2_HOR_concrete_intersectionSeparates3` — covering rank-≥3/4 single-edge
> schurian schemes, e.g. C₇/C₉). Also note `refineStep`/`refineStep_iff` were
> concretized out of the axiom basis (2026-05-30): the basis is now
> `[propext, Classical.choice, Quot.sound]`. See
> [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md) for
> the authoritative, current theorem list.

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
  squeeze. Axiom-clean: depends only on the standard basis
  `[propext, Classical.choice, Quot.sound]`.

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

*Axiom-free* (standard basis `[propext, Classical.choice, Quot.sound]` only):
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
depends only on the standard basis
`[propext, Classical.choice, Quot.sound]` — no CFI-specific axioms used).

*Stage 4 / M3.A + M3.B — multi-seed cascade setup + lifted M2 —
DONE 2026-05-26.* `ChainDescent/CFI.lean` §13.8-§13.9:

- §13.8 / M3.A — Multi-seed setup:
  - `IsCFI'.allSeeds := Finset.univ.image h.seedVertex` — the cascade
    individualization set (one seed per base graph vertex).
  - `IsCFI'.seedVertex_injective` — different bases give different
    Fin n indices.
  - `IsCFI'.allSeeds_card : |allSeeds| = h.baseSize`.
  - `individualizedColouring_eq_iff_of_mem` — generic multi-seed
    uniqueness: for `v ∈ S`, `χ_S u = χ_S v ↔ u = v`. The engine for
    lifting M2 to the multi-seed colouring.
- §13.9 / M3.B — M2 lifted to multi-seed:
  - `IsCFI'.signature_endpoint_false_ne_true_allSeeds` and
  - `IsCFI'.refineStep_endpoint_false_ne_true_allSeeds` — the M2
    endpoint split, proved under `χ_{allSeeds}` instead of the
    single-seed colouring. Same witness tuple
    `(χ seed_v, 1, P endpoint_true seed_v)`; the multi-seed uniqueness
    lemma replaces the singleton uniqueness in the proof.

All M3.A + M3.B lemmas axiom-clean. The cascade individualization
witness for M4 is now constructible (`allSeeds`) and its size is bounded
(`= h.baseSize`).

*Stage 4 / M3.C — b=true endpoint inter-gadget distinction — DONE
2026-05-26.* `ChainDescent/CFI.lean` §13.2 / §13.4 (foundation) +
§13.10 (headline). The first genuinely **inter-gadget** cascade
lemma: under `χ_{allSeeds}`, one `refineStep` round gives b=true
endpoints at different gadgets distinct colours.

- §13.2 foundation: `CFIBase.cfiAdj_aEmpty_endpoint_diff_gadget` —
  `aEmpty v` is not adjacent to `endpoint hw b` when v ≠ v'.
- §13.4 foundation: `IsCFI'.adj_seed_endpoint_diff_gadget` and
  `adj_endpoint_seed_diff_gadget` at the Fin n level.
- §13.10 headline:
  - `IsCFI'.signature_endpoint_true_inter_gadget` — signatures of
    `e^1_{v→w}` and `e^1_{v'→w'}` differ when v ≠ v'.
  - `IsCFI'.refineStep_endpoint_true_inter_gadget` — refineStep
    propagates the signature difference.

Witness tuple (analogous to M3.B): `(c_v, 1, P endpoint_v seed_v)`.
Present in `e^1_{v→w}`'s signature (via adjacency to seed_v in the
same gadget); absent from `e^1_{v'→w'}`'s signature (seed_v is in a
different gadget; multi-seed uniqueness forces any witness u to be
seed_v, but `adj_endpoint_seed_diff_gadget` shows it's not adjacent).

**The corresponding b=0 case does NOT hold at round 1.** Neither
b=0 endpoint is adjacent to its own seed, so both signatures contain
`(c_v, 0, ?)` symmetrically and the round-1 multisets coincide
(for regular H with trivial P). b=0 inter-gadget distinction
requires multi-round bridge propagation (deferred).

All M3.C lemmas axiom-clean.

Combining M3.B + M3.C: at round 1 under `χ_{allSeeds}`, the partition
distinguishes
- each seed (singleton, from individualization);
- b=0 vs b=1 endpoints at the same gadget (M3.B);
- b=1 endpoints across different gadgets (M3.C).

Remaining at round 1: b=0 endpoints across gadgets, within-gadget
endpoints toward different partners, and subset vertices a_S^v for
S ≠ ∅. These all require multi-round bridge propagation.

*Stage 4 / M3.D Phase 1 — local bridge propagation step lemma —
DONE 2026-05-26.* `ChainDescent/CFI.lean` §13.2/§13.4 (bridge
prereqs) + §13.11 (step lemma). The inductive engine for the cascade:

- §13.2 / `CFIBase.cfiAdj_bridge` — `cfiAdj (endpoint hw b)
  (endpoint (sym hw) b) = 1` (bridge edge between gadgets v and w
  is in CFI(H)'s edge set).
- §13.4 / `IsCFI'.adj_bridge` — Fin n level via h.matching.
- §13.4 / `IsCFI'.endpointVertex_ne_bridge` — endpoint and its bridge
  partner are distinct Fin n vertices (proof: v ≠ w via loopless,
  then Sigma fst projection).
- §13.11 / `IsCFI'.signature_bridge_step` and
  `IsCFI'.refineStep_bridge_step` — given arbitrary colouring χ:
  - **Precondition (P1)** `hbridge`: bridge partners distinguished by
    χ.
  - **Precondition (P2)** `hno_match`: the bridge partner's colour
    doesn't accidentally appear at any adj=1 neighbour of the second
    endpoint.
  - **Conclusion**: refineStep χ distinguishes the original endpoint
    pair.

Witness tuple `(χ bp, 1, P ev bp)` — in `ev`'s signature via the
bridge partner u = bp (adj=1, χ matches); absent from `ev'`'s
signature by (P2). Proof structure identical to M2/M3.B/M3.C.

All M3.D Phase 1 lemmas axiom-clean (standard basis
`[propext, Classical.choice, Quot.sound]`).

*Stage 4 / M3.D Phase 2.0 + 2.1 — first cascade step beyond round 1 —
DONE 2026-05-26.* `ChainDescent/CFI.lean` §13.12 (structural helpers)
+ §13.13 (first concrete application).

§13.12 / Phase 2.0:
- `IsCFI'.adj_endpointVertex_eq_one_iff` — endpoint-endpoint
  adjacency iff `v_a = w_b ∧ w_a = v_b ∧ b_a = b_b` (the bridge
  condition).
- `IsCFI'.adj_seedVertex_eq_one_iff` — `adj u (seedVertex w) = 1
  iff u = endpointVertex hx true` for some `x ∈ N(w)`. Characterises
  exactly which vertices are adjacent to a seed (b=1 endpoints in
  the seed's gadget, no others).

§13.13 / Phase 2.1:
- `IsCFI'.refineStep_endpoint_true_intra_gadget_partner` — under
  `χ_1 = refineStep χ_{allSeeds}`, applying one more `refineStep`
  distinguishes b=true endpoints at the same gadget toward different
  partners.

Proof structure (validates Phase 1 + Phase 2 strategy):
- Apply `refineStep_bridge_step` with `χ = χ_1`.
- (P1) from M3.C: bridge partners `e^1_{w→v}, e^1_{w'→v}` at gadgets
  `w ≠ w'` are distinguished by `χ_1`.
- (P2) by signature-tuple argument:
  - Witness tuple `(χ_0 seed_w, 1, P bp seed_w)` in `bp`'s signature
    (via the bridge to own-gadget seed).
  - For any `u` adj=1 to `e^1_{v→w'}`: assume tuple in `u`'s
    signature, derive `adj u seed_w = 1`, use
    `adj_seedVertex_eq_one_iff` to force `u = endpointVertex hx
    true` at gadget `w`, use `adj_endpointVertex_eq_one_iff` on
    `adj e^1_{v→w'} u = 1` to force `w' = w` — contradicts `w ≠ w'`.

All Phase 2 lemmas axiom-clean.

*Stage 4 / M3.D Phase 2.3 — subset by gadget at round 2 — DONE
2026-05-26.* `ChainDescent/CFI.lean` §13.14-§13.17. The first cascade
step distinguishing **subset vertices** (parallel to Phase 2.1, which
handled endpoint-by-partner). Four sub-sections:

§13.14 / Phase 2.3 prereqs (subset vertex infra):
- `CFIBase.subset hS` — abstract subset vertex constructor for
  arbitrary even subsets (generalises `aEmpty v` from §13.1, which is
  the S=∅ case).
- `IsCFI'.subsetVertex hS` — Fin-n level extractor; `seedVertex v` is
  the empty-subset case.
- `subsetVertex_ne_endpointVertex` — distinctness (Sum-tag mismatch).
- `adj_subsetVertex_endpoint_same_gadget_true_of_not_mem` — Phase 2.3
  witness adjacency: subset_v has e^1_{v→w} as adj=1 neighbour when
  w ∈ N(v) \ S.
- `adj_subsetVertex_endpoint_diff_gadget` — cross-gadget non-adjacency.
- `adj_subsetVertex_eq_one_iff` — characterisation lemma (parallel to
  `adj_seedVertex_eq_one_iff` from §13.12; the S=∅ specialisation):
  `adj u (subsetVertex_{v'} hS') = 1` iff `u = endpointVertex hw' b'`
  at gadget v' with `(w' ∈ S') ⊕ b' = true`.

§13.15 / Phase 2.3 prereqs (M3.B+ general parity distinction):
- `signature_endpoint_b0_ne_b1_general_allSeeds` /
  `refineStep_endpoint_b0_ne_b1_general_allSeeds` — generalisation of
  M3.B from "same gadget" to "b=0 endpoint at any gadget v' vs b=1
  endpoint at gadget v are distinguished at round 1." Same witness
  tuple as M3.B+M3.C `(c_v, 1, P et seed_v)`; the absence argument
  case-splits v = v' (own-gadget) vs v ≠ v' (cross-gadget), both
  cases yielding `adj endpoint_b0 seed_v = 0`.

§13.16 / Phase 2.3 step lemma (factored Approach-3 primitive):
- `signature_subset_step` / `refineStep_subset_step` — generic step
  lemma for subset distinction. Parallel to `refineStep_bridge_step`
  (§13.11) for bridges. Takes arbitrary χ + preconditions:
  - `hwS`: w ∉ S (witness endpoint e^1_{v→w} is adj=1 to subset_v).
  - `hno_match`: χ-colour of e^1_{v→w} doesn't appear at any adj=1
    neighbour of subset_{v'}.
- Conclusion: refineStep χ distinguishes subset_v from subset_{v'}.
- This is the **Approach 3 primitive** for subset propagation —
  generic over χ, ready to apply at any cascade round once `hno_match`
  is verifiable. The 3+5 factoring promised in the original plan.

§13.16.5 / supporting helper:
- `IsCFI'.adj_symm` — `adj.adj i j = adj.adj j i` for CFI graphs, via
  `h.matching` + `cfiAdj_symm`. Reconciles the signature convention
  (subject-on-left) with the iff convention (candidate-on-left).

§13.17 / Phase 2.3 headline:
- `signature_subset_inter_gadget_round2` /
  `refineStep_subset_inter_gadget_round2` — under χ_1 = refineStep
  χ_{allSeeds}, one more refineStep distinguishes subset vertices at
  different gadgets (v ≠ v'), assuming the LHS subset has a witness
  w ∈ N(v) \ S.

Proof structure (Phase 1 + Phase 2 architecture, subset variant):
- Apply `refineStep_subset_step` with χ = χ_1.
- (P2 / hno_match): for any u adj=1 to subset_{v'} hS',
  `χ_1 u ≠ χ_1 (e^1_{v→w})`.
  - Swap convention via `adj_symm`, apply `adj_subsetVertex_eq_one_iff`
    to characterise u as `endpointVertex hw'' b''` at gadget v'.
  - Case b'' = false: M3.B+ (§13.15) gives the distinction.
  - Case b'' = true: M3.C (§13.10) gives the b=1 inter-gadget
    distinction (with hvv.symm to flip direction).

**Hypothesis qualifier.** The `w ∈ N(v) \ S` precondition (equivalently
S ≠ N(v)) is essential — for deg-even bases (e.g., Rook3x3), the
degenerate case S = N(v) has no b=1 adjacent endpoint, hence no witness
of this form. That degenerate subset is deferred to a later cascade
round once Phase 2.2 makes b=0 endpoints distinguishable by gadget
(unlocking a parallel "subset step lemma" using b=0 endpoint witnesses).

All Phase 2.3 lemmas axiom-clean (standard basis
`[propext, Classical.choice, Quot.sound]` only; no CFI-specific axioms used).

*Stage 4 / M3.D Phase 2.2 — b=0 endpoint inter-gadget at round 3 —
DONE 2026-05-26.* `ChainDescent/CFI.lean` §13.18-§13.20. Distinguishes
b=0 endpoints at different gadgets through a direct signature-tuple
argument at χ_2, using subset structure (not bridge step, since b=0
bridge partners aren't distinguished early). Three sub-sections:

§13.18 / Phase 2.2 prereq (M3.B++):
- `adj_subsetVertex_seedVertex` — subset-subset adj=0 helper.
- `signature_subsetVertex_ne_endpoint_true_allSeeds` /
  `refineStep_subsetVertex_ne_endpoint_true_allSeeds` — generalises
  M3.B from "same gadget" to "subset vertex (any gadget, any T) vs
  b=1 endpoint at gadget v" at round 1. Even cleaner than M3.B+:
  multi-seed forces u = seed_v, but subsets aren't adjacent to any
  subset (including seeds), contradiction.

§13.19 / Phase 2.2 prereq (cross-type at χ_2):
- `signature_subsetVertex_ne_endpoint_false_round2` /
  `refineStep_subsetVertex_ne_endpoint_false_round2` — at χ_2,
  subset with witness `x ∈ N(v) \ S` vs b=0 endpoint (any gadget)
  have distinct colours. Witness tuple `(χ_1 (e^1_{v→x}), 1, ?)`.
  Case analysis on u adj=1 to b=0 endpoint:
  - u = subset at gadget v_f containing w_f: M3.B++ rules out.
  - u = bridge partner: M3.B+ rules out.

§13.20 / Phase 2.2 headline:
- `signature_endpoint_false_inter_gadget_round3` /
  `refineStep_endpoint_false_inter_gadget_round3` — at round 3 under
  χ_{allSeeds}, b=0 endpoints at v ≠ v' get distinct colours, given
  a witness subset `a_S^v` with w ∈ S and x ∈ N(v) \ S.

Proof structure (signature-tuple at χ_2):
- Witness `(χ_2 (a_S^v), 1, P (e^0_{v→w}) (a_S^v))`.
- (a) In e^0_{v→w}'s χ_2-signature: via u' = a_S^v (w ∈ S adjacency).
- (b) Not in e^0_{v'→w'}'s χ_2-signature: case on u adj=1 to e^0_{v'→w'}.
  - u = subset at v' containing w': Phase 2.3 (§13.17) with our LHS
    subset's witness x rules out.
  - u = bridge partner (b=0 at gadget w'): cross-type (§13.19) rules
    out.

**Hypothesis qualifier**: The witness (S, x) with w ∈ S and x ∈ N(v) \ S
requires `deg(v) ≥ 3` (so a 2-element even subset {w, y} with y ≠ x
exists). For `deg(v) = 2`, no such witness — Phase 2.2 as stated
doesn't apply. That degenerate case needs a separate argument (more
cascade rounds via subset propagation through neighbouring gadgets).

All Phase 2.2 lemmas axiom-clean (standard basis
`[propext, Classical.choice, Quot.sound]` only; no CFI-specific axioms used).

*Stage 4 / Phase 2.X + Phase 2.4 + M4 — DONE 2026-05-26 (OddDegree
class).* `ChainDescent/CFI.lean` §13.21-§13.24 plus a new corollary.
The full cascade discharged for CFI graphs over odd-degree base graphs.

§13.21 — OddDegree predicate + witness helpers:
- `IsCFI'.OddDegree h := ∀ v, h.H.degree v % 2 = 1`.
- `exists_witness_of_oddDegree` — under OddDegree, every even subset
  `S ⊆ N(v)` has a non-element `y ∈ N(v) \ S` (since `|S|` even and
  `deg(v)` odd implies `S ⊊ N(v)`).
- `exists_phase22_witness` — under OddDegree, for any `v ∈ N(w)`,
  build an even subset `{v, x_other} ⊆ N(w)` with `v` inside and a
  third element `x ∈ N(w) \ {v, x_other}` (uses `deg(w) ≥ 3` which
  follows from odd + `deg_ge_two`).

§13.22 — Phase 2.X: b=0 within-gadget partner at round 4:
- `refineStep_endpoint_false_intra_gadget_partner_round4` —
  analogous to Phase 2.1 but uses `refineStep_bridge_step` at χ_3.
  - (P1): bridge partners (b=0 at gadgets w ≠ w') distinguished by
    χ_3 via Phase 2.2 (witness at gadget w via OddDegree).
  - (P2): for `u` adj=1 to e^0_{v→w'}, case-split:
    - u = subset at v: cross-type round-2 lifted to χ_3 (via
      OddDegree witness for the subset).
    - u = bridge partner = e^0_{w'→v}: Phase 2.2 with the gadgets
      swapped (witness at gadget v_e = w' via OddDegree).

§13.23 — Phase 2.4: subset by S at same gadget at round 5:
- `refineStep_subset_intra_gadget_S_round5` — direct signature-tuple
  argument at χ_4. Hypothesis: `y ∈ S, y ∉ S'` (a symmetric
  difference witness). Witness tuple `(χ_4 (e^0_{v→y}), 1, ?)`.
  - (b) case-split on u adj=1 to subset_v hS' via
    `adj_subsetVertex_eq_one_iff`:
    - b=false: u = e^0_{v→x} for x ∈ S' \ {y}, distinguished from
      e^0_{v→y} via Phase 2.X.
    - b=true: u = e^1_{v→x}, distinguished from e^0_{v→y} via M3.B+
      lifted χ_1 → χ_4 by a 3-step `refineStep_iff` chain.

§13.24 — Iteration helpers + **M4** (cascade discharge):
- `refineStep_iter_le_eq` — equal at iter[k+d] implies equal at
  iter[k] (refinement split-only across iterations).
- `warmRefine_eq_iter_eq` — `warmRefine` equality (iter[n]) gives
  iter[r] equality for r ≤ n.
- **`cfi_cascades_polynomially_oddDeg`** — discharges the Tier-1
  cascade axiom under (`OddDegree`, `5 ≤ n`). Witness S = allSeeds;
  `Discrete (warmRefine ...)` proved via case analysis on h.e i, h.e j
  with 10 sub-cases:
  - subset/subset (same gadget): Phase 2.4 (round 5).
  - subset/subset (diff gadget): Phase 2.3 (round 2).
  - subset/endpoint (b=true): M3.B++ (round 1).
  - subset/endpoint (b=false): cross-type round-2 (round 2).
  - endpoint/endpoint, parity mismatch: M3.B+ (round 1).
  - endpoint/endpoint, b=true, same gadget: Phase 2.1 (round 2).
  - endpoint/endpoint, b=true, diff gadget: M3.C (round 1).
  - endpoint/endpoint, b=false, same gadget: Phase 2.X (round 4).
  - endpoint/endpoint, b=false, diff gadget: Phase 2.2 (round 3).
- **`theorem_1_HOR_cfi_oddDeg`** — the **axiom-free** CFI form of
  Theorem 1 for OddDegree H. No CFI placeholder axioms in its
  dependency closure (only the standard basis
  `[propext, Classical.choice, Quot.sound]`).

**Axiom budget for Tier 1 (OddDegree subclass): 0 placeholders.**
`theorem_1_HOR_cfi_oddDeg` discharges `cfi_cascades_polynomially`
directly via constructive proof. The original axiom remains for the
general (non-OddDegree) case; future-work to fully discharge.

**Hypothesis qualifier: `5 ≤ n` (DISCHARGED 2026-05-26).** Previously
required by `warmRefine_eq_iter_eq` when applying Phase 2.4 (round 5).
Now derived inside `cfi_cascades_polynomially_oddDeg` via the
base-size dichotomy: `h.m = 0 → n = 0` (vacuous cascade with `S = ∅`)
or `h.m ≥ 1 → 6 ≤ n` (from `six_baseSize_le`). The dichotomy needs
only the existing `card_CFIVertex` and `six_baseSize_le` connectors,
not the deeper OddDegree → baseSize ≥ 4 chain originally
anticipated. `theorem_1_HOR_cfi_oddDeg` no longer carries an `hn_ge_5`
parameter.

*Stage 4 / general-degree case + saturated subsets (PENDING, future
work):*
- Drop OddDegree hypothesis. Saturated subsets `S = N(v)` arise for
  even-degree base vertices. These need additional cascade rounds
  via subset propagation through neighbouring gadgets.
- Discharge `5 ≤ n` from OddDegree automatically.
- M3.E: cross-type distinctions for the remaining cases (currently
  inlined in M4's case analysis; may benefit from factoring).

*Stage 4 / M3.C-M3.E + M4 (PENDING, multi-week):* the remaining M3
content + cascade assembly. **Note:** initial planning assumed the
inter-gadget endpoint distinction would hold at round 1 — this is
**not generally true** (a b=0 endpoint at gadget v has the same
signature as a b=0 endpoint at gadget v' for many base graphs, if P
is trivial). The cascade requires multi-round bridge propagation,
which requires careful invariant design. Realistic decomposition:
- M3.C — Per-CFI-vertex-type signature classification under
  `χ_{allSeeds}`: catalogue what the signature multiset looks like
  for each (seed, non-seed subset, b=0 endpoint, b=1 endpoint).
- M3.D — Bridge propagation step lemma: distinction at bridge
  partner pair at round `r` ⟹ distinction at original pair at
  round `r+1`. The inductive engine.
- M3.E — Subset vertex distinction: `a_S^v` vs `a_{S'}^v` split by
  S, via endpoint-adjacency pattern differences.
- M4 — Assemble all of M3 with multi-round induction on
  `refineStep` to prove `warmRefine adj P χ_{allSeeds}` is
  `Discrete`. Discharges `cfi_cascades_polynomially`.

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

**Update — Tier 2 discharged concretely, no axioms (2026-05-27 →
2026-05-29).** The Tier-2 Fact-A axiom (`schurian_scheme_profile_exists`)
is no longer the route: a concrete predicate `IsSchurianSchemeGraph'`
plus a Lean proof of Step 2 (`Step2_target`) now give `theorem_2_HOR`
**unconditionally** (axiom-clean: only the standard basis
`[propext, Classical.choice, Quot.sound]`) for a growing class, in
[`ChainDescent/Scheme.lean`](../GraphCanonizationProofs/ChainDescent/Scheme.lean):

- **Depth-1 convergence (2026-05-27).** Step 2 reduces to a depth-2
  recursive partition `schemePart_at`; the substantive inductive
  refinement `iter_refines_schemePart_at` is proved, and convergence at
  depth 1 (`step2_converges_at_one_of_det`) discharges `rank ≤ 2 ∧ |J|=1`
  — covering Petersen / Kneser `K(5,2)` / Johnson `J(5,2)`
  (`theorem_2_HOR_concrete_rank_two_J_singleton`).
- **Depth-2 convergence (2026-05-29).** §10.9 adds the depth-2 layer
  (`Depth2Det`, `step2_converges_at_two_of_det2`) mirroring the depth-1
  chain. §10.10 discharges it abstractly via `IntersectionSeparates`
  (`intersectionNumber j0 j0 ·` separating the non-edge relations):
  `theorem_2_HOR_concrete_intersectionSeparates` covers the first
  genuinely rank-≥-3 single-edge schemes — where adjacency-to-`v` alone
  cannot separate the relations (depth-1 insufficient) but the
  common-edge-neighbour count does (depth-2 sufficient). The 7-cycle
  scheme is the smallest instance. Strictly subsumes the rank-2/`|J|=1`
  case.

- **Relation-isolation bootstrap (2026-05-29).** §10.11 generalises the
  depth-1/depth-2 results into one mechanism. `RelIsolatedAt G P v k l`
  says relation `l`'s `schemePart_at k` class is exactly its block `R_l`.
  The edge relation is isolated at depth 1 (`relIsolatedAt_one_j0`); the
  bootstrap `relIsolatedAt_succ` isolates a further relation at depth
  `k+1` once its intersection counts into the already-isolated relations
  pin it (`isolatedCount_eq` is the reusable counting heart); isolation
  is monotone (`relIsolatedAt_mono`). When every relation is isolated by
  some depth `k`, Theorem 2 follows (`theorem_2_HOR_concrete_of_isolation`).
  The depth-2 `IntersectionSeparates` result is the `Iso = {j0}` instance;
  `theorem_2_HOR_concrete_intersectionSeparates3` chains one round further
  (a depth-2-isolated anchor `l0`) to reach rank-≥-4 schemes like the
  9-cycle, where depth-2 alone cannot split the distance-3/4 relations.

Open: full general convergence `Step2_converges_at … (rank+1)` (the
coherent-algebra intersection-matrix full-rank theorem) — now cleanly
restated as *"every relation eventually isolates"* (an isolation chain
exists); and no concrete scheme is constructed in Lean (all results take
`IsSchurianSchemeGraph'` as hypothesis, matching the abstract style).

> **Update (2026-06-02) — the rank ladder is closed for the metric class
> (the "de-classing" pivot).** Rather than discharge convergence rank-by-rank,
> the general engine is now built (axiom-clean, `[propext, Classical.choice,
> Quot.sound]`; full build green). **Strategy:** stop the per-rank ladder; prove
> *non-class-specific* convergence once. **Progress:**
> - `ChainDescent/Saturation.lean` (NEW, Mathlib-only): generic
>   `exists_iterate_isFixed_within` — an extensive `Finset` operator saturates
>   to a fixpoint within `|B| − |s₀|` rounds. The reusable engine (also the
>   Leg-A support-induction skeleton).
> - `Scheme.lean §10.12`: `isolationStep` (closure round), `EdgeGenerates`
>   (closure of `{R₀,R_{j0}}` reaches every occurring relation),
>   **`theorem_2_HOR_of_edgeGenerates`** — one uniform theorem; the old
>   `…rank_two`/`…intersectionSeparates`/`…Separates3` are now special cases.
> - `Scheme.lean §10.13`: `PPolynomial` (metric/distance-regular predicate),
>   **`theorem_2_HOR_of_pPolynomial`** — **the entire metric/DRG family (cycles,
>   Johnson, Hamming, all DRGs) in one theorem**, no per-scheme separation data.
>
> **Honest scope:** unconditional "all schurian schemes converge" is *false*
> (imprimitive schemes deadlock — correctly: 1-WL doesn't recover their orbits).
> `EdgeGenerates` is the exact necessary condition; `PPolynomial` the clean
> structural sufficient one. **Next:** this is the rehearsal for **Leg A** —
> `EdgeGenerates` is a concrete **D1** instance, `PPolynomial` a *graded* D1, and
> the saturation engine transplants to Leg A's support induction
> ([harvest-window](./chain-descent-harvest-window.md) gap 3). Full doc/index
> update deferred; authoritative state is the Lean sources.

**Tier-3 connection (flagged 2026-05-29).** The isolation bootstrap is a
concrete model of the (O\*) **self-detection** lemma that the Tier-3
decomposability plan ([`chain-descent-tier3-decomposability.md`](./chain-descent-tier3-decomposability.md)
§8.1) hunts for: *structure that obscures a hidden symmetry is itself
detectable, and detecting it exposes the symmetry.* Here the edge
relation is "free" (adjacency reveals it at depth 1) and every other
relation becomes detectable **only by counting into already-detected
ones** — detection bootstraps, monotonically. The "isolation chain
exists" condition is the operational form of "residue is rigid / all
symmetry unconditional" (the deferred-decisions framing). A scheme with a
relation that *never* isolates would be a concrete obstruction — exactly
the object Tier 3 / the construction question seeks.

**Lean idioms / gotchas (CFI/Scheme proofs).** Developer time-savers
collected while formalizing the above — proof-engineering notes, not
research claims:

- `subst` is unreliable on equations; prefer `rw`. In particular,
  `subst hva` on `hva : v = a` *eliminates* the parameter — use
  `rw [hva]` instead to keep `a, b` in scope.
- `Classical.decPred` to get a `Decidable` instance on recursive `Prop`s.
- `▸` (the rewrite arrow) fails on dependent motives — fall back to an
  explicit `rw`/`cases`.
- Watch `Finset.sum_const_nat` (the constant-summand simp lemma).
- `cases hc : σ.σ x x` substitutes the value into the goal; close the
  unknown branch with `rfl`.

(The `Set.ncard ↔ Finset.filter` card bridge is covered above under §14's
`ncard_setOf_eq_filter_card`.)

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

## 13. What's settled and what's next

> **Witness-layer caveat (read §0).** "Settled" below is current (these are the witnesses).
> The "**Next**" list is the **historical** per-class plan (sketch Tier-2 paper, discharge
> Fact-A axioms, Tier-3) — **superseded** by de-classing: the metric/DRG class is now one
> theorem and the tier ladder is the witness layer. For what is actually next, see
> [`chain-descent-declassing.md`](./chain-descent-declassing.md) §9 and
> [`chain-descent-schreier-sims.md`](./chain-descent-schreier-sims.md).

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

**Full Tier 2 Lean discharge plan written 2026-05-26:** see
[`chain-descent-tier2-lean-plan.md`](./chain-descent-tier2-lean-plan.md)
for the phase-by-phase build order (T2.1 association-scheme
infrastructure → T2.2 v-profile + Step 1 → T2.3 Step 2 intersection
numbers → T2.M4 assembly). Catalogues what transfers from Tier 1's
OddDegree discharge (notably the iteration helpers
`refineStep_iter_le_eq` / `warmRefine_eq_iter_eq` and the Approach-3
step-lemma pattern), what's fully new (association schemes don't
exist in Mathlib), and gives a ~9-12 day effort estimate.

**Tier 2 Lean execution — T2.1 STARTED 2026-05-26.** New module
[`ChainDescent/Scheme.lean`](../GraphCanonizationProofs/ChainDescent/Scheme.lean)
(default build target). Iteration helpers relocated to
`ChainDescent.lean §16.4` (axiom-clean, tier-agnostic).

*Stage T2.1.a (AssociationScheme structure):* `AssociationScheme n`
structure with fields `rank`, `rel : Fin (rank+1) → Fin n → Fin n →
Bool`, `rel_zero_iff_eq` (diagonal), `rel_symm`, `rel_partition`
(`∃!` per pair), `intersectionNumber`, and `intersectionNumber_well_defined`
(the load-bearing axiom). Plus `relOfPair`, `rel_relOfPair`,
`relOfPair_unique`, `rel_iff_relOfPair`, `relOfPair_symm`,
`relOfPair_self`, `relOfPair_eq_zero_iff` helpers.

*Stage T2.1.b (scheme automorphisms + SchurianScheme):* `IsSchemeAut
S π` predicate (π preserves every relation), with `refl`/`trans`/`symm`
group structure and `relOfPair_eq` (scheme-Aut preserves relOfPair).
`SchurianScheme n` extends `AssociationScheme` with the `schurian`
field — any two pairs in the same relation are connected by some
scheme-Aut.

*Stage T2.1.c (smoke test):* `trivialScheme : AssociationScheme 1`
and `trivialSchurianScheme : SchurianScheme 1` (single-vertex scheme,
identity-only Aut). Confirms structures are inhabited.

All T2.1 declarations axiom-clean (only `propext`, `Classical.choice`,
`Quot.sound`).

*Stage T2.2 — DONE 2026-05-26.* §4 of `Scheme.lean`. Defines
`vProfile (S : AssociationScheme n) (v : Fin n) : Colouring n`
(noncomputable) with helpers `vProfile_self`, `vProfile_eq_iff`,
`vProfile_eq_zero_iff`, `vProfile_ne_self_of_ne` (matches
`SchemeProfile.v_singleton`). `SchemeOrbitPartition` (v-stabilized
scheme-Aut orbit) with refl/symm/trans. Step 1's algebraic core:
`vProfile_aut_invariant` (forward via `IsSchemeAut.relOfPair_eq`),
`SchurianScheme.vProfile_eq_imp_schemeOrbit` (reverse via the
`schurian` field), and the combined `vProfile_iff_schemeOrbit`.

*Stage T2.3 infrastructure — DONE 2026-05-26.* §5-§7 of `Scheme.lean`.
- **§5 — `SchemeGraph`**: `scheme + J + zero_notMem_J` structure,
  derived `adj : AdjMatrix n` (noncomputable), plus `adj_eq_one_iff`,
  `adj_eq_zero_iff`, `adj_self`, `adj_symm`, `adj_eq_zero_or_one`.
- **§6 — `SchurianSchemeGraph`**: extends `SchemeGraph` with two
  schurian fields w.r.t. graph-Aut (`schurian_transitive` and
  `isAut_imp_isSchemeAut`). Provides `relOfPair_aut_eq` and
  `vProfile_aut_invariant` in graph-Aut terms.
- **§7 — Step 1 in graph-Aut terms**: `GraphOrbitFixing adj v w u`
  predicate (refl/symm/trans). Headlines
  `vProfile_eq_imp_graphOrbit` (forward, uses `schurian_transitive`),
  `graphOrbit_imp_vProfile_eq` (reverse, uses
  `isAut_imp_isSchemeAut`), and the combined
  `vProfile_iff_graphOrbit`. This is the
  `SchemeProfile.profile_iff_orbit`-shaped statement, modulo the
  P-preservation bridge (which collapses when `P` is
  permutation-invariant).

All T2.2 + T2.3 prerequisites axiom-clean.

*Stage T2.3 / Step 2 — S2.a DONE 2026-05-27.* §8.a of `Scheme.lean`
(~70 lines, axiom-clean). The **round-1 lemma**: for any `adj, P`
and any `v`, if `refineStep adj P χ_v w = refineStep adj P χ_v u`
for `w, u ≠ v`, then `adj w v = adj u v` (and `P w v = P u v`).

Three forms exported:
- `refineStep_round1_pair_eq`: both adj and P conjuncts (the full
  multiset-tuple match content).
- `refineStep_round1_adj_eq`: adj-only specialisation.
- `SchemeGraph.refineStep_round1_J_eq`: scheme-specific form —
  round-1 equality implies same J-class membership of `relOfPair v ·`.
  This is the round-1 "vProfile coarsening" used by downstream S2.b.

Plus helper `individualizedColouring_singleton_eq_v_iff` (a
tier-agnostic `χ_v u = χ_v v ↔ u = v` lemma).

**Next** (deferred to future session): S2.b (inductive step via
intersection numbers), S2.c (convergence at depth `≤ rank + 1`),
S2.d (lift via `warmRefine_eq_iter_eq`). Then T2.M4 (SchemeProfile
constructor + P-preservation bridge + discharge
`schurian_scheme_profile_exists`). Full plan in
[`chain-descent-tier2-lean-plan.md`](./chain-descent-tier2-lean-plan.md)
§7.

*Stage T2.3 / Step 2 — §8.b infrastructure + count bridge +
partial result DONE 2026-05-27.* ~280 lines, axiom-clean. Three
layers:

- **§8.b.1 — iteration framework:** `iter_succ_eq_iff` (round-by-
  round unfolding), `AssociationScheme.intersectionCount_via_w`
  (scheme-axiom packaging), `Step2_target` def naming the eventual
  full claim. Plus `iterSignature` and the trivial corollary
  `intersectionCount_eq_of_vProfile_eq`.
- **§8.b.2 — count bridge:** `signature_count_eq_card` and the
  general `signature_countP_eq_card` (Multiset.count → Finset.card
  via `Multiset.count_map` + `Finset.filter_val` +
  `Finset.filter_filter`). Plus the count-equality consequences:
  `signature_eq_card_eq`, `signature_eq_countP_eq`,
  `iter_succ_count_eq`, `iter_succ_countP_eq`,
  `iter_succ_colour_count_eq`. The workhorse for the inductive
  step.
- **§8.b.3 — partial Step 2:** `iter_succ_adj_eq` (S2.a lifted to
  any depth ≥ 1 via `refineStep_iter_le_eq`), `warmRefine_adj_eq`
  (warmRefine version), and **`SchurianSchemeGraph.warmRefine_J_eq`**
  — the first concrete partial Step 2 theorem: warmRefine cells
  refine the J-class partition of `vProfile`. (Coarsest non-trivial
  vProfile refinement; the full Step 2 keeps refining via
  intersection numbers until reaching `vProfile` itself.)

**Remaining for full Step 2 (rank ≥ 2):** the recursive partition Π_k
beyond J-class for general schurian schemes. Either (i) abstract
Setoid-valued Π_k with inductive refinement proof, or (ii) direct
induction on "iter[k] χ_v refines partition by intersection-number-rows
up to depth k" using `intersectionCount_via_w`. Decide at next session.

*Stage T2.M4 — full SchemeProfile constructor + concrete predicate +
trivial/rank-1 instances DONE 2026-05-27.* §9 of `Scheme.lean`
(~250 lines, axiom-clean):

- **`SchurianSchemeGraph.toSchemeProfile`**: SchemeProfile
  constructor taking `(G, P, v, hP_invariant, hStep2)`. The
  P-invariance hypothesis bridges `GraphOrbitFixing` to
  `OrbitPartition adj P {v}` (drops the P-preservation conjunct
  to/from the orbit predicate). Step2 hypothesis populates the
  `warm_refines_profile` field.
- `trivialPMatrix` + `trivialPMatrix_invariant`: the all-`unknown`
  PMatrix is trivially permutation-invariant, so `toSchemeProfile_trivialP`
  needs only the Step2 hypothesis.
- **`IsSchurianSchemeGraph'`**: concrete predicate replacing the
  abstract `IsSchurianSchemeGraph` axiom from `ChainDescent.lean §18`.
  Bundles `(G : SchurianSchemeGraph, matching : G.adj = adj)`.
- **`theorem_2_HOR_concrete`**: the `theorem_2_HOR`-shaped statement
  derivable from `IsSchurianSchemeGraph'` + P-invariance + Step2,
  matching `ChainDescent.lean §18`'s assembly form.
  `theorem_2_HOR_concrete_trivialP`: trivial-P specialisation.

**End-to-end unconditional Theorem 2 instances** (no remaining
"open piece" for these cases):
- **`theorem_2_HOR_trivial`** (§9.3): trivial 1-vertex scheme.
  First fully discharged Theorem 2 instance — validates the
  architecture end-to-end.
- **`step2_of_rank_le_one`** + **`theorem_2_HOR_concrete_rank_le_one`**
  (§9.4): all schurian scheme graphs with `rank ≤ 1` (covers
  `K_n` with `J = {1}`). Proof: case-split on (w = v, u = v); the
  inductive intersection-number argument isn't needed when vProfile
  has at most 2 values.

*Stage T2.3 / Step 2 inductive step + convergence framework — DONE
2026-05-27.* §10 of `Scheme.lean` (~280 lines, axiom-clean).
**Major milestone**: the technical heart of Step 2's intersection-
number induction is now proved.

- **`Step2_at_depth G P v k`** + **`step2_of_step2_at_depth`**:
  framework lifting depth-k discharge to `Step2_target`.
- **`schemePart_at G P v k`** (noncomputable): recursive partition
  predicate. Equivalence (refl/symm/trans).
- **`iter_refines_schemePart_at` (PROVED)** — `iter[k] χ_v`
  partition refines `schemePart_at G P v k` for every `k`. The
  substantive inductive step. Proof via `iter_succ_eq_iff` +
  `signature_eq_countP_eq` + the inductive-hypothesis-derived
  equivalence "schemePart_at k u' w' ↔ ∃ x, iter[k] x = iter[k] u'
  ∧ schemePart_at k x w'".
- **`Step2_converges_at G P v k`**: convergence statement (the
  single remaining content piece).
- **`step2_of_converges_at`**: assembles convergence + the
  inductive step into `Step2_target`.

**The Tier 2 architecture is now complete except for the
convergence claim.** Once `Step2_converges_at G P v (rank+1)` is
proved for schurian schemes (classical coherent algebra content),
every schurian scheme graph gets a fully unconditional
`theorem_2_HOR_concrete` instance.

*Convergence at depth 1 — DONE 2026-05-27.* The Set.ncard
restructure landed and unblocked the depth-1 extraction.
§10.5-§10.8 of `Scheme.lean` (~280 lines, axiom-clean).

- §10.1 (revised) — `schemePart_at` now uses
  `Set.ncard {u' | ...}` instead of `(Finset.univ.filter ...).card`,
  sidestepping the `Decidable` instance bridging issue. Bridge
  lemma `ncard_setOf_eq_filter_card` (Set.ncard ↔ Finset.filter.card
  under a DecidablePred) does the connecting work.
- §10.3 (`iter_refines_schemePart_at`) re-proved cleanly against
  the new definition.
- §10.5 — **`schemePart_at_one_to_v`** (the originally-blocked
  depth-1 extraction, now proved): for `w, u ≠ v`,
  `schemePart_at G P v 1 w u → adj w v = adj u v ∧ P w v = P u v`.
- §10.6 — **`RelOfPairDetByAdjP`** depth-1 separation predicate,
  plus **`step2_converges_at_one_of_det`** (Step 2 convergence at
  depth 1 under depth-1 separation).
- §10.7 — **`theorem_2_HOR_concrete_of_det`**: end-to-end
  unconditional Theorem 2 given depth-1 separation.
- §10.8 — Cleaner reformulation as `AdjSeparatesRelations` (`(· ∈ J)`
  injective on non-diagonal relations), with the rank-2 + |J|=1
  instance: **`adjSeparates_of_rank_two_J_singleton`** and the
  headline **`theorem_2_HOR_concrete_rank_two_J_singleton`** —
  unconditional Theorem 2 for Petersen / Kneser `K(5,2)` /
  Johnson `J(5,2)` (and any other rank-2 schurian scheme graph
  with `|J| = 1`).

**Coverage delivered:** Theorem 2 is now unconditional for all
schurian scheme graphs with `rank ≤ 2 ∧ |J| ≤ 1` (or `|J| ≥ rank`).
This covers all the small classical examples enumerated in §7's
empirical landscape — Petersen and J(5,2) match here, K_n is in
`rank ≤ 1`. Higher-rank schemes (Hamming `H(2, 3)`, Johnson
`J(m, k)` for `k ≥ 3`) still need deeper convergence — depth 2+
via intersection-number reasoning, sketched in §10.6 docs but
left to a follow-on session as a per-scheme strengthening.

All new lemmas axiom-clean (standard basis
`[propext, Classical.choice, Quot.sound]`; no scheme-specific axioms).

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

*(Historical framing.)* Once G1–G4 and G7 had explicit paragraphs, Theorem 2 would be
**paper-finalized**. **Superseded:** the per-class Theorem-2 paper goal is replaced by the de-classing
result `theorem_2_HOR_of_pPolynomial` (the whole metric/DRG family in one theorem); the material below
stands as the witness-layer record. See [declassing §3](./chain-descent-declassing.md).

**Note on the Tier 1 / Tier 2 contrast:**

Tier 1 needed `≤ tw(H)` individualizations because CFI graphs are
specifically constructed to defeat 1-WL — the gauge structure hides
orbits behind cycle-space obstacles that only `tw(H)` individualizations
can resolve. Tier 2 graphs (scheme graphs) have no such obstacles — the
scheme's algebraic structure is exactly what 1-WL is good at capturing.

This is the **algebraic / non-algebraic split** in disguise: schemes
are algebraic, CFI is non-algebraic (the gauge action is what makes
CFI an obstacle to algebraic methods).
