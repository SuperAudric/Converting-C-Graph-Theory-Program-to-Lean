# Tier 2 Lean formalization plan — schurian scheme orbit recovery

Plan for discharging the remaining Tier 2 axioms in Lean. Written after
Tier 1's OddDegree cascade was fully discharged (2026-05-26); collects
the Tier 2 state, what carries over, what is fully new, and a
phase-by-phase build order so a reader can pick up and execute.

---

## 1. Context

**Theorem 2 (paper, orbit-recovery doc §14.2):** Let `G = (V, E)` be a
scheme graph for a vertex-transitive **schurian** association scheme
`S = (R_0, …, R_d)` with `E = ⋃_{j ∈ J} R_j`. Then for any single
fresh-colour individualized vertex `v ∈ V`, 1-WL refinement on `(G, v)`
produces a partition equal to `Aut(G)_v`-orbits.

Headline contrast with Tier 1: **depth 1 always suffices** for Tier 2
(vs. `≤ tw(H)` for Tier 1). Scheme graphs are algebraically regular —
1-WL captures the scheme's coherent algebra in one round.

**Why this matters:** Tier 2 subsumes Piece C of
[`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)
and covers Johnson, Hamming, distance-transitive DRGs in one statement.

**Paper status:** Theorem 2's proof is paper-rigorous in
[`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md)
§14.3. Empirical G6 (depth-1 verification on Petersen and J(5,2)) is
done — both pass cleanly.

---

## 2. Current Lean state

Lives in [`ChainDescent.lean`](../GraphCanonizationProofs/ChainDescent.lean)
§18 (lines ~3766-3924). Two layers:

### 2.1 Assembly (already in place, axiom-clean)

- **`SchemeProfile adj P v`** (§18.1) — a `structure` bundling four
  fields:
  - `profile : Colouring n` — the v-profile colouring.
  - `v_singleton` — v is alone in its profile class.
  - `profile_iff_orbit` — Step 1 field: profile classes = `Aut_v` orbits.
  - `warm_refines_profile` — Step 2 field: 1-WL on `(G, v)` refines profile.
- **`SchemeProfile.warm_iff_profile`** — derived squeeze: 1-WL =
  profile via composing Step 2 with §16.3's trivial direction +
  Step 1.
- **`theorem_2_HOR_of_profile`** — Theorem 2 conclusion given a
  `SchemeProfile` witness. Proof is one line: chain the two
  bidirectional fields.

All four assembly items are **axiom-clean** (only `propext`,
`Classical.choice`, `Quot.sound`).

### 2.2 Axiomatic content (to be discharged)

- **`IsSchurianSchemeGraph`** — abstract Prop axiom. Placeholder for
  "this graph admits a vertex-transitive schurian association scheme
  containing its edge relation."
- **`schurian_scheme_profile_exists`** — Tier-2 Fact-A-shaped
  existence axiom. Given `IsSchurianSchemeGraph adj` and any vertex
  `v`, asserts `Nonempty (SchemeProfile adj P v)`.
- **`theorem_2_HOR`** — unconditional Theorem 2, currently conditional
  on the two axioms above.

**Goal of this plan:** discharge `schurian_scheme_profile_exists` by
constructively producing a `SchemeProfile` for any schurian scheme
graph + vertex pair. Once done, `theorem_2_HOR` becomes axiom-free
(except for `IsSchurianSchemeGraph`'s abstract placeholder, which gets
replaced by a concrete predicate at the same time).

---

## 3. Discharge plan overview

The constructive `SchemeProfile` constructor needs three ingredients:

1. **Association scheme infrastructure** — definitions and basic
   lemmas. Pure new content (Mathlib doesn't have this).

2. **Step 1 — schurian → orbits = profile classes** (the algebraic
   half). Group-theoretic argument: scheme relations are
   `Aut`-orbital classes by the schurian assumption; restricting to
   `Aut_v` gives profile classes as orbits.

3. **Step 2 — 1-WL refines profile** (the combinatorial half).
   Intersection-number induction: at each round, the partition refines
   based on the scheme's structure constants; converges to the profile
   partition.

4. **Assembly** — package the three above into a `SchemeProfile`
   constructor, then discharge `schurian_scheme_profile_exists`.

This mirrors Tier 1's split: Stages 1-2 (CFI infrastructure), Stage 3
(`Aut(CFI(H)) ≅ Z₂^β ⋊ Aut(H)`, the algebraic half — deliberately
skipped for Tier 1 since not load-bearing), Stage 4 (M2-M4, the
combinatorial cascade), and the final discharge.

---

## 4. Tier 1 ↔ Tier 2 parallel

| Aspect | Tier 1 (CFI) | Tier 2 (Schemes) |
|---|---|---|
| **Headline depth** | `≤ tw(H)` | exactly 1 |
| **Mathlib infra gap** | None — built from `Fin`, `Sum`, `Sigma`, `Finset` directly | Need association schemes (~300-500 lines) |
| **Algebraic half** | Stage 3 (`Aut ≅ Z₂^β ⋊ Aut(H)`) — **skipped** as not load-bearing | Step 1 (schurian → orbits = profile) — **required** (it's the profile structure itself) |
| **Combinatorial half** | Stage 4 / M2-M4: per-round cascade, 10 sub-cases at rounds 1-5 | Step 2: per-round intersection-number induction, depth 1 only |
| **Per-round count** | 5 rounds (Phase 2.1-2.4 + M3.B+/C/B++) | 1 round (depth 1 is the headline) |
| **Hypothesis qualifier** | `OddDegree`, `5 ≤ n` | `IsSchurianSchemeGraph` (already a hypothesis), `Nonempty (Fin n)` perhaps |
| **Assembly structure** | `cfi_cascades_polynomially_oddDeg` → `theorem_1_HOR_cfi_oddDeg` | `schurian_scheme_profile_exists` → `theorem_2_HOR` |
| **Discharge effort** | ~3000 lines (CFI.lean), achieved in ~1 week of focused work | Estimated ~600-1000 lines (scheme infrastructure dominates) |

The structural parallel is real but the **balance flips**: Tier 1's
combinatorial cascade is the bulk of the work and the algebraic half
was skipped; Tier 2's algebraic half (scheme structure, Step 1) is the
bulk and the combinatorial half (Step 2) is a single induction.

---

## 5. What transfers from Tier 1 (reusable)

These pieces are tier-agnostic or have direct analogues:

### 5.1 Helpers already in shared infrastructure

In [`ChainDescent.lean`](../GraphCanonizationProofs/ChainDescent.lean)
§16 (shared infra) — already used by Tier 2 assembly:

- `individualizedColouring`, `FixesPointwise`, automorphism invariance
  lemmas.
- `OrbitPartition adj P S v w` — the Aut_S orbit equivalence relation.
- `OrbitPartition.subset_warmRefine` — orbits refine 1-WL cells (the
  trivial direction). Already powers Tier 2's `warm_iff_profile`
  reverse direction.

### 5.2 Helpers introduced for Tier 1, transferable

In [`ChainDescent/CFI.lean`](../GraphCanonizationProofs/ChainDescent/CFI.lean)
§13.24, but **truly tier-agnostic** (not CFI-specific):

- **`refineStep_iter_le_eq`** — equal at iter[k+d] implies equal at
  iter[k]. Pure property of `refineStep_iff`. Tier 2's Step 2 will
  need this to lift any per-round result.
- **`warmRefine_eq_iter_eq`** — `warmRefine` equality (= iter[n])
  gives iter[r] equality for r ≤ n. Tier 2 will use at r = 1.

**Action item for Tier 2:** relocate these to `ChainDescent.lean`
§16 (or a new §16.4 "iteration helpers") so they don't live behind
the CFI import.

### 5.3 Proof patterns transferable

Tier 1's M3.B / M3.B+ / M3.B++ / M3.C are all **witness-tuple
signature arguments**:
- Pick a tuple `t = (χ u_witness, adj-value, P-value)`.
- Show `t` is in the LHS signature (concrete adjacency).
- Show `t` is absent from the RHS signature (no `u'` matches).
- Conclude signatures differ → refineStep distinguishes.

Tier 2's Step 2 will need analogous per-round signature arguments,
just with different witness structures (intersection-number-derived
rather than CFI-gadget-derived). The **factored Approach-3 step lemma
pattern** from Phase 2.3 / 2.X (`refineStep_subset_step`,
`refineStep_bridge_step`) is a direct template.

### 5.4 Style/structure conventions

- **Concrete-round headline + generic step lemma**: e.g.,
  `refineStep_subset_inter_gadget_round2` (concrete) wraps
  `refineStep_subset_step` (generic over χ). Phase 2.X
  (`refineStep_endpoint_false_intra_gadget_partner_round4`) does the
  same with `refineStep_bridge_step`. Tier 2's Step 2 should follow
  this: a generic "scheme-relation-refinement step lemma" + a
  concrete headline applied at the right round.

- **`adj_symm` reconciliation**: `signature` puts adj-subject on the
  left; iff-characterizations typically put adj-candidate on the
  left. Tier 2's scheme-adjacency will likely need the same
  reconciliation helper. The CFI-specific `IsCFI'.adj_symm` is a
  template, but Tier 2 needs its own (depends on scheme structure).

---

## 6. What's fully new for Tier 2

All of these live in scheme territory; no Tier 1 analogue.

### 6.1 Association scheme datatype

```
structure AssociationScheme (n : Nat) where
  rank : Nat                                 -- d, number of non-trivial relations
  rel : Fin (rank + 1) → Fin n → Fin n → Bool -- R_0, R_1, ..., R_d
  rel_zero_iff_eq : ∀ v w, rel 0 v w = true ↔ v = w
  rel_symm : ∀ i v w, rel i v w = rel i w v
  partition : ∀ v w, ∃! i, rel i v w = true  -- relations partition V×V
  intersection_number : Fin (rank+1) → Fin (rank+1) → Fin (rank+1) → Nat
  intersection_well_defined : ∀ i j k,
    ∀ v w, rel k v w = true →
    (Finset.univ.filter (fun u => rel i v u = true ∧ rel j u w = true)).card
      = intersection_number i j k
```

Plus derived helpers: `rel_decidable`, `valencies`, scheme-graph
construction (`edges := ⋃ {j ∈ J}, R_j`), `Fintype` instances, etc.

### 6.2 Schurian property

```
structure SchurianScheme (n : Nat) extends AssociationScheme n where
  /-- Schurian: relations are exactly Aut-orbital classes. -/
  schurian : ∀ v w v' w',
    rel i v w = true → rel i v' w' = true →
    ∃ g : (AdjMatrix.scheme_edge_set this).Automorphism,
      g v = v' ∧ g w = w'
```

The `Automorphism` here refers to graph-Aut of the scheme graph;
needs a small bridge between scheme structure and graph adj matrix.

### 6.3 v-profile

For a fixed `v`, the v-profile assigns each `w ≠ v` the index of the
relation containing `(v, w)`:

```
def vProfile (S : AssociationScheme n) (v : Fin n) : Colouring n :=
  fun w => if w = v then 0 else
    (Classical.choose (S.partition v w)).val.val + 1
    -- "+1" reserves 0 for v itself
```

### 6.4 Step 1 (schurian ⟹ profile = orbits)

The algebraic core. Three sub-claims:

- **S1.a (Aut_v preserves profile):** if `g ∈ Aut_v`, then for all `w`,
  `vProfile (g w) = vProfile w`. Proof: `g` preserves all relations (as
  an automorphism), so `(v, w) ∈ R_i` ⟺ `(g(v), g(w)) ∈ R_i` ⟺
  `(v, g(w)) ∈ R_i` since `g(v) = v`.

- **S1.b (profile equality ⟹ Aut_v-equivalence):** if `vProfile w =
  vProfile w'` and both are non-v, then `(v, w)` and `(v, w')` are in
  the same scheme relation `R_j`. By schurian, some `g ∈ Aut` sends
  `(v, w) ↦ (v, w')`. This `g` fixes the first coordinate, hence
  `g ∈ Aut_v`. So `w, w'` are Aut_v-related.

- **S1.c (singleton v):** `v` has its own profile colour (the "0"
  reserved value). Trivial by construction.

These combine into the `profile_iff_orbit` field.

### 6.5 Step 2 (1-WL refines profile)

The combinatorial core. Per the paper proof:

- **S2.a (round 1):** under `χ_{v} = individualizedColouring n {v}`,
  refineStep distinguishes vertices by adjacency-to-`v`. Specifically:
  edges of `G` are `R_{j₁} ∪ R_{j₂} ∪ …`, so `(v, w) ∈ R_{j}` for
  `j ∈ J` gives `adj v w = 1`; otherwise `adj v w = 0`. Round 1
  signatures distinguish `{w : (v,w) ∈ R_j, j ∈ J}` from
  `{w : (v,w) ∈ R_j, j ∉ J}`.

- **S2.b (inductive step):** if at round `r`, the partition refines
  the profile coarsened by some equivalence `≡_r`, then at round
  `r + 1`, by the intersection-number well-definedness, the partition
  refines a strictly-finer equivalence. Convergence to the full
  profile partition at some bounded round.

- **S2.c (depth-1 case for the concrete theorem):** for the
  Theorem 2 statement (1-WL fixpoint at single individualization),
  the convergence depth is bounded by the scheme rank `d + 1`. Apply
  `warmRefine_eq_iter_eq` to lift from the bound to the fixpoint.

The intersection-number argument is the technical heart. Reference:
Cai-Fürer-Immerman 1992 (general WL theory) or Babai 1979 (coherent
configurations) — citation precision pending (G2 in orbit-recovery
§14.5).

### 6.6 SchemeProfile constructor

The assembly. Given a `SchurianScheme adj`, a vertex `v`, and `P`:
- Build `profile := vProfile S v`.
- Prove `v_singleton` from the `+ 1` convention.
- Prove `profile_iff_orbit` from S1.a + S1.b.
- Prove `warm_refines_profile` from S2 (specifically S2.c at depth 1).

Then discharge `schurian_scheme_profile_exists` by `⟨constructed
SchemeProfile⟩`.

---

## 7. Phase-by-phase plan (named milestones)

Following Tier 1's naming convention (Stages + M-numbers):

### Stage T2.1 — association scheme infrastructure — DONE 2026-05-26

Landed in
[`ChainDescent/Scheme.lean`](../GraphCanonizationProofs/ChainDescent/Scheme.lean)
(~165 lines, all axiom-clean: `propext` + `Classical.choice` +
`Quot.sound`, no `refineStep`).

- **T2.1.a — DONE** — `AssociationScheme n` structure with
  `rank`, `rel`, `rel_zero_iff_eq`, `rel_symm`, `rel_partition`
  (`∃!`), `intersectionNumber`, `intersectionNumber_well_defined`.
  Helpers: `relOfPair` (noncomputable, from `Classical.choose`),
  `rel_relOfPair`, `relOfPair_unique`, `rel_iff_relOfPair`,
  `relOfPair_symm`, `relOfPair_self`, `relOfPair_eq_zero_iff`.
- **T2.1.b — DONE** — `IsSchemeAut S π` predicate (preserves every
  relation index), with `IsSchemeAut.refl`/`trans`/`symm`/`relOfPair_eq`.
  `SchurianScheme n` extends `AssociationScheme n` with the
  `schurian` field. **Aut-action bridge deferred** to T2.M4 —
  T2.2/T2.3 work with `IsSchemeAut`-based orbits, and the
  scheme-Aut → graph-Aut inclusion gets discharged once a
  `SchemeGraph` structure is built.
- **T2.1.c — DONE** — `trivialScheme : AssociationScheme 1` and
  `trivialSchurianScheme : SchurianScheme 1` (single-vertex,
  identity-only Aut). Confirms inhabitedness. Heavier examples
  (`JohnsonScheme m k`) deferred until T2.M4 when concrete instances
  matter.

**Build target:** `ChainDescent.Scheme` added to `lakefile.toml`
`defaultTargets`.

**Iteration helpers relocated:** `refineStep_iter_le_eq` and
`warmRefine_eq_iter_eq` moved from `CFI.lean §13.24` to
`ChainDescent.lean §16.4`. Both tiers now use them without a CFI
import; both remain axiom-clean.

### Stage T2.2 — v-profile + Step 1 (algebraic) — DONE 2026-05-26

Landed as §4 of `Scheme.lean` (~150 lines, axiom-clean).

- **T2.2.a — DONE** — `vProfile (S : AssociationScheme n) (v : Fin n)
  : Colouring n` (noncomputable; depends on `relOfPair`). Helpers:
  `vProfile_self` (= 0 at v), `vProfile_eq_iff` (equality ↔
  `relOfPair` equality), `vProfile_eq_zero_iff` (= 0 ↔ = v),
  `vProfile_ne_self_of_ne` (the `SchemeProfile.v_singleton` field).
- **T2.2.b (S1.a) — DONE** — `vProfile_aut_invariant`: v-stabilizing
  scheme-Aut preserves `vProfile`. Proof: `IsSchemeAut.relOfPair_eq`
  plus `π v = v`.
- **T2.2.c (S1.b) — DONE** — `SchurianScheme.vProfile_eq_imp_schemeOrbit`:
  profile equality ⟹ v-stabilized scheme-Aut orbit equivalence. Uses
  the `schurian` field directly.
- **T2.2.d — DONE** — `SchurianScheme.vProfile_iff_schemeOrbit`:
  combined Step 1 bidirectional form in scheme-Aut terms.

Also added: `SchemeOrbitPartition` predicate
(v-stabilized scheme-Aut orbits), with `refl`/`symm`/`trans` and
`vProfile_eq_of_schemeOrbit` (the trivial direction packaged
separately).

### Stage T2.3 — Step 2 (combinatorial) — INFRASTRUCTURE LANDED 2026-05-26

§5-§7 of `Scheme.lean` (~200 lines, axiom-clean) build the
prerequisites for Step 2 and discharge **Step 1 in graph-Aut terms**
(the form that bridges to `OrbitPartition`).

**§5 — `SchemeGraph` structure (DONE).** Bundles `scheme :
AssociationScheme n`, `J : Finset (Fin (scheme.rank + 1))` of edge
relations, and `zero_notMem_J` (looplessness). Provides:
- `adj : AdjMatrix n` (noncomputable, derived from `relOfPair ∈ J`).
- `adj_eq_one_iff`, `adj_eq_zero_iff`, `adj_self`, `adj_symm`,
  `adj_eq_zero_or_one`.

**§6 — `SchurianSchemeGraph` (DONE).** Extends `SchemeGraph` with
*two* schurian fields (necessary; one alone doesn't imply the other):
- `schurian_transitive`: any two `R_i`-pairs are connected by some
  graph-Aut.
- `isAut_imp_isSchemeAut`: every graph-Aut preserves every relation
  (i.e., is a scheme-Aut).

Helpers: `relOfPair_aut_eq` and `vProfile_aut_invariant` lifted to
graph-Aut.

**§7 — Step 1 in graph-Aut terms (DONE).** Defines
`GraphOrbitFixing adj v w u := ∃ π, IsAut π adj ∧ π v = v ∧ π w = u`
(with refl/symm/trans), and proves:
- `vProfile_eq_imp_graphOrbit` (forward, uses `schurian_transitive`).
- `graphOrbit_imp_vProfile_eq` (reverse, uses
  `isAut_imp_isSchemeAut`).
- `vProfile_iff_graphOrbit` (combined).

This is the **graph-Aut shape of `SchemeProfile.profile_iff_orbit`**
modulo the P-preservation bridge (when `P` is permutation-invariant,
`GraphOrbitFixing` and `OrbitPartition adj P {v}` coincide).

**Step 2 proper — phase plan**

The substantive content: show `warmRefine adj P χ_v w = warmRefine adj
P χ_v u → vProfile w = vProfile u` for a schurian scheme graph and
any (compatible) P. Detailed phases:

### S2.a — round-1 adj-to-v lemma — DONE 2026-05-27

> For `w, u ≠ v`, if `refineStep adj P χ_v w = refineStep adj P χ_v u`,
> then `adj w v = adj u v` (and `P w v = P u v`).

Landed as §8.a of `Scheme.lean` (~70 lines, axiom-clean):
- `individualizedColouring_singleton_eq_v_iff`: helper proving
  `χ_v u = χ_v v ↔ u = v`. (Tier-agnostic; useful elsewhere too.)
- **`refineStep_round1_pair_eq`**: the headline — packs both
  `adj w v = adj u v` and `P w v = P u v` (multiset-tuple match
  gives both).
- **`refineStep_round1_adj_eq`**: convenience specialisation
  (adj-only conjunct).
- **`SchemeGraph.refineStep_round1_J_eq`**: scheme-specific
  specialisation — under `χ_v` for a scheme graph, round-1
  equality implies matching J-class membership of `relOfPair v ·`
  (the "edge to v vs non-edge to v" partition coincides with the
  J-membership classification of vProfile).

Proof technique: extract `signature` equality from `refineStep_iff`,
note the unique colour-positive tuple in signature(w) is from
`u' = v` (since χ_v is positive only at v), transport to
signature(u) via multiset equality, extract preimage u'' with
χ_v u'' = χ_v v hence u'' = v.

Generic: no scheme structure needed for the first two; the third is
the SchemeGraph instantiation. Stated outside any namespace so it
can also support Tier 1 or other depth-1 reasoning.

### S2.b — inductive partition refinement

The technical heart. Define a sequence of partitions
`Π_0, Π_1, …, Π_rank` of `Fin n` (depending on the scheme + `v`)
such that:

1. **Π_0 = {{v}, Fin n \ {v}}** — the χ_v partition itself.
2. **Π_k strictly refines Π_{k-1}** (or stabilises) — `Π_k` uses
   the intersection-numbers up to depth `k` to separate more
   `vProfile`-distinct vertices.
3. **Π_k → vProfile partition** as `k` grows, eventually stabilising
   at vProfile (S2.c).
4. **Invariant: `((refineStep adj P)^[k]) χ_v` refines Π_k.** This
   is the inductive claim.

The clean phrasing of Π_k is the technical question. Candidates:
- **"Walk count" partition** — `Π_k` lumps `w, u` iff for every
  sequence of relation indices `(i_1, …, i_k)`, the count of walks
  `w = x_0 → x_1 → … → x_k` with `(x_{j-1}, x_j) ∈ R_{i_j}` and
  `(v, x_k) ∈ R_*` matches between `w` and `u`. Captured by
  intersection-number well-definedness.
- **"Cell-multiplicities" partition** — `Π_k` lumps `w, u` iff for
  every cell `C` of `Π_{k-1}`, the count of `u' ∈ C` with `adj w u'
  = 1` matches that of `adj u u' = 1`. Directly the signature-based
  refinement.

The second is closer to what `refineStep` actually computes; likely
the cleaner Lean formulation. The intersection-number axiom is
what guarantees these counts are determined by `vProfile`.

**S2.b infrastructure + count bridge + partial result landed
2026-05-27** (§8.b of `Scheme.lean`, ~280 lines, axiom-clean):

### §8.b.1 — Iteration framework
- `iterSignature adj P v k w` (noncomputable def) — signature
  multiset of `w` against the iter[k] refinement of `χ_v`.
- **`iter_succ_eq_iff`** — round-by-round unfolding:
  `iter[k+1] χ_v w = iter[k+1] χ_v u` ↔ `iter[k] χ_v w = iter[k]
  χ_v u` ∧ `iterSignature ... k w = iterSignature ... k u`. The
  primary inductive-step tool.
- **`AssociationScheme.intersectionCount_via_w`** — scheme axiom
  in usable form: count of `u'` with `(v, u') ∈ R_i ∧ (w, u') ∈
  R_l` equals `intersectionNumber i l (relOfPair v w)`. Pure
  scheme algebra, no `refineStep`.
- `AssociationScheme.intersectionCount_eq_of_vProfile_eq` —
  trivial corollary.
- `Step2_target G P v` — the eventual full Step 2 claim.

### §8.b.2 — Count bridge (Multiset.count → Finset.card)
- **`signature_count_eq_card`** — `Multiset.count` of a specific
  tuple in `signature` equals `Finset.card` of matching preimage
  filter over `u' ≠ w`. Built via `Multiset.count_map` +
  `Finset.filter_val` + `Finset.filter_filter`.
- **`signature_countP_eq_card`** — generalised to any decidable
  predicate `p`.
- **`signature_eq_card_eq`** / **`signature_eq_countP_eq`** —
  corollaries: signature equality between `w` and `u` gives
  matching preimage counts.
- **`iter_succ_count_eq`** / **`iter_succ_countP_eq`** /
  **`iter_succ_colour_count_eq`** — iter[k+1] equality versions:
  the workhorse for the inductive step. Counts of intermediate
  vertices `u'` satisfying any decidable predicate on
  `(iter[k] colour, adj w u', P w u')` (or just colour) match
  between `w` and `u`.

### §8.b.3 — Partial Step 2 result (J-class refinement)
- **`iter_succ_adj_eq`** — S2.a iteratively lifted: iter[k+1]
  equality at any depth k ≥ 0 already forces `adj w v = adj u v`
  (via `refineStep_iter_le_eq` from §16.4).
- **`warmRefine_adj_eq`** — warmRefine version: two non-v
  vertices in the same warmRefine cell share adj-to-v.
- **`SchurianSchemeGraph.warmRefine_J_eq`** — **the first concrete
  Step 2 partial theorem**: warmRefine cells refine the J-class
  partition of `vProfile`. This is the "level 1" refinement; the
  full Step 2 keeps refining via intersection-number induction
  until reaching `vProfile` itself.

**Remaining for full S2.b (rank ≥ 2): only the convergence content.**
The inductive intersection-number step `iter_refines_schemePart_at`
is **proved 2026-05-27**. See §10 below for details.

### S2.b rank ≤ 1 case + Theorem 2 instance — DONE 2026-05-27

`step2_of_rank_le_one` (§9.4 of `Scheme.lean`, ~30 lines,
axiom-clean): for any schurian scheme graph with `rank ≤ 1`, Step 2
holds. Proof: case-split on `(w = v, u = v)`. The trivial cases
(both = v or both ≠ v with rank ≤ 1 forcing vProfile ≡ 1) close
algebraically; the mixed cases (one = v, other ≠ v) derive a
contradiction from `warmRefine_eq_iter_eq` at r = 0 (= χ_v) plus
`individualizedColouring_singleton_eq_v_iff`.

`theorem_2_HOR_concrete_rank_le_one`: Theorem 2 unconditional for
this case. Covers `K_n` schurian schemes (rank = 1, J = {1}). First
concrete schurian scheme graph class with the full theorem
discharged.

For `rank ≥ 2` schemes (Johnson, Petersen, distance-regular), the
inductive intersection-number argument is needed.

### §10 framework — `Step2_at_depth`, `schemePart_at`, `iter_refines_schemePart_at`, `Step2_converges_at` — DONE 2026-05-27

The Step 2 architecture is now built end-to-end except for the
**single remaining content piece**: convergence of `schemePart_at`
to `vProfile` at some bounded depth.

- `Step2_at_depth G P v k`: iter[k] equality implies vProfile
  equality. Lifts to `Step2_target` via `step2_of_step2_at_depth`
  (uses `warmRefine_eq_iter_eq`).
- `step2_at_depth_zero_of_rank_le_one`: cleaner restatement of
  `step2_of_rank_le_one` via the depth-0 framework.
- **`schemePart_at G P v k`**: the **recursive partition predicate**
  on `Fin n × Fin n`. Depth 0 = χ_v partition; depth k+1 = depth
  k AND for every (adj-value, P-value, class-representative), the
  count of u' in that depth-k class with matching adj/P values
  matches between w and u. Noncomputable (uses
  `Classical.decPred` for the recursive filters).
- `schemePart_at_refl/_symm/_trans`: equivalence-relation
  structure.
- **`iter_refines_schemePart_at`** — **THE INDUCTIVE STEP, PROVED**.
  iter[k] χ_v partition refines `schemePart_at G P v k`. Proof: by
  induction on k, using `iter_succ_eq_iff` + `signature_eq_countP_eq`
  + the equivalence "schemePart_at k u' w' ↔ ∃ x, iter[k] x = iter[k]
  u' ∧ schemePart_at k x w'" (from the inductive hypothesis +
  transitivity).
- **`Step2_converges_at G P v k`**: convergence statement —
  schemePart_at-k equivalence implies vProfile equality. **The
  single remaining content piece.**
- **`step2_of_converges_at`**: assembly — convergence at any k ≤ n
  gives `Step2_target` via `iter_refines_schemePart_at` +
  `warmRefine_eq_iter_eq`.
- `step2_converges_at_zero_of_rank_le_one`: convergence at depth 0
  for the rank-≤-1 case (sanity check that the framework recovers
  the simple case).

**What remains for full Step 2 on rank ≥ 2 schemes:** prove
`Step2_converges_at G P v (k_bound)` for some specific bound (e.g.,
`k_bound = G.scheme.rank + 1`). This is the classical "coherent
algebra rank for schurian schemes" content. Once discharged, every
schurian scheme graph gets a fully unconditional Theorem 2 instance.

### Convergence attempt (depth 1, attempted 2026-05-27)

Tried: extract `adj v w = adj v u` from `schemePart_at G P v 1 w u`
via the depth-1 count condition at `w' = v`. Conceptually
straightforward — LHS-filter = `{v}` (since `schemePart_at_0 u' v`
forces `u' = v`), so |LHS| = 1; by hkey |RHS| = 1; combined with
`RHS ⊆ {v}`, get `RHS = {v}`; extract `adj u v = adj w v`.

**Blocked by Lean technical obstacle.** Lean cannot unify the
`Finset.filter` expression inside `hcount`'s output (which uses
`schemePart_at`'s internal `Classical.decPred` via `letI`) with an
identical-looking filter expression written externally (using a
freshly-elaborated `Classical.decPred`). The two `Decidable`
instance terms are not definitionally equal. Standard workarounds
(`convert ... using N`, `Subsingleton.elim` on `Decidable`,
`Eq.trans` chains, `▸` notation, `classical` tactic) all fail —
the mismatch is at a level that congruence-based tactics don't
bridge.

**Cleaner restructure for future work.** Rewriting `schemePart_at`
to use `Set.ncard` of `{u' | ...}` (decidability-uniform via
Classical) instead of `(Finset.univ.filter ...).card` should
sidestep the issue. This would require updating
`iter_refines_schemePart_at`'s proof correspondingly. Estimated
1-2 sessions; left as the single remaining open piece of Tier 2
formalization.

### S2.c — convergence bound

> `Π_k = vProfile partition` for `k ≥ rank + 1` (or some other
> explicit bound).

**Justification:** the coherent algebra generated by adj is the
adjacency algebra of the scheme; for schurian schemes it has rank
`≤ rank + 1` as a module, so `rank + 1` rounds of 1-WL exhaust its
distinctions.

The bound may need tightening or relaxing depending on what S2.b's
exact invariant gives.

### S2.d — lift to warmRefine

Use `warmRefine_eq_iter_eq` (in `ChainDescent.lean §16.4`,
axiom-clean): `warmRefine adj P χ_v w = warmRefine adj P χ_v u` ⟹
`((refineStep adj P)^[k]) χ_v w = ((refineStep adj P)^[k]) χ_v u`
for any `k ≤ n`.

Pick `k = rank + 1`. We need `rank + 1 ≤ n`. Holds in any
non-trivial scheme (`n ≥ 1` and `R_0 ⊆ V × V` implies `rank + 1 ≤ ?`;
actually only `rank + 1 ≤ n` if the relations are "tight"; needs
a side condition or specialisation).

For Theorem 2 we assume `n ≥ rank + 1` (or equivalent), which is
automatic for any vertex-transitive scheme with `n ≥ 2`.

### S2 assembly

> `theorem warm_refines_vProfile (G : SchurianSchemeGraph n) (P :
> PMatrix n) (v : Fin n) : warmRefine G.adj P (individualizedColouring
> n {v}) w = warmRefine G.adj P (individualizedColouring n {v}) u →
> vProfile G.scheme v w = vProfile G.scheme v u`

This is the future `SchemeProfile.warm_refines_profile` field.

**Estimated remaining (after S2.a):** ~250 lines, 2-3 sessions.
S2.b's inductive invariant is the open design question; once that's
fixed the rest is mechanical.

### Stage T2.M4 — assembly + discharge

- **T2.M4.a** — `SchurianScheme.toSchemeProfile`: constructor
  producing a `SchemeProfile adj P v` from a `SchurianScheme adj` +
  vertex `v`. Uses T2.2.d for `profile_iff_orbit`, T2.3.d for
  `warm_refines_profile`.

- **T2.M4.b** — replace `IsSchurianSchemeGraph` abstract axiom with
  the concrete predicate `IsSchurianSchemeGraph' adj := Nonempty
  (SchurianScheme n) ∧ (compatibility with adj)`. (Mirrors how Tier 1
  replaced `IsCFI` axiom with `IsCFI'` structure.)

- **T2.M4.c** — discharge `schurian_scheme_profile_exists` as a
  theorem: given `IsSchurianSchemeGraph' adj`, extract the scheme
  and call `toSchemeProfile`.

- **T2.M4.d** — `theorem_2_HOR_concrete`: axiom-free Theorem 2 over
  the concrete predicate.

**Estimated:** ~100-200 lines. Assembly is short; the work is upstream.

---

## 8. Specific lemmas to write (priority order)

Starter list — each item is a Lean lemma name + one-sentence statement.
These would form the contents of new files
`GraphCanonizationProofs/ChainDescent/Scheme.lean` and
`GraphCanonizationProofs/ChainDescent/Scheme/Schurian.lean` (file split
TBD by size).

**Infrastructure (T2.1):**
- `AssociationScheme` structure.
- `AssociationScheme.relation : Fin (d+1) → Fin n → Fin n → Bool`.
- `AssociationScheme.rel_of_pair : Fin n → Fin n → Fin (d+1)` (the
  unique relation containing the pair).
- `AssociationScheme.intersection_number_well_defined` (axiom-field).
- `AssociationScheme.valency` (degree in each relation).
- `JohnsonScheme : ∀ m k, AssociationScheme (Nat.choose m k)`.
- `SchurianScheme` extending with `schurian` field.

**v-profile (T2.2):**
- `vProfile (S : AssociationScheme n) (v : Fin n) : Colouring n`.
- `vProfile_self v : vProfile S v v = 0`.
- `vProfile_ne_self_pos : w ≠ v → vProfile S v w ≠ 0`.
- `vProfile_eq_iff : vProfile S v w = vProfile S v w' ↔ rel_of_pair v w = rel_of_pair v w'`.
- `vProfile_aut_invariant (g : Aut_v) : vProfile S v (g w) = vProfile S v w`.
- `vProfile_eq_imp_orbit (h_schurian) : vProfile S v w = vProfile S v w' → OrbitPartition adj P {v} w w'`.

**Step 2 (T2.3):**
- `signature_round1_via_vProfile : signature adj P χ_{v} w depends only on vProfile w`.
- `refineStep_scheme_step_lemma` — generic Approach-3 step lemma for
  scheme-relation refinement.
- `warm_refines_vProfile_at_depth (h : depth_bound) : iter[d+1] χ_{v} w = iter[d+1] χ_{v} w' → vProfile w = vProfile w'`.
- `warm_refines_profile_of_scheme` — composing the above to give the
  `warm_refines_profile` field of `SchemeProfile`.

**Assembly (T2.M4):**
- `SchurianScheme.toSchemeProfile : SchurianScheme adj → ∀ v, SchemeProfile adj P v`.
- `IsSchurianSchemeGraph' : Prop` — concrete predicate.
- `schurian_scheme_profile_exists_proof : ∀ {adj} (h : IsSchurianSchemeGraph' adj) (P : PMatrix n) (v : Fin n), Nonempty (SchemeProfile adj P v)`.

---

## 9. Risks and open questions

### 9.1 Mathlib alignment

Mathlib has `Matrix.IsAdjMatrix`, `SimpleGraph`, and `Quotient` but
**no association schemes**. Building from scratch costs ~300 lines
just for the datatype + basic instances. Worth considering:

- Does a Mathlib PR exist or is one in progress? Quick search needed
  before committing to from-scratch implementation.
- Could the scheme be encoded indirectly via `SimpleGraph.distance` for
  distance-regular graphs only? Would simplify Johnson/Hamming but
  exclude general schurian schemes.

### 9.2 Schurian formalisation

The schurian property requires quantifying over **graph automorphisms**.
Tier 1 deliberately skipped its Stage 3 (`Aut(CFI(H)) ≅ Z₂^β ⋊ Aut(H)`)
because Fact B let us avoid the Aut group altogether. Tier 2 cannot
skip — schurian is intrinsically about Aut.

**Question:** what's the cleanest formalisation of `Aut(G)` for an
`AdjMatrix`? Options:
- `{ σ : Equiv.Perm (Fin n) // ∀ i j, adj.adj (σ i) (σ j) = adj.adj i j }`
  (direct as a subgroup of permutations).
- Mathlib's `SimpleGraph.Iso` if we bridge to `SimpleGraph`.
- A custom `AdjMatrix.Automorphism` structure parallel to `IsCFI'`.

Likely the cleanest is a custom structure; the bridge to permutations
is short.

### 9.3 Step 2's exact proof

The intersection-number induction has a precise statement but its
exact phrasing matters. Two flavours in the literature:
- **Babai/coherent configurations:** show 1-WL computes the coherent
  algebra closure; appeal to coherent-algebra theory.
- **Direct intersection-number induction:** prove by induction on rounds
  that the partition refines into vProfile classes.

The second is more elementary and likely easier in Lean. The first
would require building coherent algebra infrastructure, an
even-larger undertaking.

### 9.4 Convergence depth

For Theorem 2 we only need 1-WL at single individualization to recover
orbits. **Depth 1** is the headline, but the underlying convergence
to the profile partition may take more rounds inside the warmRefine
iteration. The proof needs:
- A specific bound `k` such that iter[k] χ_{v} = vProfile (refining).
- `k ≤ n` so that `warmRefine_eq_iter_eq` applies.

For a scheme of rank `d`, `k ≤ d + 1` should suffice (one round per
relation distinction). For `n ≥ d + 1` (which holds since the
diagonal relation is always there), the helper applies.

### 9.5 Hidden Johnson connection

Tier 2 directly subsumes Piece C of hidden-johnson.md for the **visible**
Johnson case. The **encoded** Johnson case (the open construction
question) is separate; Tier 2 doesn't address it but does dispense with
the visible-Johnson worry, freeing focus for the construction problem.

---

## 10. Effort estimate

Based on Tier 1's actual time (~1 week focused for ~3000 lines):

| Stage | Lines | Days |
|---|---|---|
| T2.1 (infra) | ~300 | 2-3 |
| T2.2 (Step 1) | ~200 | 2 |
| T2.3 (Step 2) | ~400 | 3-5 |
| T2.M4 (assembly) | ~150 | 1 |
| Mathlib bridges + smoke tests | ~150 | 1 |
| **Total** | **~1200** | **~9-12** |

T2.3 (Step 2) is the dominant uncertainty — the intersection-number
induction could go cleanly or could surface unexpected scaffolding
needs. Recommend starting with T2.1 + T2.2 (lower variance), then
re-estimating T2.3 with infrastructure in hand.

---

## 11. Pickup quickstart

For someone starting fresh on Tier 2:

1. **Read first:** orbit-recovery doc §14 (paper proof of Theorem 2,
   including G1-G7 gap notes); this doc.

2. **Inspect:** `ChainDescent.lean` §18 — assembly already in place.
   Understand what shape `SchemeProfile`'s four fields have; that's
   what the constructor must produce.

3. **Relocate first:** move `refineStep_iter_le_eq` and
   `warmRefine_eq_iter_eq` from `CFI.lean` §13.24 into
   `ChainDescent.lean` (probably §16.4 new section). These are
   tier-agnostic and Tier 2 will need them.

4. **Start T2.1:** create `ChainDescent/Scheme.lean`, write
   `AssociationScheme` structure, prove a triangle/K_n smoke test.

5. **Then T2.2:** add `vProfile` + S1 proofs. The algebraic half is
   the cleaner of the two technical halves; do it first to fix the
   data layout for Step 2.

6. **Then T2.3:** intersection-number induction. Expect this to be
   the hardest stage; design the inductive invariant carefully before
   writing code.

7. **Finally T2.M4:** assembly + replacing the abstract
   `IsSchurianSchemeGraph` axiom. Mirror Tier 1's `IsCFI` → `IsCFI'`
   refactor.

**Build target:** add `ChainDescent.Scheme` to `defaultTargets` in
`lakefile.toml` once T2.1 lands.

**Smoke tests to keep alongside:** `JohnsonScheme 5 2 = Petersen
(scheme)` and `JohnsonScheme 4 2 = K_3 ⊕ K_3` (or whatever; use
`native_decide` like `triangleBase_cfiVertex_card`).

---

## 12. Out-of-scope follow-ons

These are NOT in this plan but worth noting:

- **Tier 1 general-degree case** (saturated subsets) — independent of
  Tier 2; tackled after Tier 2 if interest remains.
- **Tier 1 `5 ≤ n` discharge** under OddDegree — cleanup, low priority.
- **Hidden-Johnson encoded case** — open construction question,
  separate research program (not a Lean cleanup).
- **Tier 3 (cascade-class generalization)** — speculative; depends on
  whether Tier 1 + Tier 2 reveal a common abstraction.

---

## 13. Cross-references

- [`chain-descent-orbit-recovery.md`](./chain-descent-orbit-recovery.md)
  §14 — Theorem 2 paper proof.
- [`ChainDescent.lean`](../GraphCanonizationProofs/ChainDescent.lean)
  §18 — current Tier 2 Lean assembly.
- [`ChainDescent/CFI.lean`](../GraphCanonizationProofs/ChainDescent/CFI.lean)
  §13.21-§13.24 — Tier 1 OddDegree discharge (the template Tier 2
  parallels).
- [`chain-descent-hidden-johnson.md`](./chain-descent-hidden-johnson.md)
  §5 — Piece C, subsumed by Tier 2 (visible Johnson case).
