# Chain descent — the self-detection lemma: plan to make the seal unconditional

> **STATUS (2026-06-08): Phase 1 COMPLETE (Increments 1 + 2 LANDED, axiom-clean, build green) — the seal is
> reduced end-to-end to the SEMANTIC crux `SelfDetectsStably` (primitive small ⟹ cells = orbits above a
> bounded set). FUSED SEAL LANDED (2026-06-08, axiom-clean): `reachesRigidOrCameron_viaFusedSeal`
> (`Cascade.lean`) is the single headline capstone — `((SchemeBlockRecovered ∨ AbelianConsumed) ∨
> SchemeRecoveredByDepth bound) ∨ IsCameronScheme` — each non-Cameron branch through its strongest form: the
> **primitive floor (cascade) reduced to the semantic crux `SelfDetectsStably`**, the imprimitive branch on
> earned `SchemeBlockRecovered ∨ AbelianConsumed` (carried `hImprim`, tower-reducible to the same floor),
> Cameron = cited G3. Fuses `viaStableRecovery` + `viaBlockRecovery` into ONE statement of the conditional seal
> `modulo {G3 + self-detection}` (carries exactly two inputs, `hSelfDetect` crux + `hImprim`). Phase 2 STARTED —
> affine beachhead Increment A1 LANDED (single-base recovery is free; the crux is multi-base); **M0/M0.3/M1.0/M1.0b
> AND M1.1/M1.2 LANDED (2026-06-08, axiom-clean)** — the orbital-scheme constructor, the affine model `V⋊G₀`,
> and the bridge `isPrimitive_affineScheme_imp_irreducible` (primitive ⟹ `G₀` irreducible, via the
> `ClosedSubset`-from-invariant-`Submodule` construction = the §5.3 template). **M2 REDUCTION LANDED (2026-06-08,
> axiom-clean):** `stablyRecoverable_of_discrete` + `selfDetectsStably_of_discretizes` reduce the *entire* crux —
> for **any** schurian scheme — to **"primitive small ⟹ bounded individualization discretizes"** (a refinement-only,
> orbit-free statement; faithful/lossless). **Remaining Phase 2 = M2-B**: the affine discreteness proof itself
> (`irreducible G₀ ⟹ ∃ bounded S₀, Discrete(warmRefine affine schemeAdj S₀)`) — base term easy (spanning set ⟹
> `Stab=1`), `s(C)` stickiness term = the open citation-free WL-dimension content; then M3 (wire) is mechanical.
> **M2-B DEPTH-1 SLICE + STEP-1 SEAL-WIRING LANDED (2026-06-08, axiom-clean):** `discrete_of_jointProfileSeparates`
> / `discrete_affineScheme_of_jointSeparates` (the depth-1 discreteness producer) + `DepthOneSeparable` /
> `selfDetectsStably_of_depthOneSeparable` / `reachesRigidOrCameron_viaDepthOneSeparable` (the seal closed for the
> `s(C)=1` slice, manifestly conditional, exposing the engine slot). **ROUTE-SCAN DONE + REMAINING-PIECES PLAN
> WRITTEN — §11 is now the PICK-UP for continuing Phase 2** (the conceptual frame [k≡1, not k-WL], the route-scan
> verdict [affine-cyclic beachhead], and the implementation plan for the cyclotomic bound proof + wiring). §9 is the
> earlier affine build plan (M0–M3, M0/M1 landed); §10 is the M1.1/M1.2 + gotchas handoff. A fresh reader continuing
> Phase 2 should start at **§11**, then §10.3 (gotchas).
> **E1 ENGINE FIRST BRICKS LANDED (2026-06-08, axiom-clean, `Cascade.lean §13b`):** `twoRoundCount_eq_of_warmRefine`
> (the depth-2 separation primitive, the `schemeAdj` analogue of `IntersectionSeparates`) +
> `discrete_of_twoRoundProfileSeparates` (the depth-2 discreteness producer, feeding `selfDetectsStably_of_discretizes`).
> Finding: the engine is inherently **multi-base** (single-base depth-2 collapses to intersection numbers,
> `intersectionCount_via_w`); see §11.5's LANDED box. Remaining for the cyclotomic slice: **E2** (the `cyclotomicScheme`
> model + the Frobenius/Galois bound = the open `s(C)` content) + **E3** (wiring).
> The oracle-capability seal is a conditional theorem
> `modulo {G3 cited classification + G2-B}` (seal-handoff §2, §4.0). Every provable-now slice is banked
> (G1a depth-graded, G1b leg B, G2-A imprimitive block recovery). The **sole irreducible carried input**
> is `hCascade` (small primitive ⟹ recovers = G2-B). Both empirical falsifiers are clean: the affine
> probe (seal-handoff §G2 (g)) and the **exhaustive Hanaki–Miyamoto catalogue** (orders 5–30, 481
> primitive schemes, all recover — `CatalogueSchemeProbe.cs`, §G2 (f)). This doc plans the one theorem
> that discharges `hCascade` and closes the seal: the **self-detection lemma**.
>
> **The honest framing up front.** Proving the self-detection lemma in full is *open mathematics* (no
> citation bounds `s(C)` for primitive schurian schemes; seal-handoff §6 insight 2, exhaustive-obstruction
> §0.7.6). This plan therefore has two halves with very different risk: **Phase 1 (the multi-base engine +
> the precise crux statement)** is mechanical, axiom-clean, and high-value — it converts the prose
> conjecture into *one falsifiable Lean proposition* and wires it to the seal. **Phase 2 (proving that
> proposition)** is research; it is attacked sub-case first, affine beachhead, and may not fully close.
> Quality bar unchanged: axiom-clean `[propext, Classical.choice, Quot.sound]`, build green, no fresh `axiom`.

---

## 1. The target — discharge `hCascade`

The seal's abstract capstone `reachesRigidOrCameron` (`Cascade.lean`) carries exactly two branch reductions
under any keying (seal-handoff §4.0):

```
hImprimitive : ¬ IsPrimitive → ReachesRigid     -- LANDED: SchemeBlockRecovered (G2-A block recovery)
hCascade     : ¬ NonCascade  → ReachesRigid     -- OPEN: small ⟹ recovers  = G2-B
```

`hImprimitive` is folded (the imprimitive branch is *earned* from visible block recovery, reducing — via the
block tower, ≤ log₂ n layers — to the **primitive floor**). So the lone open input is

> **`hCascade` : a *small* (¬`IsLargeSchemeViaAut`), *primitive* schurian scheme residual reaches a rigid
> residual — i.e. it *recovers* (cells become orbits at bounded individualization depth).**

The self-detection lemma is precisely the proof of this for the primitive floor. With it, the block tower
discharges G2-A onto it, and the seal becomes **unconditional modulo only G3** (the cited Cameron
classification, "as closed as it gets" — seal-handoff §G3).

---

## 2. The engine inventory — what the lemma builds on (all landed, axiom-clean)

The single-base recovery engine is complete; the lemma reuses it wholesale.

| Piece | Where | What it gives |
|---|---|---|
| `EdgeGenerates G v j0` | `Scheme.lean:3169` | depth-1 recovery: the isolation closure of `{R₀,R_{j0}}` reaches all relations |
| `relIsolatedAt_succ`, `IsoPinned`, `isolationStep`, `stage_relIsolatedAt` | `Scheme.lean:2888,3077,3086,3133` | the closure→isolation engine; `IsoPinned` = a relation is the **unique** one with its intersection-count signature into the isolated set |
| `theorem_2_HOR_of_edgeGenerates` | `Scheme.lean:3181` | **P1**: `EdgeGenerates ⟹ cells = orbits` (recovery), no rank ladder |
| `IsoPinned.mono` + saturation (`exists_iterate_isFixed_within`) | `Scheme.lean:3253`, `Saturation.lean` | the "graded pinning saturates the closure in ≤ n rounds" skeleton — **reuse for multi-base** |
| `vProfile_iff_schemeOrbit` | `Scheme.lean:576` | **the load-bearing bridge**: for a schurian scheme, `relOfPair(v,·)`-classes **are** the `Stab(v)`-orbits |
| `schemePartFrom`, `iterFrom_refines_schemePartFrom`, `iterSet_refines_schemePartFrom` | `Scheme.lean:1833,1877,1952` | **the realization half** (multi-base): a depth-k counting partition from an arbitrary base **set** is *refined by* warm refinement — i.e. *any multi-base counting separation is seen by 1-WL* |
| `IntersectionSeparates`, `depth2Det_of_intersectionSeparates` | `Scheme.lean:2524,2535` | the **two-base** realization instance (depth-2 determinacy from intersection-number separation) |
| `RecoverableByDepth`, `CellsAreOrbits`, `recoverableByDepth_univ` | `CascadeOracle.lean:804,268,862` | the **recovery target**: `∃ S, |S| ≤ bound ∧ cells-from-S = orbits-from-S`; vacuous at `bound = n` (the non-vacuity hinge) |
| `SchemeRecoveredByDepth`, `reachesRigidOrCameron_viaDepthRecovery` | `Cascade.lean` (G1a) | the **seal sink**: bounded shallow + deep visible realizers ⟹ the capstone |
| `ClosedSubset`, `IsPrimitive`, `cell_splits_of_imprimitive`, `BlockRefinementVisible`, `SchemePartSeparatesBlock` | `Scheme.lean:164,212,4014,3940,3987` | the **block side** and the named Gate-G predicate (`SchemePartSeparatesBlock` = "the depth-n counting partition respects the block I") |

**Two insights from this inventory that shape the whole attack:**

1. **The gap is PURELY separability, not orbit-vs-cell** (via `vProfile_iff_schemeOrbit`). For a schurian
   scheme the relations *are* the suborbits from a base, so there is no hidden orbit structure for 1-WL to
   miss at the relation level. Recovery fails *only* because iterated counting on the descent's edge relation
   cannot reconstruct `relOfPair` (`¬EdgeGenerates`). **So the crux is a statement about intersection-number
   determinacy of the scheme — attackable on the existing scheme machinery, with no group/orbit detour.**
   (This kills the old "non-abelian ⟹ asymmetric counts" route — `not_comm_of_orbit_disagree` is the *wrong*
   object; seal-handoff §G2 board "C₇ correction".)

2. **The realization half is already landed** (`schemePartFrom`/`iterSet_refines_schemePartFrom`). A
   *multi-base counting separation is automatically a warm-refinement split.* So the lemma never has to prove
   "refinement sees it"; it only has to prove **existence**: that a small base set whose counting *does*
   separate everything exists. The whole burden is the converse — the producer side.

---

## 3. The corrected target — depth-1 is provably insufficient; the object is multi-base

The single-base `EdgeGenerates` is **not** the right recovery notion, and both probes prove it:

- **Cyclotomic affine schemes** (Singer index-3, `|V|=16,64,256`) **fail depth-1 `EdgeGenerates`** — the
  three equal-valency relations are a single-base counting twin — **yet recover at flat depth 4/3/3** and are
  **primitive** (affine probe, §G2 (g)). A single-base deadlock fusion is therefore **NOT** a block:
  primitivity survives it.
- The catalogue confirms it at scale: **5 primitive schemes** (order 16 #20/#21; order 25 #17/#18/#39)
  **fail depth-1 `EdgeGenerates` but recover at bounded WL-depth** (`CatalogueSchemeProbe.cs`).

So the recovery notion must be **base + O(1)** (`RecoverableByDepth bound`, small `bound`), and the deadlock
object must be the **base-homogeneous** twin — a relation pair no *multi-base* counting separates — not the
single-base one. This is the source of the entire engineering need in Phase 1.

> **The non-vacuity hinge.** `RecoverableByDepth adj P n` is vacuously true (`recoverableByDepth_univ`).
> Everything in this plan must be keyed on a *small* bound (`base + c`, `base ≤ log₂|Aut|`). "Small bound"
> is where the open quantitative content lives — it is the WL-dimension / `s(C)` (seal-handoff §6 insight 2).

---

## 4. Phase 1 — the precise crux statement + the `hCascade` wiring (mechanical, the buildable substrate)

Goal: convert the prose conjecture into **one Lean proposition** whose proof discharges `hCascade`, and prove
everything around it.

> **Scope refinement (2026-06-08, from reading the seal source).** The reduction and the crux *statement*
> work on the **semantic** recovery notion already landed — `CellsAreOrbits S` / `RecoverableByDepth bound`
> (`CascadeOracle.lean`) and `SchemeRecoveredByDepth` (`Cascade.lean` G1a) — and do **not** need the heavy
> algebraic multi-base isolation engine (`EdgeGeneratesFromSet`). The reason: `CellsAreOrbits S` (warm cells
> from base set `S` = `Stab(S)`-orbits) *is* multi-base recovery, semantically; the algebraic
> `EdgeGenerates`-style closure is only needed to make recovery **checkable** on a concrete family, which is a
> Phase-2 (crux-proof) concern. So **the multi-base isolation engine (plan §4.1 in the original) defers to
> Phase 2**; Phase 1 is the lighter, fully-achievable reduction below.
>
> **The key wiring fact.** The trichotomy's cascade branch is proved *inside* `by_cases hprim : IsPrimitive`
> (true) — so it can carry `IsPrimitive`. Strengthening it makes `hCascade`'s obligation exactly the
> **primitive floor** (`IsPrimitive ∧ ¬NonCascade ⟹ recovers`), which is what self-detection delivers; the
> imprimitive branch stays on the landed block recovery. This is the honest shape of the open content.

**4.1 — Strengthen the trichotomy / capstone to carry `IsPrimitive` in the cascade branch.**
- `exhaustiveObstruction_scheme_nonCascade_trichotomy'` (`Scheme.lean`) — middle disjunct
  `(IsPrimitive ∧ ¬NonCascade)` instead of `¬NonCascade`. Trivial strengthening (`hprim` is already in scope
  in that branch of the existing proof).
- `reachesRigidOrCameron'` (`Cascade.lean`, abstract) and `reachesRigidOrCameron_viaDepthRecovery'` (concrete)
  — `hCascade : IsPrimitive ∧ ¬NonCascade → ReachesRigid`. So the cascade obligation is the **primitive floor**.

**4.2 — Name the self-detection proposition + the reduction.**
- `SelfDetectsAtDepth (bound) : Prop` (**landed**; planned in earlier drafts as `PrimitiveFloorRecovers`, which
  was never the source name) — *a small, primitive, rank-≥3 schurian scheme residual is
  `SchemeRecoveredByDepth … bound`* (the precise, non-vacuous content: `SchemeRecoveredByDepth` is keyed on
  visible realizers + a bounded shallow phase, false for high `s(C)`; seal-handoff §3). This is exactly the
  sharpened `hCascade`.
- `reachesRigidOrCameron_viaSelfDetection` — from `SelfDetectsAtDepth bound` (cascade branch) + the landed
  imprimitive block recovery (`hImprim`), the seal `SchemeRecoveredByDepth ∨ Cameron`. The whole open seal is
  now the single hypothesis `SelfDetectsAtDepth` + cited G3.

**4.3 — The crux statement (the Phase-2 target), on semantic recovery.**
- **`not_isPrimitive_of_persistentGap`** (THE CRUX — **target name, NOT yet in source**; the open Phase-2 goal):
  for a bound `≥ base + C`, `¬ RecoverableByDepth adj P bound → ¬ IsPrimitive` (equivalently: primitive ⟹
  recovers at `base + C`). The "persistent gap" object (`¬CellsAreOrbits S` for every small `S` = a
  same-cell-different-orbit pair surviving every small base) is the semantic twin; `vProfile_iff_schemeOrbit`
  makes it a pure separability statement about intersection numbers. Proving it gives `SelfDetectsAtDepth`,
  closing the seal. (The §5 block-side vocabulary names the **same** open statement
  `not_isPrimitive_of_baseHomogeneousTwin` — two faces of one Phase-2 target; **neither is landed**.)

**Phase-1 outcome (achievable, axiom-clean):** the seal is reduced to the single proposition
`SelfDetectsAtDepth` (the primitive-floor `hCascade`; satisfied by proving the crux
`not_isPrimitive_of_persistentGap`, the open Phase-2 target) + the cited G3, with `IsPrimitive` honestly
carried into the cascade branch and the imprimitive branch on landed block recovery. The catalogue probe (`CatalogueSchemeProbe.cs`) *already tests this proposition's emptiness
empirically* (a persistent-gap primitive scheme would be a non-recovering primitive scheme — none in orders
5–30). Phase 1 makes the open gap a *precise, falsifiable, single* statement — genuine progress independent of
whether Phase 2 closes. The algebraic multi-base isolation engine (`EdgeGeneratesFromSet`) is deferred to
Phase 2, where it makes the crux *checkable* on the affine family (§5.1).

> **INCREMENT 1 LANDED (2026-06-08, axiom-clean `[propext, Classical.choice, Quot.sound]`, full build green).**
> §4.1 + §4.2 are done:
> - `exhaustiveObstruction_scheme_nonCascade_trichotomy'` (`Scheme.lean`) — middle disjunct carries
>   `IsPrimitive`.
> - `reachesRigidOrCameron'` (abstract) + `reachesRigidOrCameron_viaDepthRecovery'` (concrete) (`Cascade.lean`)
>   — `hCascade : IsPrimitive ∧ ¬NonCascade → ReachesRigid`, the primitive-floor obligation.
> - `SelfDetectsAtDepth` (`Cascade.lean`) — the named self-detection proposition (primitive ∧ small ⟹
>   `SchemeRecoveredByDepth`), the seal's single open content.
> - `reachesRigidOrCameron_viaSelfDetection` (`Cascade.lean`) — the seal from `SelfDetectsAtDepth` + landed
>   imprimitive block recovery.
>
> **INCREMENT 2 LANDED (2026-06-08, axiom-clean, build green) — the semantic-recovery bridge.** A scope
> finding shaped it: `SchemeRecoveredByDepth`'s deep clause quantifies over **every** `T ⊇ S₀`, so a single
> `CellsAreOrbits S₀` is *not* enough (the per-`T` realizers must fix `T`'s extra points — the localisation,
> insight 7). The honest semantic match is **stable** recovery:
> - `StablyRecoverable adj P S₀ := ∀ T ⊇ S₀, CellsAreOrbits adj P T` (`Cascade.lean`) — cells = orbits *above*
>   `S₀`; non-vacuous (false for high `s(C)`), exactly what separability monotonicity yields.
> - `schemeRecoveredByDepth_of_stablyRecoverable` — the clean bridge `StablyRecoverable (|S₀| ≤ bound) ⟹
>   SchemeRecoveredByDepth bound` (gens = all residual auts at ∅; deep clause from `CellsAreOrbits T` via
>   `orbitPartition_iff_residualAut` + `mem_stabilizerAt_empty`; base from `exists_isBase_saturated`).
> - `SelfDetectsStably` + `selfDetectsAtDepth_of_selfDetectsStably` + `reachesRigidOrCameron_viaStableRecovery`
>   — the seal reduced to the **semantic** crux: *primitive small ⟹ ∃ small `S₀`, cells = orbits above `S₀`*.
>
> **Net: the seal's entire open content is now a statement about `CellsAreOrbits` (separability), not the
> harvest-witness `SchemeRecoveredByDepth`** — the object Phase 2's affine argument produces and the catalogue
> probe measures. **Phase 1 reduction is complete end-to-end.** Next is Phase 2 (the crux proof, §5).

---

## 5. Phase 2 — proving the crux (research; sub-case first)

The crux (**target name, NOT yet in source** — the block-side face of §4.3's `not_isPrimitive_of_persistentGap`)
`not_isPrimitive_of_baseHomogeneousTwin` = "a base-homogeneous twin forces a non-trivial `ClosedSubset`." The
mechanism (seal-handoff §G2 anatomy, Thread T2 / P3): **a gap that survives every base is base-homogeneous =
supported by an invariant subspace / block system; primitivity forbids it.** Three attack surfaces, by Lean
tractability:

**5.1 — Affine / translation-scheme beachhead (PRIMARY — Mathlib has the tools).** For a translation scheme
`V⋊G₀` over `F_p^d`, a base-homogeneous twin ⟺ a `G₀`-invariant `F_p`-subspace `W ⊆ V` (the "linear coupling"
= the gap's only base-homogeneous support), which **is** a block system ⟹ imprimitive. Primitive ⟺ `G₀`
irreducible ⟹ no proper invariant `W` ⟹ no twin ⟹ recovers. **Why this is the beachhead:** Mathlib *has*
modules, `Submodule`, `GL`, irreducibility (`IsSimpleModule`) — the substrate the Bose–Mesner/eigenvalue route
(5.3) entirely lacks (exhaustive-obstruction §4 R5). The proof is linear algebra over `F_p^d`. **Honest gap:**
needs translation schemes *modelled in Lean* (today only in `AffineSchemeProbe.cs`) as a `SchurianScheme`
instance — a real but self-contained infrastructure build, and the affine probe is the executable spec.
Predicted to close for bounded `d` (mirrors Ponomarenko's prime-power circulant `WL-dim ≤ 3`). This is the
sharpest concrete instance of the crux and the recommended first proof.

> **LOAD-BEARING INSIGHT (2026-06-08, from reading the recovery semantics — generalizable to the whole crux).**
> The seal's recovery predicate is `CellsAreOrbits (schemeAdj S) …`, and **`schemeAdj S` encodes the *full*
> scheme** (`adj v w = (relOfPair v w).val`, a multi-valued edge label `signature` reads in full). Consequences:
> 1. **Single-base recovery is FREE for every schurian scheme.** `warmRefine` from `{v}` separates by
>    `relOfPair(v,·)` (the unique colour of the individualized `v` makes the `v`-neighbour tuple identify the
>    relation), and for a schurian scheme `relOfPair(v,·)`-classes **are** the `Stab(v)`-orbits
>    (`vProfile_iff_schemeOrbit`). With `orbits ⊆ cells` (auts preserve `warmRefine`), this forces
>    `cells = orbits` at `{v}`. So `CellsAreOrbits (schemeAdj S) … {v}` holds **unconditionally** — *no*
>    `EdgeGenerates`, *no* affine structure. (This is *not* the `theorem_2_HOR`/`EdgeGenerates` setting, which is
>    the harder *single-relation* graph `J={j0}` — `schemeAdj` is the full colouring, where recovery is free.)
> 2. **The entire crux is therefore MULTI-BASE** (`|T| ≥ 2`). The `s(C)` gap is that the *joint* profile
>    `(relOfPair(v,·), relOfPair(x,·))` need not determine the *joint* `Stab(v,x)`-orbit — there iterated 1-WL
>    can fall short. `StablyRecoverable S₀ = ∀ T ⊇ S₀, CellsAreOrbits T` is genuinely about these multi-base `T`.
> 3. **This is *why* the reduction is non-vacuous** (resolves the §3 worry concretely): single-base is free but
>    `StablyRecoverable` quantifies over *all* supersets, and multi-base recovery is the real `s(C)` content.
> 4. **Generalizable target shape:** the crux = "primitive ⟹ a *bounded* base set makes the *joint* profile
>    determine the *joint* orbit." For affine, "joint profile determines joint orbit" becomes a linear-algebra
>    statement about `(G₀)_x`-orbits and invariant subspaces; for the general crux it is the multi-base
>    separability bound. The single-base theorem is the shared base case.
>
> **Modelling note:** the `schemePart_at`/`relIsolatedAt`/`EdgeGenerates` machinery is built for
> `SchurianSchemeGraph` (a `J`-binarized adjacency), **not** `schemeAdj` (full `relOfPair`). Recovery proofs on
> the seal's `schemeAdj` need their own `warmRefine`-internals lemmas (or a `schemeAdj`↔`SchurianSchemeGraph`
> bridge). The single-base theorem (Increment A1) builds the first such lemma.

**Increment A1 — LANDED (2026-06-08, axiom-clean `[propext, Classical.choice, Quot.sound]`, build green).**
The single-base recovery theorem (general, the insight as a theorem):
- `cellsAreOrbits_schemeAdj_singleton (S : SchurianScheme n) (v) : CellsAreOrbits (schemeAdj S…) … {v}` — for
  *every* schurian scheme, `warmRefine` cells at a single base coincide with the `Stab(v)`-orbits.
- `relOfPair_eq_of_warmRefine_singleton` — `warmRefine` from `{v}` separates by `relOfPair(v,·)` (peel to one
  round via `iterate_refineStep_colour_refines`, `refineStep_iff`, then the count bridge `signature_eq_card_eq`
  — the individualized `v`'s unique colour isolates its neighbour-tuple). Combined with `vProfile_iff_schemeOrbit`
  + `isAut_schemeAdj_iff`. Helpers: `iterate_refineStep_colour_refines`, `individualizedColouring_singleton_sep`;
  made `signature_count_eq_card`/`signature_eq_card_eq` public.

**Net:** single-base recovery on `schemeAdj` is now a *theorem* (free, general — not affine-specific), confirming
the insight and giving the reusable base case. **The remaining crux is exactly the multi-base extension**
(`StablyRecoverable {v}` = `∀ T ⊇ {v}, CellsAreOrbits T`, where `|T| ≥ 2` is the `s(C)` content). Next: the
affine multi-base argument — model `V⋊G₀` and show irreducible `G₀` ⟹ a bounded base makes the *joint* profile
determine the *joint* `(G₀)_x`-orbit (twin ⟺ invariant subspace ⟺ block).

**5.2 — Rank-3/4 slice (connects to G3, possibly citation-light).** A primitive **rank-3** scheme is an SRG;
a base-homogeneous twin can only be between the two non-diagonal relations `R₁,R₂`, forcing equal valency +
matched intersection numbers = a conference-graph-type degeneracy. Whether *every* primitive rank-3/4
schurian scheme recovers at bounded depth (`s(C)` bounded) is a sharp, finite-flavoured question; if true it
closes the rank-3/4 G2-B slice **without** the G3 citation (and dovetails with G3 being solid exactly at rank
3/4). Risk: SRG WL-dimension is not universally bounded in general, so this may itself be a real sub-theorem —
but it is the most self-contained *combinatorial* slice and a good correctness check on Phase 1's twin object.

**5.3 — The structural P3 / Gate-G (general, hardest).** `BaseHomogeneousTwin ⟹ ClosedSubset` directly:
build `I` from the twin's "difference support" and verify the complex-product closure axiom (`ClosedSubset`,
`Scheme.lean:164`) using base-homogeneity to discharge each closure obligation. The **realization warm-up is
landed** (`schemePartFrom` + `iterSet_refines_schemePartFrom`); the converse is the open content. This is the
fully general statement and the eventual goal, but it needs the multi-base fusion-coherence theory (a fusion
of an association scheme is an association scheme) which Mathlib lacks — heaviest. Pursue only after 5.1.

> **The reusable template for this is now concrete — see §10.1 (I2).** M1 (affine) is the *rehearsal* of exactly
> this `BaseHomogeneousTwin ⟹ ClosedSubset` shape: it builds a `ClosedSubset` from a `G₀`-invariant `Submodule`
> and shows primitivity forbids it. The §5.3 general proof swaps `Submodule` ↔ fusion/`ClosedSubset` and
> "invariant subspace" ↔ "block system." Do the affine one (M1.2) first; the shape transfers. §10.1 (I1, I3)
> spell out why the content is *separability of the orbit Schur ring* and why primitivity is the lever.

**The logic threading all three:** *a separability gap that is invariant under every base is a linear /
character degeneracy = a sub-structure (subspace 5.1 / closed subset 5.3) that primitivity rules out.* The
affine case makes "sub-structure" a literal `Submodule` (Mathlib-native); the general case makes it a
`ClosedSubset` (project-native). Same theorem, two vocabularies — prove the affine one first.

---

## 6. The gate already in place — the catalogue falsifier

`CatalogueSchemeProbe.cs` (board item (f), DONE) is the empirical gate on the crux: it exhaustively checks
that **no small primitive schurian scheme is non-recovering** (orders 5–30: 481 primitive, all recover, 0
candidates, validated against the published catalogue counts). A genuine `BaseHomogeneousTwin` primitive
scheme *is* a non-recovering primitive scheme — so the probe is the executable contrapositive of the crux.
**Before any heavy Phase-2 Lean investment, extend the probe's order range** (the catalogue goes past 30; the
data fetch is wired) — a counterexample there would change the *statement*, not the proof, and is far cheaper
to find than to rule out in Lean.

---

## 7. Honest scope — what closes, what stays open

- **Phase 1 is DONE** (axiom-clean, Increments 1+2 landed): the seal reduced to one precise *landed*
  proposition — `SelfDetectsStably` (semantic) / `SelfDetectsAtDepth` (its harvest-witness form) — via the
  multi-base engine and the `hCascade` wiring. Net: seal = unconditional **modulo {G3 + `SelfDetectsStably`}**,
  with the proposition empirically gated by the catalogue probe. (Proving `SelfDetectsStably` is Phase 2; its
  open crux is `not_isPrimitive_of_baseHomogeneousTwin` = `not_isPrimitive_of_persistentGap`, target-only.)
- **Phase 2, 5.1 (affine) plausibly closes** the affine slice of the crux (bounded `d`), with new Lean
  infrastructure (translation schemes). 5.2 (rank-3/4) is a sharp finite-flavoured slice. **5.3 (general) is
  open mathematics** — there is no citation, and the full "primitive schurian ⟹ separable" may be a genuine
  research theorem in its own right.
- **The seal becomes fully unconditional** only when 5.3 (or a union of slices covering all primitive
  residuals) lands. That is the frontier; this plan makes it a *single, stated, tested* frontier rather than a
  diffuse conjecture.

**Recommended first build: Phase 1 (§4) — the multi-base engine + the crux statement + the `hCascade`
wiring.** It is mechanical, axiom-clean, reuses the landed single-base skeleton, and is the necessary
substrate for *every* Phase-2 attack. Phase 2 starts at the affine beachhead (§5.1).

---

## 8. Cross-references

- [`chain-descent-seal-handoff.md`](./chain-descent-seal-handoff.md) §4.0 (no re-keying closes the seal),
  §G2 anatomy + attack board (the conjecture, the conservation route, the probes), §6 insights 2/8/9/10.
- [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md) §0.7.2 (the bottom-up
  derivation), §0.7.6 (the `s(C)` verdict: open, uncitable).
- `Scheme.lean` §10 (the isolation engine, `schemePartFrom` realization), §1.2 (`ClosedSubset`/`IsPrimitive`),
  §13 (`BlockRefinementVisible`/`SchemePartSeparatesBlock`/`cell_splits_of_imprimitive`).
- `Cascade.lean` (G1a `SchemeRecoveredByDepth`, the seal capstones), `CascadeOracle.lean`
  (`RecoverableByDepth`/`CellsAreOrbits`).
- `GraphCanonizationProject.Tests/CatalogueSchemeProbe.cs`, `AffineSchemeProbe.cs` (the empirical gates).

---

## 9. Affine multi-base — the detailed build plan (PICK UP HERE)

> **For a fresh reader.** Phase 1 is done: the seal closes once you prove `SelfDetectsStably S IsLarge bound`
> for every primitive small schurian residual `S` (def in `Cascade.lean`; = *primitive ∧ small ⟹ ∃ S₀,
> |S₀| ≤ bound ∧ `StablyRecoverable (schemeAdj S) … S₀`*, where `StablyRecoverable adj P S₀ := ∀ T ⊇ S₀,
> CellsAreOrbits adj P T`). **Increment A1** landed the base case: `cellsAreOrbits_schemeAdj_singleton` —
> single-base recovery (`CellsAreOrbits … {v}`) is **free** for every schurian scheme. The remaining content
> is **multi-base** recovery (`|T| ≥ 2`), and the affine family `V⋊G₀` over `F_p^d` is the beachhead where
> Mathlib's linear algebra applies. This section is the build plan: the model (M0), the block↔subspace bridge
> (M1), the recovery crux (M2), the wiring (M3) — with signatures, Mathlib/project anchors, risks, and the
> build order. The executable spec for every object below is `AffineSchemeProbe.cs` (it builds exactly these
> orbital schemes, intersection numbers, primitivity = irreducibility, recovery = `EdgeGenerates`/depth).

### 9.0 Two constraints found while planning (read first — they shape everything)

1. **The project's `AssociationScheme` is SYMMETRIC** (`Scheme.lean:64`, field `rel_symm : ∀ i v w, rel i v w
   = rel i w v`). So every relation is its own transpose. For a translation scheme the relation of `(x,y)` is
   the `G₀`-orbit of `y − x`; it is symmetric **iff `G₀`-orbits are closed under negation** (`−v` in the same
   orbit as `v`), i.e. **iff `−1 ∈ G₀`** (or one symmetrizes by merging `O` with `−O`). **Decision for the
   beachhead: restrict to `−1 ∈ G₀`.** Many interesting irreducible groups contain `−1` (orthogonal groups,
   most Singer normalizers); the cyclotomic probe families can be chosen so. (Generalizing the framework to
   *commutative* non-symmetric schemes is a much larger change — out of scope; flag it but do not do it.)
2. **There is NO group-orbital `SchurianScheme` constructor yet** — only `trivialScheme`/`trivialSchurianScheme`
   (rank 1, `Scheme.lean:335/353`). M0 must build one. **Before building from scratch, check** how the Cameron
   battery built Johnson/Hamming schemes (`CameronGraphGenerator.cs` is C#; the Lean side may only have
   `SchurianSchemeGraph` via `IsSchurianSchemeGraph'`, the `J`-binarized form — *not* a full `SchurianScheme`).
   The reusable abstraction to build is **the orbital scheme of a transitive permutation group** (M0 below);
   affine is then one instance, and it also serves any future Phase-2 family (PSL, classical — §5.2).

### 9.1 M0 — the model: orbital scheme of a transitive group (the infrastructure)

> **M0 LANDED (2026-06-08, axiom-clean `[propext, Classical.choice, Quot.sound]`, full build green, `Scheme.lean
> §3.1`).** The general orbital-scheme constructor is built — Option A (full `SchurianScheme`), on `Fin n`
> (so **no `V ≃ Fin(p^d)` transport**, the key simplification). Landed decls:
> - `Orbital G := Quotient (orbitRel G (Fin n × Fin n))` (the orbitals) + `orbMk v w`; `orbMk_eq_iff`
>   (same orbital ⟺ `∃ g ∈ G` carrying the pair), `orbMk_smul` (`g ∈ G` fixes orbitals), `orbMk_diag_iff`
>   (diagonal orbital ⟺ `v=w`, under transitivity), `orbMk_out` (representative pair).
> - The indexing: `orbitalRank G := #orbitals − 1`, `orbitalRank_succ`, `orbitalIdx : Fin (rank+1) ≃ Orbital G`
>   with `orbitalIdx_zero` (index `0` = diagonal, via `Equiv.swap`).
> - **`orbitalAssocScheme G htrans hsymm : AssociationScheme n`** — all 7 fields; the load-bearing
>   `intersectionNumber_well_defined` via `Finset.card_bij'` with the bijection `u ↦ ↑(g⁻¹) u` (transitivity on
>   each orbital ⟹ constant witness count).
> - **`orbitalScheme G htrans hsymm : SchurianScheme n`** — the schurian field (same-orbital pairs are
>   `G`-related; witness `g ∈ G` is a `IsSchemeAut`). Pluggable into `SelfDetectsStably`/the seal.
>
> Hypotheses: `[Nonempty (Fin n)]`, `htrans : MulAction.IsPretransitive G (Fin n)`, `hsymm` = generous
> transitivity (`orbMk v w = orbMk w v`, the symmetric-scheme constraint 9.0(1) — affine discharges it via
> `−1 ∈ G₀`). **Next: M0.3** — the affine instance `affineScheme := orbitalScheme (image of V⋊G₀) …`, then M1.

**Goal.** A constructor `orbitalScheme : (G : Subgroup (Equiv.Perm (Fin n))) → (htrans : transitive) →
SchurianScheme n`, then the affine instance `G = image of V⋊G₀ in Perm(V)` via `V ≃ Fin (p^d)`.

**M0.1 — the general orbital `AssociationScheme`.** Relations = the 2-orbits (orbitals) of `G` on `Fin n ×
Fin n`. Concretely:
- `orbitalSetoid : Setoid (Fin n × Fin n)` = `MulAction.orbitRel G (Fin n × Fin n)` under the diagonal action.
- `rank + 1 = Fintype.card (Quotient orbitalSetoid)`; pick an indexing `Fin (rank+1) ≃ Quotient …` with the
  diagonal orbital `{(v,v)}` mapped to `0` (it is one orbital because `G` is transitive).
- `rel i v w := (orbital index of (v,w)) = i`; `relOfPair v w := that index`.
- `intersectionNumber i j k := |{u : (v,u) ∈ R_i ∧ (u,w) ∈ R_j}|` for a chosen `(v,w) ∈ R_k`.
- **Axioms:** `rel_zero_iff_eq` (diagonal orbital ↔ `v=w`), `rel_symm` (**needs the orbital closed under
  swap** — true iff `G` is *generously transitive* / the scheme symmetric; this is exactly constraint 9.0(1),
  so for affine assume `−1 ∈ G₀`), `rel_partition` (orbitals partition pairs — `Quotient` is a partition),
  `intersectionNumber_well_defined` (the count is constant on `R_k` — **the load-bearing axiom**, follows from
  `G`-transitivity on the orbital `R_k`: any two `R_k`-pairs are `G`-related, and `g` bijects the witness
  sets). The well-definedness proof is the main work; it is the orbital-counting-is-`G`-equivariant argument.
- **Mathlib anchors:** `MulAction.orbitRel`, `MulAction.orbit`, `Quotient`, `Fintype.card`,
  `MulAction.IsPretransitive`. Project: mirror `trivialScheme`'s field-filling style.

**M0.2 — schurian.** `IsSchemeAut (orbitalScheme G) g` for `g ∈ G` (G preserves its own orbitals), and the
schurian property (relations = orbitals of `SchemeAutGroup ⊇ G`). Since orbitals of `Aut ⊇ G` refine the
`G`-orbitals but `Aut` preserves relations, they coincide — so `orbitalScheme G` is schurian with
`SchemeAutGroup ⊇ G`. (For affine, `SchemeAutGroup = V⋊G₀` exactly when `G₀` is the full linear stabilizer;
in general `⊇`, which is fine — schurian only needs *some* transitive group with these orbitals.)

> **M0.3 LANDED (2026-06-08, axiom-clean `[propext, Classical.choice, Quot.sound]`, full build green,
> `Cascade.lean §AffineScheme`).** The affine beachhead model is built — and **simpler than the original M0.3
> sketch**: rather than `AffineEquiv`/`linearHom`/`permCongrHom`/double-`.map`, the affine group is built
> directly as `Subgroup.closure` of explicit affine perms, reusing landed `orbitalScheme`. Decls:
> - `affineE : (Fin d → ZMod p) ≃ Fin (p^d)` (transport, via `affV_card`); `affineEquivV g₀ t : Perm V`
>   (`x ↦ g₀ x + t`, explicit inverse); `affinePermFin g₀ t := affineE.permCongr (affineEquivV g₀ t)` +
>   `affinePermFin_apply`.
> - `affineGenSet G₀` (`{x ↦ g₀ x + t | g₀ ∈ G₀}`), **`affineG G₀ := Subgroup.closure (affineGenSet G₀)`**
>   (the affine group `V ⋊ G₀` ≤ `Perm (Fin (p^d))`).
> - `affineG_isPretransitive` (translations, `g₀=1`); `affineG_generous` (`-1 ∈ G₀` ⟹ `orbMk x y = orbMk y x`,
>   via the swap `u ↦ -u + (x+y)`).
> - **`affineScheme G₀ (hneg : LinearEquiv.neg (ZMod p) ∈ G₀) : SchurianScheme (p^d)`** :=
>   `orbitalScheme (affineG G₀) …` — pluggable into `SelfDetectsStably`/the seal.
>
> Parameters: `{p d : ℕ} [Fact p.Prime]`, `G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))`,
> `hneg`. The relations are the `G₀`-orbits on differences (`relOfPair x y` = orbit of `y−x`) — *to be
> characterized in M1*. **Next: M1** (block ⟺ `G₀`-invariant subspace; `IsPrimitive` ⟺ irreducible).
>
> **Generalization insight (captured in source).** The construction uses only *regular abelian translations*
> + a *point-stabilizer closed under negation*; nothing is special to `F_p^d` beyond `V` being a finite
> module. The same shape models any **translation scheme** (`T ⋊ G₀`, `T` regular abelian = the Schur-ring
> setting M2 targets). The linear structure of `V` only enters at M1/M2.

**M0.3 — the affine instance.** `V := Fin d → ZMod p` (a finite `Module (ZMod p)`, `Fintype`, `card = p^d`).
`G₀ : Subgroup (V ≃ₗ[ZMod p] V)` with `−1 ∈ G₀`. The affine group acts on `V` by `(t, g)·x = g x + t`.
Transport to `Equiv.Perm (Fin (p^d))` via `e : V ≃ Fin (p^d)` (`Fintype.equivFinOfCardEq`). Define `affineG :
Subgroup (Equiv.Perm (Fin (p^d)))` as the image; `affineScheme := orbitalScheme affineG htrans`. Transitivity
is free (translations act transitively). **Mathlib anchors:** `Module (ZMod p)`, `LinearEquiv`,
`SemidirectProduct` (or hand-roll the action), `Fintype.equivFinOfCardEq`, `MulEquiv`/`Equiv.Perm` transport.
**Risk:** the `V ≃ Fin (p^d)` transport bureaucracy is annoying but mechanical; budget for it.

> **Decision point (M0).** *Option A — full `SchurianScheme`* (above): heavier, but plugs directly into the
> seal (`SelfDetectsStably` is stated on `SchurianScheme`). *Option B — direct colored graph*: build the
> colored Cayley graph on `V` (`adj x y = relOfPair x y`), prove recovery there, bridge to `SchurianScheme`
> separately. B isolates the *math* (recovery) from the *packaging*, but you still need the packaging for the
> seal. **Recommend A** via the general `orbitalScheme` constructor — it is reusable for §5.2 and avoids a
> second bridge. Estimate M0 at the bulk of the affine build.

### 9.2 M1 — block ⟺ invariant subspace; primitive ⟺ irreducible (the insight, Mathlib-clean)

> **M1.0 + M1.0b LANDED (2026-06-08, axiom-clean, full build green, `Cascade.lean §AffineScheme`).**
> - **M1.0 (foundational refactor):** `affineG` is now the **carrier-set subgroup** of affine perms (was
>   `Subgroup.closure`), via algebra helpers `affinePermFin_one`/`affinePermFin_mul` (`affinePermFin g₀ t *
>   affinePermFin h₀ s = affinePermFin (g₀h₀) (g₀s+t)`)/`affinePermFin_inv`. Gives **`mem_affineG_iff`** :
>   `σ ∈ affineG ↔ ∃ g₀∈G₀, ∃ t, σ = affinePermFin g₀ t` (`Iff.rfl`) — transparent membership.
> - **M1.0b (the Schur-ring characterization):** **`orbMk_affine_eq_iff`** : `orbMk x y = orbMk x' y' ↔
>   ∃ g₀∈G₀, g₀ (e⁻¹y′−e⁻¹x′) = e⁻¹y−e⁻¹x`. I.e. relations of `affineScheme` ↔ `G₀`-orbits on differences =
>   the orbit Schur ring `A(G₀)`. This is the bridge the block ⟺ invariant-subspace argument runs on.
>
> **M1.1 + M1.2 LANDED (2026-06-08, axiom-clean `[propext, Classical.choice, Quot.sound]`, full build green,
> `Cascade.lean §AffineScheme` + `Scheme.lean §1.2`).** The irreducibility bridge is built — `primitive ⟹ G₀
> irreducible`, the §5.3 template instantiated. Decls:
> - **M1.1c (general, `Scheme.lean`):** `AssociationScheme.exists_composable_of_intersectionNumber` —
>   `R_k` nonempty ∧ `intersectionNumber i j k ≠ 0 ⟹ ∃ x y z, rel i x y ∧ rel j y z ∧ rel k x z`. **Stated
>   generally** (the §5.3-reusable ingredient; `R_k`-nonemptiness is an explicit hypothesis since the scheme
>   axioms do not force every index inhabited).
> - **M1.1a:** `affineScheme_rel_iff` (`rel i x y = true ↔ orbitalIdx i = orbMk x y`), `affineScheme_relOfPair`
>   (`relOfPair = orbitalIdx.symm ∘ orbMk`), `affineScheme_relOfPair_eq_iff` (same relation ⟺ same orbital).
> - **M1.1b:** `def G₀Irreducible` = `∀ W : Submodule (ZMod p) (Fin d → ZMod p), G₀-invariant W → W = ⊥ ∨ W = ⊤`
>   (self-contained, **no** `IsSimpleModule`/`IsPreprimitive` — see gotcha below for why this is cleaner).
> - **Well-definedness:** `affineRelDiff` (a relation's representative difference) + `affineRelDiff_zero`
>   (diagonal → `0`) + **`affineRelDiff_mem_iff`** (`affineRelDiff i ∈ W ⟺ (e⁻¹y−e⁻¹x) ∈ W` for any pair in
>   `R_i`, `W` invariant) — where invariance does the work (all `R_i`-pairs are `G₀`-translates).
> - **M1.2 (THE BRIDGE):** **`isPrimitive_affineScheme_imp_irreducible`** : `IsPrimitive (affineScheme) →
>   G₀Irreducible`, by contrapositive — from a proper invariant `W`, build `I := {i | affineRelDiff i ∈ W}`,
>   prove `ClosedSubset I` (`0 ∈ I` via `affineRelDiff_zero` + `W.zero_mem`; closure via the composable triple's
>   differences adding + `W.add_mem`), `I ≠ {0}` (a nonzero `w ∈ W`), `I ≠ univ` (a `v ∉ W`) — contradicting
>   primitivity. **The §5.3 "block = sub-structure; primitivity forbids it" template, concretely realized.**
>
> **DECISION (corrected from the §9.2 prose below): M1.2 is proved DIRECTLY, not through Mathlib
> `isPreprimitive_iff_isPrimitive`.** The prose route (scheme `IsPrimitive` ⟺ `IsPreprimitive (SchemeAutGroup)`
> ⟺ no invariant subspace) needs the Mathlib fact "blocks of `V⋊G₀` through 0 ↔ `G₀`-invariant subgroups,"
> which is *not* in Mathlib and would itself need proving. The direct `ClosedSubset`-from-`Submodule`
> construction sidesteps that entirely and is the §5.3-faithful shape. The `isPreprimitive_iff_isPrimitive`
> bridge stays available for G3 but is **not** on M1.2's path. The converse (`G₀Irreducible → IsPrimitive`,
> §10.2 nice-to-have) is **not** built — M3 only consumes the forward direction.
>
> **GENERALIZATION INSIGHT (carry to §5.3 — see §10.1 I2 augmented).** The §5.3 general crux needs exactly the
> same proof skeleton with two substitutions: (a) `affineRelDiff_mem_iff`'s role — "a relation-invariant
> quantity that a sub-structure can't separate" — becomes "the difference support of a base-homogeneous twin";
> (b) `exists_composable_of_intersectionNumber` is **already general** (lives in `Scheme.lean`), so the
> closure clause of the general `ClosedSubset` reuses it verbatim. The *additive* structure (`δ_k = δ_i + δ_j`
> on a composable triple ⟹ `W.add_mem`) is what makes "a relation-subset closed under the complex product"
> into "a subspace" — the precise reason primitivity (no proper invariant sub-structure) forces recovery. In
> the general scheme this `+` is replaced by the fusion/complex-product itself, so the general `ClosedSubset`
> *is* the closure object with no module needed — the affine `Submodule` is just the linear shadow.
>
> **NEXT: M2** (irreducible `G₀` ⟹ `StablyRecoverable` bounded; M2-cyclic first) then M3 (wire to
> `SelfDetectsStably`). M0+M1 are now a complete, reusable "affine primitive ⟺ irreducible" theorem.

**Goal.** Translate the seal's `IsPrimitive` hypothesis into `G₀`-irreducibility, which M2 consumes.

- **M1.1 — `ClosedSubset` ⟺ `G₀`-invariant subspace.** For the affine scheme, a `ClosedSubset I`'s block of
  `0` (`{y | schemeEquiv I 0 y}`) is the union `W = ⋃_{i∈I} O_i ⊆ V`. Show `W` is an **`F_p`-subspace**: `0 ∈
  W` (`R_0`), closed under `+` (the complex-product-closure of `ClosedSubset` ↔ `O_i + O_j ⊆ W`), and
  `G₀`-invariant (orbits). Conversely a `G₀`-invariant subspace `W` gives `I = {orbits in W}`, a `ClosedSubset`.
  **Mathlib:** `Submodule (ZMod p) V`, `Submodule.add_mem`, `AddSubgroup` (over `F_p`, subgroup = subspace via
  `zsmul`). Project: `ClosedSubset`, `schemeEquiv`, `schemeEquiv_class_eq_iff` (`Scheme.lean`).
- **M1.2 — `IsPrimitive` ⟺ `IsSimpleModule (ZMod p) V` (irreducible `G₀`).** Chain: scheme `IsPrimitive`
  ⟺ (landed `isPreprimitive_iff_isPrimitive`, `Scheme.lean:3665`) Mathlib `IsPreprimitive (SchemeAutGroup) V`
  ⟺ (affine: blocks-through-0 = invariant subspaces, M1.1) no proper non-trivial `G₀`-invariant subspace
  ⟺ `G₀` acts irreducibly. **Mathlib:** `MulAction.IsPreprimitive`, `MulAction.IsBlock`, `IsSimpleModule`,
  and the affine-primitivity fact (blocks of `V⋊G₀` through 0 ↔ `G₀`-invariant subgroups — may need proving;
  search Mathlib `IsBlock` + normal-subgroup-of-regular for a shortcut). This is the clean, reusable
  "block = sub-structure, primitivity forbids it" piece — the generalizable insight made concrete.

### 9.3 M2 — the recovery crux: irreducible `G₀` ⟹ `StablyRecoverable` bounded (THE RESEARCH CONTENT)

> **M2 REDUCTION LANDED (2026-06-08, axiom-clean, full build green, `Cascade.lean`) — the crux is now a
> refinement-only (orbit-free) statement, FOR ANY SCHURIAN SCHEME.** Two general theorems:
> - **`stablyRecoverable_of_discrete`** : `Discrete (warmRefine adj P (individualizedColouring n S₀)) →
>   StablyRecoverable adj P S₀`. Discreteness propagates to every `T ⊇ S₀` (`individualizedColouring_refines`
>   + `warmRefine_refines_initial`: a finer initial colouring stays discrete), then `cellsAreOrbits_of_discrete`.
> - **`selfDetectsStably_of_discretizes`** : `SelfDetectsStably` ⟸ *"primitive small ⟹ ∃ bounded `S₀`,
>   `warmRefine`-from-`S₀` discrete"*.
>
> **So the ENTIRE seal crux reduces to: "primitive small ⟹ bounded individualization discretizes."** This is
> the cleanest form — pure refinement reaching singletons, no orbits — and it holds for *any* schurian scheme
> (not just affine), so it advances the whole crux, not only the affine slice. **Faithful, not lossy:** at the
> primitive floor `StablyRecoverable S₀` forces `CellsAreOrbits` at a base above `S₀` where orbits are trivial,
> hence discreteness there — `Discrete` and `StablyRecoverable` are equivalent for the crux. **GENERALIZATION
> INSIGHT (carry to §5.3 / §10.1):** discretization depth splits as **base(G)** [group-theoretic: a spanning set
> of ≤ d points gives trivial stabilizer — easy] **+ s(C)** [WL-dimension stickiness — the OPEN term]; the
> reduction isolates the open content to exactly `s(C)`. It unifies the crux with CFI's
> `theorem_1_HOR_cfi_oddDeg` (discreteness at depth `tw`), `isBase_of_discrete_warmRefine`, and the probes
> (which measure greedy depth-to-discreteness). **What remains open (M2-B, below) is the affine discreteness
> proof itself** — `irreducible G₀ ⟹ ∃ bounded S₀, Discrete(warmRefine affine schemeAdj S₀)` — whose `s(C)`
> term is the genuine, citation-free WL-dimension content. The base term (a spanning set ⟹ `Stab = 1`) is the
> easy half.

> **M2-B DEPTH-1 PRODUCER LANDED (2026-06-08, axiom-clean, full build green, `Cascade.lean`).** A concrete,
> finite, checkable *sufficient condition* for the discreteness `stablyRecoverable_of_discrete` needs:
> - **`discrete_of_jointProfileSeparates`** (general, any scheme): if the depth-1 joint profile
>   `(relOfPair t ·)_{t∈T}` is **injective**, then `warmRefine (schemeAdj S)` from `T` is `Discrete`. Mechanism:
>   cells refine the joint profile — the multi-base generalization of A1's `relOfPair_eq_of_warmRefine_singleton`,
>   which **reduces to the single-base A1 lemma** via `warmRefine_refines_initial` (warmRefine-from-`T` refines
>   warmRefine-from-`{t}`), no fresh signature argument; pairs meeting `T` collapse by singleton preservation
>   (`individualizedColouring_mem_sep`).
> - **`discrete_affineScheme_of_jointSeparates`** (affine `G₀`-orbit form): for `affineScheme`, the condition is
>   that the `G₀`-orbits of the differences `(u−t)_{t∈T}` jointly separate `V` — the **depth-1 affine
>   separability** target the probe measures. With `stablyRecoverable_of_discrete` + `selfDetectsStably_of_discretizes`
>   this discharges the seal for any **depth-1-separating** (`s(C)=1`) primitive small affine residual.
>
> **Honest scope:** this is the **depth-1 (`s(C)=1`) producer + the multi-base infrastructure** the iterated case
> needs. It covers the separable primitives (most of the catalogue/affine probe's primitives recover at depth 1).
> **OPEN remainder = the iterated (`s(C) ≥ 2`, cyclotomic depth-4) version** of the same joint separation — that is
> the genuine citation-free WL-dimension content, and it needs a `schemeAdj`-level iterated-profile engine (the
> `schemePartFrom`/`iterSet` machinery is built for the `J`-binarized graph, not `schemeAdj`), a substantial
> infrastructure build. **Did not over-reach on it.** Insight: depth-1-separating = multi-base-`EdgeGenerates`;
> the iterated case is the multi-base analogue of the `isolationStep`/`EdgeGenerates` closure engine on `schemeAdj`.

> **STEP 1 — DEPTH-1 SLICE CLOSED END-TO-END (2026-06-08, axiom-clean, full build green, `Cascade.lean`).** The
> depth-1 pieces are now composed into named, *manifestly conditional* capstones that close the seal **for the
> `s(C)=1` slice only** — designed to **expose the exact slot for the engine** (the anti-"looks-complete" design):
> - **`DepthOneSeparable S bound`** (predicate): `∃ T, |T| ≤ bound ∧ the depth-1 joint profile separates`. The
>   named `s(C)=1` object; docstring flags it is a *special case* (not the crux) + the bound-non-vacuity hinge
>   (`DepthOneSeparable S n` trivially true via `T=univ`, cf. `recoverableByDepth_univ`).
> - **`selfDetectsStably_of_depthOneSeparable`** : `(primitive ∧ small → DepthOneSeparable S bound) →
>   SelfDetectsStably`. **THE SLOT** — the engine adds a *sibling* `selfDetectsStably_of_boundedDepthSeparable`
>   (a weaker bounded-depth/iterated predicate) right here, **not** a replacement of the seal.
> - **`reachesRigidOrCameron_viaDepthOneSeparable`** : the fused seal with `hSelfDetect` discharged via the above;
>   still carries `hClassify` (G3) + `hImprim` + **`hDepthOne`**, so visibly conditional. Docstring: "closes the
>   seal ONLY for `s(C)=1`; do not read as seal-closed-for-primitives."
>
> **Net:** the chain M0→M1→M2→M3→fused-seal now composes non-vacuously end-to-end (the §3 vacuity guard), with a
> genuine stated partial theorem (seal closed for the separable / `s(C)=1` class = most primitives per the probe).
> **WHERE THE ENGINE SLOTS IN (next agent):** build a `schemeAdj`-level *iterated* joint-profile separation engine;
> expose it as `BoundedDepthSeparable S bound` (weaker than `DepthOneSeparable`: separation after ≤ `bound` *rounds*,
> not 1) + `selfDetectsStably_of_boundedDepthSeparable` + `reachesRigidOrCameron_viaBoundedDepthSeparable` carrying
> the weaker hypothesis. The `s(C)≥2` content = proving `BoundedDepthSeparable` for primitive small (irreducible
> affine / cyclotomic) — the open WL-dimension math.

**Goal (M2-B, the open iterated affine discreteness — the remaining research content).** `irreducible G₀ ⟹ ∃ S₀,
|S₀| ≤ bound ∧ Discrete (warmRefine (schemeAdj affineScheme) … (individualizedColouring _ S₀))`, where the
depth-1 case is the landed `discrete_affineScheme_of_jointSeparates` and the open part is the **iterated**
separation (cyclotomic / `s(C) ≥ 2`). (Was: the `CellsAreOrbits`-at-all-`T` form below;
`stablyRecoverable_of_discrete` reduces it to this Discrete form.)
The original `CellsAreOrbits` unfolding, kept for the orbit-level intuition:

**The object, unfolded (affine).** WLOG `0 ∈ T` (translate). For `T = {0, x₁, …, x_k}`: `Stab(T)`-orbits are
`(G₀)_{x₁,…,x_k}`-orbits (pointwise stabilizer in `G₀`). `warmRefine`-from-`T` first round colours `u` by the
**joint profile** `(orbit_{G₀}(u), orbit_{G₀}(u−x₁), …, orbit_{G₀}(u−x_k))`, then iterates (1-WL on the
colored Cayley graph). `CellsAreOrbits T` ⟺ the iterated joint profile **separates exactly** the
`(G₀)_{x_i}`-orbits. The `s(C)` gap is a `u ≠ u'` with the same iterated joint profile but different
`(G₀)_{x_i}`-orbit.

**The right vocabulary — Schur rings (matches the literature, Evdokimov–Ponomarenko/Ryabov).** The affine
orbital scheme is the **orbit Schur ring** `A(G₀)` over `V` (span of the `G₀`-orbit sums in `ℤ[V]`). 1-WL from
base `T` computes the **`T`-rooted WL Schur ring**. `CellsAreOrbits T` ⟺ the rooted WL ring equals the
`Stab(T)`-orbit ring. **Separability** `s(A(G₀)) ≤ |T|` ⟺ `A(G₀)` is determined by its `|T|`-dim structure
constants. The crux is: **irreducible `G₀` ⟹ `s(A(G₀)) ≤ base + O(1)`** (bounded separability).

**The mechanism (M2a — persistent gap ⟹ invariant subspace).** A gap that survives every bounded base is
**base-homogeneous** = an *algebraic* automorphism `σ` of `A(G₀)` (a permutation of orbits preserving all
structure constants) **not realized by any `g ∈ G₀`**. For translation rings the support of such a `σ` is a
`G₀`-invariant subgroup `W ⊊ V` (the "linear coupling" — the only base-homogeneous support; this is the
S-ring-theoretic heart). `W` is a proper non-trivial `G₀`-invariant subspace ⟹ contradicts irreducibility
(M1.2). **This is the affine instance of the general "persistent gap ⟹ block" — swap `Submodule` for
`ClosedSubset` and it is the §5.3 general crux.** Making "base-homogeneous σ ⟹ invariant subspace" rigorous is
the genuine S-ring research content (Ryabov's wreath/tensor structure theory for S-rings over `F_p^d`).

**The bound (M2b — bounded base suffices).** `irreducible ⟹ a base of size O(d)` (a linear base: `{0}` ∪ a
generating set making `(G₀)_{base} = 1`) ∪ `O(1)` extra to break the residual WL gap. For `−1 ∈ G₀`
irreducible the predicted bound is `base(G₀) + O(1)` (cf. Ponomarenko's prime-power circulant `WL-dim ≤ 3`).
`base(G₀) ≤ log₂|G₀|` is landed-style (`exists_isBase_saturated`); the `O(1)` stickiness is the WL gap M2a
closes.

**Sub-slices, by tractability (build in this order):**
- **M2-cyclic (FIRST, most tractable):** `G₀` cyclic (Singer/cyclotomic, the affine probe's flat-depth-4
  family). The gap is the *Galois* gap (cyclotomy), bounded by `d`. A cyclic `G₀` has a clean
  invariant-subspace structure (eigenspaces over `F̄_p`), so M2a/M2b may close with elementary linear algebra
  + a counting argument. This is the recommended first *proof* (the probe confirms the verdict: depth 4 flat).
- **M2-general-irreducible (the full crux):** open S-ring content. Attempt only after M2-cyclic and M1 are
  solid; gate behind the catalogue/affine empirics (already clean) and the literature (Ryabov S-ring
  separability over `F_p^d`).

**Honest difficulty (M2).** M2a (gap ⟹ subspace) in full generality is the **open** part — there is no
citation (seal-handoff §6 insight 2; exhaustive-obstruction §0.7.6). M2-cyclic is plausibly provable and is the
right first target. Do **not** expect M2-general to close quickly; its value is also as the *template* for the
§5.3 general crux.

### 9.4 M3 — wiring to `SelfDetectsStably` (mechanical, once M1+M2 exist)

`SelfDetectsStably (affineScheme) IsLarge bound` — **now via the M2 discreteness reduction (landed):** it
suffices to supply, for primitive small affine, a **bounded `S₀` with `warmRefine`-from-`S₀` discrete**, then
`selfDetectsStably_of_discretizes` closes it. So M3 is:
1. Apply `selfDetectsStably_of_discretizes`; intro `⟨hprim, hsmall⟩`. `hprim : IsPrimitive` → (M1.2)
   `irreducible G₀`.
2. (M2-B, the open affine discreteness) → `∃ S₀, |S₀| ≤ bound ∧ Discrete (warmRefine (schemeAdj affineScheme) …
   (individualizedColouring _ S₀))`. **This is the remaining research content** (the `s(C)` term).
3. **The "small" hypothesis (`hsmall : ¬ IsLargeSchemeViaAut`).** For affine, `|SchemeAutGroup| = p^d·|G₀|`;
   "small" = `|G₀|` poly = `d, p` bounded. The discretization bound is `base(G₀)+O(1) = O(log|G₀|)+O(1)`, which is
   `≤ bound` exactly in the small regime. Thread `bound := base(G₀) + C` and discharge `|S₀| ≤ bound` from
   `hsmall`. (`selfDetectsAtDepth_of_selfDetectsStably` + `reachesRigidOrCameron_viaStableRecovery`/`viaFusedSeal`
   then give the seal on the affine residual — both landed.)

### 9.5 Build order, risk, and the reusable-for-the-general-crux payoff

**Order:** M0 (model) → M1 (block↔subspace, primitive↔irreducible) → M2-cyclic (first recovery proof) →
M3 (wire) → M2-general (the open crux, template for §5.3). M0+M1 are mechanical/Mathlib-clean and **worth
landing regardless of M2** (they make "affine primitive ⟺ irreducible" a theorem and build the reusable
orbital-scheme constructor). M2-cyclic is the first genuine recovery proof. M2-general is research.

**Risk map:** M0 = medium (bureaucracy: orbital indexing, `intersectionNumber_well_defined`, `Fin n ≃ V`,
`rel_symm` ⟹ `−1 ∈ G₀`). M1 = low–medium (Mathlib `Submodule`/`IsPreprimitive`, the landed bridge). M2-cyclic
= medium–high (a real proof, but bounded and empirically confirmed). M2-general = open research. M3 = low.

**Reusable patterns for the general crux (§5.3), harvested from doing affine right:**
- The `orbitalScheme` constructor (M0) serves *every* schurian-residual family (PSL, classical — §5.2).
- M1's "block ⟺ sub-structure, primitivity forbids it" is the *template*: the general crux replaces
  `Submodule` with `ClosedSubset` and "invariant subspace" with "block system". Prove it concretely on affine
  first; the shape transfers.
- M2a's "base-homogeneous gap ⟹ a sub-structure" is the general self-detection mechanism; affine makes it
  linear (Mathlib-native) so it is the place to learn the argument before abstracting.
- **The single-base-free insight (A1) is general** (`cellsAreOrbits_schemeAdj_singleton`, every schurian
  scheme): in any Phase-2 family, only multi-base needs proving.

### 9.6 Anchors a fresh reader needs

- **Landed to build on:** `cellsAreOrbits_schemeAdj_singleton`, `relOfPair_eq_of_warmRefine_singleton`,
  `iterate_refineStep_colour_refines`, `signature_eq_card_eq` (`Cascade.lean §13a`); `StablyRecoverable`,
  `schemeRecoveredByDepth_of_stablyRecoverable`, `SelfDetectsStably`, `selfDetectsAtDepth_of_selfDetectsStably`,
  `reachesRigidOrCameron_viaStableRecovery` (`Cascade.lean`, Increment 2); `vProfile_iff_schemeOrbit`,
  `isAut_schemeAdj_iff`, `schemeAdj`, `isPreprimitive_iff_isPrimitive`, `ClosedSubset`, `IsPrimitive`,
  `SchemeAutGroup`, `trivialScheme`/`trivialSchurianScheme` (`Scheme.lean`).
- **Executable spec:** `GraphCanonizationProject.Tests/AffineSchemeProbe.cs` (the orbital scheme, intersection
  numbers, primitive = irreducible, recovery = `EdgeGenerates`/greedy depth — mirror it exactly in Lean).
- **Empirics already in hand:** affine probe (cyclotomic flat depth 4; non-abelian `ΓL(1,2^d)` flat depth 4,
  0 leaks) and the Hanaki–Miyamoto catalogue (orders 5–30, all primitive recover) — both confirm M2's verdict,
  so the proof is "establish the known-true," not "discover."
- **Literature for M2:** Evdokimov–Ponomarenko (separability number `s(C)`), Ryabov
  (arXiv:1709.03937/1812.11313, S-ring separability over abelian/`F_p^d`), Ponomarenko (arXiv:2206.15028,
  prime-power circulant `WL-dim ≤ 3`), Wu–Ren–Ponomarenko (arXiv:2507.10116). See exhaustive-obstruction §0.7.6.
- **Mathlib for M0/M1/M2:** `MulAction.orbitRel`/`IsBlock`/`IsPreprimitive`/`stabilizer`, `Submodule`,
  `IsSimpleModule`, `Module (ZMod p)`, `LinearEquiv`, `SemidirectProduct`, `Fintype.equivFinOfCardEq`.

---

## 10. HANDOFF (2026-06-08) — durable insights, the M1.1/M1.2 build plan, and session gotchas

> **Read this if you are picking up Phase 2.** M0, M0.3, M1.0, M1.0b are LANDED (axiom-clean, build green). This
> section makes the *non-durable* context durable: (10.1) the generalization insights that must survive to the
> §5.3 general-crux design (you will likely run out of context before designing it); (10.2) the exact M1.1/M1.2
> build plan (signatures + proof sketches); (10.3) Lean facts/gotchas learned this session so they are not
> rediscovered.

### 10.1 The generalization insights (DURABLE — carry these to the §5.3 general crux)

The affine beachhead is not just a special case to grind; it is a **template** whose shape transfers verbatim to
the general crux (§5.3, `BaseHomogeneousTwin ⟹ ClosedSubset`). Three insights, in increasing depth:

**(I1) A schurian scheme IS an orbit Schur ring; the affine scheme is the translation-Schur-ring `A(G₀)`.**
`orbMk_affine_eq_iff` (M1.0b) proves: *relations of `affineScheme` ↔ `G₀`-orbits on `V` (differences)*. More
generally (M0/`orbitalScheme`): *relations of any orbital scheme ↔ orbitals of the group*. So "intersection
numbers / structure constants" = "orbit-counting data," and **recovery (cells = orbits) ⟺ the structure
constants determine the scheme = separability** (`vProfile_iff_schemeOrbit` already gives relations = suborbits).
This is why the crux is a *separability* statement, attackable on scheme machinery with no group detour.

**(I2) The reusable template: "a block is a sub-structure; primitivity forbids it."** M1's whole content is one
correspondence, instantiated three ways:

| setting | "block" object | "sub-structure" | "primitivity forbids it" |
|---|---|---|---|
| **affine (M1, here)** | `ClosedSubset I` of `affineScheme` | `G₀`-invariant `Submodule (ZMod p) V` | irreducible `G₀` ⟹ no proper invariant subspace |
| **general (§5.3, future)** | `ClosedSubset I` of any schurian scheme | a *fusion / closed sub-configuration* (the "difference support" of a base-homogeneous twin) | scheme `IsPrimitive` ⟹ only trivial `ClosedSubset` |

The affine proof (M1.2) is the *concrete rehearsal*: build the closed subset from the substructure and back. The
general proof swaps `Submodule (ZMod p) V` ↔ `ClosedSubset`/fusion and "invariant subspace" ↔ "block system." The
**direction that matters** in both is `¬(no proper substructure) → ¬IsPrimitive` (i.e. `IsPrimitive →
irreducible/separable`), because the seal's cascade branch *hands you* `IsPrimitive` and you must extract the
structural consequence that drives recovery (M2).

**(I3) The crux's actual content is base-homogeneity = a coupling that survives every base.** A persistent
recovery gap (`¬StablyRecoverable`) is a same-cell-different-orbit pair surviving *every* bounded base — a
**base-homogeneous twin**. The §G2-anatomy mechanism: such a twin is supported by a *linear/character-degenerate
coupling*, which in the affine world IS a `G₀`-invariant subspace `W ⊊ V` (the "linear room" for the degeneracy),
and in the general world is a `ClosedSubset`/fusion. **Primitivity (irreducibility) removes the only place the
coupling can live ⟹ no twin ⟹ recovers at base + O(1).** The bound `O(1)` is the bounded-`s(C)` content
(Ponomarenko's prime-power circulant `WL-dim ≤ 3` is the affine-cyclic instance; M2-cyclic proves it there).
This is the ONE conjecture (`SelfDetectsStably`) the whole seal now rests on — see §G2 anatomy in
[`chain-descent-seal-handoff.md`](./chain-descent-seal-handoff.md).

> **Single-base-free is general (do not re-derive).** `cellsAreOrbits_schemeAdj_singleton` (Increment A1) proves
> single-base recovery is FREE for *every* schurian scheme. So in **any** Phase-2 family (affine, PSL, classical,
> general) only the **multi-base** (`|T| ≥ 2`) gap needs proving. The crux is purely multi-base everywhere.

### 10.2 The M1.1/M1.2 build plan (exact, pick-up-and-build)

Goal: **`IsPrimitive (affineScheme G₀ hneg) → G₀Irreducible G₀`** — what M3 consumes. Prove the contrapositive
`¬G₀Irreducible → ¬IsPrimitive` (build a nontrivial `ClosedSubset` from a proper invariant subspace). Steps:

**M1.1a — lift M1.0b to `relOfPair`.** Need `affineScheme_relOfPair_eq_iff`:
`(affineScheme G₀ hneg).relOfPair x y = (affineScheme G₀ hneg).relOfPair x' y' ↔ ∃ g₀∈G₀, g₀(δ') = δ`
(`δ := affineE.symm y − affineE.symm x`). Route: prove the small helper
`affineScheme_rel_iff : (affineScheme G₀ hneg).rel i x y = true ↔ orbitalIdx (affineG G₀) i = orbMk x y`
(unfold `affineScheme`→`orbitalScheme`→`orbitalAssocScheme`; the `.rel` field is `decide (orbitalIdx i = orbMk
…)`, so `simp only [affineScheme, orbitalScheme, orbitalAssocScheme, decide_eq_true_eq]` or a `show`). Then
`relOfPair x y = relOfPair x' y' ↔ orbMk x y = orbMk x' y'` (forward: both `rel (relOfPair _) _ _ = true` ⟹ both
`orbitalIdx (relOfPair _) = orbMk _`; converse: `relOfPair_unique`). Compose with `orbMk_affine_eq_iff` (M1.0b).

**M1.1b — define irreducibility self-contained** (avoid Mathlib `IsSimpleModule`/`IsPreprimitive` — they need the
group-algebra/`IsBlock` plumbing; a direct predicate is cleaner):
```
def G₀Irreducible (G₀ : Subgroup ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p))) : Prop :=
  ∀ W : Submodule (ZMod p) (Fin d → ZMod p),
    (∀ g₀ ∈ G₀, ∀ w ∈ W, g₀ w ∈ W) → W = ⊥ ∨ W = ⊤
```

**M1.1c — a general scheme lemma (the one genuinely new ingredient).** Needed for the `ClosedSubset` closure
clause:
`intersectionNumber i j k ≠ 0 → ∃ x y z, rel i x y = true ∧ rel j y z = true ∧ rel k x z = true`.
For the orbital scheme `R_k` is always nonempty: take `(x,z) := ((orbitalIdx k).out.1, (orbitalIdx k).out.2)`,
which satisfies `rel k x z` (via `orbMk_out` + `affineScheme_rel_iff`). Then `intersectionNumber_well_defined`
makes the count for `(x,z)` equal `intersectionNumber i j k ≠ 0`, so the witness filter is nonempty ⟹ `∃ y` with
`rel i x y ∧ rel j y z`. (State it for `orbitalAssocScheme`/`affineScheme`; or generally for any scheme with
`R_k` nonempty.)

**M1.2 — the bridge.** `theorem isPrimitive_affineScheme_imp_irreducible (hneg) : IsPrimitive (affineScheme …) →
G₀Irreducible G₀`, via contrapositive:
- Take proper invariant `W` (`hW0 : W ≠ ⊥`, `hWT : W ≠ ⊤`, `hWinv`).
- `I := Finset.univ.filter (fun i => ∃ x y, (affineScheme …).relOfPair x y = i ∧ affineE.symm y − affineE.symm x ∈ W)`.
- **`ClosedSubset I`:** `0∈I` (any `x=y`, diff `0∈W`); closure (`i,j∈I`, `intersectionNumber i j k ≠ 0`): get the
  triple `x y z` (M1.1c), diffs `δ_i = e⁻¹y−e⁻¹x ∈ W` and `δ_j = e⁻¹z−e⁻¹y ∈ W` (i,j∈I, with M1.1a giving
  well-definedness: the diff-in-`W` property is constant on a relation because same relation ⟹ `g₀·δ'=δ`, `W`
  invariant), so `δ_k = e⁻¹z−e⁻¹x = δ_i + δ_j ∈ W` (`W.add_mem`) ⟹ `k∈I`.
- **`I ≠ {0}`:** `W≠⊥` ⟹ `∃ 0≠w∈W`; the relation of `(affineE 0, affineE w)` has diff `w≠0` so its index `≠0`
  (`relOfPair = 0 ↔ diff = 0`) and is in `I`.
- **`I ≠ univ`:** `W≠⊤` ⟹ `∃ v∉W`; relation of `(affineE 0, affineE v)` has diff `v∉W`, index `∉I`.
- `IsPrimitive` says `I = {0} ∨ I = univ` — contradiction either way.
- (For `IsPrimitive → G₀Irreducible` directly: same construction; primitivity forces `I∈{{0},univ}`, pull back to
  `W∈{⊥,⊤}`.) **Gotcha:** "diff ∈ W constant on a relation" needs `W` `G₀`-invariant + M1.1a — do this as a clean
  `have` lemma first (`relOfPair x y = relOfPair x' y' → (δ ∈ W ↔ δ' ∈ W)`).

**Converse (`G₀Irreducible → IsPrimitive`, nice-to-have, NOT on the M3 critical path):** from a closed subset
`I`, set `W := {y | relOfPair (affineE 0) y ∈ I}` as an `AddSubgroup` (0∈W; `+`-closed via the composition/closure
clause and translation-invariance; over `F_p` an `AddSubgroup` is automatically a `Submodule` — use
`AddSubgroup.toIntSubmodule` then `ZMod p`-scaling is `ℤ`-scaling, or build `Submodule` directly), `G₀`-invariant
(orbit). Irreducible ⟹ `W∈{⊥,⊤}` ⟹ `I∈{{0},univ}`.

### 10.3 Session gotchas / Lean facts (so the next agent does not rediscover them)

- **`affineG` is the CARRIER-SET subgroup** (not `closure`) — `mem_affineG_iff` is `Iff.rfl`; destructure
  membership directly (`obtain ⟨g₀,hg₀,t,ha⟩ := a.2` for `a : ↥(affineG G₀)`). `mem_affineG_iff` has `G₀`
  **explicit** (it is under `variable (G₀)`): write `mem_affineG_iff G₀` / `(mem_affineG_iff G₀).mp`, or just use
  `a.2`.
- **`LinearEquiv.automorphismGroup`**: `mul f g = g.trans f`, so `(f*g) x = f (g x)` (`LinearEquiv.mul_apply`);
  `coe_one : ⇑(1) = id`; `coe_neg : ⇑(LinearEquiv.neg R) = -id` (so `(neg R) z` needs `simp [Pi.neg_apply, id_eq]`
  → `-z`). `LinearEquiv.neg (ZMod p)` is the element required `∈ G₀` (the `−1`, for the symmetric scheme).
- **`Equiv.permCongr_apply` is `rfl`/`@[simp]`**: `e.permCongr p x = e (p (e.symm x))`. Used to compute
  `affinePermFin_apply`.
- **`Finset.card_bij'`** signature (Mathlib `Data/Finset/Card.lean`): `(i : ∀ a ∈ s, β) (j : ∀ a ∈ t, α) (hi) (hj)
  (left_inv) (right_inv)` — dependent maps, this argument ORDER. Used in `orbitalAssocScheme`'s
  `intersectionNumber_well_defined`.
- **`abel`** needs `import Mathlib.Tactic.Abel` (added to `Cascade.lean`); the affine arithmetic
  (`a+(b−a)=b`, `−b+(a+b)=a`, assoc) is all `abel`. For an equality `e A = e B` under a coercion, do `congr 1;
  abel`.
- **`Nonempty (Fin (p^d))`** for `orbitalScheme`: `haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩` then
  `⟨⟨0, Nat.pos_of_ne_zero (pow_ne_zero d (NeZero.ne p))⟩⟩` (see `affineScheme`).
- **Generous transitivity constraint (9.0.1):** the scheme is symmetric ⟹ need `−1 ∈ G₀`. Carried as the `hneg`
  hypothesis everywhere. For M2-cyclic, pick the cyclotomic `G₀` containing `−1` (Singer normalizers do).
- **`card_bij'`/intersection-number proofs are ~40 lines and ~40s to compile** — `orbitalAssocScheme` is the
  heaviest single decl. Budget build time.
- **Module split:** M0 (`orbitalScheme`) is in `Scheme.lean §3.1` (no heavy imports); the affine instance + M1/M2/M3
  are in `Cascade.lean §AffineScheme` (heavy `ZMod`/`Module`/`Abel` imports isolated in the last module).
- **`orbMk_out` / `orbitalIdx` / `orbitalIdx_zero` / `orbMk_diag_iff` take `G` EXPLICITLY** (they are under
  `variable (G)` in `Scheme.lean §3.1`, not `{G}`). Write `orbMk_out (affineG G₀) q`, not `orbMk_out q`
  (the latter parses `q` as `G`). Cost an iteration in M1.1.
- **The `Fin (orbitalRank G + 1)` vs `Fin ((affineScheme …).rank + 1)` ascription trap (load-bearing for M2).**
  These two index types are **defeq but NOT syntactically equal** (`affineScheme.rank` only *reduces* to
  `orbitalRank (affineG G₀)`). So a bare `0`/`i` re-elaborated at one type does **not** `rw`-match a term carrying
  the other — `rw [heq]` fails with "did not find pattern" even when the goal visibly contains it (the printer
  suppresses the type ascription on `OfNat`). **Rule:** keep every index at the `affineScheme.rank` type (what
  `rel`/`ClosedSubset`/`IsPrimitive` use); prove diagonal facts via `rel_zero_iff_eq` (affineScheme-typed),
  **not** `orbitalIdx_zero` (orbitalRank-typed); ascribe explicitly (`(0 : Fin ((affineScheme G₀ hneg).rank+1))`)
  when a bare literal would re-elaborate at the wrong type. `affineRelDiff_zero` is the worked example.
- **M1.2 needs `import Mathlib.Algebra.Module.Submodule.Lattice`** (added to `Cascade.lean`) — gives `Submodule`,
  `⊥`/`⊤`, `Submodule.ne_bot_iff`, `Submodule.eq_top_iff'`, `add_mem`/`zero_mem`. `Equiv.Module.Equiv.Basic`
  (already imported for `≃ₗ`) does **not** pull `Submodule`.
- **`Nonempty (Fin (p^d))`** for the M1 lemmas (outside `affineScheme`'s local `haveI`): the section-level
  `private instance instNonemptyAffV` supplies it. `Nonempty` is a `Prop`, so proof-irrelevance makes instances
  interchangeable — that is *not* the source of the ascription trap above (the index-type is).

---

## 11. ROUTE-SCAN VERDICT + the remaining-pieces implementation plan (PICK UP HERE for Phase 2)

> **Read this first to continue Phase 2.** It supersedes §9.3/§9.5's "M2-cyclic" sketch with (a) the conceptual
> frame that fixes what the work *is* (§11.1 — there is no k-WL climb), (b) the route-scan verdict on *where* to
> build (§11.2), and (c) an implementation-ready plan for the remaining pieces (§11.3–§11.7). The depth-1 slice
> is LANDED (`reachesRigidOrCameron_viaDepthOneSeparable`); the open content is the `s(C) ≥ 2` bound, attacked at
> the affine-cyclic beachhead.

### 11.1 Conceptual frame — what the "engine" is and is NOT (settle this before coding)

Three clarifications that correct earlier loose framing; internalize them or the work goes sideways:

1. **`k` (WL arity) is FIXED at 1 — there is no k-WL climb, ever.** The project uses only ordinary colour
   refinement (`refineStep`/`warmRefine` = 1-WL to fixpoint). Matching a graph's k-WL dimension by raising `k`
   would be the super-polynomial trap, and it is **out of scope by design** (calculator §7, strategy §9).
2. **Three distinct "depths" — only one is the open/bounded quantity:**
   - *WL arity `k`* — always 1, never tuned.
   - *Refinement rounds* — `warmRefine = refineStep^[n]`, always run to the 1-WL fixpoint (≤ n rounds,
     **polynomial**); not a parameter.
   - *Individualizations* — `|T|` (= the `bound` in `RecoverableByDepth`/`DepthOneSeparable`/`SchemeRecoveredByDepth`).
     **This is the only open quantity**; polynomial time ⟺ it stays bounded (`base(G) + s(C)`, `< n` or vacuous
     per `recoverableByDepth_univ`).
3. **The engine reasons about the (polynomial) 1-WL fixpoint from a BOUNDED number of individualizations.** It is
   NOT a k-WL implementation. The landed `relOfPair_eq_of_warmRefine_singleton` peels *one* `refineStep` round; the
   only thing genuinely missing is reasoning about the *full fixpoint* (several rounds, still polynomial) when one
   round is insufficient (`s(C) ≥ 2`). That is an induction over rounds, not a climb in `k`.

**The unification (carry this — it is why the work matters):** *the algorithm's polynomial-and-no-flag runtime*,
*the lockstep/harvest completeness*, and *the seal's self-detection content* are **one boundary, three faces**:

| face | "good" condition |
|---|---|
| runtime (poly + no flag?) | bounded `s(C)` (+ not IR-core) |
| harvest/lockstep complete? | bounded `s(C)` |
| the engine / seal theorem | "primitive small ⟹ bounded `s(C)`" |

**The engine's job is to prove a *uniform bound exists* for the class — NOT to compute a per-scheme formula.** The
target is the existence/upper-bound theorem "`base + O(1)` individualizations suffice for **every** primitive small
scheme" (≡ `s(C)` bounded on the class). The exact `s(C)` value of any scheme is a fact the algorithm never needs.

**`selfDetectsStably_of_discretizes` is ALREADY the engine interface** — `∃ T, |T| ≤ bound ∧ Discrete(warmRefine
from T)`. There is **no new `BoundedDepthSeparable`-by-rounds predicate to build** (an earlier suggestion; it was a
confusion — rounds are free, individualizations are the bound). The remaining work plugs a *proof of that
discreteness* into this interface; `DepthOneSeparable` is the already-landed `s(C)=1` plug, and the open work is the
`s(C) ≥ 2` plug for the affine-cyclic family.

### 11.2 Route-scan verdict — affine-cyclic beachhead (and why)

Candidate slices for the first bound proof: **affine-cyclic** (cyclotomic/Singer), affine-general-irreducible,
**rank-3/4 SRG**, **§5.3 general**. The decision-driving questions and their answers (from the project's own record —
exhaustive-obstruction §4 R5 + §0.7.6, the probes — *not* external research, per the design-fit concern):

- **Q1 — Mathlib substrate (dominates feasibility).** Mathlib has **zero** substrate for association schemes /
  coherent configurations / Bose–Mesner / DRG / scheme spectral theory (R5). So **rank-3/4 SRG and §5.3 would each
  require building scheme spectral theory from scratch** on top of the open math ("cleaner math ⟹ *more* Lean").
  **Affine is the only route with substrate** (Mathlib `Submodule`, `IsSimpleModule`, finite-field `Frobenius`/Galois,
  eigenspaces) — which is exactly why M1 went through cleanly.
- **Q2 — is there an elementary beachhead?** Affine-**cyclic** is the one slice with a plausibly *elementary* proof:
  `V ≅ F_{p^d}`, `G₀ = ⟨α⟩`, the gap is the **bounded Galois/cyclotomy gap** (Frobenius), provable by finite-field
  linear algebra + counting (Mathlib has the Galois machinery). Probes: cyclotomic AND non-abelian `ΓL(1,2^d)` both
  flat at depth 4. General-irreducible and rank-3/4 have no comparable elementary handle.
- **Q3 — engine reuse.** The multi-round separation reasoning on `schemeAdj` is genuinely new (`schemePartFrom`/
  `iterSet` exist only for the `J`-binarized graph), reusable across slices, and seeded by the landed depth-1
  reduction-to-single-base trick. Affine difference-coordinates do *not* bypass it (warmRefine still runs on
  `schemeAdj`); they only make the *bound argument* tractable.
- **Q4 — payoff / non-vacuity.** Cyclotomic is exactly the `s(C) ≥ 2` zone depth-1 misses (genuinely new beyond
  G1a/G1b). Rank-3/4 has higher strategic payoff (would *complete* rank 3/4 with G3 at its strongest — small→recover,
  large→Cameron) but Q1 makes it prohibitively expensive; a blocked route has zero realized payoff.
- **Q5 — design fit (the "don't warp the design" guard).** The faithful engine extends the project's
  `refineStep`/`warmRefine`/`isolationStep`/`s(C)` idiom (an induction over the 1-WL fixpoint), **not** an
  off-the-shelf k-WL / coherent-configuration framework. Importing a generic refinement framework is the warp to avoid.

> **VERDICT: build the cyclotomic (affine-cyclic) bound proof first; defer rank-3/4 and §5.3.** Extract reusable
> multi-round lemmas *from* that proof rather than building a speculative general engine first (the §3 discipline:
> build what the proof consumes, not a big engine that then hits the open-math wall). Q1 is decisive — substrate, not
> payoff, picks the slice.

### 11.3 Build order for the remaining pieces

```
E2 (cyclotomic bound proof)  ──drives──►  E1 (reusable round-propagation lemmas, EXTRACTED, not pre-built)
        │
        ▼
E3 (wire to the seal — mechanical, via selfDetectsStably_of_discretizes → fused seal)
        │
        ▼
[deferred] general-irreducible affine  →  rank-3/4 SRG  →  §5.3 general  (each gated by its substrate cost)
```

**Do NOT build E1 as a speculative standalone engine.** Start E2; when a multi-round refinement fact is needed,
prove it as a general `schemeAdj` lemma (E1) and consume it. This keeps the engine exactly as large as the proof
needs and avoids over-building toward the open wall.

### 11.4 E2 — the cyclotomic bound proof (the research content; model is buildable, the key lemma is open)

**Goal.** For the cyclotomic affine scheme (cyclic irreducible `G₀`), exhibit a **bounded** base `T`
(`|T| ≤ base(G₀) + C`, `C = O(1)`) with `Discrete(warmRefine (schemeAdj affineScheme) … (individualizedColouring _ T))`.
Then E3 wires it through `selfDetectsStably_of_discretizes` to the seal on this family.

**The model (buildable now, mechanical–medium).**
- Reuse `affineScheme G₀ hneg` (landed) with `G₀ = ⟨α⟩` a cyclic Singer subgroup of `GL(d,p)` containing `−1`.
  *Anchor:* `G₀` is the multiplicative `⟨α⟩ ≤ F_{p^d}^*` acting on `V ≅ F_{p^d}` by multiplication; need `−1 ∈ ⟨α⟩`
  (true iff `α` has even order / index is odd — Singer normalizers contain `−1`; pick accordingly, cf. §10.3 gotcha).
- The relations are the `⟨α⟩`-cosets of differences (landed `orbMk_affine_eq_iff`): `relOfPair x y` = coset of `y−x`.
- **Mathlib anchors:** `Mathlib.FieldTheory.Finite.Basic` (`F_{p^d}` structure), `FiniteField.frobenius`/
  `frobeniusEquiv`, `Mathlib.FieldTheory.Galois` (Gal(`F_q/F_p`) = `⟨φ⟩` cyclic order `d`), `IsCyclic`,
  `Subgroup.zpowers`. Modelling `V ≅ F_{p^d}` as a *field* (not just a module) is the new modelling step — the
  cyclic case wants the multiplicative + Galois structure the generic `affineScheme` (a `Fin d → ZMod p` module)
  does not expose. Decide: either (i) instantiate `affineScheme` with `G₀` the image of `⟨α⟩` under a fixed
  `F_{p^d} ≃ₗ (Fin d → ZMod p)`, or (ii) build a parallel `cyclotomicScheme` directly on `F_{p^d}` via
  `orbitalScheme` of the 1-dim affine group `F_{p^d} ⋊ ⟨α⟩`. **(ii) is likely cleaner** — it keeps the field
  structure native and avoids the module-transport bureaucracy; `orbitalScheme` (M0, landed) accepts any transitive
  generously-transitive `G ≤ Perm (Fin q)`, and `F_{p^d} ⋊ ⟨α⟩` is one.

**The separation argument (the open core — `s(C)` bounded by the Galois gap).** The structure, in project terms:
- *Why depth-1 fails (the gap):* the `r` cosets are permuted by the Galois group `Γ = ⟨φ⟩` (Frobenius), and the
  scheme's intersection numbers are `Γ`-invariant — so from a single base, 1-WL cannot tell `φ`-conjugate cosets
  apart by counting. This is the separability gap `Ĝ ⊋ G` (`Ĝ` includes the colour-*permuting* algebraic
  automorphism `φ`; `G = ⟨α⟩ ⋉ V` is colour-*preserving*). `s(C) > 1` ⟺ this gap is nonempty.
- *Why bounded extra individualization closes it:* `φ` moves points (it is not a scheme automorphism in `G`), so
  individualizing points outside the `φ`-fixed field `F_p` breaks `Γ`. Once `T` contains points whose joint
  `Γ`-stabilizer is trivial — at most `O(d)` points, since `|Γ| = d` is cyclic — the gap closes and warmRefine
  discretizes. **Target bound: `base(G₀) + O(log d)` (or `+ d`), i.e. `s(C) = O(d) = O(log q)`** — matching
  Ponomarenko's prime-power circulant `WL-dim ≤ 3` regime and the probe's flat depth 4.
- *The hard lemma (open, no citation):* "individualizing a `Γ`-breaking set of `O(d)` points makes the 1-WL fixpoint
  separate `φ`-conjugate cosets, hence (with the base) discretize." This is where E1's multi-round reasoning is
  consumed: a single round after individualizing `x` distinguishes a coset `C_i` from `φ(C_i)` iff the count
  `#{z : z−0 ∈ C_i ∧ z−x ∈ J}` differs from the `φ(C_i)` count — the **two-base intersection count** (cf. the
  landed J-world `IntersectionSeparates`/`depth2Det_of_intersectionSeparates`, Scheme.lean:2524 — to be **re-proved
  on `schemeAdj`** as an E1 lemma). Iterate over the `O(d)` base points.

**Honest difficulty.** The model (ii) is mechanical–medium. The *bound lemma* is genuine research: even the cyclic
case needs the Frobenius-breaking counting argument formalized, and there is no citation for `s(C)` bounded. M2-cyclic
is "plausibly provable with elementary finite-field linear algebra + counting" (the project's standing assessment),
but budget it as real work, gated behind the (already-clean) probe empirics. **Sub-steps, in order:**
1. **E2.1** — the cyclotomic model on `F_{p^d}` (option (ii)): `cyclotomicScheme p d α : SchurianScheme q` via
   `orbitalScheme`, with `relOfPair` = coset-of-difference. *Buildable now.*
2. **E2.2** — the Frobenius action on relations: `φ` permutes cosets, intersection numbers are `Γ`-invariant
   (the gap, stated). *Mechanical given Mathlib Galois.*
3. **E2.3** — the two-base count separates `φ`-conjugate cosets after individualizing a `Γ`-breaking point (the
   E1 `schemeAdj` two-base lemma + the field counting). *The first genuinely-hard step.*
4. **E2.4** — iterate (E1 multi-round / saturation over the `O(d)` base) to `Discrete(warmRefine from T)`,
   `|T| ≤ base + O(d)`. *The research crux.*

### 11.5 E1 — the reusable round-propagation lemmas (EXTRACTED from E2, not pre-built)

> **E1 FIRST BRICKS LANDED (2026-06-08, axiom-clean `[propext, Classical.choice, Quot.sound]`, build green,
> `Cascade.lean §13b`).** The depth-2 separation engine's core pair — the `schemeAdj` analogue of
> `IntersectionSeparates`/`depth2Det`, the §11.4 E2.3 named consumable:
> - **`twoRoundCount_eq_of_warmRefine`** — same `warmRefine (schemeAdj S)`-from-`T` cell ⟹ equal depth-2 count
>   profile: `∀ c b, #{z ≠ w : refineStep·z = c ∧ relOfPair w z = b} = #{z ≠ u : … relOfPair u z = b}`. Peels
>   `warmRefine = refineStep^[n] → refineStep^[2]` (`warmRefine_eq_iter_eq`), `refineStep_iff`, count bridge
>   `signature_eq_card_eq`. Generalizes the single-base depth-`k` count machinery (`iter_succ_count_eq`, keyed on
>   `individualizedColouring n {v}`) to a base **set** `T`.
> - **`discrete_of_twoRoundProfileSeparates`** — depth-2 profile separates ⟹ `Discrete(warmRefine from T)`; the
>   depth-2 analogue of `discrete_of_jointProfileSeparates`, feeding `stablyRecoverable_of_discrete` →
>   `selfDetectsStably_of_discretizes`. The producer the cyclotomic (E2.4) bound discharges.
>
> **KEY FINDING (carry to E2 / the general crux): the engine is inherently MULTI-BASE.** From a *single* base,
> depth-2 counts collapse to intersection numbers (`AssociationScheme.intersectionCount_via_w`:
> `#{z : relOfPair v z = a ∧ relOfPair w z = b} = intersectionNumber a b (relOfPair v w)`), which `w, u` already
> share at depth-1 — so single-base depth-2 adds nothing (consistent with `cellsAreOrbits_schemeAdj_singleton`).
> The genuine `s(C) ≥ 2` content is the JOINT count over `≥ 2` bases (`#{z : relOfPair v z = a ∧ relOfPair x z =
> a' ∧ relOfPair w z = b}`), which is *not* a single intersection number — exactly where the Frobenius/Galois
> separation (E2.3) bites. The `twoRoundCount` lemma's one-round-colour grouping `refineStep·z = c` already
> encodes the joint `(relOfPair t ·)_{t∈T}` profile (depth-1 §13a), so it carries the multi-base information; the
> consumer converts colour-grouping → relation-grouping via `relOfPair_eq_of_warmRefine_singleton`.
>
> **Remaining E1 (extract as E2 needs):** the colour→relation-grouping conversion corollary (sum over one-round
> colours sharing a joint relation profile) if the Frobenius argument wants relation-indexed counts; and a thin
> saturation wrapper if depth-2 alone is insufficient (cyclotomic depth-4 = base-2 + 2 rounds). Do NOT pre-build
> the full `isolationStep` mirror (§11.5 note below).

The `schemeAdj`-native generalization of the landed single-round `relOfPair_eq_of_warmRefine_singleton`. Build
*only* what E2 consumes; candidates (state generally for any `AssociationScheme`, prove via induction on
`refineStep` rounds, reusing `iterate_refineStep_*`, `signature_eq_card_eq`, `warmRefine_refines_initial`):
- **`twoBaseSeparates`** (the depth-2 `schemeAdj` analogue of `IntersectionSeparates`): if a two-base intersection
  count distinguishes `u, u'`, then `warmRefine` from `{t, t'}` separates them. (The depth-1 lemma is the one-base
  case; this is the next round.) *The first E1 lemma E2.3 needs.*
- **`separationPropagates`** (the inductive step): if some already-separated neighbourhood difference exists for
  `(u,u')`, one more `refineStep` separates them — the engine of E2.4's iteration. Likely phrased as a saturation
  (`exists_iterate_isFixed_within`-style) over the "separated-pairs" set, mirroring `isolationStep` at the vertex
  level on `schemeAdj`.
- **`discrete_of_separationSaturates`**: if the separated-pairs saturation reaches all pairs, `warmRefine` from `T`
  is discrete (feeds `stablyRecoverable_of_discrete`). The `schemeAdj` analogue of `theorem_2_HOR_of_edgeGenerates`'s
  finish, on vertices not relations.

**Note (do not over-reach):** E1 might be just `twoBaseSeparates` + a thin saturation wrapper. Resist building a
full general "iterated isolation engine" mirroring all of `isolationStep`/`IsoPinned`/`EdgeGenerates` on `schemeAdj`
speculatively — that is the over-build the route-scan warns against. Extract per E2's actual needs.

### 11.6 E3 — wiring (mechanical, once E2 lands)

`selfDetectsStably_of_depthOneSeparable` is the template. The cyclotomic capstone:
1. `selfDetectsStably_of_discretizes` with the E2 discreteness witness ⟹ `SelfDetectsStably (cyclotomicScheme …)`.
2. `reachesRigidOrCameron_viaFusedSeal` (or `…_viaDepthOneSeparable`'s sibling) ⟹ the seal on the cyclotomic family,
   with `hImprim` discharged (primitive ⟹ no imprimitive branch) and G3 cited.
3. Thread `bound := base(G₀) + C` (C from E2.4); discharge `|T| ≤ bound` from "small" (`|G₀|` poly ⟹ base `O(log)`).
**Anti-"looks-complete":** name it `reachesRigidOrCameron_viaCyclotomic` (or `_affineCyclic`) and keep it carrying
`hClassify` (G3); it closes the seal only for the *cyclotomic* family — the general primitive case stays open.

### 11.7 Deferred routes + the honest open core

- **General-irreducible affine** — after cyclotomic; replaces the Frobenius/Galois gap with a general
  invariant-subspace argument (M2a: base-homogeneous gap ⟹ `G₀`-invariant subspace ⟹ contradicts irreducibility,
  M1.2). Heavier (S-ring separability theory); the cyclotomic proof is its rehearsal.
- **Rank-3/4 SRG** — high strategic payoff (completes rank 3/4 with G3), but blocked by Q1 (no Mathlib scheme/SRG
  substrate). Revisit only if scheme spectral theory gets built for another reason.
- **§5.3 general** (`BaseHomogeneousTwin ⟹ ClosedSubset`) — the eventual goal; rehearsed by M1.2's template
  (swap `Submodule` ↔ `ClosedSubset`). Attack by analogy *after* affine, when value/cost is clear.

> **THE OPEN CORE (state plainly at every handoff).** The `s(C)`-bounded conjecture for primitive small schemes is
> **uncited open mathematics** (seal-handoff §6 insight 2, exhaustive-obstruction §0.7.6). Even a fully successful
> E1+E2+E3 closes only the **cyclotomic** slice; the general primitive case may never close from Mathlib. The seal's
> honest end-state remains a conditional theorem `modulo {G3 + the s(C) bound}`. Every capstone built here MUST carry
> the open hypothesis visibly (the anti-"looks-complete" discipline) so the slot stays obvious. The engine is *1-WL
> reasoning over a bounded base* throughout — it never climbs `k`, never goes super-polynomial by design; where the
> bound is unbounded (the leak), the algorithm flags, it does not raise `k`.
