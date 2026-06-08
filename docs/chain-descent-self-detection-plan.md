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
> affine beachhead Increment A1 LANDED (single-base recovery is free; the crux is multi-base). The **detailed,
> pick-up-and-build plan for the remaining affine multi-base work is §9 below** — a fresh reader should start
> there. See §4 outcome box (Phase 1), §5.1 (Phase 2 overview).** The oracle-capability seal is a conditional theorem
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

**Goal.** `irreducible G₀ ⟹ ∃ S₀, |S₀| ≤ bound ∧ ∀ T ⊇ S₀, CellsAreOrbits (schemeAdj affineScheme) … T`.

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

`SelfDetectsStably (affineScheme) IsLarge bound`:
1. Intro `⟨hprim, hsmall⟩`. `hprim : IsPrimitive` → (M1.2) `irreducible G₀`.
2. (M2) → `∃ S₀, |S₀| ≤ bound ∧ StablyRecoverable (schemeAdj affineScheme) … S₀`. Done.
3. **The "small" hypothesis (`hsmall : ¬ IsLargeSchemeViaAut`).** For affine, `|SchemeAutGroup| = p^d·|G₀|`;
   "small" = `|G₀|` poly = `d, p` bounded. M2's bound is `base(G₀)+O(1) = O(log|G₀|)+O(1)`, which is `≤ bound`
   exactly in the small regime. Thread `bound := base(G₀) + C` and discharge `|S₀| ≤ bound` from `hsmall`.
   Then `selfDetectsAtDepth_of_selfDetectsStably` (Increment 2, landed) + `reachesRigidOrCameron_viaStableRecovery`
   (landed) give the seal on the affine residual.

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
