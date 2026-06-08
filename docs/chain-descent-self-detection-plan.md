# Chain descent — the self-detection lemma: plan to make the seal unconditional

> **STATUS (2026-06-08): PLANNING.** The oracle-capability seal is a conditional theorem
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
| `isolationStep`, `IsoPinned`, `relIsolatedAt_succ`, `stage_relIsolatedAt` | `Scheme.lean:2888,3077,3086,3133` | the closure→isolation engine; `IsoPinned` = a relation is the **unique** one with its intersection-count signature into the isolated set |
| `theorem_2_HOR_of_edgeGenerates` | `Scheme.lean:3181` | **P1**: `EdgeGenerates ⟹ cells = orbits` (recovery), no rank ladder |
| `IsoPinned.mono` + saturation (`exists_iterate_isFixed_within`) | `Scheme.lean:3253`, `Saturation.lean` | the "graded pinning saturates the closure in ≤ n rounds" skeleton — **reuse for multi-base** |
| `vProfile_iff_schemeOrbit` | `Scheme.lean:576` | **the load-bearing bridge**: for a schurian scheme, `relOfPair(v,·)`-classes **are** the `Stab(v)`-orbits |
| `schemePartFrom`, `iterFrom_refines_schemePartFrom`, `iterSet_refines_schemePartFrom` | `Scheme.lean:1833,1877,1952` | **the realization half** (multi-base): a depth-k counting partition from an arbitrary base **set** is *refined by* warm refinement — i.e. *any multi-base counting separation is seen by 1-WL* |
| `IntersectionSeparates`, `depth2Det_of_intersectionSeparates` | `Scheme.lean:2524,2535` | the **two-base** realization instance (depth-2 determinacy from intersection-number separation) |
| `RecoverableByDepth`, `CellsAreOrbits`, `recoverableByDepth_univ` | `CascadeOracle.lean:804,268,862` | the **recovery target**: `∃ S, |S| ≤ bound ∧ cells-from-S = orbits-from-S`; vacuous at `bound = n` (the non-vacuity hinge) |
| `SchemeRecoveredByDepth`, `reachesRigidOrCameron_viaDepthRecovery` | `Cascade.lean` (G1a) | the **seal sink**: bounded shallow + deep visible realizers ⟹ the capstone |
| `ClosedSubset`, `IsPrimitive`, `cell_splits_of_imprimitive`, `BlockRefinementVisible`, `SchemePartSeparatesBlock` | `Scheme.lean:164,212,3990,3916,3963` | the **block side** and the named Gate-G predicate (`SchemePartSeparatesBlock` = "the depth-n counting partition respects the block I") |

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

## 4. Phase 1 — the multi-base engine + the precise crux statement (mechanical, the buildable substrate)

Goal: convert the prose conjecture into **one Lean proposition** `not_isPrimitive_of_baseHomogeneousTwin`
whose proof discharges `hCascade`, and prove everything around it. Generalizes the single-base engine of §2
along the `schemePartFrom`/base-set axis that the realization half already opened.

**4.1 — Multi-base isolation closure (generalize §2's engine from `v` to a base set `S`).**
- `isolationStepFrom S` / `IsoPinnedFrom S` — pinning by the *multi-base* intersection-count signature
  (counts of `relOfPair`-from-`S` profiles), the base-set analogue of `IsoPinned`. Reuse `IsoPinned.mono` +
  the saturation fixpoint verbatim (the skeleton is base-agnostic).
- `EdgeGeneratesFromSet S : Prop` — the multi-base closure reaches every relation-from-`S`.
- `theorem_2_HOR_of_edgeGeneratesFromSet` — `EdgeGeneratesFromSet S ⟹ CellsAreOrbits S`. The multi-base
  analogue of `theorem_2_HOR_of_edgeGenerates`; the realization direction is already supplied by
  `iterSet_refines_schemePartFrom` + the multi-base `vProfile_iff_schemeOrbit` (relOfPair-from-`S` =
  `Stab(S)`-orbits). *This is the main mechanical theorem.*

**4.2 — The deadlock / twin object (P2, multi-base).**
- `BaseHomogeneousTwin G (bound) i j : Prop` — relations `i ≠ j` carry identical multi-base intersection
  signatures for **every** base set of size `≤ bound` (the gap survives every small base).
- `twin_of_not_recoverableByDepth` — `¬ RecoverableByDepth adj P bound ⟹ ∃ i j, BaseHomogeneousTwin … i j`.
  Provable by pigeonhole over the finite relation set + the finite family of size-`≤bound` base sets, using
  that the multi-base WL-closure is a well-defined coarsening of the orbit partition (a *fusion* fixpoint);
  non-recovery ⟹ the fixpoint is non-discrete ⟹ a stable twin pair. (Mirror of `stage_relIsolatedAt`'s
  saturation argument, on the base-set lattice.)

**4.3 — The precise crux + the wiring.**
- **`not_isPrimitive_of_baseHomogeneousTwin`** (THE CRUX, stated here, proved in Phase 2):
  `(∃ i j, i ≠ j ∧ BaseHomogeneousTwin G bound i j) → ¬ G.scheme.IsPrimitive`. Contrapositive:
  **primitive ⟹ no base-homogeneous twin ⟹ `RecoverableByDepth bound`** (via 4.2's contrapositive + 4.1).
- `selfDetection_dischargesCascade` — `RecoverableByDepth bound ⟹ SchemeRecoveredByDepth … bound` (assemble
  the G1a witness: `S₀` = the recovering base set, deep phase = visible realizers, which hold because
  `CellsAreOrbits S₀`). Then `hCascade` is discharged and `reachesRigidOrCameron_viaDepthRecovery` fires
  unconditionally on the primitive branch.

**Phase-1 outcome (achievable, axiom-clean):** the seal is reduced to the single proposition
`not_isPrimitive_of_baseHomogeneousTwin` + the cited G3. The catalogue probe (`CatalogueSchemeProbe.cs`)
*already tests this proposition's emptiness empirically* (a base-homogeneous-twin primitive scheme would be a
non-recovering primitive scheme — none in orders 5–30). Phase 1 makes the open gap a *precise, falsifiable,
single* statement — genuine progress independent of whether Phase 2 closes.

---

## 5. Phase 2 — proving the crux (research; sub-case first)

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

- **Phase 1 closes** (achievable, axiom-clean): the seal reduced to one precise proposition
  `not_isPrimitive_of_baseHomogeneousTwin`; the multi-base engine; the wiring discharging `hCascade` *given*
  that proposition. Net: seal = unconditional **modulo {G3 + that one proposition}**, with the proposition
  empirically gated by the catalogue probe.
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
