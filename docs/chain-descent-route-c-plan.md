# Route C — the constructive form-recovery route to a POLYNOMIAL forms-graph canonizer

> **What this is.** The self-contained build plan for **Route C**: proving the affine forms-graph residue is
> canonized in **polynomial** time by *recovering the defining algebraic structure* (the form/geometry) from the
> abstract graph and then using its **known** automorphism group — instead of driving Weisfeiler–Leman refinement to
> orbits. Route C **sidesteps the node-4 WL-dimension wall** that closed the direct recovery route
> ([`chain-descent-recovery-route.md`](./chain-descent-recovery-route.md) §9.8.9). This doc is the staging point: a
> fresh reader should be able to read it and build forward. It carries the plan, the knowledge foundation, the exact
> names of the preexisting lemmas Route C rides on, and the probe evidence.
>
> **Relation to the other docs.** The SEAL (correctness disjunction `reachesRigidOrCameron`) is **already banked at
> quasipoly** and is *not* Route C's job. The direct WL/poly routes (A/B, `bᵢ=1` via `ColorRefinesGramK`) **STALLED**
> at the node-4 wall — full verdict in the recovery doc §9.8.9. Route C is the **bounded, guaranteed-poly alternative**
> that route pointed to. The forms-graph plan ([`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md))
> §11.4/§11.5 has the per-family (alternating / half-spin / Suzuki–Tits / char-2) analysis this doc's architecture generalizes.

---

## STATUS (read first)

**Where Route C stands (2026-07-03).** Scoped and de-risked at the algorithm level; no Lean/C# build committed yet.

- **The two correctness hypotheses are both probe-validated (decisively):**
  - **A1 — form recovery** (`route_c_reconstruct_probe.py`): the isotropic cone determines `Q` up to scalar by ONE
    linear solve — degree-2 vanishing dim `= 1` in **every** case tested (ε=±, d=4,6,8, q=3,5,7,11). No small-`q`
    exception in the target range.
  - **F1 — additive-structure recovery** (`route_c_f1_probe.py`): `O_p(Aut)` (normal-closure computation) recovers the
    regular elementary-abelian translation group `T ≅ (𝔽_p)^d` **exactly**, **scramble-invariantly**, and the recovered
    coordinates make the connection set a quadric cone (`coneVanishDim = 1`) — the clean F1→A1 hand-off. Validated on
    VO^ε₄(3), VO^ε₄(5) (both types).
- **The back-half is already LANDED and axiom-clean** — `coords_determine` (nondeg form-coords determine the vector) and
  `reachesRigidOrCameron_viaOrthogonalForm` (the isometry scheme discretizes at the `d+1` frame). See §4.
- **The genuinely-new Lean content is narrow** — the *refinement bridge* (recovered `Q` upgrades the similitude graph
  to the isometry scheme) + the iso-invariance of the recovered structure. See §2c and F5/A3 in §6.
- **Next concrete step:** either the C# F1 build (host `O_p` + coordinatization on `PermutationGroup.cs`) or spike the
  A3 refinement bridge in Lean. See §6 "Sequencing".

**Quality bar (project-wide):** every Lean theorem axiom-clean `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no fresh `axiom`; `native_decide` banned; full build green when ported. "Poly time" stays a **meta-argument** (the
project formalizes no runtime model): the structural deliverables are the seal disjunction `reachesRigidOrCameron`
(banked) and the *bounded-base discreteness object* Route C constructs; "poly" is the meta-claim over that + poly
per-node.

---

## 1. The claim, and why Route C

**The claim.** The abstract forms graph determines its defining form `Q` (up to scalar) by elementary linear algebra;
its automorphism group is then the **known** affine similitude group `AΓO^ε(Q)`, whose canonicalization is standard
poly group theory (Schreier–Sims — already implemented, §4). No WL-reaches-orbits, no count crux.

**Why Route C (the wall it dodges).** The direct routes canonize by driving refinement to the orbit partition. On the
forms graph the descent runs on the **similitude SRG**, whose relations record only the **isotropy class** of a
difference (zero / nonzero-isotropic / anisotropic), *not* the exact `Q`-value. Recovering the exact bilinear values
from bounded-base isotropy counts is the **node-4 WL-dimension wall** — open both ways, and it closed the direct build
(`ColorRefinesGramK` is circular; the round-2 colouring is a character-handleless "count of counts"; the FLAG lead is
negative — recovery doc §9.8.9). Route C reads `Q` off the cone **directly** (the cone is an iso-invariant of the
graph; the degree-2 form vanishing on it is canonical up to scalar), so it never touches that wall.

**Where it sits.** Banked quasipoly seal `AffinePolarSeal.reachesRigidOrCameron_affinePolar` = the floor (correctness).
Route C = the poly-cost upgrade for the forms-graph residue. It is a **larger build + a behavioural change** (a
structure-recovery pre-processor); pursue it *because* the lighter WL route stalled, not before.

---

## 2. Knowledge foundation

### 2a. The object
- **Graph.** `V = K^d` (`K = 𝔽_q`, `q = p^e`, `d = 2m`); adjacency `Q(x − y) = 0` for a nondegenerate quadratic form
  `Q` of type `ε` — the affine-polar forms graph `VO^ε_{2m}(q)`. A translation (Cayley) scheme ⟹ vertex-transitive,
  schurian, primitive rank-3 SRG.
- **Automorphisms.** `Aut = ` translations `⋊ ΓO^ε(Q)` (affine similitudes: linear maps `g` with `Q(gx) = μ(g)·σ(Q(x))`
  for a scalar `μ` and a field automorphism `σ`; for prime `q`, just `GO^ε(Q)`, no field twist). `|Aut|` is huge (e.g.
  `VO⁻₄(3)`: `233280 = 3⁴·|GO⁻₄(3)|`) — the graph is far from rigid, which is *why* the harvest keeps branching small.
- **The two forms `make_Q` uses** (probe ground truth): `ε=+1`: `Σᵢ x_{2i}x_{2i+1}` (hyperbolic); `ε=−1`:
  `Σ x_{2i}x_{2i+1} + x_{d-2}² − g·x_{d-1}²` with `g` = least non-square (elliptic).
- **Skresanov isolation.** The seal's residue is the schurian affine slice `{1-dim cyclotomic (cited) + forms-graphs
  (c)–(f)}`; Route C's recovery is needed on (c)–(f) `{affine-polar / alternating / half-spin / Suzuki–Tits}`.

### 2b. Why the cone determines `Q` (the algebra that dodges the wall)
The connection set from the origin is the punctured isotropic cone `C = {x ≠ 0 : Q(x) = 0}`. The homogeneous degree-2
forms vanishing on `C` form a vector space; for a nondegenerate quadric with `d ≥ 3` and non-tiny `q` that space is
**1-dimensional = ⟨Q⟩** (a classical finite-geometry fact; probe-confirmed dim `= 1` with no exceptions in range).
So `Q` is recovered by ONE linear solve over the `d(d+1)/2` degree-2 monomials — poly, non-circular (no WL, no orbits).
The cone only fixes `Q` **up to scalar `μ`**, but that is exactly right: `O(Q) = O(μQ)` and `GO(Q) = GO(μQ)`, so the
recovered object is well-defined, and in the refined colouring the global `μ` cancels in every comparison.

### 2c. The honest subtlety — isometry scheme vs. the given similitude graph
The landed `reachesRigidOrCameron_viaOrthogonalForm` (§4) seals `affineScheme (isometryGroup Q)` — the **isometry**
scheme `O(Q)`, whose relations are the **exact** `Q`-value of a difference. But the *given graph* is
`affineScheme (similitudeGroup Q)` — the **similitude** scheme `GO(Q)`, whose relations are only the isotropy class
(`∃ g∈GO(Q), g(u−t)=u'−t ⟺ isoClass(u−t)=isoClass(u'−t)`). At any bounded base the isotropy profile does **not**
jointly-separate — that is the stall. So Route C's load-bearing new content is **not** "invoke `viaOrthogonalForm`";
it is:

> **The recovered form `Q` refines the similitude graph to the isometry scheme.** Colour each pair `(t, z)` by `Q(z − t)`
> (well-defined up to the *global* scalar `μ`, which cancels in comparisons). That refined colouring is (i)
> **iso-invariant** (a graph iso carries the cone to the cone, hence `Q` to a scalar multiple), and (ii) **discretizes
> at a spanning base** via `coords_determine` / `spanning_sameExactGram_determines`.

`coords_determine` and the spanning generalization are landed; the refinement bridge + its iso-invariance are the new
lemmas (A3 / F4 in §6).

---

## 3. The architecture — 1 engine + N adapters (the merge)

The families **merge at the "recovered structure → iso-invariant refining data on `V`" boundary**. Once a family hands
the generic engine (a) the recovered form as a colouring of pairs and (b) a "form-values-at-a-base determine the vertex"
certificate, everything downstream is shared. So Route C is **one generic engine + a small `IFormStructure` interface
with 4 implementations** — *not* four separate objects, and *not* one monolith with four branches.

```
        ┌─────────────── GENERIC ENGINE (1 copy, all families) ───────────────┐
 graph ─►  F1 recover additive/affine structure  (T = O_p(Aut), the socle)      │  ← family-agnostic
        │  F2 [q=pᵉ] recover 𝔽_q-scalar structure  (Frobenius/ΓL seam)          │  ← family-agnostic
        │                         │                                             │
        │      IFormStructure.RecoverForm(graph, V) ──► φ         ◄── family     │  ← family hook 1
        │                         │                                             │
        │  refine pairs by φ  (iso-invariant colouring; global scalar cancels)  │
        │      IFormStructure.Separates(φ, base) ──► certificate  ◄── family     │  ← family hook 2
        │                         │                                             │
        │  canonical spanning base + discretize ──► canonical labelling         │
        │     (OR IFormStructure.AutGens(φ) ──► existing Schreier–Sims → |Aut|)  │  ← family hook 3 (|Aut| side)
        └──────────────────────────────────────────────────────────────────────┘
```

**Merge boundaries — what is shared vs. family-specific:**

| layer | shared (1 impl) | family-specific (N adapters) |
|---|---|---|
| additive/affine recovery (F1) | ✅ `T = O_p(Aut)` — identical for all | — |
| 𝔽_q-scalar recovery (F2) | ✅ | — |
| the generic engine (refine-by-φ, canonical base, discretize) — F3/F5 | ✅ | — |
| Schreier–Sims / `PermutationGroup.cs` | ✅ (exists) | — |
| iso-invariant base construction, direction-blind lex-min | ✅ | — |
| **`RecoverForm`** (which variety / linear system) | — | **the form/geometry object** |
| **`Separates`** (the `coords_determine` analog) | — | **the form's nondegeneracy** |
| **`AutGens`** (classical-group generators; only for the \|Aut\| side) | — | **the classical group** |

Affine-polar / alternating / half-spin share ~all of `RecoverForm` and `Separates` (all recover a bilinear/quadratic
form and separate by polar-nondegeneracy). **Suzuki–Tits is the one genuinely-different adapter** (non-form σ-twisted
ovoid, char-2 — same interface, different internals; folds into the char-2 track, plan §11.5).

---

## 4. The preexisting foundation Route C rides on (exact names)

### Lean — LANDED & AXIOM-CLEAN (the back-half + the generic spine)
All in `GraphCanonizationProofs/ChainDescent/` unless noted. Index rows = `GraphCanonizationProofs/PublicTheoremIndex.md`.

| name | location | what it gives Route C |
|---|---|---|
| `affineScheme (G₀) (hneg)` | `CascadeAffine.lean:2204` | **the generic merge point** — the affine scheme of any `G₀ ≤ GL(V)` with `−1∈G₀`; `SchurianScheme (p^d)` |
| `discrete_affineScheme_of_jointSeparates` | `CascadeAffine.lean:2427` | **generic** — a base `T` that jointly-separates ⟹ `warmRefine` from `T` is `Discrete`. The only family input is the separation hypothesis `hsep` |
| `coords_determine` | `CascadeAffine.lean:2640` (idx 1211) | `Q` nondeg polar + `Q v`, `Q(v−eᵢ)` agree with `v'` ⟹ `v = v'` — **the `Separates` certificate for the quadratic case** |
| `coords_determineK` | `FieldGeneric.lean:87` | the field-generic (`[Field K]`) version of `coords_determine` |
| `spanning_sameExactGram_determines` | `ScratchBranchDepth.lean:65` | generalizes `coords_determine` to any **spanning** base (not just the standard frame) |
| `spanning_exactQ_determines` | `ScratchDominatorForms.lean:67` | the affine-isometry-scheme form of the above (Q-value-of-difference data) |
| `isometryGroup Q` | `CascadeAffine.lean:2656` | `O(Q) = {g : ∀x, Q(gx)=Q(x)}` as a `Subgroup` |
| `neg_mem_isometryGroup` | `CascadeAffine.lean:2678` | `−1 ∈ O(Q)` (the `hneg` for `affineScheme`) |
| `frameBase`, `frameBase_card_le` | `CascadeAffine.lean:2684`,`:2688` (idx 1215-6) | the `{0,e₁,…,e_d}` base and `card ≤ d+1` |
| `reachesRigidOrCameron_viaOrthogonalForm` | `CascadeAffine.lean:2704` (idx 1217) | **the back-half** — `O(Q)` (nondeg) discretizes at `frameBase` and seals via `viaSpielman`. NB: **isometry** scheme, not the given similitude graph (§2c) |
| `similitudeGroup Q`, `neg_mem_similitudeGroup`, `isometry_le_similitude` | `CascadeAffine.lean:2746`,`:2766`,`:2771` | `GO(Q)` = the given graph's linear group; `O(Q) ≤ GO(Q)` |
| `reachesRigidOrCameron_viaSpielman` | `Cascade.lean:4690` | the wrapper: a bounded-base discreteness witness ⟹ the seal disjunction (Cameron-free sub-exp floor) |
| `reachesRigidOrCameron_viaAffineFormScheme` | `CascadeAffine.lean:2057` (idx 1207) | Stage-A capstone; the seal wiring for the forms-graph residue (context) |
| `orbMk_affine_eq_iff`, `affineScheme_relOfPair_eq_iff`, `affineScheme_relOfPair_translation` | `CascadeAffine.lean:2218`,`:2281`,`~:2438` | the affine-scheme relation↔difference-orbit dictionary (used to state the refined colouring) |
| `AffinePolarSeal.reachesRigidOrCameron_affinePolar` | `AffinePolarSeal.lean:410` | the **banked quasipoly seal** (in `build.sh`) — the floor Route C upgrades |

> **⚠ Do NOT build on these (superseded/false at the plain frame, idx 1221-1226,1237):**
> `SimilitudeFrameSeparates`, `reachesRigidOrCameron_viaSimilitudeForm`, `…viaCountsDetermineFrameQ`,
> `…viaIsotropyCounts`. They ask the similitude scheme to separate at the *frame*, which is FALSE for minus-type (the
> node-4 stall). Route C avoids them by recovering `Q` and refining to the isometry scheme (§2c), not by counting.

### C# — EXISTS (the group back-end + the seam + the pre-processor template)
In `GraphCanonizationProject/`.

| file | what it gives Route C |
|---|---|
| `PermutationGroup.cs` | **full Schreier–Sims** — stabilizer chain, `AddGenerator`, `Order`, `Contains`, `Orbit`, `BasePoints`, `IsAbelian`, `IsElementaryAbelian`. Route C's group back-end is a **call, not a build**; F1's `O_p`/normal-closure hosts here |
| `ITransversalOracle.cs` | the T-C seam (`Classify(n, adj, targetCell, path, knownGroup) → representatives`) — where a Route-C oracle plugs in |
| `CascadeOracle.cs` | the all-reps oracle (returns the whole cell; harvest prunes a-posteriori) — the current default |
| `ChainDescent.cs` | the harness: cross-branch harvest + prune (`CoveredByPathFixingAut`, ~`:589`), deferral selector (~`:251-281`) |
| `Option2ExtractionProbe.cs`, `TwistConstruction.cs` | **the pre-processor template** — Option 2's Layer D (the F₂/rigid mirror). Route C's engine is the *symmetric-form clone* of this architecture (§6) |

---

## 5. The probes (what is already validated, and how to re-run)

All in `GraphCanonizationProofs/` (pure Python, `python3 <file>`; reuse `model_gap.py` helpers `make_Q`/`sub`/`polar`/
`isoclass`/`add`).

- **`route_c_reconstruct_probe.py` — A1 (form recovery).** For each `(ε,d,q)`, builds the isotropic cone and computes
  the rank of the degree-2 vanishing system. **Result: `vanishDim = 1` everywhere** (ε=±, d=4,6,8, q=3,5,7,11) ⟹ `Q`
  reconstructible up to scalar by one linear solve, no small-`q` exception. (Odd `q`; char-2 is a separate track — over
  `𝔽_{2^k}` squaring collapses degree, so the degree-2 vanishing space differs; handled by the Arf/char-2 substrate.)
- **`route_c_f1_probe.py` — F1 (additive-structure recovery).** Builds `VO^ε₄(q)` with true translations + monomial
  isometries, **scrambles** by a random relabelling, then recovers `O_p` via normal closures with **no ground-truth
  reference**. **Result (VO^ε₄(3), VO^ε₄(5), both types): `Op == T` exactly, regular, elementary-abelian, and the
  recovered coordinates give `coneVanishDim = 1`** ⟹ recovery is method-correct, scramble-invariant, and hands A1 a
  valid coordinatization. (Odd `q`: `−1` is a `p'`-element so `G₀` is a `p'`-group and `O_p(G)=T` is clean; char-2
  recovers `T` the same way but needs Aut's `p'`-part, e.g. `S₅` for Clebsch.)
- **Supporting (from the direct route, still relevant):** `model_gap.py` (the isoClass scheme + orbit/refinement
  helpers), `factorization_probe.py`/`flag_stall_probe.py` (the node-4 stall evidence that motivates Route C).

---

## 6. The build plan

### Foundation (must exist before the family builds)

| # | piece | side | status / notes |
|---|---|---|---|
| **F1** | **Additive/affine recovery** — `T = O_p(Aut)` (the socle), a basis → coordinates, any vertex → origin | C#+Lean | **algorithm probe-validated** (`route_c_f1_probe.py`). Build = host `O_p`/normal-closure on `PermutationGroup.cs`, consuming harvested-Aut generators; emit basis + origin. "`soc = O_p = T`" = the affine-primitive **socle theorem** (cite) |
| **F2** | **𝔽_q-scalar recovery** (q=pᵉ) — recover the field/Frobenius structure (the ΓL/semilinear seam) | C#+Lean | **new; deferrable.** `q=p` needs nothing (additive = 𝔽_p-linear automatically). `FieldGeneric`/`efield` = the template; same seam the WL route had (plan Layer D) |
| **F3** | **`IFormStructure` interface + generic engine** (refine-by-φ, canonical base, discretize) | C# | new, thin; the merge point |
| **F4** | **Iso-invariance of the recovered `φ`** — the `forcedNode_relabel` analog: `RecoverForm` is relabeling-equivariant up to scalar | Lean | **new; vacuity-trap-prone** (cf. `SchemeReproduced` — get the equivariant predicate right). Mirrors landed `forcedNode`/`forcedNode_relabel` |
| **F5** | **Generic seal→poly spine** — `RecoverForm ⟹ refined scheme ⟹ discrete_affineScheme_of_jointSeparates ⟹ viaSpielman` | Lean | **downstream all landed & generic**; only the A3 refinement bridge is new |

### Instance 1 — affine-polar `VO^ε` (proves the whole spine)

| # | piece | status |
|---|---|---|
| **A1** | `RecoverForm` = solve the degree-2 vanishing system on the cone | **probe ✓** (`vanishDim=1`); Lean = a finite-geometry nondegeneracy lemma (`⟨Q⟩` = the vanishing space) |
| **A2** | `Separates` = `coords_determine` / `spanning_sameExactGram_determines` | **LANDED, axiom-clean** |
| **A3** | **the refinement bridge** — recovered `Q` colours pairs by `Q(z−t)` (global scalar cancels) ⟹ isometry-scheme separation ⟹ `discrete_affineScheme_of_jointSeparates` | **new — the genuine Route-C Lean content** (§2c) |
| **A4** | `AutGens` = `GO(Q)` generators (reflections) → existing `PermutationGroup` (only for the \|Aut\| side) | Schreier–Sims exists; generator list is standard classical-group data |

Instance 1 forces F1/F3/F4/F5 into existence, so it is **most of the total work**; the other three families then
reduce to writing their `IFormStructure` implementation.

### Instances 2–4 — reuse the engine, write only the adapter (plan §11.4/§11.5)
- **Alternating (d):** `RecoverForm` recovers an alternating bilinear `B`; `Separates` = the symplectic analog of
  `coords_determine` (radical-nondegeneracy). ~90% shared. *Medium.*
- **Half-spin (e):** form-adjacent spinor incidence; expect `RecoverForm`/`Separates` close to affine-polar. *Medium–high.*
- **Suzuki–Tits (f):** the outlier — `RecoverForm` recovers the σ-twisted ovoid polynomial (char-2), `AutGens = Sz(q)`.
  Same interface, mostly-new internals; folds into the char-2 track. *Hardest; do last.*

### C# / Lean split, and the reuse to exploit
- **The C# engine is the symmetric mirror of Option 2's Layer D** (IR doc §11.10, built through D-M4 as a Phase-2
  pre-processor: recover structure → refine/solve → plug the existing seam). **Clone that architecture**, swapping
  `IFormStructure` for the F₂ extractor. This is the payoff of the recovery↔co-recovery duality
  ([[project_recovery_corecovery_duality_2026-07-03]]): the two pre-processors share a skeleton.
- **Lean deliverable is the poly-supporting structural object**, not a runtime proof: "the recovered-form-refined
  scheme discretizes at an iso-invariantly-constructible `O(d)` base" (F5 + A3), with "poly" the meta-claim over that
  bounded base + the existing Schreier–Sims meta-cost (same discipline as Part A's `Order = ∏ orbit sizes`).

### Sequencing & risks
1. **F1 + F3 + A1 + A3 + F5** (affine-polar, `q=p`, discretization spine) — the critical path; delivers poly for the
   sealed family and builds the whole generic engine.
2. **F4** iso-invariance — the vacuity-trap-prone piece; get the equivariant predicate right before leaning on it.
3. **F2** (`q=pᵉ` seam) — deferrable; the same Layer-D seam the WL route had.
4. **Instances 2→3→4** — pure adapters; Suzuki last (needs the char-2 substrate as its own prerequisite).

**Definition of done (Route C, affine-polar):** F1 recovers coordinates iso-invariantly; A1 recovers `Q`; A3 refines
to the isometry scheme; F5 discretizes at the `O(d)` base and seals via `viaSpielman` — the structural bounded-base
discreteness object complete, "poly" the meta-claim over it. The C# engine reproduces `|Aut|` via `PermutationGroup`.

---

## 7. Honest scope — what Route C does and does NOT do
- **Does:** upgrade the **forms-graph** residue from the banked quasipoly seal to **polynomial**, family by family,
  via a shared engine. Sidesteps the node-4 WL wall entirely (recovery is linear algebra, not WL).
- **Does NOT:** touch the **rigid mirror** (the IR-solver **row 4** / multipede / non-schurian residue). There is no
  large classical group to recover there — Route C is structurally inapplicable. That residue is Option 2's job
  (F₂-structure recovery, IR doc §11). **But the meta-strategy is identical** — "recover the algebraic substrate, use
  exact algebra instead of WL" — so the two pre-processors share the Layer-D architecture (§6).
- **Char-2 / Suzuki:** a separate analytic track (Arf/additive-trace, no `χ`); the *combinatorial* engine (F1/F3/F5)
  transfers char-agnostically, only `RecoverForm`/`Separates` change.
- **Dead ends (do not re-walk):** the WL/`bᵢ=1` build via `ColorRefinesGramK` (circular, node-4 wall, recovery doc
  §9.8.9); the frame-locked similitude predicates (idx 1221-1226, §4). δ′ dominator-closure is walled for `bᵢ=1`
  (dimensional wall, `ScratchDominatorForms`).

---

## 8. Pointers
- **Live route it replaces:** [`chain-descent-recovery-route.md`](./chain-descent-recovery-route.md) (STATUS + §7 Route
  C sketch + §9.8.9 stall verdict).
- **Per-family analysis:** [`chain-descent-formsgraph-wldim-plan.md`](./chain-descent-formsgraph-wldim-plan.md) §11.4
  (alternating/half-spin/Suzuki), §11.5 (char-2), §1 item 1 (the Route A/B/C fork).
- **The rigid mirror (same meta-strategy):** [`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md)
  §11 (Option 2, Layer D) + [[project_option2_f2_gap_2026-06-20]].
- **The seal it upgrades:** `AffinePolarSeal.reachesRigidOrCameron_affinePolar` (banked, in `build.sh`);
  `GraphCanonizationProofs/PublicTheoremIndex.md` idx 1207-1237 (Stage A/B decl map).
- **What's-left map:** [`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md) §3a.1, §4.
- **Cross-session memory:** [[project_recovery_corecovery_duality_2026-07-03]],
  [[project_formsgraph_wldim_viability_2026-06-28]].

---

*Maintenance: update STATUS as F1–F5 / A1–A4 land; keep the exact-name table (§4) in sync with source line numbers
(they drift — verify before citing); this doc is the Route-C staging point, the recovery doc §9.8.9 is the reason it exists.*
