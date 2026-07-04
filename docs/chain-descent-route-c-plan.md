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

**Where Route C stands (2026-07-03) — handoff snapshot.** The Route-C **Lean spine is assembled and fully axiom-clean**
(`ScratchRouteC.lean`, 34 decls, all `[propext, Classical.choice, Quot.sound]`, NOT in `build.sh`). Landed:
- **The single-form spine (affine-polar):** F1+A1 (C#, confirmed vs the real harness) → A3 brick 1 (isometry scheme
  refines the graph) → discretize at a spanning base (`viaOrthogonalForm_spanning`) → **F4** iso-invariance
  (`recoveredForm_colouring_equivariant`). Rests on ONE exact scoped citation, `NondegQuadricDeterminesForm` (below).
- **F2 (`q=pᵉ` Frobenius/ΓL seam):** semilinear iso-invariance (`recoveredForm_colouring_equivariant_semilinear`),
  rests on the cited `ConePreservingCollineationIsSemiSimilitude` (fundamental thm of projective geometry).
- **F3 the engine interface (`IFormStructure`):** `FormAdapter` + `FormAdapter.reachesRigidOrCameron` (any adapter ⟹
  the seal). **Instance 1 (affine-polar) `affinePolarAdapter` ✅. Instance 2 (alternating `Alt(5,q)`) ✅ SEALED**
  (`reachesRigidOrCameron_alternating`, via the multi-quadric engine `multiFormAdapter`/`coords_determine_multi` +
  the concrete Plücker sub-Pfaffians `plucker_hjoint`) — first non-quadratic family. **Instance 3 (half-spin) ✅
  SEALED** (`reachesRigidOrCameron_halfSpin`, via the 10 validated D₅ spinor quadrics `S0..S9` + `spinor_hjoint` +
  `multiFormAdapter`; brick-1 `halfSpin_refines_coneScheme`; full instance-1 parity); **Instance 4 (Suzuki) not
  started.**
- **Multi-quadric bridges (NEW 2026-07-03, axiom-clean) — brings the multi-form families to full instance-1
  parity.** Previously the `multiFormAdapter` families (alternating, half-spin) carried only the *seal* leg, not
  the *refinement* + *iso-invariance* legs the single-quadratic instance has. Both now supplied GENERICALLY over
  the form family: **brick-1-multi** `multiIsometryScheme_refines_coneScheme` (the recovered joint-isometry scheme
  `⨅ₖ O(Q_k)` refines the *graph-intrinsic* cone-stabilizer scheme `jointConeStab Qs` — cleaner than the
  single-form case, since the cone stabilizer is defined from the connection set, not a form-defined group) and
  **F4-multi** `recoveredFamily_colouring_equivariant` + `recoveredFamily_partition_isoInvariant` (a graph iso
  transports the value-tuple colouring by a global INJECTIVE `Φ`, so the colour partition is iso-invariant; `Φ`
  is the multi-form replacement for the single-form scalar `μ`; rests on the carried scoped citation
  `JointVarietyDeterminesFamily`, the multi-form sibling of `NondegQuadricDeterminesForm`). Factored the generic
  `affineScheme_refines_of_le` (`H ≤ G ⟹` finer; `isometryScheme_refines_similitudeScheme` is now its corollary);
  concrete `alternating_refines_coneScheme` / `halfSpin_refines_coneScheme` confirm the bridge fires on the real
  Plücker / spinor families. **⟹ alternating AND half-spin both at full instance-1 parity.**
- **Both review-flagged items resolved:** the classical carry is **discharged as an exact scoped citation**
  (`NondegQuadricDeterminesForm`); the **meta-poly bootstrapping is assessed sound** (§7a — global coordinatization,
  not the node-4 wall in disguise).

**▶ PICK UP HERE (next actionable steps, in rough priority):**
0. ✅ **Multi-quadric bridges — DONE 2026-07-03** (brick-1-multi + F4-multi, generic; alternating at full
   instance-1 parity, half-spin pre-equipped). See STATUS "Multi-quadric bridges".
1. ✅ **Half-spin instance — DONE 2026-07-03** (`reachesRigidOrCameron_halfSpin`, axiom-clean). The 10 validated D₅
   spinor quadrics `S0..S9` are transcribed (`ScratchRouteC.lean §HalfSpin`), `spinor_hjoint` proved from `S0..S4`
   by coordinate isolation, sealed via `multiFormAdapter` + the shared engine; brick-1 `halfSpin_refines_coneScheme`
   landed; F4 generic. Full instance-1 parity. **⟹ 3 of 4 form families sealed; only Suzuki remains.**
2. **Suzuki–Tits instance (last):** char-2, σ-twisted ovoid, needs the char-2 substrate first (§11.5); not a
   multi-quadric family — the outlier. §6 "Instances 2–4".
3. **After the four seals — the combined correctness object + the C# runtime: see §9 (FORWARD PLAN).** The four
   adapters combine into ONE clean seal via a single cited classification premise + one iso-invariance lemma (L1,
   the load-bearing new piece — spot-check it first); the C# canonizer still lacks *all* family handlers (C1–C4).
   §9.0 explains why "4 seals + finite exceptions" collapses to "1 citation + 1 lemma" (Route C is threshold-free).
4. **The two carried citations** (optional, to remove them from the spine): a full Lean proof of
   `NondegQuadricDeterminesForm` and `ConePreservingCollineationIsSemiSimilitude` (finite-geometry developments).
5. **The meta-poly rigor side (last):** residuals R1–R3 (§7a) — build the Aut-free geometric
   coordinatizer (also delivers F2's field recovery), name Buekenhout–Shult (R2), double-check `d=4` (R3).

**✅ DONE — the C# recovery front (abstract graph → coordinates → form → graph), confirmed against the REAL harness.**
- **F1 — additive-structure recovery** (`PermutationGroup.RegularNormalPSubgroup` + `AffineStructureRecovery.Recover`):
  `T = O_p(Aut)` (the socle) recovers the regular elementary-abelian translations `≅ (𝔽_p)^d`, and a basis coordinatizes
  the vertices. Probe `route_c_f1_probe.py` (algorithm) + `RouteCF1Probe.cs` (production, vs the real `ResidualGroup`,
  ground-truth exact).
- **A1 — form recovery** (`QuadraticFormRecovery.RecoverForm`): recovers `Q` up to scalar by ONE degree-2 kernel solve
  on the cone. Probe `route_c_reconstruct_probe.py` (`vanishDim=1` all ε/d/q) + `RouteCF1Probe.cs`: the recovered `Q` +
  coords **reconstruct the entire graph** (`Q(coords[x]−coords[y])=0 ⟺ x~y`, **0 mismatches**, VO^±₄(3), VO^±₄(5)).
- Both odd-q and char-2 for F1 (full `Aut` delivered); A1 is odd-q (char-2 = separate Arf track). All C# tests green,
  existing `PermutationGroup` tests unaffected.

**✅ DONE — the Lean spine (`ChainDescent/ScratchRouteC.lean`, all axiom-clean, NOT in `build.sh`).**
- `coords_determine_spanning` + `reachesRigidOrCameron_viaOrthogonalForm_spanning` — the **spanning-base** generalization
  of the landed `coords_determine`/`viaOrthogonalForm`: the isometry scheme `O(Q)` discretizes at ANY base whose
  differences span (Route C individualizes an iso-invariantly chosen base, not the literal standard frame).
- `isometryScheme_refines_similitudeScheme` (**A3 brick 1**) — `O(Q)≤GO(Q)` ⟹ the isometry scheme (exact-`Q` relations)
  refines the given similitude graph (isotropy-only). The consistency half of the bridge.
- **F4 equivariance core (NEW 2026-07-03, axiom-clean):** `recoveredForm_colouring_equivariant` — the linear part `g` of
  a graph iso carries the `Q`-cone to the `Q'`-cone, hence (via the carried `NondegQuadricDeterminesForm`) the recovered
  **difference colouring** transports by one global scalar: `Q'(g u − g t) = μ · Q(u − t)`. Provable bricks
  `similitude_colouring_equivariant` (the equivariance identity) + `similitude_conePreserving` (cone consistency); the
  one non-elementary link is `NondegQuadricDeterminesForm` (below).
- **The assembled spine:** recover `Q` (F1+A1, C# done) → work on the finer isometry scheme (refines the given graph,
  brick 1) → discretize at a spanning base (`viaOrthogonalForm_spanning`, landed) → the whole thing is iso-invariant
  (F4). **Discreteness does NOT transfer down to the similitude scheme** (that's the node-4 stall) — so Route C is a
  *distinct canonicalization object*, and F4 supplies exactly the iso-invariance that makes "discrete ⟹ canonical".

**◻ REMAINING — the classical carry, the meta claim, and the bootstrapping question.**
- **✅ `NondegQuadricDeterminesForm` — DISCHARGED as an exact citation (2026-07-03).** "a nondegenerate quadric
  determines its quadratic form up to a nonzero scalar" (the `vanishDim=1` fact, = A1's Lean side = F4's one
  non-elementary link — they unify). Now a **correctly-scoped named premise** (`p ≠ 2`, `4 ≤ d`, `Q.polarBilin`
  nondegenerate) — the *exact range where it is TRUE* (the unrestricted `∀ Q R` form is FALSE at `d=3,q=3`: a conic's 4
  points lie on a pencil, `vanishDim=2`). Carried like `Theorem41Statement`/G3 (Mathlib has no quadric Nullstellensatz);
  reference = Hirschfeld, *Projective Geometries over Finite Fields* / the projective Nullstellensatz for a nondegenerate
  quadric; probe-confirmed exactly in-scope (`d=4,6,8`, `q=3,5,7,11`). A full Lean proof (finite-geometry development) is
  optional future work; the citation is exact + non-vacuous, so the carry is legitimate.
- **Meta poly claim:** "poly" stays a meta-argument over the bounded-base discreteness object + poly per-node (no runtime
  model in Lean).
- **★ ASSESSED — meta-poly bootstrapping (spotted + resolved 2026-07-03; full write-up §7a):** F1 as built recovers
  coordinates from `T = O_p(Aut)` — it **consumes `Aut`**, whose poly computation is the open T0 problem Route C sidesteps
  (potential circularity). **Verdict: resolved at the meta level — Route C is genuinely poly, non-circular.** Key points:
  (i) coordinatization is a **global** computation, not bounded-round WL, so it is NOT the node-4 wall in disguise; (ii)
  `O_p(Aut)` was only a de-risking shortcut — the poly pipeline uses **Aut-free geometric coordinatization** (recover the
  polar-space geometry from the graph, coordinates via Buekenhout–Shult, rank≥3 / `d≥6`; `d=4` = GQ special case); (iii)
  the enabling primitive is **probe-confirmed Aut-free** (`route_c_bootstrap_probe.py`: the local invariant separates
  collinear triangles and recovers spanning isotropic lines, all VO^± `d=4,6` `q=3,5`). Residuals (record, don't block):
  build the geometric coordinatizer (R1), name the geometry-recovery citation (R2), double-check `d=4` (R3). The Lean
  object (F4) is unaffected (no runtime model in Lean). See §7a.
- **◑ F2 (`q=pᵉ` Frobenius seam) — Lean core LANDED (2026-07-03, axiom-clean):**
  `recoveredForm_colouring_equivariant_semilinear` — the recovered form is iso-invariant up to scalar **and** a field
  automorphism σ (a graph iso over 𝔽_q is 𝔽_p-semilinear, `g = M∘σ̂`). `q=p` is the `σ=id` case. Remaining F2 = the C#
  field-recovery side, which folds into R1 (geometric coordinatization recovers PG over 𝔽_q, field included).
- **◑ F3 (`IFormStructure` engine interface) — Lean interface LANDED + 2 instances SEALED (2026-07-03, axiom-clean):**
  `FormAdapter` + `FormAdapter.reachesRigidOrCameron` (any adapter ⟹ seal); **instance 1 affine-polar**
  (`affinePolarAdapter`) + **instance 2 alternating `Alt(5,q)`** (`reachesRigidOrCameron_alternating`, via
  `multiFormAdapter` + the Plücker forms) both sealed; **instance 3 half-spin** scoped + `halfSpin_reduction` landed.
  Each family reduces to one `FormAdapter` (supply `G₀` + `separates`); the multi-quadric families (alternating,
  half-spin) reduce further to just `Qs` + `hjoint` via `multiFormAdapter`.
- **Remaining instances:** **half-spin** (the 10 D₅ spinor quadrics + `hjoint` — §6 "Half-spin"; engine + reduction
  already landed) and **Suzuki** (char-2 outlier, last) + the C# side of the engine.

**▶ VERIFY what's landed (fresh-reader commands):**
- Lean: `cd GraphCanonizationProofs && lake env lean ChainDescent/ScratchRouteC.lean` (exit 0, clean). Axiom-check by
  appending `#print axioms ChainDescent.RouteC.<name>` and re-running (expect `[propext, Classical.choice, Quot.sound]`).
- C#: `cd GraphCanonizationProject.Tests && dotnet test --filter "FullyQualifiedName~RouteCF1Probe.F1_Recovers_TranslationGroup&Category!=LongRunning"`
  (fast, q=2,3; the `_Large` q=5 cases are `LongRunning`, ~5 min each — canonizer cost, not F1/A1).
- Python probes: `cd GraphCanonizationProofs && python3 route_c_reconstruct_probe.py` / `route_c_f1_probe.py`.

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
| `RouteC.coords_determine_spanning` | `ScratchRouteC.lean` (**Route C, NEW, axiom-clean**) | spanning generalization of `coords_determine`: `Q`-values at any *spanning* base `S` (`span S = ⊤`) determine the vertex |
| `RouteC.reachesRigidOrCameron_viaOrthogonalForm_spanning` | `ScratchRouteC.lean` (**Route C, NEW, axiom-clean**) | spanning generalization of `viaOrthogonalForm`: `O(Q)` discretizes at any base `T∋o` whose differences `{t̄−ō}` span — the iso-invariantly-chosen base Route C needs |
| `RouteC.isometryScheme_refines_similitudeScheme` | `ScratchRouteC.lean` (**Route C A3 brick 1, NEW, axiom-clean**) | `O(Q)≤GO(Q)` ⟹ the isometry scheme refines the given similitude graph (finer `relOfPair`) — the recovered form is consistent, not fabricated |
| `RouteC.NondegQuadricDeterminesForm` | `ScratchRouteC.lean` (**Route C — the exact carried classical citation, NEW**) | scoped premise (`p≠2`, `4≤d`, `Q` nondeg): same isotropic cone ⟹ scalar-multiple form (A1's `vanishDim=1` uniqueness). The EXACT true statement (unrestricted form false at `d=3,q=3`); Hirschfeld / projective Nullstellensatz; carried like `Theorem41Statement` |
| `RouteC.similitude_colouring_equivariant`, `RouteC.similitude_conePreserving` | `ScratchRouteC.lean` (**Route C F4 bricks, NEW, axiom-clean**) | a form similitude carries the difference colouring by one scalar (`Q'(gu−gt)=μ·Q(u−t)`) + preserves the cone — pure linearity |
| `RouteC.recoveredForm_colouring_equivariant` | `ScratchRouteC.lean` (**Route C F4 capstone, NEW, axiom-clean**) | graph-iso cone-preservation + `NondegQuadricDeterminesForm` ⟹ the recovered difference colouring is equivariant (iso-invariant up to global scalar) — the "discrete ⟹ canonical" link |
| `RouteC.frobVec`, `RouteC.frobVec_sub`, `RouteC.semisimilitude_colouring_equivariant` | `ScratchRouteC.lean` §F2 (**Route C F2 bricks, NEW, axiom-clean**) | coordinate-wise Frobenius σ̂ + its additivity + the semilinear equivariance identity `Q'(M(σ̂u)−M(σ̂t))=μ·σ(Q(u−t))` |
| `RouteC.ConePreservingCollineationIsSemiSimilitude` | `ScratchRouteC.lean` §F2 (**Route C F2 cited premise, NEW**) | scoped (`(2:K)≠0`, `4≤d`): cone-preserving collineation `g` ⟹ `g=M∘σ̂` semi-similitude (fundamental thm of projective geometry + `NondegQuadricDeterminesForm`; carried) |
| `RouteC.recoveredForm_colouring_equivariant_semilinear` | `ScratchRouteC.lean` §F2 (**Route C F2 capstone, NEW, axiom-clean**) | q=pᵉ: the recovered form is iso-invariant up to scalar **and** field auto σ — F4 for the semilinear (ΓL) case; `q=p` = the `σ=id` specialization |
| `RouteC.FormAdapter`, `RouteC.FormAdapter.reachesRigidOrCameron` | `ScratchRouteC.lean` §F3 (**Route C engine interface, NEW, axiom-clean**) | the `IFormStructure` interface (`G₀` + `−1∈G₀` + bounded base + `separates`) + the shared engine theorem (any adapter ⟹ the seal). 1 engine, N family adapters |
| `RouteC.affinePolarAdapter` | `ScratchRouteC.lean` §F3 (**Route C instance 1, NEW, axiom-clean**) | affine-polar `VO^ε` as a `FormAdapter` (`G₀=O(Q)`, frame base, `coords_determine` certificate) — validates the interface, reproduces `viaOrthogonalForm` |
| `RouteC.coords_determine_multi`, `RouteC.coords_determine_multi_spanning` | `ScratchRouteC.lean` (**Route C alternating-family `separates` core, NEW, axiom-clean**) | a *family* `{Q_k}` with trivial common polar-radical determines the vertex from the joint value-profile (frame / spanning base) — the multi-quadric `separates` for `Alt(n≥5,q)` (Plücker quadrics), generalizes `coords_determine` |
| `RouteC.multiFormAdapter` | `ScratchRouteC.lean` (**Route C alternating engine hookup, NEW, axiom-clean**) | a form family `{Q_k}` with joint nondegeneracy ⟹ a `FormAdapter` (`G₀ = ⨅ₖ O(Q_k)` the joint isometry group, frame base, `coords_determine_multi` certificate). `affinePolarAdapter` = the `ι=Unit` case |
| `RouteC.Plucker.{Pf0..Pf4, pluckerForms, plucker_hjoint}` | `ScratchRouteC.lean §Plucker` (**Route C alternating instance, NEW, axiom-clean**) | the concrete 5 sub-Pfaffian quadrics on `𝔽_p^10` (via `linMulLin`) + their joint nondegeneracy `plucker_hjoint` (the sole geometric input) |
| `RouteC.Plucker.alternatingAdapter`, `RouteC.Plucker.reachesRigidOrCameron_alternating` | `ScratchRouteC.lean §Plucker` (**Route C instance 2 CAPSTONE, NEW, axiom-clean**) | `Alt(5,q)` as a sealed `FormAdapter` + the rigid-or-Cameron seal — the **first concrete non-quadratic (multi-form) Route-C family, end to end** |
| `RouteC.affineScheme_refines_of_le` | `ScratchRouteC.lean` (**generic refinement bridge, NEW, axiom-clean**) | `H ≤ G` (both `∋ −1`) ⟹ `affineScheme H` refines `affineScheme G`. The reusable core of every Route-C refinement brick; `isometryScheme_refines_similitudeScheme` is now its one-line corollary |
| `RouteC.jointConeStab`, `RouteC.neg_mem_jointConeStab`, `RouteC.iInf_isometryGroup_le_jointConeStab` | `ScratchRouteC.lean` (**multi-quadric bridges, NEW, axiom-clean**) | the **graph-intrinsic** setwise stabilizer of the joint cone `{v : ∀k, Q_k v=0}` (= the connection set) as a `Subgroup` + `−1∈` it + `⨅ₖ O(Q_k) ≤` it. The multi-form analog of `similitudeGroup`, defined from the graph not the form |
| `RouteC.multiIsometryScheme_refines_coneScheme` | `ScratchRouteC.lean` (**brick-1-multi, NEW, axiom-clean**) | the recovered joint-isometry scheme `⨅ₖ O(Q_k)` refines the cone-stabilizer scheme — the multi-form refinement leg (analog of `isometryScheme_refines_similitudeScheme`), tied to the actual graph via `jointConeStab`. `alternating_refines_coneScheme` = the concrete `Alt(5,q)` application |
| `RouteC.multiSimilitude_colouring_equivariant`, `RouteC.JointVarietyDeterminesFamily`, `RouteC.recoveredFamily_colouring_equivariant`, `RouteC.recoveredFamily_partition_isoInvariant` | `ScratchRouteC.lean` (**F4-multi, NEW, axiom-clean**) | the multi-form iso-invariance leg: provable equivariance brick (colouring transports by global `Φ`) + the scoped carried citation `JointVarietyDeterminesFamily` (joint variety determines the family up to invertible `Φ`; multi-form sibling of `NondegQuadricDeterminesForm`) + capstone (injective `Φ`) + partition-invariance payoff (`Φ` cancels in comparisons) |
| `RouteC.polar_linMulLin` | `ScratchRouteC.lean` (**reusable primitive, NEW, axiom-clean**) | `polar (linMulLin f g) x y = f x·g y + f y·g x` — the polar of a Clifford-term-sum quadric (Plücker / spinor forms) |
| `RouteC.HalfSpin.{S0..S9, spinorForms, S0_polar..S4_polar, spinor_hjoint}` | `ScratchRouteC.lean §HalfSpin` (**Route C instance 3, NEW, axiom-clean**) | the 10 concrete D₅ spinor quadrics on `𝔽_p^16` (validated by `route_c_halfspin_probe.py`: dim=10, exact 𝔽₂ count 2296, radical 0) + their joint nondegeneracy `spinor_hjoint` (from the 5 quadruple forms by coordinate isolation) |
| `RouteC.HalfSpin.{halfSpin_reduction, spinAdapter, reachesRigidOrCameron_halfSpin, halfSpin_refines_coneScheme}` | `ScratchRouteC.lean §HalfSpin` (**Route C instance 3 CAPSTONE, NEW, axiom-clean**) | half-spin as a sealed `FormAdapter` (`spinAdapter`) + the rigid-or-Cameron seal (`reachesRigidOrCameron_halfSpin`) + brick-1 (`halfSpin_refines_coneScheme`) — instance 3 DONE, full instance-1 parity |
| `RouteC.Suzuki.{ovoidC, SF0..SF4, suzukiForms, four_eq_zero, suzukiForms_ovoid, suzukiForms_infty, suzukiForms_homog}` | `ScratchRouteC.lean §Suzuki` (**Route C instance 4 — the σ-twisted forms rederived, NEW, axiom-clean**) | over a char-2 `CommRing K` with a Tits endo `σ` (`σ∘σ=(·)²`): the 5 σ-twisted Suzuki forms + proofs they cut the cone (vanish on the ovoid + at infinity + σ-twisted homogeneous). De-risk-validated (`route_c_suzuki_probe.py`, joint zero=cone exact). Remaining Suzuki = the σ-twisted `separates` + module bridge |
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
| `PermutationGroup.cs` | **full Schreier–Sims** — stabilizer chain, `AddGenerator`, `Order`, `Contains`, `Orbit`, `BasePoints`, `IsAbelian`, `IsElementaryAbelian`. **+ Route-C F1 ops (NEW 2026-07-03):** `RegularNormalPSubgroup(p)` (the socle/translations), `NormalClosure`, `Elements`, `HasExponentDividing`, `Perm.Order`/`Pow` |
| `AffineStructureRecovery.cs` | **Route C, NEW 2026-07-03** — `Recover(aut, p, origin)` = F1's entry point: socle `T` + `Dim` + vertex→`(𝔽_p)^Dim` coordinate map (via `T`'s regular action). Confirmed by `RouteCF1Probe.cs` |
| `QuadraticFormRecovery.cs` | **Route C, NEW 2026-07-03 (A1)** — `RecoverForm(adj, n, aff)`: recovers `Q` up to scalar by the degree-2 kernel solve on the cone; `RecoveredForm.Evaluate`. The quadratic family's `RecoverForm`. Odd-q; confirmed to reconstruct the whole graph |
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
- **`RouteCF1Probe.cs` — F1 + A1 against the REAL harness (C#, `GraphCanonizationProject.Tests/`).** Builds `VO^ε₄(q)`,
  runs the actual chain-descent canonizer, and confirms end-to-end (via the **production** methods) that (I)
  `CanonResult.ResidualGroup` contains the translations and has full `|Aut|`, (II) `AffineStructureRecovery.Recover`'s
  translation group equals `T` **exactly** (ground-truth), regular + elementary-abelian, and (III)
  `QuadraticFormRecovery.RecoverForm`'s `Q` + those coordinates **reconstruct the entire graph** (`Q(coords[x]−coords[y])
  =0 ⟺ x~y`, 0 mismatches). **All pass** (q=2,3 fast, both types; q=5 `LongRunning`). Confirms the harness↔F1↔A1 chain.
- **`route_c_halfspin_probe.py` — the D₅ half-spin spinor-quadric de-risking (2026-07-03).** Generates genuine
  pure spinors via the char-free big-cell Pfaffian formula and empirically fits the degree-2 vanishing ideal, then
  validates: dim `= 10` (q=3,5,7,11), **exact 𝔽₂ zero-locus count `= 2296` = the spinor-variety target** (`1+(q−1)∏₁⁴(qⁱ+1)`),
  𝔽₃ Monte-Carlo match (z=0.10), and **joint polar radical `= 0`** (= the Lean `hjoint`, provable from the 5 quadruple
  forms). Prints the 10 explicit forms (§6). Caught that the naive moment map gave the wrong forms — the reason to
  de-risk empirically, not template. The port reference for instance 3.
- **`route_c_suzuki_probe.py` — the Suzuki–Tits (f) de-risk (2026-07-04, q=8).** Builds GF(8) + the Tits
  endomorphism `σ` + the ovoid + cone + VSz(8) (Cayley on 𝔽₂¹², adjacency = 12-bit XOR ∈ cone). Validates the object
  (`σ²=Frob`, `|O|=65`, `|cone|=455`, SRG(4096,455,6,56) — ovoid formula `c=ab+σ(a)a²+σ(b)` correct) and measures the
  `separates` base three ways: **plain-cone direct-profile > 30 (rank-3 ⟹ ≥log₂n ⟹ quasipoly)**, **iterated
  refinement = 4**, and — decisive — **joint σ-form-value profile injective at base 4 ≤ d+1 (POLY)**. Also derives the
  poly object: a **5-dim family of σ-twisted forms** whose joint zero = cone exactly ⟹ Suzuki = **multi-(σ)-form
  adapter** (σ-twisted sibling of alternating/half-spin). §6 "Suzuki".
- **`route_c_bootstrap_probe.py` — the meta-poly bootstrapping crux (§7a).** Confirms the isotropic-line geometry through
  `o` is recoverable from **adjacency alone** (no `Aut`): the local invariant `|N(o)∩N(x)∩N(y)|` **perfectly separates**
  collinear from non-collinear isotropic triangles (all VO^± `d=4,6` `q=3,5`), and the recovered lines' directions **span
  `V`**. This is the Aut-free enabling primitive that de-circularizes F1's coordinatization.
- **Supporting (from the direct route, still relevant):** `model_gap.py` (the isoClass scheme + orbit/refinement
  helpers), `factorization_probe.py`/`flag_stall_probe.py` (the node-4 stall evidence that motivates Route C).

---

## 6. The build plan

### Foundation (must exist before the family builds)

| # | piece | side | status / notes |
|---|---|---|---|
| **F1** | **Additive/affine recovery** — `T = O_p(Aut)` (the socle), a basis → coordinates, any vertex → origin | C#+Lean | **✅ CONFIRMED + PRODUCTIONIZED (2026-07-03).** Confirmed against the REAL harness (`RouteCF1Probe.cs`): recovers `T` exactly (ground-truth), regular + elementary-abelian, coordinatizes the cone (`vanishDim=1`) — VO^ε₄(q), q=2,3,5, both types; char-agnostic (full `Aut` delivered). **Production code landed:** general group ops on `PermutationGroup.cs` (`RegularNormalPSubgroup(p)`, `NormalClosure`, `Elements`, `HasExponentDividing`, `Perm.Order`/`Pow`) + `AffineStructureRecovery.Recover` (coordinatization); the probe now exercises the production path (all pass; 26 existing `PermutationGroup` tests green). "`soc = O_p = T`" = the affine-primitive **socle theorem** (cite). Remaining: the Lean side (F4 iso-invariance) + `q=pᵉ` (F2). |
| **F2** | **𝔽_q-scalar recovery** (q=pᵉ) — recover the field/Frobenius structure (the ΓL/semilinear seam) | C#+Lean | **◑ SEMILINEAR CORE LANDED (2026-07-03, axiom-clean, `ScratchRouteC.lean` §F2):** `recoveredForm_colouring_equivariant_semilinear` — a graph iso over 𝔽_q is 𝔽_p-**semilinear** (`g = M∘σ̂`), so the recovered form transports up to scalar **and** field auto σ: `Q'(gu−gt)=μ·σ(Q(u−t))`. Bricks `frobVec`/`frobVec_sub`/`semisimilitude_colouring_equivariant` (provable) + cited `ConePreservingCollineationIsSemiSimilitude` (fundamental thm of proj. geometry, carried). The `q=p` case = the `σ=id` specialization. **𝔽_q-structure RECOVERY** (getting the field) is subsumed by geometric coordinatization (§7a/R1: Buekenhout–Shult recovers PG over 𝔽_q). Remaining: C# field recovery (with R1) |
| **F3** | **`IFormStructure` interface + generic engine** (refine-by-φ, canonical base, discretize) | C#+Lean | **◑ LEAN INTERFACE LANDED (2026-07-03, axiom-clean, `ScratchRouteC.lean`):** `FormAdapter` (bundles `G₀` + `−1∈G₀` + a bounded base + the `separates` certificate) + `FormAdapter.reachesRigidOrCameron` (the shared engine theorem: any adapter ⟹ the seal, family-agnostic) + `affinePolarAdapter` (instance 1, validates non-vacuity, reproduces `viaOrthogonalForm`). Each family now = **one `FormAdapter`** (supply only `separates`). C# side (thin merge point) still to build |
| **F4** | **Iso-invariance of the recovered `φ`** — the `forcedNode_relabel` analog: `RecoverForm` is relabeling-equivariant up to scalar | Lean | **✅ EQUIVARIANCE CORE LANDED (2026-07-03, axiom-clean, `ScratchRouteC.lean`):** `recoveredForm_colouring_equivariant` (+ bricks `similitude_colouring_equivariant`/`similitude_conePreserving`). Rests only on `NondegQuadricDeterminesForm` — **discharged as an exact scoped citation** (= A1's finite-geometry uniqueness; F4 and A1-Lean unify). Not vacuous (scoped `p≠2`/`d≥4`, exactly the true range) |
| **F5** | **Generic seal→poly spine** — `RecoverForm ⟹ refined scheme ⟹ discrete_affineScheme_of_jointSeparates ⟹ viaSpielman` | Lean | **downstream all landed & generic**; only the A3 refinement bridge is new |

### Instance 1 — affine-polar `VO^ε` (proves the whole spine)

| # | piece | status |
|---|---|---|
| **A1** | `RecoverForm` = solve the degree-2 vanishing system on the cone | **✅ CONFIRMED + PRODUCTIONIZED (2026-07-03, `QuadraticFormRecovery.RecoverForm`):** recovers `Q` up to scalar by one kernel solve on F1's coordinates; the recovered `Q` + coords **reconstruct the entire graph** (`Q(coords[x]−coords[y])=0 ⟺ x~y`, **0 mismatches**, VO^±₄(3)). Odd-q (returns null in char-2). Lean side = a finite-geometry nondegeneracy lemma (`⟨Q⟩` = the vanishing space) |
| **A2** | `Separates` = `coords_determine` / `spanning_sameExactGram_determines` | **LANDED, axiom-clean** |
| **A2⁺** | the spanning back-half — `RouteC.coords_determine_spanning` + `RouteC.reachesRigidOrCameron_viaOrthogonalForm_spanning` (isometry scheme discretizes at any iso-invariantly-chosen spanning base) | **✅ LANDED 2026-07-03, axiom-clean** (`ScratchRouteC.lean`, NOT in `build.sh`) |
| **A3** | **the refinement bridge** — recovered `Q` upgrades the similitude graph to the isometry scheme, which `viaOrthogonalForm_spanning` discretizes | **◑ brick 1 LANDED (2026-07-03, axiom-clean, `ScratchRouteC.lean`):** `isometryScheme_refines_similitudeScheme` — `O(Q)≤GO(Q)` ⟹ the isometry scheme (exact-`Q` relations) refines the given similitude graph (isotropy-only). The consistency half. Remaining A3 content = the discreteness-transfer, now discharged by **F4** (`recoveredForm_colouring_equivariant`, ✅ landed 2026-07-03) — the iso-invariance that makes "discrete ⟹ canonical" |
| **A4** | `AutGens` = `GO(Q)` generators (reflections) → existing `PermutationGroup` (only for the \|Aut\| side) | Schreier–Sims exists; generator list is standard classical-group data |

Instance 1 forces F1/F3/F4/F5 into existence, so it is **most of the total work**; the other three families then
reduce to writing their `IFormStructure` implementation.

### Instances 2–4 — reuse the engine, write only the adapter (plan §11.4/§11.5)
**The Lean interface `FormAdapter` (F3) is now LANDED** — each family reduces to **one `FormAdapter` instance**, i.e.
supplying its `G₀`, base, and `separates` certificate; `FormAdapter.reachesRigidOrCameron` then seals it for free.
The genuine per-family content is exactly `separates` (+ identifying `G₀`):
- **Alternating (d) — SCOPED + build STARTED (2026-07-03).** `Alt(n,q)`: vertices `Λ²(𝔽_q^n)` (alternating
  matrices), adjacency `rank(A−B)=2`. **Two regimes:**
  - **`n=4` is affine-polar in disguise:** `Λ²(𝔽_q^4)≅𝔽_q^6`, `rank<4 ⟺ Pf=0`, and the Pfaffian `Pf=A₁₂A₃₄−A₁₃A₂₄
    +A₁₄A₂₃` is a single **nondegenerate quadratic form** ⟹ `Alt(4,q)=VO⁺₆(q)`, already covered by `affinePolarAdapter`
    (`Q:=Pf`). **Not a new family.** (Buildable now: define `Pf`, prove nondeg, instantiate — deferred, low value.)
  - **`n≥5` is the genuinely-new family — MULTI-QUADRIC:** `rank≤2` is cut out by the **Plücker quadrics** (4×4
    sub-Pfaffians; 5 for `n=5`), so the connection set is their **joint cone** (Grassmann `G(2,n)`). Each Plücker form
    is individually degenerate; only *jointly* do their polar forms separate. **✅ `Alt(5,q)` FULLY SEALED
    (2026-07-03, axiom-clean, `ScratchRouteC.lean §Plucker`):** the concrete 5 sub-Pfaffians `Pf₀..Pf₄` on `𝔽_p^10`
    (built via `linMulLin`), their joint nondegeneracy `plucker_hjoint` (`Pf₀` isolates coords `4..9`, `Pf₁` isolates
    `1,2,3`, `Pf₂` isolates `0`), assembled by `multiFormAdapter` into `alternatingAdapter`, sealed by the capstone
    **`reachesRigidOrCameron_alternating`** — the first concrete **non-quadratic (multi-form)** Route-C family, end to
    end. (Honest scope: the seal is for `affineScheme(⨅ₖ O(Pf_k))`; that this scheme *is* `Alt(5,q)` is the modeling
    claim, same status as `affinePolarAdapter` modeling `VO^ε`.) The rank-3 alternating forms graph is exactly
    `Alt(4,q)` [=affine-polar] + `Alt(5,q)` [sealed], so **instance 2 (alternating) is DONE — now at full
    instance-1 parity** (all three legs: seal + brick-1-multi `alternating_refines_coneScheme` +
    F4-multi `recoveredFamily_colouring_equivariant`, the last resting on the carried `JointVarietyDeterminesFamily`).
    *Was Medium — landed.*
- **Half-spin (e) — SCOPED + reduction LANDED + ✅ SPINOR QUADRICS DE-RISKED & VALIDATED (2026-07-03).** The
  **D₅ half-spin** action: `Spin₁₀(q)` on the 16-dim half-spin module `𝔽_q^16`, rank 3. Connection set = the
  **pure-spinor cone** (spinor variety `S₅ ⊂ P^15`), cut out by **10 quadratic equations** (the D₅ vector rep = the
  Berkovits SO(10) pure-spinor constraint `λΓ^aλ=0`). Another MULTI-QUADRIC family — reuses `multiFormAdapter` +
  `coords_determine_multi` + the just-landed generic bridges (**no new engine, no new bridges**). `halfSpin_reduction`
  (axiom-clean, `§HalfSpin`) commits the dimensions and reduces to: supply the 10 spinor quadrics `Qs` + `hjoint`.
  **✅ DE-RISKING PASS DONE — the 10 equations are FOUND, EXPLICIT, and VALIDATED (`route_c_halfspin_probe.py`).**
  Method: generate genuine pure spinors by the char-free big-cell Pfaffian formula (`ω(b)_∅=1`, `ω(b)_{ij}=b_{ij}`,
  `ω(b)_{ijkl}=Pf(b|_{ijkl})`) and empirically fit the degree-2 vanishing ideal (bulletproof — the naive moment map
  `(ω∧Γ^aω)_top` gave WRONG forms, caught by the probe). **Validation (all pass):** dim of vanishing ideal `= 10`
  exactly (q=3,5,7,11); **EXACT 𝔽₂ point count of the joint zero locus `= 2296 = 1+(q−1)∏₁⁴(qⁱ+1)`** (the forms cut
  *precisely* the spinor cone, nothing bigger); 𝔽₃ Monte-Carlo count matches target (z=0.10); **joint polar radical
  `= 0` (the Lean `hjoint`)**, and it holds already from just the 5 "quadruple" forms — so `hjoint` is provable by the
  `plucker_hjoint` coordinate-isolation pattern (each `Q_a` isolates ∅, its own quadruple, and 6 pairs). **The 10
  forms, in port-ready `Fin 16` indexing** (`0:∅`; pairs `1:12 2:13 3:23 4:14 5:24 6:34 7:15 8:25 9:35 10:45`;
  quadruples `11:1234 12:1235 13:1245 14:1345 15:2345`), each a 4-term `linMulLin` sum like the Plücker `Pf`:
  - **quadruple forms** (`x_∅·x_{ijkl} = Pf`): `Q₀=-x₀x₁₁+x₁x₆-x₂x₅+x₃x₄`, `Q₁=-x₀x₁₂+x₁x₉-x₂x₈+x₃x₇`,
    `Q₂=-x₀x₁₃+x₁x₁₀-x₄x₈+x₅x₇`, `Q₃=-x₀x₁₄+x₂x₁₀-x₄x₉+x₆x₇`, `Q₄=-x₀x₁₅+x₃x₁₀-x₅x₉+x₆x₈`  ← these 5 give `hjoint`.
  - **pair×quadruple forms**: `Q₅=-x₁x₁₄+x₂x₁₃-x₄x₁₂+x₇x₁₁`, `Q₆=-x₁x₁₅+x₃x₁₃-x₅x₁₂+x₈x₁₁`,
    `Q₇=-x₂x₁₅+x₃x₁₄-x₆x₁₂+x₉x₁₁`, `Q₈=-x₄x₁₅+x₅x₁₄-x₆x₁₃+x₁₀x₁₁`, `Q₉=-x₇x₁₅+x₈x₁₄-x₉x₁₃+x₁₀x₁₂`  ← needed to model
    the graph (cone = joint zero of all 10), not for `hjoint`.
  **✅ PORTED & SEALED (2026-07-03, axiom-clean, `ScratchRouteC.lean §HalfSpin`):** the 10 forms `S0..S9` transcribed
  via `linMulLin`+`LinearMap.proj`; polars `S0_polar..S4_polar`; `spinor_hjoint` proved from `S0..S4` by the
  `plucker_hjoint` coordinate-isolation pattern; assembled by `multiFormAdapter` into `spinAdapter`, sealed by
  `reachesRigidOrCameron_halfSpin`; brick-1 `halfSpin_refines_coneScheme` (F4 generic). **Instance 3 DONE, full
  instance-1 parity.** *Was Medium–high — de-risked then landed.*
- **Suzuki–Tits (f) — SCOPED (2026-07-03). The outlier, but much cleaner under Route C than the old pair-route
  framing.** `VSz(q)` = the Cayley graph on `GF(q)^4` (`q=2^{2e+1}`), connection set = the cone over the **Tits ovoid**
  `O={(1,a,b,ab+a^{σ+2}+b^σ)}∪{(0,0,0,1)}`, `σ` = the Tits endomorphism (`σ²=Frob`; `q=8⟹σ(x)=x⁴`); small-Aut
  (`Sz(q)⊂Aut`, `|Aut|~q⁴`), **cospectral with `VO⁻₄(q)`** (separated only by `Sz(q)`).
  - **Route-C shape: a PLAIN `FormAdapter`, NOT a `multiFormAdapter`** (there is no quadratic-form family; the ovoid
    polynomial is σ-twisted, non-quadratic). `G₀` = the ovoid-cone stabilizer linear group (`⊇ Sz(q)`), viewed over
    `𝔽₂` after restricting scalars from `GF(q)` (module `Fin d → ZMod 2`, `d=4(2e+1)`). `base` = an `O(1)` base (an
    old probe shatters at base 9 ≪ √4096). `separates` = the **only** bespoke content.
  - **★ THE BIG WIN — Route C sidesteps Suzuki's worst risk.** The old plan's Handle 2 (σ-twisted exponential-sum
    *count*, "the highest analytic risk of any family", Weil/Deligne territory — formsgraph-plan §11.4) is a
    WL-refinement/counting artefact. Route C never counts; it only needs **discreteness at a bounded base** =
    **Handle 1** (direct geometric individualization on the explicit Tits coordinates: individualize `O(1)` reference
    vertices, read off σ-twisted incidences ⟹ pin `(a,b,c)` combinatorially). So the Weil risk is OFF THE TABLE, and
    no char-2 `χ`/Gauss/Arf substrate is needed for the ENGINE (that was a pair-route requirement).
  - **✅ VERIFIED — the shared engine is char-2-ready (Lean-checked 2026-07-03).** `FormAdapter.reachesRigidOrCameron`
    elaborates and seals at `p=2`, and **`neg_mem` is FREE** in char 2 (`LinearEquiv.neg (ZMod 2)` *is* the identity,
    so it lies in any `G₀`). So the entire engine + seal wiring + F1 translation-recovery are shared/free; **`separates`
    is the sole bespoke piece.**
  - **Discharging `separates` (= the ovoid-stabilizer discretizes at a bounded base):** neither `Sz(q)` nor the Tits
    ovoid nor `σ` (`σ²=Frob` over `GF(2^{2e+1})`) is in Mathlib, so a full proof is a major standalone build.
    **Recommended = carry it as a scoped citation** `SuzukiOvoidStabilizerSeparatesAtBase` (the geometric
    individualization / `Sz(q)` 2-transitivity + short stabilizer chain), same discipline as
    `NondegQuadricDeterminesForm` — but a *bigger* carry (the other families PROVE `separates`; only Suzuki cites it),
    reflecting the outlier status. Fixed-`q` `decide` is infeasible (`n=4096`, `native_decide` banned).
  - **✅ DE-RISK PROBE DONE (2026-07-04, `route_c_suzuki_probe.py`, q=8) — object validated + a design-changing
    finding.** (i) **Object EXACTLY validated:** `σ²=Frob`; `|O|=q²+1=65`; `|cone|=(q²+1)(q−1)=455`; VSz(8) =
    **SRG(4096,455,6,56)** — the ovoid formula `c = a·b + σ(a)·a² + σ(b)` is correct (the connection set the Lean
    adapter models). (ii) **★ Poly-vs-quasipoly finding:** VSz is a **rank-3 SRG** (1-WL stable at 1 colour;
    per-base-point relation is only 2-valued). So Route C's **direct** orbit-profile `separates`
    (`discrete_affineScheme_of_jointSeparates`) on the **plain cone scheme** needs a base `≥ log₂n = 12` (probe: greedy
    `> 30`, never injective) ⟹ **only QUASIPOLY = no improvement over the banked floor.** Iterated
    individualization+1-WL discretizes at base **4** (the `Sz(q)` 2-transitivity mechanism), but that is *not* the
    direct-profile the engine uses.
  - **✅ POLY PATH CONFIRMED (2026-07-04 follow-up) — Suzuki is a MULTI-(σ)-FORM adapter, the σ-twisted sibling of
    alternating/half-spin.** No *single* σ-twisted form cuts the cone (the derived `F = x₃x₀^{σ+1}+x₁x₂x₀^σ+x₁^{σ+2}+
    x₂^σx₀²` over-vanishes: `|{F=0}|=512≠456`; the Tits ovoid isn't that hypersurface). **BUT** a **5-dim family
    `{F_k}` of σ-twisted type-(1,2) forms** (`σ(xₐ)·x_b·x_c`) has **joint zero locus = cone EXACTLY (456)** — probe
    `route_c_suzuki_probe.py`. And the **joint `F_k`-value profile separates at base 4 ≤ d+1** (injective over all 4096
    at the frame) ⟹ **POLY**, exactly the `coords_determine_multi` mechanism. (Plain cone scheme stays quasipoly.) The
    5 forms have **all-unit coefficients** (`F₀` = the derived `F`; `F₁..F₄` trim the spurious zeros) — clean,
    representation-independent support, ready to transcribe.
  - **⟹ Lean design (the σ-twisted analog of the multi-quadric adapter):** `σ` (a Frobenius power over `GF(q)`) + the
    5 σ-twisted forms `F_k` + a **σ-twisted `coords_determine_multi`** (`separates` via the joint `F_k`-value profile —
    the genuine bespoke content; prove or carry scoped) + `G₀ = ⨅ₖ {g : F_k∘g = F_k}`. **NOT the quadratic
    `multiFormAdapter`** (the `F_k` are σ-twisted, not quadratic — over the `𝔽₂` linearization they are cubic), so it
    needs a σ-twisted *sibling* of `coords_determine_multi`; but the generic `FormAdapter` engine + `neg_mem` + seal are
    shared/free (char-2-ready, verified). Then `suzukiAdapter` → `reachesRigidOrCameron_suzuki`.
  - **✅ REDERIVATION LANDED (2026-07-04, axiom-clean, `ScratchRouteC.lean §Suzuki`):** over an abstract char-2
    `CommRing K` with a Tits endomorphism `σ` (`σ∘σ = (·)²`), the 5 σ-twisted forms `SF0..SF4` + the `ovoidC`
    parametrization are defined, and each is **proven to cut the cone**: `suzukiForms_ovoid` (vanish on the affine
    ovoid `(1,a,b,ovoidC a b)` — via `σ` a ring hom + `σ∘σ=(·)²`, char-2 cancellation), `suzukiForms_infty` (vanish
    at `(0,0,0,1)`), `suzukiForms_homog` (σ-twisted homogeneous `SF_k(λx)=σλ·λ²·SF_k(x)`, so `{SF_k=0}` is a cone).
    `SF0` = the single derived form; `SF1..SF4` trim its spurious zeros. Representation-independent (all-unit coeffs).
  - **Remaining (next):** the σ-twisted **`coords_determine_multi`** (`separates` — the joint-value determiner) + the
    `GF(q)^4 ↔ 𝔽₂^d` module bridge to the char-2-ready engine → `suzukiAdapter` → `reachesRigidOrCameron_suzuki`.
  *Single family, no Weil, no char-2 χ-substrate, no engine work. Forms rederived + proven to model the connection
  set; a multi-σ-form adapter with a confirmed O(d) poly base — genuinely "the same shape" as alternating/half-spin.*

### C# / Lean split, and the reuse to exploit
- **The C# engine is the symmetric mirror of Option 2's Layer D** (IR doc §11.10, built through D-M4 as a Phase-2
  pre-processor: recover structure → refine/solve → plug the existing seam). **Clone that architecture**, swapping
  `IFormStructure` for the F₂ extractor. This is the payoff of the recovery↔co-recovery duality
  ([[project_recovery_corecovery_duality_2026-07-03]]): the two pre-processors share a skeleton.
- **Lean deliverable is the poly-supporting structural object**, not a runtime proof: "the recovered-form-refined
  scheme discretizes at an iso-invariantly-constructible `O(d)` base" (F5 + A3), with "poly" the meta-claim over that
  bounded base + the existing Schreier–Sims meta-cost (same discipline as Part A's `Order = ∏ orbit sizes`).

### Sequencing & risks (updated 2026-07-03)
1. ✅ **F1 + A1** (C# recovery front) — DONE + confirmed against the real harness (`AffineStructureRecovery`,
   `QuadraticFormRecovery`, `RouteCF1Probe.cs`).
2. ✅ **A2⁺ + A3 brick 1** (Lean spine from landed pieces) — DONE, axiom-clean (`ScratchRouteC.lean`).
3. ✅ **F4** equivariance core — **LANDED 2026-07-03, axiom-clean** (`recoveredForm_colouring_equivariant` + bricks).
   Rests only on `NondegQuadricDeterminesForm` — now DISCHARGED as an exact scoped citation (§ STATUS remaining).
4. ✅ **Meta-poly bootstrapping** — ASSESSED + RESOLVED (§7a): Route C is poly, non-circular (global coordinatization ≠
   bounded WL; Aut-free geometric recovery, probe-confirmed enabling primitive). Residuals R1–R3 deferred to the rigorous
   C#→Lean runtime stage (build the geometric coordinatizer; name Buekenhout–Shult; double-check `d=4`).
5. ◑ **F2** (`q=pᵉ` semilinear seam) — **Lean core LANDED** (`…_semilinear`, axiom-clean): the recovered form is
   iso-invariant up to scalar **and** Frobenius σ. Remaining: the C# field-recovery side (folds into R1's geometric
   coordinatizer — Buekenhout–Shult recovers PG over 𝔽_q, field included).
6. ◑ **Instances 2→3→4** — F3 interface LANDED; **instance 1 (affine-polar) + instance 2 (alternating `Alt(5,q)`)
   both SEALED axiom-clean; instance 3 (half-spin) SCOPED + reduction landed (`halfSpin_reduction`)** — a multi-quadric
   family, reuses the engine; remaining = the 10 D₅ spinor quadrics + `hjoint`. Then Suzuki (f, char-2 last).

**Definition of done (Route C, affine-polar):** F1 recovers coordinates iso-invariantly (F4 ✅ equivariance core); A1
recovers `Q` (C# ✅; Lean uniqueness = the carried `NondegQuadricDeterminesForm`); A3 refines to the isometry scheme (brick 1
✅); `viaOrthogonalForm_spanning` discretizes at the `O(d)` base and seals via `viaSpielman` (✅) — the structural
bounded-base discreteness object complete, "poly" the meta-claim over it **modulo the bootstrapping question**. The C#
engine reproduces `|Aut|` via `PermutationGroup`. **The Lean spine is now assembled;** the open items are the classical
carry + the meta-poly bootstrapping.

### 6a. F4 — iso-invariance of the recovered form (✅ LANDED 2026-07-03; kept as the design record)

**What F4 is.** The recovered `Q` (and hence F1's coordinates and the isometry-scheme colouring) must be a *canonical
function of the graph*: a graph isomorphism `σ` must carry the recovered structure of `G` to the recovered structure of
`σ(G)` (up to the scalar ambiguity of `Q`). Concretely, the connection set (cone) is carried to the connection set, so
the degree-2 form vanishing on it is carried to a scalar multiple — the recovered-`Q` difference colouring is
relabeling-**equivariant**. This is what makes "canonicalize via the recovered form" produce a *canonical* labelling
(the same up to iso), i.e. it is the iso-invariance the poly canonicalization claim needs.

**Why it's the last load-bearing piece.** The spine (recover → isometry scheme → discretize) is assembled: brick 1 says
the isometry scheme refines the given graph; `viaOrthogonalForm_spanning` says it discretizes. What is *not* yet Lean-
certified is that the isometry scheme used is derived *iso-invariantly* from the given graph — without which "discrete"
does not give "canonical". F4 supplies exactly that. (Discreteness does not transfer down to the similitude scheme — the
node-4 stall — so F4 is genuinely needed; it is not implied by the banked seal.)

**The template to mirror (landed).** The symmetry-phase iso-invariant-node machinery in `Cascade.lean`:
`forcedNode` (`:2752`), `forcedNode_image` (`:2830`, image under an automorphism), `movedSet_relabel` (`:3004`),
`forcedNode_relabel` (`:3024`, equivariance under an arbitrary relabelling). F4 is the *form-recovery* analog:
`recoveredForm(σ • G) = σ • recoveredForm(G)` (up to scalar). State it against the abstract-graph relabelling the same
way `forcedNode_relabel` does.

**Risk — the vacuity trap (cf. `SchemeReproduced`, memory `project_...`).** Make the equivariant predicate strong enough
to be *useful* (it must actually pin the colouring iso-invariantly) yet true (holds for the real recovery). Check
non-vacuity against the C# ground truth (`RouteCF1Probe.cs` already exhibits the recovered `Q` reconstructing the graph —
the semantic content F4 formalizes).

**How it composes (the end state).** F4 (equivariant recovery) + brick 1 (isometry refines the graph) +
`viaOrthogonalForm_spanning` (isometry discretizes at a spanning base) ⟹ the graph has an iso-invariant discrete
colouring at an `O(d)` base ⟹ (meta) poly canonical labelling. That is the Route-C deliverable for affine-polar.

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

## 7a. The meta-poly bootstrapping — assessment & resolution (2026-07-03)

**The concern.** Route C's poly claim runs: recover coordinates (F1) → recover `Q` (A1, one linear solve) → `Aut = AΓO(Q)`
known → canonicalize. A1 and canonicalization are clearly poly *given coordinates*. But **F1 as built/documented
recovers coordinates from `T = O_p(Aut)` — it consumes `Aut`** (`AffineStructureRecovery.Recover(PermutationGroup aut,…)`;
the socle theorem gives `O_p(Aut)=T` *given* `Aut`, not `Aut` itself). Poly-time computation of `Aut` for this SRG
residue is *itself* the open T0 problem Route C advertises it sidesteps (recovery §7 "does not depend on the open core").
So the meta-poly *first step* is potentially circular. This must be resolved before the cost analysis, not after.

**Resolution — three findings, verdict: sound (not circular, not the node-4 wall in disguise).**

1. **Global computation ≠ bounded-round WL — the distinction that keeps Route C alive.** The node-4 wall is specifically
   that *bounded-round WL refinement* stalls (cannot recover `gramK` at a bounded base — recovery §9.8.9). Coordinatization
   is a **global** computation (all `n` vertices, linear algebra / geometry recovery), a strictly stronger model in which
   poly is reachable even when bounded-WL-dimension is unbounded (this is the whole individualization-beats-WL premise).
   So recovering coordinates is **not** the node-4 wall re-encountered — provided a concrete *global, Aut-free* procedure
   exists. It does (finding 2).

2. **`T = O_p(Aut)` was only a de-risking shortcut; the poly pipeline uses Aut-free GEOMETRIC coordinatization.** The graph
   is the collinearity graph of the affine polar space. Recover the classical geometry (isotropic points/lines) from the
   graph and read off coordinates by the **fundamental theorem of projective geometry / Buekenhout–Shult** (a polar space
   of rank ≥ 3 is classical ⟹ embeds in `PG(d,q)` ⟹ coordinates up to `PΓO`), then lift to affine — poly and **needing no
   `Aut`**. The `O_p(Aut)` route was a valid *shortcut for the de-risking probes* (which had `Aut` from the harness), not
   the poly argument. Rank ≥ 3 means **`d ≥ 6`; `d = 4` (Witt index 2) is the generalized-quadrangle special case** (outside
   Buekenhout–Shult's rank≥3 hypothesis — flagged for the rigorous stage, but the enabling primitive holds there too,
   finding 3).

3. **The enabling primitive is confirmed Aut-free — probe `route_c_bootstrap_probe.py` (2026-07-03).** The local graph
   invariant `|N(o) ∩ N(x) ∩ N(y)|` (common cone-neighbours of an isotropic triangle) **perfectly separates collinear from
   non-collinear** triangles — a clean gap in *every* case (VO^±, `d=4,6`, `q=3,5`: e.g. VO⁺₄(5) collinear=42 vs non=22;
   VO⁻₆(3) 60 vs 6). Reconstructing the isotropic lines through `o` from that invariant alone (no `Aut`, no ground truth)
   recovers exactly the punctured lines (`q−1` points each), and **their directions span `V`** uniformly. So the geometry
   is poly-recoverable from adjacency — the step that turns "recover coordinates" from circular into a standard geometry
   problem. (`d = 4` included: the primitive separates and spans there too, evidence the GQ case also goes through.)

**Verdict.** The bootstrapping is **resolved at the meta level: Route C is genuinely poly, non-circular.** The poly first
step is *geometric coordinatization* (global, Aut-free, probe-confirmed enabling primitive + Buekenhout–Shult for the
coordinate read-off), **not** `O_p(Aut)`. Route C sidesteps the *WL-refinement* crux and does **not** inherit it in
disguise (global ≠ bounded-WL).

**Residuals for the later rigorous (C#→Lean runtime) stage — record, don't block:**
- **(R1) Build the Aut-free geometric coordinatizer** to replace/supplement `AffineStructureRecovery.Recover`'s
  `O_p(Aut)` path (which is fine for de-risking but is the circular step for the poly claim). The enabling primitive
  (line recovery) is confirmed; the remaining engineering is line-geometry → frame → coordinates (the group-law/embedding).
- **(R2) Name + verify the geometry-recovery citation** (Buekenhout–Shult / recovering a polar space from its point graph)
  and its poly bound — the citation the poly claim now rests on (analogous to how the seal rests on G3).
- **(R3) Double-check `d = 4` (GQ, rank 2)** — outside the rank≥3 embedding theorem; the probe supports it, but the
  coordinate read-off needs its own (standard) argument for generalized quadrangles.

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

## 9. After the four seals — the combined correctness object + the C# runtime (FORWARD PLAN, build later)

**Status when this section applies:** the four per-family adapters are sealed (affine-polar ✅, alternating ✅,
half-spin ✅; Suzuki = the last). Each gives `reachesRigidOrCameron (affineScheme A.G₀)` for a *concrete* group
`A.G₀` built from recovered forms. This section records how those four combine into ONE correctness object, and
how the C# canonizer gets the family handlers it currently lacks. **Neither is built yet; this is the roadmap.**

### 9.0 The key structural fact that keeps it clean (read first)

Route C's `FormAdapter.reachesRigidOrCameron` is **threshold-free**: it is `viaSpielman ∘
discrete_affineScheme_of_jointSeparates`, needing only *nondegeneracy* + *a bounded base* — **no `q ≥ 256` /
`q ≳ 32d` floor** (those were the pair-route/quasipoly seal's Gauss-sum thresholds, which Route C does not touch),
and the `hjoint` lemmas (`plucker_hjoint`, `spinor_hjoint`) are proved for **all primes `p`** (coordinate
isolation, ±1 coeffs, no division — not even `p≠2`). Consequence: **the small-`q`/small-`d`/sporadic cases do NOT
pile up as Route-C exceptions.** Route C only ever engages the *unbounded-WL-dimension* residue (the infinite
families); any finite/sporadic small graph has bounded `|V|` ⟹ bounded base ⟹ it is already sealed by the
*generic* bounded-base machinery (`viaSpielman` on a trivial base) and never reaches the forms-graph residue. So
the combined object carries **no finite exception pile** — the only systematic split is **char 2** (→ the
Suzuki / Arf branch, one branch, not scattered exceptions). This is why "4 seals + finitely many exceptions"
collapses to "1 classification citation + 1 iso-invariance lemma".

### 9.1 The Lean correctness object — one dispatch theorem over one cited premise

Target shape (the clean "reaches rigid or Cameron via Route C"):
```
theorem reachesRigidOrCameron_formsGraphResidue
    (hclass : FormsGraphResidueClassification)      -- the ONE cited premise that combines the 4
    (X) (hX : «X = the unbounded-WL rank-3 primitive schurian affine residue») :
    reachesRigidOrCameron X := by
  rcases hclass X hX with ⟨Q, hiso⟩ | ⟨Qs, hiso⟩ | ⟨Qs, hiso⟩ | ⟨ov, hiso⟩   -- affine-polar / alt / half-spin / Suzuki
  -- each case: transport the matching adapter's concrete seal along hiso
```
Beyond the four adapters this needs exactly two things:

- **(L1) Scheme-level iso-invariance of `reachesRigidOrCameron`** — `X ≅ Y → (reachesRigidOrCameron X ↔
  reachesRigidOrCameron Y)`, so each adapter's *concrete* `affineScheme(G₀)` seal transports onto the abstract
  `X`. **This is the one genuinely load-bearing NEW lemma.** Requires each disjunct (`SchemeBlockRecovered`,
  `AbelianConsumed`, `SchemeRecoveredByDepth`, `IsCameronScheme`) to be iso-invariant. *NB: distinct from F4 —
  F4 is iso-invariance of the recovered form (for the runtime canonicalization); L1 is iso-invariance of the
  seal predicate (for the correctness statement). Both needed, different halves.* **De-risk first:** spot-check
  whether the four disjuncts are already iso-invariant before committing (cheap, and it validates the whole plan).
- **(L2) The dispatch theorem** above, gated on **(L3) `FormsGraphResidueClassification`** = the cited premise
  (Skresanov's rank-3 2-closure classification: the unbounded-WL rank-3 primitive schurian affine residue is
  *exactly* affine-polar / alternating / half-spin / Suzuki, and it *hands over the concrete structure*
  `Q`/`Qs`/ovoid so the adapter can be built). Carried like `Theorem41Statement`/`G3` — **one named premise, not
  a finite pile**. This premise IS the "combination".
- **(L4) Wire into the existing residue seam** `reachesRigidOrCameron_viaAffineFormScheme` (idx 1207, the node-4
  hook), retiring its quasipoly `hFormCert` in favour of this poly seal.

Sizing: L1 medium (the real work), L2 small once L1 exists, L3 a citation/scoping task, L4 small–medium.

### 9.2 The C# runtime — the family handlers the canonizer currently lacks

The harness (`ChainDescent.cs`) has **none** of the Route-C family handlers wired. Built so far: F1
(`AffineStructureRecovery`) + A1 (`QuadraticFormRecovery`, quadratic only), confirmed vs the real harness
(`RouteCF1Probe.cs`); the Lean `FormAdapter` interface exists but has **no C# engine**. Remaining:

- **(C1) `RecoverForm` for the multi-quadric families** (Plücker, spinor) + Suzuki — generalize
  `QuadraticFormRecovery` from a single quadratic to a form *family* (solve the degree-2 vanishing system on the
  cone → the span of quadrics; §2b). The quadratic case is the `ι = Unit` instance already built.
- **(C2) The dispatch** — from an abstract rank-3 SRG residue, detect *which* family it is (SRG parameters /
  cone-geometry signature) and select the adapter. This is the C# analog of L3's classification.
- **(C3) Wire recovered-`Aut` canonicalization into the harness** at the residue seam (`ChainDescent.cs`
  `target == −1`, near `CoveredByPathFixingAut ~:589`): once the form is recovered, `Aut = AΓO(Q)` is known →
  hand its generators to the existing `PermutationGroup` Schreier–Sims for the canonical labelling.
- **(C4) F2 field recovery / the Aut-free geometric coordinatizer** (= §7a R1) for `q = pᵉ` — Buekenhout–Shult
  recovers `PG(d,q)` including the field; also de-circularizes F1 (replaces the `O_p(Aut)` shortcut). Delivers
  both F2's field side and the non-circular poly first step in one build.

C1–C4 are independent of the Lean seal (L1–L4) and can proceed in parallel. The C# engine is the **symmetric
mirror of Option 2's Layer D** (§6 / [[project_recovery_corecovery_duality_2026-07-03]]) — clone that
architecture, swapping `IFormStructure` for the F₂ extractor.

### 9.3 Later — the meta-poly rigor stage

The §7a residuals R1–R3 (build the geometric coordinatizer, name Buekenhout–Shult + its poly bound, double-check
`d=4` GQ) and, at the far end, the C#-design-into-Lean runtime model that makes "poly" (nearly) rigorous rather
than a meta-argument. This is the project's planned final stage; nothing above blocks on it.

### 9.4 Suggested ordering
1. Finish Suzuki (all four sealed).
2. **L1 spot-check** (are the four `reachesRigidOrCameron` disjuncts iso-invariant?) — cheap, de-risks the whole
   combination; do before L2.
3. L1 → L2/L3 → L4 (the clean Lean object), in parallel with C1–C3 (the runtime).
4. C4 + the R1–R3 / meta-poly rigor stage last.

---

## 8. Pointers  <!-- (kept below §9 for git-history stability; §9 is the forward plan) -->
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
(they drift — verify before citing); this doc is the Route-C staging point, the recovery doc §9.8.9 is the reason it exists.
§9 = the forward plan for combining the four seals (Lean L1–L4) + wiring the C# runtime (C1–C4), to build after Suzuki.*
