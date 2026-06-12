# Chain descent — the GENERAL-CC SEPARABILITY build (the unconditional seal's last piece)

> **This document is the exclusive, durable home for the one remaining piece of the unconditional seal: the
> general coherent-configuration (CC) separability theory.** It is aimed to be self-contained — a fresh reader
> should need nothing else to begin or continue, however still seek it out if something else is needed.
> Everything the build consumes, the math it formalises, the plan, the ruled-out routes, and the running log 
> live here. Cross-references to other docs are for provenance or if more clarification is needed than provided
> in here.

---

## STATUS (read first)

- **Goal of the whole project:** a polynomial-time graph canonizer / the **unconditional oracle-capability seal**
  `reachesRigidOrCameron` (currently conditional `modulo {G3 cited + G2-B open}`). Closing **G2-B** is the only
  open mathematical content; **this build is the one known route that closes it.**
- **What this build owns:** the two — and *only* two — remaining obligations of the seal-bridge (see §1–§2):
  - **(A)** `Separable (orbitalScheme H)` for the residue family — the Ponomarenko Thm-4.1 separability result.
  - **(B)** the transport `Separable ⟹ CellsAreOrbits at a bounded base` (`SeparabilityTransports`).
  Both are **coupled** — they share the *same* general-CC substrate (point-extension-as-CC, general algebraic
  isomorphism, separability of an extension). Building that substrate is the whole job.
- **What is already done and feeding in** (all axiom-clean, build green): the seal-bridge gate, the sink, the
  `b(X)`-tail, and **(C) the group base is FREE** (`exists_greedy_base_le_log` + the seal's "small" antecedent).
  So nothing peripheral remains — see §2.
- **Empirical license to build:** seven falsifiers returned **0 G2-B witnesses**, including the on-target
  **ℤ₄² amorphic-NLS Clebsch bullseye** (recovers at WL-depth 2). The target statement is almost certainly true;
  the risk is proof-effort, not falsification. A witness would be a *statement change* (the seal is false) — equally
  a real result.
- **Quality bar (non-negotiable):** every theorem axiom-clean `[propext, Classical.choice, Quot.sound]`; full build
  green (`bash scripts/build.sh`, serial ~60–120 s); **no `sorry`, no fresh `axiom`** (cited classifications are
  theorem-statement *hypotheses*); **do not commit** (the user commits between messages).
- **CURRENT STATE: nothing of the general-CC substrate is built yet.** This doc is the plan. **NEXT ACTION:**
  Stage 0 (the modeling decision, §5) then Stage 1 (the general-CC type). The increment log is §8 — append to it.

---

## 0. How to work in this build

- **One rule:** treat every summary — this doc included — as a *hypothesis* to confirm against the Lean source and
  the primary papers. The source wins.
- **Build:** `bash scripts/build.sh` (serial, ~60–120 s; parallel `lake build` thrashes swap — don't). Add new
  modules to `scripts/build.sh` `MODULES=(…)` in topological order. Verify axioms with
  `lake env lean /tmp/check.lean` containing `#print axioms <decl>` (run from `GraphCanonizationProofs/`).
- **Papers / extraction:** `pdf2txt <file.pdf> [first] [last]` is on PATH (`~/.local/bin`, user-site PyMuPDF).
  arXiv ids are stable; re-fetch with `curl -sL https://arxiv.org/pdf/<id> -o /tmp/x.pdf`. **Extracted already:**
  `/tmp/p4paper.txt` = arXiv:2006.13592 (the Thm-4.1 paper), `/tmp/cartan.txt` = arXiv:1602.07132 (Cartan/Thm 3.1).
- **GOTCHA (will bite you):** `grep` **fails silently** on these extracted files — the locale is broken
  (`setlocale: LC_ALL` warnings) and UTF-8 ligatures (ﬁ, ﬀ, ←, ̸=) make `grep` return *nothing* with no error.
  Use **python** (`open(...,encoding='utf-8',errors='replace').read()` + `.count`/`.find`) or `LC_ALL=C grep`.
- **Index:** after landing decls, regen `PublicTheoremIndex.md` via
  `python3 scripts/GenerateTheoremIndexes.py rewrite --with-line-numbers` then hand-fill Descriptions and delete
  stale rows by hand.

---

## 1. Why this doc exists — the reduced problem

The seal canonizes by descending the individualization–refinement tree, asking an oracle to sort each cell into
orbits. Its open content (G2-B) reduces to: **a primitive, small, non-abelian residual scheme `recovers`** — i.e.
individualizing a *bounded* base discretizes it. In the project's terms the seal consumes

> **`SeparatesAtBoundedBase S bound`** := `∃ S₀, |S₀| ≤ bound ∧ Discrete (warmRefine (schemeAdj S) … (individualizedColouring n S₀))`.

This *is* the **base number** `b(X) ≤ bound` (the WL-with-`S₀`-individualized point extension is complete).

The **seal-bridge gate** (worked across prior sessions; provenance: `chain-descent-module-adjoin-plan.md §9`)
established that this consumer factors into a 3-part chain, and located exactly what is open:

```
   reachesRigidOrCameron                              (the seal; conditional modulo {G3 + G2-B})
        ⟸  SeparatesAtBoundedBase S bound            ( = b(X) ≤ bound ; discharges the G2-B crux hCrux)
             ⟸  (A) Separable (orbitalScheme H)       [s(X)=1, the algebraic-iso notion — Ponomarenko Thm 4.1]
              ∧  (B) Separable ⟹ CellsAreOrbits at T  [the transport: algebraic separability ⟹ WL recovers orbits]
              ∧  (C) a bounded group base  IsBase T    [ = b(G) ≤ bound ]                       ◀── FREE, see §2
```

**The three findings that reduced it to (A)+(B):**
1. **(C) is free.** `exists_greedy_base_le_log` (landed) proves `b(G) ≤ log₂|Aut(X)|` unconditionally; the seal's
   *existing* "small" antecedent (`¬IsLargeSchemeViaAut` = `|Aut| ≤ poly(n)`) makes it `O(log n)`. Wired:
   `separatesAtBoundedBase_of_separable_of_small`. So (C) needs no math, citation, or probe.
2. **(A) and (B) are coupled — both need general-CC separability.** `Separable X` (§S.17) is *relation-level on the
   homogeneous X*; the transport (B) needs separability of the *point extension* `X_T`, a multi-fiber **general CC**
   the project's homogeneous `AssociationScheme`/`AlgIso` **cannot even express**. So you cannot do (B) "cheaply
   first" — it requires the same substrate that proves (A). They are one build.
3. **Separability is the right and only handle.** The block / scheme-congruence route to G2-B is *provably dead* on
   the primitive floor (`intraCellRelations_eq_singleton_zero_of_primitive`: a primitive scheme forces the intra-cell
   block to `{0}`); the gap is a *non-congruence amorphic WL-fusion* (the Clebsch `S₃`) no closed-subset captures.
   The forward/counting = separability route is the only one left. Ponomarenko Thm 4.1 is its general theorem.

**So: build the general-CC separability substrate, prove (A) and (B) for the residue, and the seal closes
(modulo the cited G3 only).** That is this document.

---

## 2. The exact target (in Lean terms) — what "done" means

The build delivers two theorems for the residue family `S = orbitalScheme H` (a `SchurianScheme n`):

- **(A)** `S.toAssociationScheme.Separable`  — the §S.17 predicate (or its general-CC strengthening, §5 Stage 1).
- **(B)** `∀ T, SeparabilityTransports S T`  — i.e. `S.toAssociationScheme.Separable → TwinsRealizedByResidualAut S T`.

These compose, through **already-landed, axiom-clean** decls, straight to the seal:

| Landed decl (file) | Role |
|---|---|
| `separatesAtBoundedBase_of_separable_of_small` (`CascadeAffine.lean §S-gate`) | `(A) ∧ (B at every base) ∧ (small bound) ⟹ SeparatesAtBoundedBase` — picks the group base internally (C free) |
| `separatesAtBoundedBase_of_separable` (`CascadeAffine.lean §S-gate`) | `(A) ∧ (B at T) ∧ IsBase T ∧ |T|≤bound ⟹ SeparatesAtBoundedBase` |
| `separatesAtBoundedBase_of_twinsRealized` (`Cascade.lean`) | the sink: `TwinsRealizedByResidualAut T ∧ IsBase T ⟹ SeparatesAtBoundedBase` |
| `twinsRealizedByResidualAut_iff_cellsAreOrbits` (`Cascade.lean`) | `TwinsRealizedByResidualAut S T ↔ CellsAreOrbits (schemeAdj …) T` (the sink *is* recovery) |
| `SeparabilityTransports` / `TwinsRealizedByResidualAut` (`CascadeAffine.lean` / `Cascade.lean`) | the two obligation predicates |
| `exists_greedy_base_le_log` (`Cascade.lean`) | `b(G) ≤ log₂|Aut|` — discharges (C) |
| `PersistentTwinYieldsBlock` (`Cascade.lean:4504`) | `¬SeparatesAtBoundedBase → IsLarge ∨ ∃ block`; **proving `SeparatesAtBoundedBase` discharges it vacuously** |
| `reachesRigidOrCameron_viaPersistentTwinBlock` (`Cascade.lean:4543`) | the seal capstone consuming `hCrux : PersistentTwinYieldsBlock` (+ G3 `hClassify`, landed `hImprim`, `hne`/`hrank`) |

So the **final assembly** is: prove (A)+(B) for `orbitalScheme H` ⟹ `SeparatesAtBoundedBase S bound` (via
`separatesAtBoundedBase_of_separable_of_small`, with `bound` = the poly "small" bound) ⟹ `PersistentTwinYieldsBlock`
holds (its `¬SeparatesAtBoundedBase` antecedent is false) ⟹ feed `reachesRigidOrCameron_viaPersistentTwinBlock`.
**The seal is then unconditional modulo G3 (the cited primitive-CC classification) alone.**

**The §S.17 objects already built** (homogeneous, `Separability.lean`; the general-CC versions in Stage 1 extend
these — keep names parallel):
```lean
structure AlgIso (X Y : AssociationScheme n) where
  relEquiv : Fin (X.rank + 1) ≃ Fin (Y.rank + 1)
  map_zero : relEquiv 0 = 0
  pres_intersection : ∀ r s t, X.intersectionNumber r s t = Y.intersectionNumber (relEquiv r) (relEquiv s) (relEquiv t)
def AlgIso.InducedBy (φ : AlgIso X Y) (f : Equiv.Perm (Fin n)) : Prop := ∀ r v w, X.rel r v w = Y.rel (φ.relEquiv r) (f v) (f w)
def Separable (X : AssociationScheme n) : Prop := ∀ (Y) (φ : AlgIso X Y), ∃ f, φ.InducedBy f
def SeparableParam (X : AssociationScheme n) : Prop := 3 * X.indistinguishingNumber * (X.maxValency - 1) * X.maxValency < n  -- Thm 5.1
```
Note `Separable` here quantifies `Y` over *homogeneous `AssociationScheme n`*. Thm 4.1 quantifies over *general
CCs* `X'`; whether the homogeneous quantification suffices, or must widen to general CC, is a Stage-1 decision (§5).

---

## 3. The mathematics (self-contained)

All from Ponomarenko, *On the separability of cyclotomic schemes over finite field*, **arXiv:2006.13592**
(`/tmp/p4paper.txt`), and Ponomarenko–Vasil'ev, *Cartan coherent configurations*, **arXiv:1602.07132**
(`/tmp/cartan.txt`); foundations in Evdokimov–Ponomarenko, *Separability number and Schurity number of coherent
configurations*, EJC 2000 (their ref **[4]**). Statements below are quoted/paraphrased faithfully; verify against
the source before relying on a subtlety.

### 3.1 Coherent configurations (general, multi-fiber)
A **coherent configuration (CC)** `X = (Ω, S)`: a partition `S` of `Ω×Ω` into *basis relations* such that (a) the
diagonal `1Ω` is a union of elements of `S` (the *reflexive* ones, whose union of supports gives the **fibers** =
a partition of `Ω`), (b) `S` is closed under transpose `r ↦ r*`, and (c) for `r,s,t ∈ S` the **intersection number**
`c^t_{rs} = |{z : (x,z)∈r, (z,y)∈s}|` is constant over `(x,y)∈t`. **Homogeneous** = one fiber (`1Ω ∈ S`); this is the
project's `AssociationScheme`. The point extension below is *not* homogeneous even when `X` is — it has the
individualized points as singleton fibers. **This multi-fiber generality is the substrate the project lacks.**

### 3.2 Point extension, base, base number (Cartan §2.2)
The **point extension** `X_{α,β,…}` is the smallest CC `≥ X` having `{α},{β},…` as fibers — equivalently the
WL-refinement of `X`'s coloured graph with `α,β,…` individualized. A set is a **base** if its extension is
*complete* (all singleton fibers); `b(X)` = min base size. `b(X) ≤ bound ⟺ SeparatesAtBoundedBase S bound`. For
schurian `X = Inv(G)`: `b(G) ≤ b(X)` (inequality (2)), and `b(G)` can be ≪ `b(X)` — the gap is the recovery/`s(X)`
content.

### 3.3 Algebraic isomorphism, separability, m-extension (the heart)
An **algebraic isomorphism** `φ : X → X'` is a bijection `S → S'` preserving all intersection numbers:
`c^t_{rs} = c^{φt}_{φr,φs}`. `φ` is **induced** by `f : Ω → Ω'` if `f` is an honest isomorphism realising it. `X`
is **separable** (`s(X) = 1`) if *every* algebraic isomorphism out of `X` is induced. (Quote, p4paper §2:
"`X` is called separable if … `Iso(X,X',φ)` is nonempty.")

The **m-extension** of `X` (p4paper §2): "the minimal fission of the tensor `m`-power of `X` for which
`Diag(Ωᵐ)` is the union of reflexive basis relations." Its intersection numbers are the **m-dimensional
intersection numbers** of `X` (`m=1` = usual). `X` is **m-separable** if determined up to iso by its m-dim
intersection numbers (`s(X) ≤ m`).

### 3.4 The forced-triangle (`c=1`) calculus — ALREADY IN THE PROJECT
p4paper §2.6: `x ←r y` means `c^y_{xr} = 1`; `x ↔r y` means `x ←r y` or `y ←r* x`. **Lemma 2.7(a):** if `x ←r y`
then for any `µ` and `β ∈ µy` there is a *unique* `α ∈ µx` with `r(α,β) = r`. **This is exactly the project's
`saAdj` forced-triangle / `valency_mul_intersectionNumber` / `transport` machinery from the landed PV Thm 3.1** —
see §4. Thm 4.1's whole proof is built on this calculus; **expect heavy reuse of the PV Thm 3.1 substrate.**

### 3.5 The theorems
- **Theorem 4.1 (the build target — general sufficient condition).** Let `X = (Ω,S)` be a CC, `µ ∈ Ω`. Assume
  (i) for every `Δ ⊆ Ω, |Δ| ≤ 4`, there is `λ ∈ Ω` with `Δ ← λ` (domination), and (ii) for all `α,β,γ ∈ Ω` there is
  `m ∈ S` with `µm ≠ ∅` and the *couple* `Qµ(α,β,γ)` has an `m`-extension. **Then** every algebraic isomorphism
  `φ : X → X'` is induced by an `f` taking `µ` to any given valid `µ'`; **in particular `X` is separable.** (Proof:
  p4paper §§3–4, built on the `c=1` calculus.) The conclusion is the **pointed** form — `f` is controllable on `µ` —
  which is *stronger* than bare `Separable` and is likely what the transport (B) needs.
- **Lemma 2.6 (the key reduction, from EP [4, Thm 4.6(1)]).** *If a **one-point extension** of `X` is separable,
  then `X` is 2-separable.* This is the lever from extension-separability to 2-separability — central to both the
  transport (B) and the lighter route to (A) (§6).
- **Theorem 2.5 (Cartan, base ⟹ separability).** A CC admitting a **1-regular** extension w.r.t. `m−1` points is
  `m`-separable. (Direction: extension/base ⟹ separability. The seal needs the *other* direction, base from
  separability — supplied by the transport (B), not by Thm 2.5.)
- **Theorem 1.1 / 1.2 (the cyclotomic instance, already cited).** Every cyclotomic scheme over a finite field is
  2-separable with finitely many exceptions (`(p,d)` table: `p=2, 2≤d≤20`; `p=3, 2≤d≤10`; `p=5, 2≤d≤6`, minus a
  short list). This is the **affine slice**, already closed in Lean by *citation* (`TwinsAreSemilinear` /
  `reachesRigidOrCameron_affineSlice`). The general build *removes* this citation dependency and covers the
  *non-affine* residue too.

### 3.6 Why the residue needs the general theorem (not the sparse one already done)
The project already formalised **PV Cartan Thm 3.1** (the *sparse* sufficient condition `2c(k−1) < n ⟹` one-point
extension 1-regular `⟹ b(X) ≤ 2 ∧ 2-separable`) — see §4. The **dense amorphic residue violates `2c(k−1) < n`**
(it is dense: many equal-valency relations). Thm 5.1's parameter form `n > 3c(k−1)k` is *stricter* still, so no
parameter route reaches the residue. The dense power is **only** the m-extension route (apply the sufficient
condition to the 2-extension ⟹ 2-separability, as p4paper Thm 1.2 does via Lemma 2.6). Hence the `Ωᵐ` substrate.

---

## 4. What the project HAS vs LACKS

### HAS (build on these — decl names are load-bearing)
- **Homogeneous CC substrate** (`Scheme.lean`): `AssociationScheme n` (single-fiber, `rank`, `rel`,
  `intersectionNumber` + axioms), `ClosedSubset`, `IsPrimitive`, `schemeEquiv`, `orbitalScheme` (the residue
  constructor: `orbitalScheme H` for `H ≤ Perm Ω` is a `SchurianScheme`).
- **The §S.17 homogeneous separability layer** (`Separability.lean`): `AlgIso`, `AlgIso.InducedBy`, `Separable`,
  `SeparableParam`, `idAlgIso`. These are the `m=1`, single-fiber case of what Stage 1 generalises.
- **The landed PV Thm 3.1 substrate** (`Separability.lean §S.1–§S.16` + `CascadeAffine.lean §S-bridge/§S-stab`) —
  *this is the `c=1` forced-triangle calculus Thm 4.1 reuses*: `valency`, `maxValency`, `indistinguishingNumber`,
  `Smax`/`smaxAdj`, `saAdj` (the `c=1` local-rigidity relation) + `saAdj_symm`, `valency_mul_intersectionNumber`
  (triangle identity, = p4paper (4)), `transport`/`transport_step` (the `c=1` path-transport = Lemma 2.7-style),
  `saComp`/`compsOf` (components), `separatesAtBoundedBase_of_sparseSeparable` (the full sparse theorem), and the
  **warmRefine↔extension bridge** `relOfPair_eq_of_warmRefine_determined` (B1), `determined_of_saAdj` (B3),
  `discrete_of_connectivity` (B4), `separatesAtBoundedBase_of_connectivity` (B5) + the stabilization lemma
  `warmRefine_refineStep_samePartition`. **This is the template for the warmRefine↔CC-model bridge Stage 2 needs.**
- **The seal-bridge gate + sink + (C)** (the §2 table): the consumers (A)/(B) feed.

### LACKS (the build creates these)
- A **general (multi-fiber) coherent configuration** type — the central missing object.
- The **point extension as a CC** object (the project models it only as a `warmRefine` *colouring*, not a CC with
  intersection numbers / fibers / algebraic isos).
- **General-CC `AlgIso` / `Separable`** (the §S.17 versions are homogeneous-only).
- The **m-extension on `Ωᵐ`** + m-dim intersection numbers + m-separability.
- **Lemma 2.6** (one-point-extension separable ⟹ 2-separable) and the inheritance facts.
- **Theorem 4.1** itself (conditions (i)/(ii), the couple `Qµ`, the `m`-extending notion) — the sufficient condition.
- The **transport** `Separable ⟹ TwinsRealizedByResidualAut` proof.

### Mathlib
HAS: modules, `Basis`, `Submodule.span`, finite groups, `MonoidHom`, `Equiv.Perm`, `Finset`/`Fintype` combinatorics.
LACKS: **all** coherent-configuration / association-scheme / S-ring / separability theory. None of §3 exists in
Mathlib. `Scheme.lean` is the only CC substrate.

---

## 5. The build plan (dependency-ordered)

> Stages are dependency-ordered; within a stage, sub-items list (deliverable decl) · (depends on) · (load-bearing
> risk). "Load-bearing" = a wrong/blocked statement here invalidates the stage; "mechanical" = routine once stated.

### Stage 0 — the modeling decision (do this first; it shapes everything)
**Decision: how to model the general CC and the point extension.** Two poles, plus a hybrid:
- **Option P (faithful general-CC type).** Define `CoherentConfig` on `Fin n` with an explicit fiber partition,
  basis relations between fibers, intersection numbers, axioms. Faithful to Thm 4.1; lets you state Thm 4.1 / the
  m-extension verbatim. **Heaviest** — a new type with its own algebra. Risk: the `Ωᵐ` m-extension multiplies the
  index set, and Mathlib has no support.
- **Option Q (colouring model).** Keep the project's `warmRefine`-colouring model of the extension `X_T`; define its
  "intersection numbers" as counts in the coloured graph; define algebraic iso / separable on those counts. Lighter,
  reuses the landed warmRefine machinery and the §S-bridge; but Thm 4.1 is stated for general CCs, so a *faithful*
  formalisation of the sufficient condition is awkward here.
- **Option H (hybrid — recommended starting hypothesis).** A *minimal* general-CC layer (Option P) **only** down to
  the **one-point extension** `X_µ` and the **2-extension** (`Ω×Ω`), enough to state Lemma 2.6, the transport, and the
  *2-separability* target — and bridge the result back to the warmRefine model via the §S-bridge template (B1–B5). Do
  **not** build the full `Ωᵐ` tower unless a stage genuinely needs `m > 2`. Rationale: the residue target is
  *2-separability* (Lemma 2.6 / Thm 1.2 are about 2-separability); `m = 2` may suffice, sparing the general `Ωᵐ`.
- **Deliverable of Stage 0:** a short written decision (append to §8) fixing P/Q/H and the `CoherentConfig`/extension
  representation, *with a typechecking skeleton* (the type + a trivial inhabitant) so Stage 1 has a target.

### Stage 1 — the general-CC substrate (shared prerequisite for A and B)
1. **`CoherentConfig` type** (or the chosen representation) · Stage 0 · **load-bearing.** Fibers, basis relations,
   intersection numbers, the coherence axiom. Provide the homogeneous `AssociationScheme → CoherentConfig` coercion.
2. **The point extension `X_µ` / `X_T` as a `CoherentConfig`** · 1 · **load-bearing.** The smallest CC ≥ X with `T`
   singleton fibers. Connect to the warmRefine model: `X_T`'s fibers = `warmRefine … (individualizedColouring n T)`
   cells (the §S-bridge `relOfPair_eq_of_warmRefine_determined` is the template).
3. **General `AlgIso` / `Separable` / `m-separable`** · 1 · **load-bearing.** Generalise §S.17 to `CoherentConfig`;
   prove the homogeneous `Separable` (§S.17) is the single-fiber case (reconciliation lemma).
4. **The m-dim intersection numbers / 2-extension** · 1 · load-bearing *iff* the chosen route needs `m=2` (it does —
   Lemma 2.6 / Thm 1.2). Build `Ω×Ω` only; defer general `Ωᵐ`.

### Stage 2 — the transport (B): `Separable ⟹ CellsAreOrbits at T`
Target: `∀ T, SeparabilityTransports S T`. Route (the affine slice `powAffineSeparates_of_twinsAreSemilinear` is the
concrete template; here general):
1. **Twins ⟹ extensions algebraically isomorphic** · Stage 1.2/1.3 · **load-bearing.** A same-`warmRefine`-cell pair
   `u,u'` from `T` ⟹ `X_{T∪{u}} ≅_alg X_{T∪{u'}}` (equal intersection numbers from equal profiles). The WL-local /
   counting step — the B1–B5 analogue *on extensions* (reuse `relOfPair_eq_of_warmRefine_determined` /
   `warmRefine_refineStep_samePartition`).
2. **Separability of the extension** · Stage 1.3 + Lemma 2.6 · **load-bearing, the crux.** From `Separable X` (the
   §S.17/general predicate) derive separability of the relevant extension. Two sub-routes: (a) prove the inheritance
   `s(X_µ) ≤ s(X)` directly (EP [4]); or (b) use Thm 4.1's **pointed** conclusion (induced `f` controllable on `µ`)
   to skip an explicit inheritance lemma. **Pin which before investing** — this is the load-bearing uncertainty the
   transport surfaced.
3. **Separable extension + alg-iso ⟹ induced iso ⟹ residual aut** · 2.1+2.2 · mechanical-ish. The induced `f` fixes
   `T` (matching singleton fibers) and maps `u ↦ u'`; it is a scheme automorphism ⟹ a `ResidualAut` realising the
   twin ⟹ `TwinsRealizedByResidualAut`.

### Stage 3 — the separability theorem (A): `Separable (orbitalScheme H)` for the residue
Target: `S.toAssociationScheme.Separable`. **Route choice (see §6) — recommended: the Lemma-2.6 / 2-extension route**,
reusing the landed `c=1` machinery, rather than full general Thm 4.1.
1. **The `c=1`/domination layer** · Stage 1 + the landed `saAdj`/`transport`/`valency_mul_intersectionNumber` ·
   load-bearing. Port the p4paper §2.6 calculus (`x ←r y`, Lemma 2.7) onto the general CC — much may transfer from
   the PV Thm 3.1 substrate.
2. **Thm 4.1 conditions (i) domination + (ii) `m`-extending couples** · 1 · **load-bearing.** State and (for the
   residue / 2-extension) discharge. This is the genuine new mathematics.
3. **Assemble (A)** · 2 + Lemma 2.6 · load-bearing. Either prove `Separable` directly for the residue, or
   `2-separable` via Lemma 2.6 and feed the transport at `m=2`.

### Stage 4 — assembly + exceptional cases
1. **Wire (A)+(B) ⟹ seal** · Stages 2,3 + §2 table · mechanical. Instantiate
   `separatesAtBoundedBase_of_separable_of_small` at `orbitalScheme H`, feed `reachesRigidOrCameron_viaPersistentTwinBlock`.
2. **Exceptional `(p,d)` table** (Thm 1.1, only if the residue includes the cyclotomic/affine instances) · the C# bed
   (`AffineSchemeProbe`/`CatalogueSchemeProbe`) · mechanical. Reproduce the finite exceptions as `decide`-checked
   facts. **The non-affine NLS residue is outside the cyclotomic family, so likely N/A** — confirm per instance.

---

## 6. Route options + recommendation

**For (A) `Separable`:**
- **Route α — full Thm 4.1** (general CC, conditions (i)+(ii), arbitrary `m`). Most general, most faithful, heaviest
  (the `Ωᵐ` tower). Use only if the residue genuinely needs `m > 2`.
- **Route β — the 2-extension / Lemma 2.6 (recommended).** Prove the *one-point extension* separable (via the `c=1`
  domination calculus, reusing the PV Thm 3.1 substrate), then Lemma 2.6 ⟹ 2-separability. Caps the substrate at
  `m = 2` (Stage 1.4 builds only `Ω×Ω`). Aligns with p4paper's own Thm 1.2 proof structure.
- **Route γ — parameter (Thm 5.1, `n > 3c(k−1)k`).** RULED OUT for the residue (stricter than the sparse Thm 3.1
  already done; the dense residue violates it). Do not attempt.

**Recommended path:** Stage 0 → **Option H** (minimal general-CC to `m=2`) → Stage 1 → **Route β** for (A) and the
Lemma-2.6 inheritance for (B) Stage 2.2(a) → Stage 4. Bite off the full `Ωᵐ`/Route α only if a concrete obstruction
forces `m > 2`. **Honest scope:** research-scale, multi-session, may not close (the residue could be unbounded-`s`,
i.e. a counterexample = the seal is false = a statement change). The 0-witness probe evidence (incl. the ℤ₄²
bullseye) says closure is the likely outcome and the build is worth it.

---

## 7. Decision log — ruled out / do not re-walk

- **Block / scheme-congruence route to G2-B is DEAD on the primitive floor.**
  `intraCellRelations_eq_singleton_zero_of_primitive`: a primitive scheme forces the intra-cell block to `{0}`. The
  gap is a non-congruence amorphic WL-fusion (Clebsch `S₃`). Only the forward/separability route survives. (This is
  *why* this build exists.)
- **(C) the group base is not an obstacle** — `exists_greedy_base_le_log` + "small". Do not re-survey it.
- **The transport (B) is NOT a cheap pre-substrate de-risk** — it needs extension-separability (general CC), coupled
  to (A). Do not look for a homogeneous-only proof of `Separable ⟹ CellsAreOrbits`; it does not exist (the twin lives
  in the multi-fiber extension).
- **Thm 5.1 parameter route (γ) is ruled out** (stricter than the done sparse Thm 3.1; residue is denser).
- **The orbit-level harvest re-key is a vacuity trap** (`coversOrbits_of_realizers` keyed on `OrbitPartition` is
  trivially true — orbit-mates are aut-related by definition). Keep all recovery content on *visible* (warmRefine)
  realizers. The sink `TwinsRealizedByResidualAut` is correctly keyed (≡ `CellsAreOrbits`).
- **Do not anchor on group non-commutativity** (`not_comm_of_orbit_disagree` is the ¬leg-B / *consumption* statement,
  a different thing). C₇/`D₇` is non-abelian yet recovers via its metric structure — separability, not commutativity,
  is the content. Symmetric schemes have commutative Bose–Mesner algebras regardless of the group.
- **The affine slice is already closed by citation** (`reachesRigidOrCameron_affineSlice` via cyclotomic
  2-separability, Thm 1.1). This build *removes* that citation and covers the non-affine residue — do not re-do the
  affine slice; do reuse its template (`powAffineSeparates_of_twinsAreSemilinear` = the transport at the affine
  instance, with the realiser the explicit linear `affinePermFin`).
- **Custom-axiom-free invariant:** cited classifications (G3 `PrimitiveCCClassification`, any EP/Ponomarenko theorem
  you choose to *cite* rather than *prove*, e.g. Lemma 2.6 if you carry it) must be theorem-statement **hypotheses**,
  never fresh `axiom`s. Decide per lemma: prove it, or carry it as a named hypothesis on the final theorem.

---

## 8. Increment log (append here every session)

> Newest at the bottom. One block per landed increment: date · decls (file) · axiom-clean? · what it unlocks · next.
> The STATUS block at the top of this doc is the authoritative current state; this is the history.

- **2026-06-11 — doc created.** The plan above. Nothing of the general-CC substrate built yet. Inputs (gate, sink,
  (C)-discharge, PV Thm 3.1 substrate, §S.17 homogeneous separability) all landed and listed in §2/§4.
  **NEXT: Stage 0 — the modeling decision (Option P/Q/H), with a typechecking `CoherentConfig` (or extension)
  skeleton.** Recommended starting hypothesis: Option H (minimal general-CC to `m=2`), Route β for (A).

---

## 9. Quick reference — decl/source index

**Seal connection (landed, consume these):** `reachesRigidOrCameron_viaPersistentTwinBlock` (`Cascade.lean:4543`),
`PersistentTwinYieldsBlock` (`Cascade.lean:4504`), `SeparatesAtBoundedBase` (`Cascade.lean:4437`),
`separatesAtBoundedBase_of_separable_of_small` / `separatesAtBoundedBase_of_separable` / `SeparabilityTransports`
(`CascadeAffine.lean §S-gate`), `separatesAtBoundedBase_of_twinsRealized` / `TwinsRealizedByResidualAut` /
`twinsRealizedByResidualAut_iff_cellsAreOrbits` (`Cascade.lean`, by `SeparatesAtBoundedBase`),
`exists_greedy_base_le_log` (`Cascade.lean:916`), `CellsAreOrbits` (`CascadeOracle.lean:268`), `IsBase`
(`Cascade.lean:70`), `orbitPartition_iff_residualAut` (`Cascade.lean:477`), `orbitalScheme` (`Scheme.lean`).

**Homogeneous separability (extend these):** `AlgIso` / `Separable` / `SeparableParam` / `idAlgIso`
(`Separability.lean §S.17`).

**PV Thm 3.1 `c=1` substrate (reuse heavily):** `saAdj` / `saAdj_symm` / `valency_mul_intersectionNumber` /
`transport` / `transport_step` / `saComp` / `compsOf` / `separatesAtBoundedBase_of_sparseSeparable`
(`Separability.lean §S.1–S.16`); the warmRefine bridge `relOfPair_eq_of_warmRefine_determined` /
`determined_of_saAdj` / `discrete_of_connectivity` / `separatesAtBoundedBase_of_connectivity` /
`warmRefine_refineStep_samePartition` (`CascadeAffine.lean §S-bridge/§S-stab`).

**Papers:** Ponomarenko, arXiv:2006.13592 (`/tmp/p4paper.txt`) — **Thm 4.1** (§4, the target; statement at offset
~20137 in the extract), **Lemma 2.6** (one-pt ext separable ⟹ 2-separable), **m-extension** (§2), Thm 1.1/1.2
(cyclotomic). Ponomarenko–Vasil'ev, arXiv:1602.07132 (`/tmp/cartan.txt`) — **Thm 2.5** (1-regular `(m−1)`-ext ⟹
`m`-separable), base defs (§2.2), **Thm 3.1** (the sparse condition, already formalised). Evdokimov–Ponomarenko,
*Separability number and Schurity number of coherent configurations*, EJC 2000 (ref **[4]**) — `s(X)`/`t(X)`
foundations, Thm 4.6(1) (source of Lemma 2.6). Extraction: `pdf2txt`; read with **python, not grep** (§0 gotcha).

**Provenance (do not need to read, but for the curious):** the seal-bridge gate / transport / (C) findings are in
`chain-descent-module-adjoin-plan.md §9`; the seal state in `chain-descent-seal-handoff.md`; the project overview in
`docs/00-START-HERE.md`.
