# Proof plan — bounded WL-dimension for the affine forms-graph families (the seal's node-4 content)

> **What this is.** A concrete proof plan for the sharpened open frontier (route-doc §9.9.18b/c): prove **bounded
> Weisfeiler–Leman dimension** (= bounded individualization base ⟹ `hSmallAutThin`) for the affine forms-graph rank-3
> SRG families that constitute node-4-for-the-seal — affine polar `VO^ε_{2m}(q)`, alternating forms, half-spin, and
> Suzuki–Tits. By the Skresanov reduction (§9.9.18) these (plus the cited 1-dim cyclotomic slice) are the *entire*
> small-Aut non-geometric schurian rank-3 residue; the probe (`Probe_FormsGraphs`, §9.9.18c) shows they shatter at a
> bounded base. This plan turns that empirical shatter into a proof target with a landed engine and one crux lemma.

---

## STATUS (read first)

**★ STAGE A LANDED (2026-06-18, axiom-clean `[propext, Classical.choice, Quot.sound]`, build green).** The conditional
capstone `reachesRigidOrCameron_viaAffineFormScheme` (CascadeAffine.lean, between the §SGate2 and §AffineScheme
sections; `PublicTheoremIndex.md:1207`) is built. It carries exactly the two pieces the reduction identifies —
`hbase : IsBase … T` (the free group base) and `hFormCert : RelCountsDetermineOrbit … T` (the **only open content**) —
and composes the landed engine + base + seal (`cellsAreOrbits_of_relCountsDetermineOrbit` →
`twinsRealizedByResidualAut_iff_cellsAreOrbits` → `separatesAtBoundedBase_of_twinsRealized` →
`reachesRigidOrCameron_viaSpielman`). **Carries NO `hSmallAutThin`** — node 4 is discharged for this residue, not
assumed. The route is validated end-to-end; the open content is now exactly the one predicate `hFormCert`. **Next =
Stage B** (discharge `hFormCert` for `VO^ε_4(q)`; §3, §4). Nothing committed (user commits).

**The target is now extremely concrete** — not "all SRGs", but four explicit affine/classical-group families whose
automorphism group `G^(2)` is given structurally by Skresanov and whose base the probe measured at `≈ d+1` (flat).
**The reduction is mostly landed; the open content is ONE crux lemma — `RelCountsDetermineOrbit (affineScheme G₀) T`
at the group base**, fed into the already-built depth-`k` separation engine. **Calibration (read §7 before starting):
that lemma is UNCITED, genuine content you must prove — but it is NOT the open "WL-dim of SRGs" research problem.** The
engine has already reduced "bounded WL-dimension" to a finite, geometry-specific separation statement; the structure
(Skresanov), the base (handed by the group), and the answer+mechanism (the probe) are all known, so what remains is a
known-target classical-finite-geometry lemma (Witt-frame / intersection-number), unpublished because unneeded — a
different difficulty class from the black-box SRG problem. The realistic Lean increment is a **conditional capstone**
`reachesRigidOrCameron_viaAffineFormScheme` carrying the certificate as a probe-validated hypothesis (Stage A, wiring
now); the full discharge is a classical-geometry + Mathlib-quadratic-form effort, stageable family-by-family.

**Closes (modulo citations + this proof):** node-4-*for-the-seal*. Combined with Skresanov (residue is affine) + C3
(seal scoped to schurian, §9.9.18a), proving this discharges `hSmallAutThin` for the schurian residue. The genuinely
uncited *non-schurian* wall (IR-solver row 4) is untouched — by design, outside the seal (§9.9.18a).

---

## 1. The target theorem (uniform form)

> **Theorem (to prove).** Let `X = affineScheme G₀` be a primitive rank-3 schurian SRG on `V = F_q^d`, where
> `G₀ ≤ ΓL(V)` is a classical *similitude* group preserving a nondegenerate form `f` (quadratic/bilinear/Hermitian),
> and `d` is bounded (the small-Aut regime: `|Aut| = n^{Θ(d)}` poly ⟺ `d = O(1)`). Then `X` individualizes to a
> **discrete** coloured configuration at a base of size `≤ d+1 = O(1)`. Hence `X` has **bounded WL-dimension**, so
> `BoundedMinMult`/`hSmallAutThin` holds for `X` (the seal's node-4 obligation, for this residue class).

Why this is the seal's node-4 content: §9.9.18 (Skresanov) ⟹ every small-Aut non-geometric schurian rank-3 residue is
one of these affine families (or the cited 1-dim cyclotomic); §9.9.18a (C3) ⟹ the seal's scope IS the schurian residue.
So this theorem + the cyclotomic citation = node-4-for-the-seal, modulo the CFSG identification {Cameron, Liebeck,
Skresanov}.

---

## 2. The reduction — two halves, one open

Decompose `b(X)` (the WL/individualization base) for `X = Inv(G^(2))`, `G^(2) = V ⋊ G₀` (Skresanov):

**(i) The group base is FREE and `O(1)`.** Take `T = {0, e₁, …, e_d}` (origin + a basis of `V`). An affine map
`x ↦ g₀x + t` fixing `0` has `t=0` (linear); fixing a basis `{e_i}` pointwise forces `g₀ = 1`. So `(G^(2))_T = {1}`,
i.e. **`T` is a group base**, `|T| = d+1`. In Lean: `IsBase (schemeAdj X) _ T` holds; or use the landed
`exists_greedy_base_le_log` for an `O(log n)` base with no frame computation. Either gives the `IsBase`/bounded-`|T|`
inputs of `separatesAtBoundedBase_of_twinsRealized` for free. **Nothing open here.**

**(ii) The separation certificate is the OPEN content.** Discreteness at `T` is *not* automatic from `(G^(2))_T = {1}`
— that gives singleton *orbits*, but 2-WL must *see* them (no 2-closure deficiency at the extension `X_T`). The exact
open obligation is the engine's separation hypothesis at `T`:
> `hsep`: for all `u,u'`, if the **two-round relation-count profile** agrees
> (`∀ ρ b, #{z≠u : (∀t∈T, relOfPair t z = ρ t) ∧ relOfPair u z = b} = #{z≠u' : … u' …}`), then `u = u'`.
This is exactly the input of the **landed** `discrete_of_twoRoundRelationSeparates` (k=1) / `discrete_of_kRoundRelationSeparates`
(general `k`) (CascadeAffine.lean). Equivalently `RelCountsDetermineOrbit X T` (which, since `(G^(2))_T={1}`, collapses
to count-equal ⟹ equal). **This is the only open piece.**

**(iii) Compose (free).** `hsep` ⟹ `Discrete(warmRefine X_T)` (engine) ⟹ `SeparatesAtBoundedBase X (d+1)` (with the
(i) `IsBase`, via `separatesAtBoundedBase_of_twinsRealized` — note `Discrete ⟹ TwinsRealizedByResidualAut` trivially,
or use the engine's `Discrete` output directly) ⟹ the seal capstone. **Landed wiring.**

So: **free base (i) + landed engine (iii); the whole proof is the certificate (ii).**

---

## 3. The crux lemma — "the count profile recovers the form coordinates"

The probe pins the mechanism. A *binary* isotropy profile w.r.t. `T` would need `|T| ≥ log_q(q^d) = d` points just to
have enough profiles, and could not separate at `O(1)` — yet the probe shatters at `≈ d+1`. So the separation is *not*
from the direct (rank-3, binary) relations; it is from the **two-round COUNTS**, which recover the *field-valued* form.

> **Crux Lemma (per family, uniform skeleton).** Let `B` be the nondegenerate (bi)linear form associated to `f`. After
> individualizing `T = {0, e₁,…,e_d}`, the two-round relation-count profile of a vertex `v` determines `B(v, e_i) ∈ F_q`
> for every `i`. Since `B` is nondegenerate, `(B(v,e_i))_{i=1}^d` determines `v`. Hence the count profile is injective
> (`hsep` holds).

There are **two routes** to the certificate. Route A is elementary and Witt-free (the safe Lean path); Route B is more
geometric and is the right *mental model* (it explains why the bulk is easy), but leans on Witt's theorem, which Mathlib
**lacks** (verified 2026-06-18 — see §5 R2). Both meet at the same residual difficulty: the **non-isotropic shell**.

**Route A — explicit count-injectivity (elementary, Witt-free; the Lean default).** For affine polar `VO^ε` the count
`N_{i,b}(v) := #{z : Q(z − e_i) = 0 ∧ relOfPair v z = b}` (common "isotropic-from-`e_i`" points at relation `b` to `v`)
is an explicit function of `B(v, e_i)` via the orthogonal geometry's intersection numbers (the number of isotropic
points in the "tangent" configuration of `v, e_i` depends on whether/how `v ⊥ e_i`). Showing `N_{i,·}(v)` is injective
in `B(v,e_i)` discharges the lemma. This is classical, bounded combinatorics in the polar space — and avoids Witt.

**Route B — perp-graph + Witt frame-rigidity (the geometric picture; explains the difficulty inversion).** You do *not*
have to prove abstract count-injectivity from scratch; there is a directly geometric decomposition:
- **Individualize `0`.** `N(0)` = the nonzero isotropic vectors. The key identity: for isotropic `x,y`,
  `Q(x−y) = Q(x)+Q(y)−B(x,y) = −B(x,y)`, so **`x ~ y ⟺ B(x,y) = 0`**. Hence the subgraph induced on `N(0)` **IS the
  collinearity (perp) graph of the polar space, read straight off the rank-3 adjacency — no counting.**
- **The polar space is frame-rigid (Witt's theorem).** Individualizing a hyperbolic frame / apartment (`O(d)` isotropic
  points) trivialises its isometry-stabiliser *and* determines each isotropic point by its perp-pattern to the frame. So
  `0 + frame` (`O(d)` points) discretises the **isotropic skeleton** via the *direct* adjacency.
- **The non-isotropic shell** is then pinned by its adjacency/relation pattern to the now-discrete isotropic skeleton.
  **This is the genuinely fiddly bit** (and where Route A and Route B meet): binary adjacency `w ~ x_i ⟺ B(w,x_i)=Q(w)`
  recovers `B(w,x_i)` only *modulo the unknown scalar `Q(w)`*. Expect to need either a couple of extra base points, or
  one round of the engine's count (Route A) restricted to the non-isotropic shell.

**The difficulty inversion (why this reads harder than it is).** The hard-*looking* part — the isotropic bulk — is the
*easy* part (direct perp-graph + Witt). The residual work is the **non-isotropic shell**, a narrow, located problem.

**Per-family status of the crux lemma:**
- **(c) affine polar `VO^ε_{2m}(q)`** — quadratic form `Q`, bilinear `B(x,y)=Q(x+y)−Q(x)−Q(y)`. Mathlib `QuadraticForm`
  has exactly this. **Cleanest target; do first.**
- **(d) alternating forms `A(d,q)`** — vertices = alternating matrices = `Λ²(F_q^d)`; adjacency = rank-2 difference;
  the associated form is the alternating (symplectic) `B`. Same skeleton, `B` symplectic. **Second.**
- **(e) half-spin `VD_{5,5}(q)`** — spinor geometry; the "form" is the triality/spinor norm. Same *spirit* (a
  nondegenerate spinor pairing recovers coordinates) but heavier geometry. **Third; may defer.**
- **(f) Suzuki–Tits `VSz(q)`** — the Suzuki ovoid, **not a form-graph** (Sz(q) is a twisted group, not classical
  similitude). The form skeleton does NOT apply. **Separate argument** — either (α) a direct count in the ovoid
  geometry, or (β) fall back to the generic schurian bound: `(G^(2))_T={1}` at an `O(1)` base + a separability/no-
  deficiency argument specific to Sz(q). Honest caveat: Suzuki is the residual hard single family; flag it.

The lemma is **uniform** for the form-based families (c)–(e); (f) is the outlier.

---

## 4. The Lean formalization plan

**Reusable, landed (no rebuild):**
- Engine: `discrete_of_twoRoundRelationSeparates` / `discrete_of_kRoundRelationSeparates` / `kRoundProfileCount_eq`
  (consumes `hsep`, gives `Discrete`). `RelCountsDetermineOrbit` / `cellsAreOrbits_of_relCountsDetermineOrbit` (orbit form).
- Free base: `IsBase`, `exists_greedy_base_le_log`, `separatesAtBoundedBase_of_twinsRealized`,
  `TwinsRealizedByResidualAut`.
- Affine substrate: `affineScheme G₀` / `affineG` / `affinePermFin` — **already general in `d` and `G₀ ≤ GL_d(F_p)`**
  (verified). The cyclotomic instance (`G0cyc`/`G0pow`) is the 1-dim template to mirror.
- Mathlib: `QuadraticForm`, `LinearMap.BilinForm` (nondegeneracy), `GaloisField`, `Basis`, `Module.finBasis` — available.

**New (the build):**
1. **The form scheme instance.** Define the affine form scheme as `affineScheme G₀` with `G₀ =` the matrix similitude
   group `ΓO(Q)` (resp. `ΓSp`, `ΓU`), OR (lighter) define the Cayley scheme directly from a Mathlib `QuadraticForm`
   and prove it `SchurianScheme` via similitude-transitivity. **Dependency:** Witt-type transitivity (the similitude
   group is transitive on each form-value level set, fusing nonzero values via scalars to 2 orbits ⟹ rank 3). Check
   Mathlib for Witt's theorem / `QuadraticForm` isometry-transitivity; if absent, this is the main new infrastructure.
2. **The crux certificate lemma** (§3): the two-round count profile at `T` recovers `B(v,e_i)`; conclude `hsep`.
   The combinatorial-geometry counting. Family-specific; uniform skeleton for (c)–(e).
3. **The capstone** `reachesRigidOrCameron_viaAffineFormScheme`: compose (i)+(ii)+(iii) → `SeparatesAtBoundedBase` →
   the seal (via the landed `…viaSymmetricRecovery`/`schemeRecoveredByDepth_of_separatesAtBoundedBase`). Carries
   {G3 + the affine-form structure}; **no `hSmallAutThin`** (it is *discharged* for this family).

**Staging (build order):**
- **Stage A — the wiring + conditional capstone (cheap, do first). ✅ DONE (2026-06-18, axiom-clean, build green).**
  `reachesRigidOrCameron_viaAffineFormScheme` (CascadeAffine.lean, `PublicTheoremIndex.md:1207`) carries the certificate
  as a *named hypothesis* `hFormCert : RelCountsDetermineOrbit S.toAssociationScheme T` plus the free group base
  `hbase : IsBase … T` (probe-validated, like `clebschZ4_closure` carried δ′). Route validated end-to-end; the open
  content is isolated to the one predicate `hFormCert`.
- **Stage B — discharge the certificate for `VO^ε`** (the crux lemma, §3). The genuine combinatorial work. Start with a
  fixed small `d` (`d=4`, `VO^ε_4(q)`) generic in `q` — richest probe data (base `[5,5,6,7]` at `q=2..5`) — then general
  `d`. Use **Route B** as the picture (isotropic skeleton = direct perp-graph) but expect the formal proof to go via
  **Route A** counts (Mathlib lacks Witt, §5 R2); the residual is the **non-isotropic shell**, plan for a small `k` or
  1–2 extra base points there.
- **Stage C — alternating / half-spin** (reuse the skeleton with the symplectic / spinor `B`).
- **Stage D — Suzuki–Tits** (separate plan needed).

---

## 5. Risks, and the pragmatic fallback

- **R1 — the counting lemma is real work.** Computing intersection numbers as functions of `B(v,e_i)` and proving
  injectivity is classical but nontrivial to formalize. *Mitigation:* Stage A lands the wiring regardless; Stage B can
  start from explicit count formulas for `VO^ε_4(q)` (small `d`).
- **R2 — Witt theory is ABSENT from Mathlib (verified 2026-06-18).** `Mathlib/LinearAlgebra/QuadraticForm/` has
  `Isometry`/`IsometryEquiv`/`Radical`/`Basis`/`Dual` but **no Witt decomposition and no Witt extension theorem** (the
  only "Witt" files are `Order/BourbakiWitt`, unrelated, and `RingTheory/WittVector`, ring-theoretic). *Consequence:*
  **Route B's frame-rigidity is not free** — relying on it means building Witt's extension theorem (substantial). *Mitigation:*
  prefer **Route A** (elementary counts, Witt-free); and define the scheme directly from a `QuadraticForm`, carrying rank-3 +
  schurian as **checkable hypotheses** (the probe confirms rank 3) rather than deriving them from similitude-transitivity.
  So Stage A's capstone carries TWO named hypotheses: the certificate `hFormCert` *and* the rank-3-schurian structure.
- **R2′ — characteristic 2.** The probe spans `q = 2,4` (char 2) and `q = 3,5` (char ≠2). In char 2 the bilinear form is
  alternating (`B(x,x)=0`) and `Q` is **not** recoverable from `B` alone — the Route-A/B identities (`Q(x−y)=−B(x,y)`,
  `B(w,x_i)=Q(w)`) still hold but the "recover `Q(w)`" step needs the quadratic form directly, not just `B`. Budget the
  char-2 shell argument separately; do char-≠2 (`q=3`) first.
- **R3 — Suzuki–Tits is not a form-graph.** *Mitigation:* treat (f) separately; worst case it remains a single flagged
  family with empirical (probe) support, while (c)–(e) are proven — still a major reduction of the residue.
- **R4 — `k` (round count).** The crux is a one-round count, so `discrete_of_twoRoundRelationSeparates` (k=1) should
  suffice; if a single round only partially recovers `B`, escalate to `discrete_of_kRoundRelationSeparates` (small `k`).
  Note (engine ceiling, §9.9.15): the count profile is `k`-independent, so if k=1 fails the lever is a **larger base**
  (more frame points), not deeper `k` — the frame `T` already has `d+1` points, which is the natural fix.

**Pragmatic fallback (always available):** Stage A's conditional capstone `…viaAffineFormScheme` carrying
`hFormCert` as a probe-validated hypothesis is itself a real deliverable — it makes node-4-for-the-seal
`modulo {G3 + Liebeck + Skresanov + the affine-form certificate}`, with the certificate empirically confirmed
(§9.9.18c) and reduced to a single combinatorial predicate per family. This mirrors how the affine cyclotomic slice
was first carried (cited 2-sep) before the δ′ discharge.

---

## 6. Honest scope

- **What it closes:** with the crux lemma proved for (c)–(e) [+(f) or flagged], `hSmallAutThin` is *discharged* for the
  schurian node-4 residue — node-4-for-the-seal becomes `modulo {G3 + the CFSG identification (Cameron/Liebeck/Skresanov)
  + the affine-form certificate}`, all citations/proofs, no open wall. The empirical shatter (§9.9.18c) becomes a theorem.
- **What it does NOT close:** the non-schurian wall (IR-solver row 4, §9.9.18a) — a separate object, outside the seal by
  the C3 scoping. And the CFSG identification stays cited (like G3).
- **Relation to the rank-counting boundary (§9.9.9a):** consistent — the recovery is in the 2-WL *extension* `X_T`
  (where the depth-`k` engine lives), not the scheme-level rainbow engine (inapplicable at rank 3).

---

## 7. Difficulty calibration — why this is NOT the open SRG-WL-dimension problem

A fresh reader's natural worry (correct in part): *"the crux lemma is uncited, so it is open research, not formalisation."*
Honest calibration, from the Stage-B/C scoping handoff (2026-06-18):

**What is TRUE in that worry (do not overclaim against it):**
- The crux lemma is **uncited** — no reference to formalise from. It is genuine content you must *prove*, not look up.
  "Routine" was the wrong word; treat it as **concrete**, not easy.
- Bounded WL-dimension of the affine forms-graphs is genuinely **unpublished** (the C1 literature pass, §9.9.18b, found no
  citation).
- Uniformity over all `q` (+ the Skresanov Table-7 small-degree exceptions, §5 R4-adjacent) and the Suzuki outlier are
  real.

**What is WRONG in that worry — why this is a different difficulty class:**
The open SRG-WL problem is hard because the SRG is a **black box** (unknown automorphisms/geometry). Here every black-box
element is removed:
1. **The structure is KNOWN (Skresanov).** The residue is `affineScheme G₀` with `G₀` an explicit classical similitude
   group and an explicit nondegenerate form — you have the geometry, not an unknown SRG.
2. **The base is HANDED, not searched.** `T = {0,e₁,…,e_d}` is the group base (`(G^(2))_T={1}`, §2(i)) — no need to
   discover a good base or argue one exists.
3. **The WL machinery is ALREADY DONE.** The landed engine (`discrete_of_twoRoundRelationSeparates` /
   `discrete_of_kRoundRelationSeparates` / `kRoundProfileCount_eq`) has *already* reduced "bounded WL-dimension" to a
   finite, checkable, geometry-specific statement — the count profile at `T` separates vertices. **No WL-dimension theory
   remains to develop.** This is the whole point of building the engine first: it converts the open WL problem into
   classical finite geometry.
4. **The probe gives the ANSWER and the MECHANISM.** `Probe_FormsGraphs` (§9.9.18c) shows discreteness at base `≈ d+1` and
   the mechanism (counts recover the field-valued form, not binary isotropy). You are *verifying a known target*, not
   searching.

**So the honest framing:** the crux is *concrete uncited classical finite geometry about an explicit family with a handed
base* — unpublished because nobody needed it, not because it resists technique. **The real cost is the Lean formalisation
of finite-geometry intersection numbers, not the mathematics.** The genuine residual *mathematical* difficulty is narrow
and located: the **non-isotropic shell** (§3, the Route-A/B meeting point) and char-2 (§5 R2′). Recommended order
de-risks the wiring before the geometry: **Stage A first** (carry `hFormCert`, prove the route closes, get the exact
`hsep` shape), then attack the shell with the answer already known.

---

*Maintenance: update STATUS as stages land; keep route-doc §9.9.18b/c the empirical anchor and this doc the proof
target. If Stage A lands, record the capstone in `PublicTheoremIndex.md` + the remaining-work tracker §3a.*
