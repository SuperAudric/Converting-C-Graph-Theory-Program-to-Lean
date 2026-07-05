# Citation discharge — the project-wide tracker for turning cited premises into proofs

> **What this is.** The single home for **discharging the project's carried citations**: the register of every cited
> premise (what it is, where it is carried, its faithful source), the **discharge routes already found** (with the
> concrete Lean that works), and a **methodology** for attempting a discharge. It is the *how-to-remove-a-citation*
> companion to [`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md) §2 (which is the *what-is-left*
> census). Authoritative state = each capstone's `#print axioms` + the Lean sources; this doc is the map + the playbook.
>
> **Project discipline (why this is clean).** A cited result is **never** a fresh `axiom`. It is carried as a **named
> hypothesis** (a `def … : Prop` premise threaded onto the theorems that use it), so the build stays axiom-clean
> `[propext, Classical.choice, Quot.sound]` regardless. "Discharging" a citation means **proving it in-project and
> deleting the hypothesis** — the use sites then close unconditionally. Quality bar throughout: axiom-clean, no `sorry`,
> no fresh `axiom`, `native_decide` banned.

---

## STATUS (read first)

**Policy (user).** Eventually *all* citations except possibly **G3** (Babai / CFSG) are to be fully built in Lean;
G3 may stay cited (it is CFSG-based). Everything else is a discharge target — some already have routes.

**Headline (2026-07-04, updated 2026-07-05).** One citation is **fully discharged** (`SuzukiFormsDetermine`, Route C).
Two more (`NondegQuadricDeterminesForm`, `JointVarietyDeterminesFamily`) are now **discharged from the F4
iso-invariance object** — the vanishing-space transport of §3.2 is **BANKED** (axiom-clean, in `build.sh`; 5 lemmas in
`RouteCFormAdapters.lean`: `vanishingForm_transport_gen`, `recoveredForm_partition_isoInvariant{_gen,}`,
`recoveredFamily_partition_isoInvariant_vanishing`, `vanishingColour_refines_form`). The recovered colour partition is
proved iso-invariant with **no dimension count**, so those two citations no longer gate F4; they remain carried **only**
on the strictly-stronger `|Aut|`-naming statements (scalar-`μ` / injective-`Φ`), a C#/meta concern. The genuinely-hard
residues are named honestly (the FTPG for the `q=pᵉ` field twist; the quadric Nullstellensatz *only* for exact
`Aut`-naming; the seal's `Theorem41`/Spielman).

**★ Load-bearing reframe (verified 2026-07-04).** The four Route-C **seals** (`reachesRigidOrCameron_{affinePolar via
affinePolarAdapter, alternating, halfSpin, suzuki}`) carry **no citation** — they rest on the *proved* `separates`
certificates. The Route-C citations live **only in the F4 iso-invariance layer** (canonicalization / L1-combine
support), so discharging them is off the seal's critical path. Always check load-bearing scope before valuing a
discharge (methodology M2).

---

## 1. The methodology — suggested method to attempt a discharge

Distilled from the Suzuki win (§3.1) and the Route-C F4 analysis (§3.2). Apply in order; each step can end the attempt
early (either "discharged" or "genuinely hard, keep cited for now").

- **M1 — Verify the statement AS FORMED first (probe before proving).** Is it even true? In what scope? A citation can
  be true-but-mis-scoped, or false as literally written. *Suzuki:* `route_c_suzuki_determine_probe.py` confirmed the
  original `SuzukiFormsDetermine` was true for `q=8,32` (frame injective) and the forms were transcribed correctly —
  so the issue was *provability*, not correctness. *NondegQuadric:* the unrestricted `∀ Q R` form is **false** at
  `d=3,q=3` (`vanishDim=2`); the `p≠2, d≥4` scope is exactly the true range (`route_c_reconstruct_probe.py`). Never try
  to prove a citation you have not first pinned down empirically.
- **M2 — Locate where it is actually load-bearing (seal vs support).** A citation carried by a *support-layer* theorem
  (iso-invariance for the runtime, a cosmetic identification) is far lower priority than one in the *seal*. Check by
  reading the capstone signatures: does the headline theorem take the hypothesis? *Route C:* the seals take none — the
  three citations are only in F4. This alone may downgrade the target.
- **M3 — Look for a secretly-elementary reformulation.** Many "deep" citations hide an elementary identity once you
  change coordinates / enlarge the base / differentiate. *Suzuki:* the σ-twisted determiner looked like it needed
  `Sz(q)` 2-transitivity, but **second discrete derivatives** collapse each coordinate to a bare `x_i` (a formal char-2
  identity) once the base includes pairwise sums — see §3.1. The tell: run a **symbolic polarization probe**
  (`route_c_suzuki_symbolic.py`) to see whether difference operators drop the degree to something linear.
- **M4 — Weaken to what the consumer actually needs.** The consumer often needs *less* than the citation asserts.
  *F4:* it needs *iso-invariance of the recovered colour partition*, not "the vanishing space is 1-dimensional". The
  weaker "the vanishing space transports" is elementary (§3.2), and the full Nullstellensatz is needed only for a
  *different* goal (naming `Aut = AΓO(Q)` exactly, a C#/meta concern). Separate "what the Lean object needs" from "what
  the informal story says".
- **M5 — Name the honest hard core.** If after M1–M4 a genuine classical theorem remains (Nullstellensatz, FTPG, CFSG),
  say so, give its faithful source + a proof sketch + a rough effort, and keep it cited. Do **not** manufacture a vacuous
  or over-strong replacement (the `SchemeReproduced` vacuity trap): a discharge that proves a *false* or *trivial*
  predicate is worse than an honest citation.

---

## 2. The citation register

Every carried citation, its load-bearing scope, and discharge status. `#print axioms` on the capstones is the ground
truth for what is still carried (a discharged citation is *removed*, not merely proved-elsewhere).

| Citation (Prop) | Where carried | What it is / faithful source | Load-bearing? | Discharge status |
|---|---|---|---|---|
| **`Suzuki.SuzukiFormsDetermine`** | *(removed)* `RouteCFormAdapters` §Suzuki | σ-twisted ovoid determiner; was Suzuki 1962 / `Sz(q)` 2-trans | was Route-C Suzuki `separates` | **✅ DISCHARGED 2026-07-04** — proved outright (§3.1). Deleted. |
| **`NondegQuadricDeterminesForm`** | `RouteCFormAdapters` — **now only** the `|Aut|`-naming `recoveredForm_colouring_equivariant` (scalar-`μ`); **no longer** the F4 partition object | quadric Nullstellensatz: nondeg quadric cone ⟹ form unique up to scalar (`p≠2,d≥4`); Hirschfeld | **`|Aut|`-naming only** (F4 iso-invariance discharged) | **◑ F4 DISCHARGED — BANKED (§3.2, 2026-07-05)** — the F4 partition iso-invariance is now citation-free (`recoveredForm_partition_isoInvariant`, vanishing-space transport). Full Nullstellensatz still carried only for exact `Aut`-naming (C#/meta). |
| **`JointVarietyDeterminesFamily`** | `RouteCFormAdapters` — **now only** the `|Aut|`-naming `recoveredFamily_colouring_equivariant` (injective-`Φ`); **no longer** the F4-multi partition object | projective normality of Grassmann/spinor variety (span{Q_k} = deg-2 vanishing ideal) | **`|Aut|`-naming only** (F4-multi iso-invariance discharged) | **◑ F4 DISCHARGED — BANKED (§3.2, 2026-07-05)** — same vanishing-space route (`recoveredFamily_partition_isoInvariant_vanishing`, generic core `recoveredForm_partition_isoInvariant_gen`). Injective-`Φ` still carried only for `Aut`-naming. |
| **`ConePreservingCollineationIsSemiSimilitude`** | `RouteCFormAdapters` §F2 (`…_semilinear`) | fundamental theorem of projective geometry (collineations are semilinear) + quadric uniqueness; Artin, *Geometric Algebra* | **F2 only** (`q=pᵉ, e>1`) | **✗ HARD (§3.3)** — FTPG genuinely deep; not elementarily dischargeable. Vacuous at `q=p` (`σ=id`). Keep cited for now. |
| **`AffineSchemeTwoClosed`** | `RouteCSeam.lean` (`schemeAutGroup_affineScheme_eq_affineG` / `routeC_polySupport`) | rank-3 affine 2-closure: `SchemeAutGroup(affineScheme G₀) ≤ affineG G₀` (no unexpected automorphisms); Skresanov arXiv:2007.14696 / 2202.03746. Converse `≥` is **proved** (`affineG_le_schemeAutGroup`). | Route-C coarse-Aut pinning (the `\|Aut\|` side / meta poly) — **one named premise, all four families** via `G₀ := similitudeGroup Q` / `jointConeStab Qs` / Suzuki cone-stab | **○ CITED** — Skresanov rank-3 2-closure; formalizable, off the near-term path. Same instance as the Skresanov row below, now a concrete named Lean `Prop`. |
| **`Theorem41Statement`** | `CoherentConfig.lean` (affine-slice / seam capstones) | Ponomarenko arXiv:2006.13592 §4 (pointed separability) | seal (affine slice) | **○ PLANNED** — the separability substrate is the intended proof (Stage 3); see `chain-descent-general-cc-separability.md`. |
| **`hSpielman` (`SeparatesAtBoundedBase`)** | `Cascade.lean` (`…viaSpielman`) | Spielman STOC 1996 primitive-SRG discretization (sub-exp floor `exp(Õ(n^{1/5}))`, BCSTW FOCS'13) | the citable sub-exp floor | **○ OPTIONAL** — a genuine large WL/SRG result; off the critical path (δ′/rainbow routes bypass per-family). |
| **`hcatch`** (CFI-1992 dimWL) | seal capstones | Cai–Fürer–Immerman 1992 Thm 5.2 | collapses to the `s(C)` core | **≈ MOOT** — not a real external citation; = the project's own open core in disguise (remaining-work §1). Free where 1-WL discretizes. |
| **`PrimitiveCCClassification` (G3)** | all seal capstones (`hClassify`) | Babai ITCS'14 / J.Alg'15 / Kivva JCTB'24 / Sun–Wilmes — the Cameron classification (CFSG) | the "or Cameron" escape | **KEEP CITED** (policy) — CFSG-based; the one citation allowed to stay. |
| Skresanov / Liebeck / Ponomarenko-cyclotomic-2-sep | affine-slice / seam (remaining-work §3a) | rank-3 2-closure / primitive-group / cyclotomic 2-sep | seal (schurian affine residue) | **○ CITED** — real classical results; formalizable, off the near-term path. |

*(`hSmallAutThin` and `hImprim` are **not** citations — the first is the open research core, the second is deferred
Lean infra (block tower). See remaining-work §1. `SparseSeparable`/`Separable`/`DepthOneSeparable` are project
*definitions*, not carried citations.)*

---

## 3. The discharge routes found

### 3.1 `SuzukiFormsDetermine` — DISCHARGED (the template)

**The win, and why it generalizes.** The Suzuki `separates` looked like it needed `Sz(q)` 2-transitivity (a deep
classical-group fact). It did **not**: the σ-twisted determiner is an **elementary char-2 identity** once the base is
right. Method (the M1→M3 playbook in action):

1. **M1 verify:** `route_c_suzuki_determine_probe.py` — the original first-order frame `{0,eⱼ}` is injective for `q=8,32`
   and the Lean forms cut the cone exactly (455/31775). So the citation was *correct*, just heavy to prove.
2. **M3 reformulate:** `route_c_suzuki_symbolic.py` computed the **second discrete derivatives** `Dᵢ Dⱼ SF_k(v) :=
   SF_k(v)+SF_k(v−eᵢ)+SF_k(v−eⱼ)+SF_k(v−eᵢ−eⱼ)` over `GF(2)[x, σx]`. Result: **degree collapses to 1**, and the σ-terms
   + constants **cancel in char 2**, leaving a bare coordinate: `x₂=D₀D₁ SF0`, `x₃=D₀D₁ SF1`, `x₀=D₁D₃ SF1`,
   `x₁=D₂D₃ SF4`. Verified exact over GF(8) (all 4096) and GF(32).
3. **Discharge:** enlarge the base from `{0,eⱼ}` (5 pts) to include **pairwise sums** `{0,eᵢ,eⱼ,eᵢ+eⱼ}` (8 pts, still
   `O(d²)` poly). Then `separates` is a formal identity, valid over **any `CharP K 2` ring** — no citation, no `hσ`, no
   field-size. Lean: scalar `SF0_recover`/`SF1_recover_x3`/`SF1_recover_x0`/`SF4_recover_x1` (`simp`+`ring_nf`+char-2
   close), their `SFv`-lifts `recover_x0..x3`, and the proved determiner `suzukiForms_determine` (`funext` over `Fin 4`,
   one recovery per coordinate). `reachesRigidOrCameron_suzuki` is now citation-free, axiom-clean.

**The transferable lesson:** a "separates / determiner" citation is often secretly a **finite-difference identity** —
enlarge the base until the recovery becomes linear, then it is elementary. Run the symbolic polarization probe first.
*(This exact trick did NOT transfer to the other three — they are Nullstellensatz/normality, not difference identities;
see §3.2 for their different route.)*

### 3.2 `NondegQuadricDeterminesForm` + `JointVarietyDeterminesFamily` — F4 DISCHARGED, BANKED (vanishing-space transport)

> **★ STATUS (2026-07-05): the F4 discharge below is now BANKED, axiom-clean, in `build.sh`.** The "moderate refactor,
> not yet done" note at the end of this section is **DONE** — the five lemmas
> (`vanishingForm_transport_gen`, `recoveredForm_partition_isoInvariant_gen` + its single/multi specializations
> `recoveredForm_partition_isoInvariant` / `recoveredFamily_partition_isoInvariant_vanishing`, and the refinement fact
> `vanishingColour_refines_form`) are in `RouteCFormAdapters.lean` and prove the recovered colour partition
> iso-invariant with **no citation**. One design refinement vs. the original sketch: rather than *redefining* the
> colouring object, the payoff is stated directly as a **partition-invariance iff** over the whole vanishing space
> `W(C)` (two pairs `W(C)`-indistinguishable in the source ⟺ their `g`-images `W(C')`-indistinguishable), which is
> exactly what "the recovered colouring is a canonical refinement" means and needs neither a basis choice nor a
> dimension count. The scalar-`μ` / injective-`Φ` theorems (`recovered{Form,Family}_colouring_equivariant`) are kept as
> the strictly-stronger `|Aut|`-naming statements and still carry the two citations — the intended residual scope.


**The reduction.** Both citations assert *"the degree-2 forms vanishing on the variety = the expected span"* (`⟨Q⟩`
for the single quadric; `span{Q_k}` for Grassmann/spinor) — the projective Nullstellensatz / projective normality.
That is a genuine classical theorem with **no elementary trick** (unlike Suzuki). **But (M4) F4 does not need it.**

**What F4 actually needs, and the elementary discharge.** F4's job is *iso-invariance of the recovered colour
partition*. The **whole degree-2 vanishing space `W`** of the cone (= the connection set from the origin) is an
**intrinsic** invariant of the graph. A graph iso whose linear part `g` preserves the cone induces a canonical linear
**iso** `W' ≅ W` by pullback `F' ↦ F'∘g` — needing only cone-preservation + `g` bijective, **no dimension count**.
This compiles (verified in `RouteCFormAdapters` context, axiom-clean):

```lean
-- pullback of a form vanishing on cone(Q') vanishes on cone(Q)  (the load-bearing half)
theorem vanishingForm_transport (Q Q' : QuadraticForm R M) (g : M ≃ₗ[R] M)
    (hcone : ∀ v, Q v = 0 ↔ Q' (g v) = 0)
    (F' : QuadraticForm R M) (hF' : ∀ v, Q' v = 0 → F' v = 0) :
    ∀ v, Q v = 0 → (F'.comp (g : M →ₗ[R] M)) v = 0 := by
  intro v hv; rw [QuadraticMap.comp_apply]; exact hF' (g v) ((hcone v).mp hv)
-- and the symmetric `_inv` (via g.symm) gives W' ≅ W
```

Colouring by a basis of `W` is then (i) **iso-invariant** (transports by the invertible matrix of the pullback) and
(ii) **at least as fine as the `Q`-colouring** (since `Q ∈ W`), so `coords_determine` separation still fires. **At
`q=p` (prime), the graph iso's linear part is automatically linear** (`Gal(𝔽_p/𝔽_p)` is trivial), so this route
discharges **both** `NondegQuadricDeterminesForm` and `JointVarietyDeterminesFamily` from the F4 structural object.

**What remains genuinely cited (M5):** the full Nullstellensatz (`W = ⟨Q⟩`, i.e. `W` is *1*-dimensional) is needed only
to **name the recovered group as exactly `AΓO(Q)`** — the `|Aut|` / C#-runtime side, not the Lean iso-invariance
object. That single-quadric Nullstellensatz *does* have a semi-elementary finite-field proof (restrict to hyperbolic
planes: on a hyperbolic plane `H`, `R|_H` vanishing on the two axes forces `R|_H = c·Q|_H`; chase the constant `c`
across overlapping planes using `d ≥ 4` connectivity) — formalizable but moderate–large (needs Witt / hyperbolic-plane
plumbing). Keep it cited until the `|Aut|` side is built.

**To bank the F4 discharge — ✅ DONE (2026-07-05).** Executed as: land the pullback `vanishingForm_transport_gen`
(generic in the cone predicate `C`, so one lemma serves both single quadric and multi-form family) and its `g.symm`
inverse (folded into the payoff proof); prove the **partition-invariance iff** `recoveredForm_partition_isoInvariant_gen`
(the pullback `W(C') ≅ W(C)` plays the role of the single-form scalar `μ` / multi-form `Φ` — but with no dimension
count); specialize to `recoveredForm_partition_isoInvariant` (single) and `recoveredFamily_partition_isoInvariant_vanishing`
(multi); prove separation-preservation via `Q ∈ W` (`vanishingColour_refines_form`). All five axiom-clean, in `build.sh`.
The old `recovered{Form,Family}_colouring_equivariant` are **kept** (not rewired) — they are the strictly-stronger
`|Aut|`-naming statements and legitimately still carry the two citations, needed only on the C# `|Aut|` side.

### 3.3 `ConePreservingCollineationIsSemiSimilitude` — HARD (keep cited for now)

This is the **fundamental theorem of projective geometry** (a cone-preserving collineation of `PG(d,q)`, `d≥2`, is
semilinear `g = M∘σ̂`) composed with the quadric uniqueness of §3.2. The FTPG is genuinely deep and **not**
elementarily dischargeable — and it is *essential* for `q=pᵉ, e>1`, because for a field-twisted `g`, `F'∘g` is not even
a `K`-form without the semilinear decomposition (so the §3.2 `W`-transport needs `g` linear, which fails at `e>1`). At
`q=p` it is the `σ=id` specialization and collapses to §3.2. **Verdict:** keep cited for now; it is the one hard residue of the
Route-C citation set, and only for the field-extension case (the prime-field residue does not need it).

### 3.4 Seal-track citations (pointers, not re-derived here)

- **`Theorem41Statement`** — intended proof = the general coherent-configuration **separability substrate**
  ([`chain-descent-general-cc-separability.md`](./chain-descent-general-cc-separability.md), Stage 3). Not an
  elementary discharge; it is a planned build.
- **`hSpielman`** — a real Spielman/BCSTW WL-SRG result; buildable but off the critical path (δ′/rainbow per-family
  routes bypass it). Discharge only if a uniform sub-exp floor is wanted in-Lean.
- **`hcatch`** — not a genuine external citation; collapses onto the project's own `s(C)` core (remaining-work §1). Free
  wherever 1-WL discretizes; "discharging" it = proving the core, not importing a theorem.
- **G3 (`PrimitiveCCClassification`)** — **stays cited** (CFSG). Do not attempt.

---

## 4. Pointers
- **The what-is-left census (citation table §2):** [`chain-descent-remaining-work.md`](./chain-descent-remaining-work.md).
- **Route C (where the Suzuki + F4 citations live):** [`chain-descent-route-c-plan.md`](./chain-descent-route-c-plan.md)
  (STATUS + §6 Suzuki + §4 decl map).
- **Suzuki discharge probes:** `route_c_suzuki_determine_probe.py` (M1 verify), `route_c_suzuki_symbolic.py` (M3
  polarization). **Nullstellensatz scope probe:** `route_c_reconstruct_probe.py` (`vanishDim=1` in range).
- **The separability substrate (Theorem41 route):** [`chain-descent-general-cc-separability.md`](./chain-descent-general-cc-separability.md).

---

*Maintenance: when a citation is discharged, move its row to "✅ DISCHARGED", delete the carried hypothesis, and
confirm the consumer capstone's `#print axioms` is unchanged (axiom-clean). Add new carried citations here when they are
introduced. Keep §3 route write-ups concrete (the Lean that compiles), so a future session can execute them.*
