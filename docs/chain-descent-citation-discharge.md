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

**Headline (2026-07-04 … 2026-07-06).** Two citations are **fully discharged** (`SuzukiFormsDetermine` + now
**`NondegQuadricDeterminesForm`**, both Route C). `JointVarietyDeterminesFamily` is **discharged from the F4
iso-invariance object** — the vanishing-space transport of §3.2 is **BANKED** (axiom-clean, in `build.sh`; 5 lemmas in
`RouteCFormAdapters.lean`: `vanishingForm_transport_gen`, `recoveredForm_partition_isoInvariant{_gen,}`,
`recoveredFamily_partition_isoInvariant_vanishing`, `vanishingColour_refines_form`). The recovered colour partition is
proved iso-invariant with **no dimension count**, so it no longer gates F4; it remains carried **only** on the
strictly-stronger `|Aut|`-naming statement (injective-`Φ`), a C#/meta concern. The genuinely-hard residues are named
honestly (the FTPG for the `q=pᵉ` field twist; the seal's `Theorem41`/Spielman).

**★ `NondegQuadricDeterminesForm` FULLY DISCHARGED (2026-07-06, axiom-clean, in `build.sh`).** The 4 files ported →
`ChainDescent.Nullstellensatz{,Structural,Count,Hlink}` (Scratch prefix dropped). The **structural route** (not the
connectivity/`hconn` reroute — which needs a `k=4` cover that PROVABLY FAILS at the `d=4` elliptic `q=3` VO⁻₄(3)
boundary the citation's `p≠2` scope forces) is what closed it: the crux **`section_iso_count`** (exact isotropic-`u`
section identity, type-independent gap `(q−2)q²>0` at `q≥3`) feeds **`cone_punctured_span`** (hspan) +
**`aniso_polar_diameter_two`** (hlink) into `nullstellensatz_of_structural`, instantiated at `ZMod p` by
**`nondegQuadric_zmod_of_even`** = exact `NondegQuadricDeterminesForm p d` for **even `d`** (every `VO^ε_{2m}` use;
odd `d` open + unused). `RouteC.nondegQuadricDeterminesForm_of_even` proves the predicate; the `hcite` premise is
**deleted** from `recoveredForm_colouring_equivariant` (now carries only elementary `Even d`; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`). The old `nullstellensatz_of_connectivity`/`hconn` cut is kept as a
proven spare. **§3.5 = the design record.**

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
| **`NondegQuadricDeterminesForm`** | *(hcite removed)* — `RouteC.nondegQuadricDeterminesForm_of_even` proves it; `recoveredForm_colouring_equivariant` carries only `Even d` | quadric Nullstellensatz: nondeg quadric cone ⟹ form unique up to scalar (`p≠2,d≥4`); Hirschfeld | was `|Aut|`-naming only | **✅ DISCHARGED 2026-07-06** (axiom-clean, in `build.sh`). Ported → `ChainDescent.Nullstellensatz{,Structural,Count,Hlink}`. **Structural route** (not the `hconn` reroute — its `k=4` walk fails `q=3`): crux `section_iso_count` (exact isotropic-`u` section, gap `(q−2)q²>0`) → `cone_punctured_span` (hspan) + `aniso_polar_diameter_two` (hlink) → `nullstellensatz_of_structural` → `nondegQuadric_zmod_of_even` for **even `d`** (every `VO^ε_{2m}`; odd `d` open+unused). `#print axioms` = `[propext, Classical.choice, Quot.sound]`. `hconn` spare kept. |
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

### 3.5 `NondegQuadricDeterminesForm` — the full quadric Nullstellensatz — ✅ DISCHARGED (2026-07-06)

> **✅ DONE (2026-07-06, axiom-clean, in `build.sh`).** The text below is the DESIGN RECORD; it predates the final
> cut. What actually landed: the **structural route** (NOT the `hconn`/connectivity reroute this section explores — that
> needs a `k=4` cover which PROVABLY FAILS at the `d=4` elliptic `q=3` VO⁻₄(3) boundary). The crux was the *exact*
> isotropic-`u` section count `section_iso_count` (`ChainDescent.NullstellensatzCount`) — type-independent gap
> `(q−2)q²>0` at `q≥3` — feeding `cone_punctured_span` (hspan) + `aniso_polar_diameter_two` (hlink) into
> `nullstellensatz_of_structural`, instantiated at `ZMod p` by `nondegQuadric_zmod_of_even` for **even `d`** (every
> `VO^ε_{2m}` use; odd `d` left open + unused). Wired via `RouteC.nondegQuadricDeterminesForm_of_even`; the `hcite`
> premise is deleted from `recoveredForm_colouring_equivariant`. Files: `ChainDescent.Nullstellensatz{,Structural,Count,Hlink}`.

The §3.2 work discharged the **F4 iso-invariance** use of this citation. The *stronger* statement — "a nondegenerate
quadric determines its form up to a scalar `μ`" (`vanishDim = 1`, needed for exact `Aut = AΓO(Q)` naming) — is now being
proved outright. It is `NondegQuadricDeterminesForm` itself.

**Where it lives (two WIP scratch files, NOT in `build.sh`; each builds standalone):**
- `ChainDescent/ScratchNullstellensatz.lean` — the field-general heart + the assembly (`nullstellensatz_of_structural`).
- `ChainDescent/ScratchNullstellensatzStructural.lean` — the finite-field structural build (isotropic existence →
  `isotropic_span`), which imports the first for `quad_lin_combo`.

Namespace `ChainDescent.Nullstellensatz` throughout. **Probes** (in `GraphCanonizationProofs/`):
`nullstellensatz_structural_probe.py` (isotropic-span, aniso-connectivity, `deg2_vanishDim = 1`) and
`nullstellensatz_hspan_hlink_probe.py` (punctured-cone span, aniso diameter-2).

**The elementary path (M3-style, probe-validated — avoids Witt).** Char `≠ 2` ⟹ a quadratic form ↔ its polar bilinear
form. For anisotropic `y` and isotropic `x`, restrict `Q` to the line `x + t·y`: a quadratic in `t` with roots `t = 0`
(giving `x`) and a second root giving another isotropic point `w = Q y·x − polar Q x y·y`. Since `Z(Q) ⊆ Z(R)`,
`R(w) = 0`; expanding gives the **line-restriction identity**. Reading it as a linear functional in `x`, it forces
`polar R (·) y = (R y / Q y)·polar Q (·) y` on the isotropic cone; the isotropic cone **spanning** `V` extends it to all
`x`, and **anisotropic connectivity** makes the ratio `R y / Q y` a global constant `μ`. Then `polar R = μ·polar Q ⟹
R = μ·Q` (char `≠ 2`), with `μ ≠ 0` from the *reverse* inclusion `Q y ≠ 0 ⟹ R y ≠ 0`.

**✅ LANDED (axiom-clean) — the mathematical heart AND the full assembly:**
- `quad_lin_combo` — `Q(c•x + d•y) = c²Qx + d²Qy + cd·polar Q x y` (the workhorse expansion).
- **`nullstellensatz_core`** — the `w`-construction, **ring-general**: `polar Q x y·(polar Q x y·R y − Q y·polar R x y)
  = 0` for isotropic `x`, any `y`. The genuinely non-obvious, reusable content; no field/finiteness/dimension.
- `nullstellensatz_pointwise` — field cancellation: `polar Q x y ≠ 0 ⟹ polar Q x y·R y = Q y·polar R x y`.
- `form_eq_of_polar_eq_smul` — `polar R = μ·polar Q ⟹ R = μ·Q` (char `≠ 2`, via `polar_self`; a spare — the finish
  below uses the cleaner case-split instead).
- **`nullstellensatz_of_structural`** — **the ASSEMBLY, axiom-clean.** Reduces the full μ-scalar conclusion to the two
  structural facts below. Structure (all elementary, all proved): `nullstellensatz_core` rewrites as
  `polar Q x y · L_y(x) = 0` with `L_y(x) := Q y·polar R x y − R y·polar Q x y` **linear in `x`**; on the punctured
  cone (`hspan`) `L_y ≡ 0` by `Submodule.span_induction`, giving the per-`y` identity `Q y·polar R x y = R y·polar Q x y`
  ∀x (`key`); two `polar`-linked anisotropic vectors then share the ratio `R/Q` (`step`); the diameter-≤2 link
  (`hlink`) makes it a global constant (`const`); and `R v = μ Q v` follows by a **case split** — `Q v = 0 ⟹ R v = 0`
  (cone) `= μ·0`, else constancy — so no `polarBilin`-extension or anisotropic-span is needed. `μ ≠ 0` (⟹ `Kˣ`) from the
  reverse cone inclusion. Existence of an anisotropic vector comes from `not_nondegenerate_zero`.

**★ REROUTE (2026-07-05) — `hspan` ELIMINATED; the citation is now ONE fact (`hconn`).** The observation: the assembly's
per-`y` identity `key` (which needed `hspan`) is only ever evaluated at ANISOTROPIC vectors, and the finish needs only
that the ratio `μ_w := R w / Q w` is **constant on anisotropic `w`** — no polar-form extension, no spanning. The new
`nullstellensatz_of_connectivity` (axiom-clean) captures exactly this:
- **`ratio_step`** (axiom-clean, from `nullstellensatz_pointwise` — NO structural input): for isotropic `a` with
  `polar Q a y ≠ 0`, `μ_{y+a} = μ_y` (i.e. `R y·Q(y+a) = R(y+a)·Q y`). The engine that spreads `μ`.
- **`ratioEdge` / `ratio_step_edge` / `ratio_const_of_reflTransGen`** (axiom-clean) — package the step as a graph edge
  `a — b` (`b` anisotropic, `b−a` isotropic, non-tangent) and propagate constancy along any PATH via
  `Relation.ReflTransGen`.
- **`hconn` (THE ONE REMAINING FACT)** — the isotropic-edge graph on anisotropic vectors is **CONNECTED**:
  `Relation.ReflTransGen (ratioEdge Q)` joins any two anisotropic vectors. **Probe result** (`nullstellensatz_hconn_probe.py`,
  2026-07-05): 1 component, **diameter 3–4 for `VO^±_{4,6}(3,5,7)` INCLUDING the `d=4` elliptic `q=3` boundary** — the
  exact regime where `hspan` was hard, so the obstruction is genuinely gone (connectivity is TRUE there). **Correction to
  the first cut:** diameter-2 (a single common `m`) is FALSE (probe: ~50% of pairs have no 2-step join even at `d=6`); the
  fact is genuine connectivity, not a fixed diameter. Discharge routes: an explicit bounded walk (hyperbolic-plane hub —
  connect any anisotropic `y` to a fixed reference through the plane `⟨e,f⟩`), or the `GaussCount` `count2_eq_charsum` /
  `card_quadForm_eq` point-count for edge/step existence (after diagonalizing to the anisotropic basis it needs).

**Superseded (kept as proven spares, OFF the critical path):** the old two-fact reduction `nullstellensatz_of_structural`
(needs `hspan` + the old `hlink`) and its bedrock `isotropic_span` / `exists_isotropic_of_nondegenerate` /
`exists_hyperbolic_partner` remain axiom-clean in `ScratchNullstellensatzStructural.lean` — a valid alternative
reduction, but no longer the live route (`hspan` was the hard `d=4`-elliptic fact).

**Structural-facts build (in `ScratchNullstellensatzStructural.lean`). The citation quantifies over ARBITRARY nondeg
`Q`, so this is the general finite-field statement.**

- ✅ **BEDROCK DONE (2026-07-05, axiom-clean) — isotropic-vector existence.** `exists_isotropic_of_nondegenerate`: a
  nondegenerate `Q` in `dim ≥ 3` over a finite field of odd order has a **nonzero isotropic vector**. Route (chosen over
  Chevalley–Warning, which would need a missing `QuadraticForm → MvPolynomial` bridge): **diagonalize**
  (`equivalent_weightedSumSquares_units_of_nondegenerate'`) → find an isotropic vector for the unit-weighted sum of
  squares (`weightedSumSquares_isotropic`, the `(α,β,1,0,…)` vector with `α,β` from **`binary_represents`** =
  `A x²+B y²=c` solvable via `FiniteField.exists_root_sum_quadratic`) → transport back along the isometry. Plus the
  bridge `separatingLeft_associated_of_polarBilin_nondeg` (`polarBilin.Nondegenerate ⟹ (associated Q).SeparatingLeft`).
- ✅ **`exists_hyperbolic_partner`** (2026-07-05, axiom-clean) — an isotropic `v ≠ 0` has an isotropic `f` with
  `polar Q v f = 1` (nondeg ⟹ ∃ `u`, `polar Q v u ≠ 0`; rescale + correct by `Q u' • v`).
- ✅ **`isotropic_span`** (2026-07-05, axiom-clean) — the isotropic vectors span `V` (dim ≥ 3). Clean proof from ONE
  hyperbolic pair: for any `u`, `w := t·v + s·f + u` is isotropic for `s := 1 − polar Q v u`, `t := −(Q u + s·polar Q u f)`,
  so `u = w − t·v − s·f ∈ span{isotropic}`. Holds even at the `d = 4` elliptic boundary (uses one pair, not a Witt
  decomposition).
- ◻ **REMAINING — `hspan` and `hlink`.** Both hinge on the **Witt-index-1 / `q = 3` boundary**: at `d = 4` elliptic there
  are no two orthogonal independent isotropic vectors, so the "add an orthogonal punctured isotropic" trick (`hspan`) and
  the small-`q` in-plane constructions (`hlink`) both fail — they need the ambient `d ≥ 4`.
  - `hlink` (anisotropic `polar`-diameter ≤ 2) — a **point-count** works: `z ∉ y^⊥ ∪ y'^⊥ ∪ cone` exists when
    `q^d > 2q^{d-1} + |cone|` (exact for VO⁻₄(3): `81 > 27+27+21`). Needs a quadric cone-size bound — the project's
    `GaussCount` machinery (`card_quadForm_eq`) is the likely source, generalized to arbitrary nondeg `Q`.
  - `hspan` (punctured isotropic cone spans) — a structural argument (the punctured cone still spans despite the removed
    tangent section); the cleanest route is TBD (⊥-argument stalls at Witt-index 1; a counting/dimension argument may work).
  The assembly guarantees these two facts are all that is missing.
`vanishDim = 1` (`deg2_vanishDim` in the probe) is the sanity target the finished theorem reproduces.

**▶ VERIFY (fresh-reader notes).** `cd GraphCanonizationProofs` first.
- Build: `lake build ChainDescent.ScratchNullstellensatz ChainDescent.ScratchNullstellensatzStructural` (~5s; both green).
- Axioms: write a temp file importing `ChainDescent.ScratchNullstellensatzStructural` (it re-exports everything) with
  `#print axioms nullstellensatz_of_structural` / `exists_isotropic_of_nondegenerate` / `isotropic_span`, then
  `lake env lean /path/to/check.lean` — expect `[propext, Classical.choice, Quot.sound]` for each.
- Probes: `python3 nullstellensatz_structural_probe.py` and `python3 nullstellensatz_hspan_hlink_probe.py`.

**▶ NEXT ACTIONABLE STEP (rerouted).** `hconn` (graph connectivity) is now reduced — by the **route-(A) scaffold**
(`ratioEdge_symm` + `reflTransGen_ratioEdge_symm` + `hconn_of_hub`) and the **edge primitives** (`ratioEdge_smul`,
`ratioEdge_line`), all axiom-clean — to a single classical **counting lemma**:
> **`cone_not_covered`** — nondeg `Q` on `𝔽_q^d` (`d ≥ 4`, `q` odd not tiny), vectors `u₁,…,u_k` (`k ≤ 3`) ⟹ ∃ isotropic
> `a` with `polar Q uᵢ a ≠ 0` ∀`i` (the isotropic cone is not covered by `k` hyperplanes `uᵢ^⊥`).

With it, each walk step is exhibited via `ratioEdge_smul`/`_line` and the hub/`hconn` close. **Two findings:**
- **Elementary shortcuts RULED OUT** (each recurses to `cone_not_covered`): route (A)'s fully-explicit walk still needs
  an isotropic direction avoiding 2–3 hyperplanes per step; single-hyperplane avoidance is free from `isotropic_span`
  but ≥2 is not; the **fiber-scaling** shortcut fails by exactly the Gauss error term (`nullstellensatz_fiber_probe.py`:
  the tangent fiber can exceed the generic fiber by `~q^{d/2−1}`).
- **Unification:** `cone_not_covered` is *equivalent to the old `hspan`* (`hspan` = its `k=2`/`∀w` case), so proving it
  ALSO closes the spare `nullstellensatz_of_structural`. One lemma discharges both routes.

**Route (= route B), and the project ALREADY HAS the hard machinery.** `ChainDescent.zeroCount_sq_le` (`PairForm.lean`)
bounds, for ANY quadratic `P`, `(|{P=0}|·q − qᵈ)² ≤ (q−1)²·(qᵈ·|radical P|)` — the norm-based count bound, already
axiom-clean, no from-scratch ℂ-magnitude work needed. Bricks (in `ScratchNullstellensatzCount.lean`):
- ✅ **`radical_card_one`** + **`cone_card_lower`** (2026-07-06, axiom-clean) — nondeg ⟹ radical `{0}` ⟹
  `qᵈ − (q−1)√(qᵈ) ≤ |cone|·q`, i.e. `|cone| ≥ q^{d-1} − (q−1)q^{d/2−1}`. Direct from `zeroCount_sq_le`.
- ✅ **`card_zeros_odd`** (2026-07-06, axiom-clean) — the reusable heart: nondeg quadric in ODD dim `m` ⟹
  `|{Q=0}|·q = |V|` exactly (the `card_quadForm_eq` bracket `∑χ(t)=0` for odd power). In `ScratchNullstellensatzCount.lean`.
- ✅ **`sec_aniso`** (2026-07-06, axiom-clean) — for anisotropic `u`, `|{Q x=0 ∧ polar Q u x=0}|·q·q = |V|` (section
  `= q^{d-2}`, EXACT). `card_zeros_odd` on `(u^⊥, Q|_{u^⊥})`: `V = ⟨u⟩ ⊕ u^⊥`, `polar Q u x=0 ⟺ x∈u^⊥`; `Q|_{u^⊥}` nondeg
  proved DIRECTLY (via `V = ⟨u⟩ + u^⊥`); `finrank u^⊥ = d−1` odd via `Module.Dual.finrank_ker_add_one_of_ne_zero`.
  (Isotropic-`u` sections vary — **avoided** by using aniso vectors only.)
- ✅ **`cone_not_covered`** (2026-07-06, axiom-clean) — k=2, both `u₁,u₂` anisotropic: ∃ isotropic `a` non-tangent to
  both. Union bound `|cone| > 2·q^{d-2}` (nlinarith over ℝ; needs `finrank ≥ 4`, `q ≥ 3`, even finrank) — **no small-`q`
  tail** (exact sections).
- ◻ **the walk/hub → `hconn`** (structural, NO counting left): connect any two anisotropic `y,z` via `ratioEdge_smul/_line`
  + `cone_not_covered`. Subtle case `z−y` anisotropic: `cone_not_covered(y, z−y)` gives `a` with `s*:=Q(z−y)/polar Q(z−y)a`
  making `z−(y+s*a)` isotropic ⟹ 2-step `y —(y+s*a)— z` when `y+s*a` anisotropic (else perturb `a` / use the large good
  set, size `≥ q^{d-1}−2q^{d-2}`). Then `nullstellensatz_of_connectivity`.
Diagonalization (`equivalent_weightedSumSquares_units_of_nondegenerate'`, already used) supplies any basis needed.

When `hconn` (via `cone_not_covered` → hub) lands: (a) instantiate `nullstellensatz_of_connectivity` to prove `NondegQuadricDeterminesForm` outright
over `𝔽_q^d` (`d ≥ 4`, `q` odd); (b) **delete the carried premise** from `recoveredForm_colouring_equivariant` in
`RouteCFormAdapters.lean`, confirm `#print axioms` unchanged; (c) port the scratch files into `build.sh` (after
`RouteCFormAdapters`) and add decls to `PublicTheoremIndex.md`. Only then is this citation fully discharged.

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
