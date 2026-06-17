# Remaining work — the living tracker (modulo set · citation replacement · IR solver)

> **What this is.** The single, top-level tracker for *what is left* before the seal is unconditional and the
> canonizer is complete. It collects, in one place: the seal's current **`modulo` set** and what each hypothesis
> really is; the **citations** to be replaced by proofs (and the one that may stay cited); the **buildable
> non-research infrastructure**; and the **IR-blind-spot solver** (the forward payoff). It is a map — the
> authoritative state is each capstone's `#print axioms`, [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md),
> and the linked deep-dive docs' STATUS blocks. Quality bar throughout: axiom-clean
> `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`, `native_decide` banned.

---

## STATUS (read first)

**The headline (2026-06-17).** The seal `reachesRigidOrCameron` is assembled and axiom-clean. Its live canonical
capstone `reachesRigidOrCameron_viaBoundedMinMult` stands **`modulo {G3 + hSmallAutThin + hcatch + hImprim}`**. The
three cleanup passes this session (`hcatch`, the separation engine, `hImprim`) reached a consistent conclusion:

> **The three non-G3 hypotheses are facets of ONE open object — the residue/constituent WL-recovery (`s(C)`) core —
> not four independent gaps.** In honest substance the seal is **`modulo {G3 + [one WL-recovery / s(C) core]}`.**

So "what's left" is short: **one research core** (conditional on the cited classification G3), plus a small amount of
**citation-formalization** and **one buildable infrastructure piece** (`EdgeGeneratesFromSet`), and the **forward IR
solver** (gated on the same core). There is **no long cleanup list**.

---

## 1. The `modulo` set — what each hypothesis is, and its true status

The live capstone is `reachesRigidOrCameron_viaBoundedMinMult` (CascadeAffine §S-gate2). Capstone map:
[`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md) seal section.

| Hypothesis | What it is | True status | Collapses to |
|---|---|---|---|
| **G3** (`hClassify`, `PrimitiveCCClassification`) | "large primitive ⟹ Cameron section" — the cited classification | **Citation** (Babai/Sun–Wilmes/Kivva). The one citation that *may stay cited* (CFSG-based). | — (kept) |
| **hSmallAutThin** | "small-Aut primitive residue ⟹ bounded `minMult`" = thick⟹large-Aut | **The research core** (node 4). Sub-exp: citable (Spielman). Poly: open, GI-adjacent, no witness. | the core |
| **hcatch** | "1-WL cell ⟹ 2-WL fiber" = CFI-1992 Thm 5.2 (dimWL exchange) | At a complete extension `⟺ warmRefine discrete`. Free where 1-WL discretizes; residual = the `s(C)` certificate. | the core (§9.9.14–15) |
| **hImprim** | "imprimitive ⟹ block-recovered ∨ abelian-consumed" | Block-tower infra **built**; content = constituent WL-recovery (A2-ii), one tower-layer down. | the core (§9.9.16) |

**The collapse, precisely.** `hcatch` (1-WL↔2-WL exchange) and `hImprim` (constituent recovery) both reduce, via
landed machinery, to the same content as `hSmallAutThin`: *does the bounded-depth relation-count profile separate the
residue's orbits at a bounded base?* — the `s(C)` self-detection certificate (`RelCountsDetermineOrbit` /
`PersistentTwinYieldsBlock`). Deep-dives: [`chain-descent-a2-potential-route.md`](./chain-descent-a2-potential-route.md)
§9.9.14 (hcatch), §9.9.15 (the engine), §9.9.16 (hImprim).

**Citation-free / lighter endpoints already landed** (use these where the family fits — they carry *less*):
- `…viaRainbowRank` — rank-≥4 amorphic (rainbow-rigid) families, `modulo {G3 + hImprim}`, **no hcatch/largeness**.
- `…viaSpielman` — the **fully-citable, Cameron-free sub-exp floor**, carries only `hSpielman` (no G3/hImprim).
- `…viaG0powNeg` / `…viaG0powNeg`-family — the affine `H={±1}` family, δ′ closure **discharged** (not carried).
- `…viaCompleteBase` / `…viaBoundedMultiplicity` — node-2 discrete-base pipeline, `modulo {G3 + hcatch + hImprim}`.

---

## 2. Citation replacement — the table

Policy (user): **eventually all citations except maybe Babai (G3/CFSG) are to be fully built in Lean.** A citation is
carried as a labeled hypothesis (never a fresh `axiom`), so the build stays axiom-clean; "replacing" it means proving
it in-project and discharging the hypothesis.

| Citation | Where carried | Faithful source | Replace? | Notes |
|---|---|---|---|---|
| **G3 — primitive-CC / Cameron classification** | `hClassify` (all capstones) | Babai ITCS 2014 (rank 3) + J.Algebra 2015 (II); Kivva JCTB 164 (2024) (rank 4); Sun–Wilmes (`exp(n^{1/3})` threshold) | **Maybe not** (CFSG-based — the one allowed to stay cited) | The "or Cameron" escape. |
| **CFI-1992 Thm 5.2 — dimWL exchange** | `hcatch` | Cai–Fürer–Immerman 1992 Thm 5.2; Ponomarenko arXiv:2006.13592 eq. (41) | **Yes**, but largely **moot for the residue**: collapses onto the `s(C)` core; needs a `dimWL` framework to state verbatim. | Free where 1-WL discretizes. |
| **Spielman — primitive-SRG discretization** | `hSpielman` (`…viaSpielman`) | Spielman, STOC 1996 (`Õ(n^{1/3})` base) | **Yes** (a genuine but large WL/SRG result) | Gives the honest sub-exp floor, Cameron-free. **DELTA (2026-06-17, lit. check):** the SRG-iso *floor value* is `exp(Õ(n^{1/5}))` (Babai–Chen–Sun–Teng–Wilmes, FOCS 2013); `n^{1/3}` is the broader-PCC bound. Spielman's *individualize-to-discrete-at-base* form is what `hSpielman` consumes; confirm BCSTW gives a base statement before re-citing. See route §9.9.17 / [[reference_srg_wl_literature_2026-06-17]]. |
| **Affine cyclotomic 2-separability** | `…affineSlice` | Ponomarenko arXiv:2006.13592 Thm 1.1 | **Yes** — superseded for sub-families by the citation-free δ′/rainbow routes (`viaG0powNeg`, `viaRainbowRank`). | |
| **Babai SRG structure (node-4 form)** | `hSmallAutThin` | Babai ITCS 2014 + Kivva (the *structure*, at sub-exp threshold) | **= the research core** — at poly threshold it is *open*, not a citation. | The wall. |

**Net:** the only citation expected to remain is **G3 (Babai/CFSG)**. `hcatch`/`hImprim` are not really "citations to
replace" — they are the project's own `s(C)` core in disguise (§1). Spielman and the affine 2-sep are genuine
citations that *can* be built but are not on the critical path (the δ′/rainbow routes already bypass them per-family).

---

## 3. The remaining work items (categorized)

### 3a. The research core — `hSmallAutThin` / the `s(C)` certificate (node 4)

> **★ MAJOR REFRAME (2026-06-17, route §9.9.18, Skresanov): node-4-SCHURIAN is AFFINE, not uncited open math.**
> A schurian rank-3 residue has `Aut(X)=G^(2)` = a primitive rank-3 group; Cameron's trichotomy + small-Aut (kills
> almost-simple/grid as large) ⟹ **only affine survives**; Skresanov [arXiv:2007.14696/2202.03746] pins `G^(2)` affine.
> Merged with §9.9.9b (non-affine amorphic = non-schurian): **every small-Aut primitive *schurian* residue is affine**,
> hence in the domain of the affine slice. This moves node-4-schurian from "uncited open" to the citation stack
> `{G3 + Liebeck + Skresanov + Ponomarenko-cyclotomic-2-sep + finite exceptions}` — the "conditional on citations" goal,
> at the cost of citations beyond G3. The genuinely-uncited "thick wall, no witness" is a **non-schurian** abstract-SRG
> phenomenon that **cannot be a WL-closure residue**. **PENDING:** (C1) the forms-graph affine classes (e.g. bilinear
> `H_q(2,m)`, small-Aut + non-geometric + affine-but-not-cyclotomic) need a non-cyclotomic separability citation — the
> main open hole; (C3) confirm the seal residue is the WL-closure `Inv(G^(2))`. Until (C1)/(C3) clear, treat node 4 as
> "reduced-to-affine modulo verification," not closed.

**One object, three faces** (the residue, the 1-WL↔2-WL exchange, the imprimitive constituents). The open question:
*does the bounded-depth relation-count profile separate the small-Aut primitive residue's orbits at a bounded base?*
- **Status:** open, GI-adjacent. No constructible falsifier across every probe (sporadics, trivial-Aut, cospectral
  mates, Doob/Hamming twists, k-WL ladder — all negative). Not directly attackable by covers/regularity/WL-level/twists
  (all closed, §9.9.10–12). The honest characterization: *is the WL-dim gap `base − b(Aut)` bounded for the residue?*
- **Intended discharge:** ~~the fusion / closed-subset closure (`schemeEquiv_trans`) for `PersistentTwinYieldsBlock`~~
  **— CORRECTED (2026-06-17, route §9.9.17): the block escape is VACUOUS on the primitive floor** (a primitive scheme
  has no nontrivial proper `ClosedSubset`, so `PersistentTwinYieldsBlock` collapses to `¬Separates → IsLarge`;
  lemma `persistentTwinYieldsBlock_iff_yieldsLarge_of_primitive`). The fusion-closure block construction discharges
  only the *imprimitive* case (already `hImprim`). The primitive crux is irreducibly the **2-closure deficiency**
  `G^(2)_T / G_T` = `s(X)` wall, with no block shortcut. Project verdict unchanged: *won't close from Mathlib alone.*
- **The closure angle, precisely (route §9.9.17):** the open content factors as (A) `Separable` + (B) the transport
  + (C) a bounded group base; **(C) is FREE** (`exists_greedy_base_le_log`, `b(G)=O(log n)` for small Aut). The open
  (A)+(B) = *the point extension recovers Aut-orbits at a bounded base* = no 2-closure deficiency. Its group-theoretic
  form is **Skresanov's rank-3 2-closure** theory (`G^(2)` structure) — the closure-angle and Skresanov leads merge.
  **Concrete next:** test whether Skresanov's rank-3 `G^(2)` description trivialises the deficiency at a bounded base
  for the affine residue (an affine-rank-3 carve capstone, sibling to the cyclotomic slice). See [[reference_srg_wl_literature_2026-06-17]].
- **Floors available now:** sub-exp via `…viaSpielman` (fully citable, Cameron-free; floor value `exp(Õ(n^{1/5}))`, §2 DELTA).

### 3b. Buildable non-research infrastructure — `EdgeGeneratesFromSet`
The **checkable multi-base isolation closure** — the relation-count analogue of `dominatorReachable_of_rainbowRank`:
a structural sufficient condition that *produces* the `s(C)` separation certificate for a family (makes recovery
checkable). The single-base `EdgeGenerates` exists (`Scheme.lean`) but fails on cyclotomic/catalogue schemes; the
multi-base version is deferred ([`chain-descent-self-detection-plan.md`](./chain-descent-self-detection-plan.md) §9.3).
- **Status:** buildable, moderate; **not on the seal's critical path** (it adds checkability, not closure).
- It is the *one* shared piece behind the engine (§9.9.15) and `hImprim` (§9.9.16).

### 3c. Citation formalization (optional, off critical path)
- **Spielman** → fully built `…viaSpielman` (large WL/SRG result).
- **Affine cyclotomic 2-sep** → mostly superseded by δ′/rainbow per-family; build only if a uniform affine closure is wanted.
- **CFI-1992 dimWL exchange** → needs a `dimWL` framework; moot for the residue (§1). Lowest priority.

### 3d. Node-2 polish (optional)
A *uniform* rainbow rank for a parametric amorphic family (generalize `clebschZ4`/`clebschScheme` off `n=16`) →
feeds `…viaRainbowRank` / `…viaCompleteBase`. Honest scope (§9.9.9b): the schurian rainbow-rigid amorphic instances
are **affine** (leg-B-adjacent); the genuinely-new non-affine ones are non-schurian (not residues). So this is
citation-reduction on the affine amorphic slice, **not** new territory and **cannot** approach node 4 (rank-counting,
§9.9.9a). Low priority.

---

## 4. The IR-blind-spot solver (the forward payoff)
**Doc:** [`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md) (STATUS first).
Canonizes the **rigid** residue (incl. the multipede / IR-blind-spot that 1-WL cannot discretize) in polynomial time.
- **Gating:** its polynomiality is delivered by A2 (bounded WL-dim of the residue) — and the IR-solver's polynomiality
  and A2's last open quantity are **the same object in two languages**, so it is gated on the **same `s(C)` core** as §3a.
- **Status:** *solver not built;* prerequisites landed (deferral architecture, direction-blind canonizer substrate,
  the potential-descent engine `exists_potential_descent`, A2's consumer chain). Pick up once the core lands.
- It is the **downstream** of the seal: closing §3a unblocks both the unconditional seal *and* the IR solver.

---

## 5. One-screen summary

```
SEAL  reachesRigidOrCameron_viaBoundedMinMult   modulo {G3 + hSmallAutThin + hcatch + hImprim}
                                                  └──────────── collapses to ───────────┘
                                                  modulo {G3 (Babai, may stay cited) + ONE s(C) core}

REMAINING:
  3a  the s(C) / node-4 core .............. RESEARCH (open, GI-adjacent; sub-exp floor citable now)
  3b  EdgeGeneratesFromSet ................ BUILDABLE infra (checkability; off critical path)
  3c  citation formalization ............. OPTIONAL (Spielman / affine 2-sep / CFI dimWL; off path)
  3d  node-2 uniform rainbow rank ........ OPTIONAL (affine/leg-B; can't reach node 4)
  4   IR-blind-spot solver ............... FORWARD payoff, gated on the SAME core as 3a
```

**Bottom line:** the seal is one research core away from unconditional-modulo-Babai, with the IR solver as its
downstream — every other "gap" has been shown (this session) to be that same core in disguise, a built floor, or
optional off-path work.

---

*Maintenance: update §1's modulo table when a capstone's `#print axioms` carry-set changes; update §3 as items land;
keep the deep-dives (`chain-descent-a2-potential-route.md` §9.9.x, `-ir-blindspot-solver.md`, `-self-detection-plan.md`)
authoritative and this doc a one-screen map.*
