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
  `reachesRigidOrCameron` (currently conditional `modulo {G3 cited + G2-B open}`; every capstone *also* carries
  `hImprim`/G2-A undischarged — a separate, deferred Lean-infra piece). Closing **G2-B** is the open mathematical
  content; **this build is the one known route that closes it.**
- **G2-B is NOT "GI ∈ P, give up" — read §1A (below) before concluding any piece is hopeless.** "bounded base = bounded WL = GI∈P"
  conflates the *residue* with *all* schemes; every unbounded-WL family is carved into a separate leg (CFI→hImprim,
  abelian→leg B, large/hidden-Johnson→Cameron — this is *why* the last leg is "or Cameron"). The residue (primitive,
  small, non-abelian, non-Cameron) is the **tame remainder** — 0 empirical witnesses; isolation is the *method*
  (applied recursively), not a surrender. §1A has the full carve-out, the closure angle (separability / amorphic
  rainbow-rigidity), and the off-track falsifier.
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
- **CURRENT STATE (2026-06-12): Stage 0 DECIDED + Stage 1 LANDED — skeleton AND the §CC.8 point-extension
  construction** (`ChainDescent/CoherentConfig.lean`, axiom-clean, full build green) — the general `CoherentConfig`
  type (colour-function presentation, fibers *derived*), the homogeneous coercion
  `AssociationScheme.toCoherentConfig` (conditional on the seal's `hne`), general-CC
  `AlgIso`/`Separable`/`SeparablePointed` (the §2 soundness gate resolved by *widening*), the probe-validated
  **Thm 4.1 hypothesis predicates** (no `Ωᵐ` needed to state them), the **cited `Theorem41Statement`** (the
  staging-fallback carry, G3 pattern), `IsPointExtension` as a universal property (+ `discreteCC` non-vacuity),
  and **the construction `pointExtension X T` discharging it constructively** (`isPointExtension_pointExtension` /
  `exists_isPointExtension` / `isPointExtension_unique` — the `ExtensionSeparable` family is never empty).
  All three gate probes RAN: Stage-3 conditions (Route β viable — Stage 3.2), the Stage-2.1 direction check
  (1-WL-twin keying refuted at arbitrary `T`; bases clean — item 2 below), and **the catch-up probe-gate
  (2026-06-12, item 5: GATE GREEN at every minimal base, `b(X) = b(G)` on both instances, the `c=1` dominator
  closure discretizes from every base at SCHEME level — Route δ's engine confirmed incidentally)**. **PLUS (2026-06-12, same day):
  STAGE 2 LANDED MODULO THE CATCH-UP and THE CITATION CHECKPOINT ASSEMBLED** — the pointed-conclusion transport
  (§CC.9, citation-free core) wired into the seal (§S-gate2), with the general conditional capstone
  **`reachesRigidOrCameron_viaExtensionSeparability`** standing modulo {G3 + cited `Theorem41Statement` +
  conditions-on-the-extension + the catch-up `WarmTwinsAreFiberTwins` + a base}; the homogeneous (A)/Lemma-2.6/Ωᵐ
  obligations DISSOLVED (items 3–4 below).
  **PLUS (2026-06-12, later): THE CITATION-FREE δ′ CHECKPOINT + STAGE-3 INCREMENTS 1–3 LANDED** (`CascadeAffine.lean
  §S-bridge`/`§S-bridge-δ`/`§S-stage3`/`§S-gate2`, all axiom-clean, build green). The δ′ **dominator-closure engine**
  gives a *second, lighter, citation-free* seal checkpoint **`reachesRigidOrCameron_viaDominatorClosure`** carrying
  only {G3 + `hImprim` + `hclo : ∀ v, DominatorReachable S T v`} — **this bypasses the catch-up
  `WarmTwinsAreFiberTwins` entirely** (it is now off every critical path). Stage 3 (proving `hclo` for the residue
  family) is the lone open mathematical content, and increments 1–3 have reframed it: the forced-triangle criterion
  is now general (any scheme) and reads group-theoretically as **`Stab(α)·γ ∩ Stab(β)·γ = {γ}`**
  (`dominatorReachable_step_of_stab`), and complete closure is `Aut(S)`-equivariant (`dominatorReachable_univ_image`,
  so prove at one representative base).
- **CURRENT FRONTIER (2026-06-13) — the δ′ Stage-3 toolkit is COMPLETE; the target is now the NON-AFFINE residue,
  and its closure CONSTRUCTION has been extracted.** Since the 2026-06-12 state above: the full δ′ closure toolkit
  landed (the iteration engine `dominatorReachable_of_rank`, the cyclotomic `F_q`-power and ratio step builders, the
  one-round criterion `dominatorReachable_of_basePinsAll`), and the **first end-to-end family closures** discharged
  `hclo` *outright*: `reachesRigidOrCameron_viaG0powNeg` (the `H={±1}` odd-char family — primitive at `d=1`; seal with
  `hclo` **proved, not carried**) and `dominatorReachable_G0pow_subfield` (the multi-round subfield `H=K^×` family —
  but **imprimitive**, i.e. hImprim's job, so engine-validation not new coverage). **Reframing (read §1A):** G2-B is
  the carved *tame* residue, not GI∈P; the affine cyclotomic slice is already citation-closed, so all the affine work
  removes a citation / validates the engine — **the genuine open target is the NON-AFFINE residue (ℤ₄² amorphic-NLS,
  `orbitalScheme`, no field coordinates).** Its forced-triangle closure construction is now **EXTRACTED by probe**
  (`Probe_ExtractPinningRank`, §8 entry 2026-06-13): **uniform, genuinely multi-round (depth 3, layers `[2,2,6,6]`),
  driven by RAINBOW-TRIANGLE RIGIDITY** — a triangle pins ⟺ its three edges are three distinct non-diagonal colours
  (the amorphic `S₃` made operational); ℤ₄² closes from a 2-base (96/120 pairs), ℤ₂⁴ needs ≥3 (char-2 obstruction).
  **THE CONCRETE ROUTE LANDED (2026-06-13): the FIRST NON-AFFINE δ′ CLOSURE IN LEAN**
  (`ChainDescent/ClebschConcrete.lean`, axiom-clean, no `native_decide`, in the serial build ~56s). The ℤ₄²
  amorphic-NLS Clebsch scheme is hard-coded as `clebschZ4Scheme : AssociationScheme 16` (axioms by `decide`, coherence
  split per-colour to dodge OOM), and `clebschZ4_closure` proves its forced-triangle closure exhausts Ω from `{0,1}`
  (`clebschZ4_discrete`: `b(X) ≤ 2`) — the seal's `hclo` **discharged concretely for a real non-affine primitive G2-B
  residue**. Scope: one scheme, parameter-scoped to Clebsch `(16,5,0,2)`; at `AssociationScheme` level (`Discrete`),
  does NOT feed the seal capstone (needs `SchurianScheme` = auts, deferred); `decide`-checked, not a family proof.
  **NEXT:** abstract the rainbow-rigidity closure into a parameter-scoped family lemma, OR wire a `SchurianScheme`
  instance to feed the seal capstone, OR return to the general/primitive open core. **Per-increment history is in §8.**
  **REMAINING — the original Stage-1/2/3 handoff list (now HISTORY; the current frontier is the line above):**
  1. ~~**Stage 1.2(a)+(b)**~~ — **LANDED 2026-06-12 (`CoherentConfig.lean §CC.8`, axiom-clean, build green):
     the point-extension *construction* `pointExtension X T` (pair-refinement saturation on
     `Setoid (Fin n × Fin n)`, representative-indexed counts, `n²`-round pigeonhole) with
     `isPointExtension_pointExtension` discharging the universal property constructively +
     `exists_isPointExtension` (the family is never empty — `ExtensionSeparable` non-vacuous) +
     `isPointExtension_unique` (uniqueness up to mutual refinement).** Open from old 1.2: only the
     warmRefine↔fiber *bridge* — now reshaped by the direction check (item 2): state it at bases / via the
     `dimWL` +1 exchange, NOT as cells=fibers at arbitrary `T` (refuted on the bullseye).
  2. ~~**Stage 2.1's direction check**~~ — **RAN 2026-06-12 (`Probe_Stage21_DirectionCheck_CellsVsFibers`, green):
     the naive twin⟹alg-iso step is REFUTED at arbitrary `T`** — on the ℤ₄² bullseye at `T={0}`, 1-WL has 4 cells
     vs **10 fibers** (strictly finer), and 24/30 same-cell pairs have WL-INEQUIVALENT extensions (cells ⊋ orbits
     at depth 1 — the amorphic gap, live). At every tested `|T| ≥ 2`: cells = fibers and all twins
     extension-equivalent. **Consequence:** the transport must NOT be stated as "∀T, same-cell ⟹ ext alg-iso";
     the gate decls need it **at bases only**, and the +1 pattern in the data is exactly the Chen–Ponomarenko
     `dimWL(X) ≤ dimWL(X_α)+1` exchange ⟹ **sub-route (c) is now favoured; sourcing the monograph §4.2 is the
     Stage-2 gating action.** Full verdict in §5 Stage 2.1.
  3. ~~**Stage 2 — the transport**~~ — **LANDED MODULO THE CATCH-UP (2026-06-12, `CoherentConfig.lean §CC.9` +
     `CascadeAffine.lean §S-gate2`, axiom-clean).** The sourcing pass settled the route: the recursion (41) is
     CFI-1992 Thm 5.2 + FKV-2020 Thm 2.1, *graph-dimWL* currency — and **sub-route (b) won outright, with a
     citation-free core**: `SeparablePointed` of the extension applied to the **identity** alg-iso realizes every
     *fiber*-twin by a `T`-fixing automorphism that descends to the scheme
     (`fiberTwin_realized_of_separablePointed` → `twinsRealized_of_extensionPointed`). **Consequence: the
     homogeneous (A)-obligation DISSOLVES** — bare `Separable X`, Lemma 2.6, m-extensions, and the `Ωᵐ`/`m=2`
     substrate are all bypassed; the build's open content is now {Thm 4.1 on the extension (Stage 3) + the
     catch-up (item 5)}.
  4. ~~**The citation-checkpoint assembly**~~ — **LANDED (2026-06-12): `reachesRigidOrCameron_viaExtensionSeparability`**
     (`§S-gate2`) — the general conditional seal capstone, conditional on exactly {G3 `hClassify` + cited
     `Theorem41Statement` + its conditions on the extension at non-singleton fibers (probe-confirmed) + the
     catch-up `hcatch` + a bounded base (free for small) + landed `hImprim`}. The affine-slice pattern,
     generalized; plus the gate pair `separatesAtBoundedBase_of_extensionPointed`(`_of_small`) — which also
     **resolves the §5 Stage-4 keying note** (the chain consumes the general-CC predicates directly).
  5. **The catch-up discharge — `WarmTwinsAreFiberTwins` at the assembly's bases (THE isolated model gap).**
     Honest accounting: at a base with a complete extension the catch-up is equivalent in strength to the
     discreteness conclusion itself — its value is that it carries **no separability/group content**, only the
     1-WL↔pair-WL model comparison, so it is attackable by the refinement engines alone.
     **THE PROBE-GATE RAN (2026-06-12, `Probe_CatchUpGate_BasesAndDominators`, green) — GATE GREEN + the engine
     confirmed, at scheme level (full verdict in §8):** the catch-up holds at **every** minimal group base of both
     residue instances (ℤ₄²: all 96 of 96; ℤ₂⁴: all 480 of 480 — exhaustive sweeps against exactly-computed
     `Aut(X)`), indeed at every swept `|T| ≥ 2`; every minimal base is 1-WL-discrete and extension-complete, so
     **`b(X) = b(G)` on both instances** (2 resp. 3) and the catch-up at minimal bases *is* the discreteness
     statement (the honest accounting, now exhibited). The `c=1` two-endpoint dominator closure (the B3 `saAdj`
     pinning shape) **discretizes from every tested minimal base using only X's own rank-4 classes** — no
     extension classes needed — and is 1-WL-sound there (0 violations); off bases it is provably 1-WL-unsound
     (ℤ₄² `T={0}`: 3 violations), so any B3-style lemma stays base-keyed.
     **THE δ′ ENGINE LANDED 2026-06-12 (`CascadeAffine.lean §S-bridge-δ` + `§S-gate2`, axiom-clean, build green
     49s):** the *two-endpoint forced-triangle closure* is now a citation-free Lean path to the seal, sibling to
     the extension-separability checkpoint and **strictly lighter** (no CC-extension, no `Separable`, no catch-up,
     no group base). Decls: **B3′** `determined_of_forcedTriangle` (the smax-free generalisation of
     `determined_of_saAdj` — the `saAdj` proof never used its two `smaxAdj` conjuncts, so the `c=1` pinning works
     off the maximal-valency locus); the inductive closure **`DominatorReachable S T`** (base = `t∈T`, step = a
     rigid triangle pins `γ` from two reachable points); `determinedAt_of_dominatorReachable` (B2 seed + B3′
     step); **`discrete_of_dominatorClosure`** (closure exhausts Ω ⟹ `Discrete`); **`separatesAtBoundedBase_of_
     dominatorClosure`** (⟹ the seal consumer directly); and the capstone **`reachesRigidOrCameron_viaDominator
     Closure`** carrying exactly {G3 + `hImprim` + the single structural hypothesis `hclo : ∀ v, DominatorReachable
     S T v`}. **So item 5's Lean obligation is DISCHARGED as plumbing** — the catch-up is no longer on any critical
     path (the δ′ capstone bypasses it). What is now open is purely **item 6 / Stage 3** (below), in the
     citation-free form "prove `hclo` for the residue family: the `c=1` forced-triangle closure of a bounded base
     exhausts Ω" — the probe-confirmed, family-level open mathematics.
  6. **Stage 3 — the genuine open mathematics, now with TWO interchangeable target forms** (prove either; both are
     probe-backed and family-level): **(β)** Thm 4.1's conditions (i)/(ii) for the residue family's extensions
     (feeds `reachesRigidOrCameron_viaExtensionSeparability`; witness-constructive per `Theorem41ConditionsProbe`);
     or **(δ′, recommended — citation-free)** `∀ v, DominatorReachable S T v` for a bounded base `T` of the residue
     family (feeds `reachesRigidOrCameron_viaDominatorClosure`; probe-confirmed at every minimal base). δ′ is the
     lighter target — it asks only that the landed `c=1` forced-triangle closure completes from a base, with no
     separability/CC machinery — and is the same open content as β in citation-free clothing.
     **STAGE-3 INCREMENT 1 LANDED 2026-06-12 (`CascadeAffine.lean §S-stage3`, axiom-clean, build green 36s): the
     affine forced-triangle criterion.** `affineScheme_interNum_eq_one_of_unique` translates the abstract dominator
     premise (`intersectionNumber … = 1`) into the affine model's **`G₀`-orbit uniqueness on differences** — `γ` is
     pinned by `α, β` iff it is the *unique* `u` with `u−α ∼ γ−α` and `β−u ∼ β−γ` (proof: the forced-triangle
     filter is the singleton `{γ}`); `dominatorReachable_affine_step` is the matching `DominatorReachable` builder.
     So the δ′ family argument now runs entirely on `G₀`-orbit-of-difference combinatorics (no scheme-level
     intersection-number bookkeeping).
     **STAGE-3 INCREMENT 2 LANDED 2026-06-12 (`CascadeAffine.lean §S-bridge-δ`, axiom-clean, build green 63s): the
     closure equivariance.** `dominatorReachable_map` proves the dominator closure is scheme-automorphism-equivariant
     (a `π ∈ Aut(S)` mapping `T` into `T'` maps `T`-reachable to `T'`-reachable — the forced-triangle premise is
     `π`-invariant via `IsSchemeAut.relOfPair_eq`); `dominatorReachable_univ_image` is the payoff: **complete closure
     transports across automorphic base images**, so for a vertex-transitive residue, proving the closure for ONE
     base discharges the whole `Aut(S)`-orbit of bases. **Remaining (the genuine open math): the single-base
     closure** — exhibit ONE bounded base `T₀` and show every `v ∈ V` is `DominatorReachable` via iterated
     `dominatorReachable_affine_step`, for the residue family (`G0pow β` cyclotomic / amorphic-NLS). The probe
     confirms it holds; the proof is the orbit combinatorics. The equivariance means this need only be done at one
     representative base.
     **STAGE-3 INCREMENT 3 LANDED 2026-06-12 (`CascadeAffine.lean §S-bridge-δ`, axiom-clean, build green 94s): the
     general + schurian forced-triangle criterion.** `interNum_eq_one_of_forcedUnique` lifts the affine criterion to
     **any scheme** (`c=1` ⟺ the forced-triangle filter is `{γ}`), `dominatorReachable_step_of_unique` its step
     builder (subsumes the affine one + reaches non-affine residues), and **`dominatorReachable_step_of_stab`** the
     conceptual key: on a schurian scheme the criterion reads **`Stab(α)·γ ∩ Stab(β)·γ = {γ}`** (point-stabiliser
     orbits) — the geometric form the closure argument wants, since a base has `⋂ Stab(t) = 1`. **Remaining (the
     genuine open math): the single-base closure** — exhibit ONE base `T₀` and show the stabiliser-orbit-intersection
     condition propagates from `T₀` to all of `V`, for the residue family. The probe confirms it; the proof is the
     orbit/stabiliser combinatorics, now framed group-theoretically. **⟶ Read §5 "Stage 3 (δ′ route)" before
     attempting increment 4** — it carries the worked-by-hand planning insights (the cyclic `(r+1−rh)∈H→h=1`
     arithmetic reduction, the affine-vs-non-affine strategic choice, and the realistic "clean sufficient condition"
     endpoint).
     **STAGE-3 INCREMENT 4a LANDED 2026-06-13 (`CascadeAffine.lean §S-bridge-δ`, `dominatorReachable_of_rank`,
     axiom-clean, build green 198s): the iteration engine.** The δ′ toolkit had step builders + equivariance but no
     way to *iterate* the step to exhaust Ω. `dominatorReachable_of_rank` supplies it: a rank function `rank : Ω → ℕ`
     with every rank-`0` point in `T` and every positive-rank `γ` forced-triangle-pinned by two strictly-lower-rank
     points ⟹ `∀ v, DominatorReachable S T v` (strong induction on rank). **Net: the open content is reduced to the
     concrete, checkable "exhibit a pinning rank" — the clean sufficient condition the endpoint targets.** Remaining
     (the genuine `s(C)` math): define the rank + verify the pinning per level for the residue family (the cyclic
     arithmetic core, char-2 midpoints excluded).
     **STAGE-3 INCREMENT 4b LANDED 2026-06-13 (`CascadeAffine.lean §S-stage3-δ`, `fieldOf` / `G0pow_orbit_iff` /
     `dominatorReachable_G0pow_step`, axiom-clean, build green 121s): the affine cyclic arithmetic reduction.**
     Translates the cyclotomic family's orbit-of-difference pinning into pure `F_q`-power arithmetic. `G0pow_orbit_iff`:
     a `G0pow g`-orbit relation is multiplication by `g^k` through the field iso (`∃ g₀ ∈ G0pow g, g₀ v = w ↔
     ∃ k, g^k·efield.symm v = efield.symm w`, from `sigmaPow_zpow_apply`). `dominatorReachable_G0pow_step`: the
     forced-triangle step builder with `huniq` in `F_q` powers (`g^k·(fieldOf u−fieldOf α)=fieldOf γ−fieldOf α`,
     etc.). So the δ′ cyclotomic closure now runs on `F_q` arithmetic with no orbital bookkeeping.
     **STAGE-3 INCREMENT 4c LANDED 2026-06-13 (`CascadeAffine.lean §S-stage3-δ`, `dominatorReachable_G0pow_ratio_step`,
     axiom-clean, build green 115s first try): the ratio-form step builder.** Field-division packaging of 4b: for
     distinct field coords, `γ` is pinned once the only `h` with `h ∈ ⟨g⟩` and `1 + r·(1−h) ∈ ⟨g⟩` (`r=(c−a)/(b−c)`)
     is `h=1` — the `(r+1−r·h) ∈ ⟨g⟩ → h=1` reduction, making the **char-2-midpoint obstruction** explicit in Lean
     (`r=1 ⟹ 2−h=h` in char 2 ⟹ nothing pins). **The δ′ cyclotomic toolkit is now COMPLETE** (4a iteration engine +
     4b `F_q`-power step + 4c ratio step). The lone open piece is the **pinning-rank witness**: exhibit `T₀` + a rank
     whose per-level pinning these builders discharge — the genuine open `s(C)` math (affine slice cited-closed, so the
     new-coverage target is the non-affine residue via the general/schurian step builders).
     **STAGE-3 — FIRST END-TO-END FAMILY CLOSURE LANDED 2026-06-13 (`§S-bridge-δ` + `§S-stage3-δ`;
     `dominatorReachable_of_basePinsAll`, `dominatorReachable_G0pow_neg`, `reachesRigidOrCameron_viaG0powNeg`,
     all axiom-clean, build green, all first try).** The first **actual discharge** of the open `hclo` on a real
     `affineScheme` family: for `g = -1` (`⟨g⟩ = {±1}`), **odd characteristic**, every point is dominator-reachable
     from any 2-base (one round) — `dominatorReachable_G0pow_neg` — because the cross-ratio of distinct points avoids
     `{0,-1}`, so `1+2r ∉ {±1}` and only `h=1` survives. `reachesRigidOrCameron_viaG0powNeg` feeds it into the δ′
     checkpoint: **the seal on the whole `g=-1` family (q ≥ 5) with `hclo` PROVED, not carried** (only standard
     {G3+hne+hrank+hImprim} remain). Proves the δ′ route is non-vacuous; char≠2 is exactly the char-2-midpoint
     obstruction. **Still open (the genuine `s(C)` core):** larger `H` (multi-round), char-2 (Clebsch), and the
     **non-affine** residue (the new-coverage target). NEXT = larger `H` / multi-round rank witness, or non-affine.
     **STAGE-3 MULTI-ROUND LANDED 2026-06-13 (`§S-stage3-δ`; `dominatorReachable_G0pow_subfield`(`_step`),
     `ratio_not_mem_num_out`/`_denom_out`, all axiom-clean, build green):** the first `|H|>2` closure. One-round
     works iff `|H|≤2`, so `|H|>2` needs iteration; the **subfield family `H=K^×`** (`K⊊F_q`) closes in **2 rounds**
     from a 2-`K`-point base, via the size-free pinning rule `r=(c−a)/(b−c)∉K ⟹ pinned`. **CAVEAT: `K^×` is
     IMPRIMITIVE** (scalars preserve every `F_p`-subspace) — the hImprim/G2-A case, not primitive G2-B; this validates
     the multi-round engine + gives a reusable subfield pinning lemma, but the **primitive irreducible** larger-`H`
     case (no subfield shortcut) remains the open core. Carries `⟨g⟩=K^×` + non-`K` witness (field-theory plumbing).
  Parked smaller items (see the 2026-06-12 review entry in §8): ~~Route δ feasibility probe~~ (RAN + the engine
  LANDED — items 5/6 above); pin the `IsLarge` threshold vs Sun–Wilmes; v=64 Davis–Xiang NLS falsifier;
  strategy-§15 gaps tracking note.
  The increment log is §8 — append to it.

---

## 0. How to work in this build

- **One rule:** treat every summary — this doc included — as a *hypothesis* to confirm against the Lean source and
  the primary papers. The source wins.
- **Build:** `bash scripts/build.sh` (serial, ~60–120 s; parallel `lake build` thrashes swap — don't). Add new
  modules to `scripts/build.sh` `MODULES=(…)` in topological order. Verify axioms with
  `lake env lean /tmp/check.lean` containing `#print axioms <decl>` (run from `GraphCanonizationProofs/`).
- **Papers / extraction:** the two load-bearing extracts are **version-controlled in
  [`docs/papers/`](./papers/README.md)** (2026-06-12; `/tmp` copies do not survive a reboot):
  `docs/papers/p4paper-arxiv-2006.13592.txt` (the Thm-4.1 paper) and `docs/papers/cartan-arxiv-1602.07132.txt`
  (Cartan/Thm 3.1). Both cleaned + greppable. For anything else: `pdf2txt <file.pdf> [first] [last]` is on PATH
  (`~/.local/bin`, user-site PyMuPDF); arXiv ids are stable, re-fetch with
  `curl -sL https://arxiv.org/pdf/<id> -o /tmp/x.pdf`.
- **GOTCHA — `grep`/`rg` find NOTHING on a *fresh* `pdf2txt` extraction. Run the cleaner first.** The cause is **NUL
  bytes** in the pdf2txt output: `grep` treats any file containing a NUL as *binary* and silently refuses to print
  matches (`LC_ALL=C grep` fails for the same reason — it is NOT a locale problem; the `setlocale: LC_ALL` warnings are
  noise). Secondary: pdf2txt uses ligatures *inside words* — "conﬁguration" (ﬁ), "diﬀerent" (ﬀ) — so even after NUL
  stripping `grep configuration` would miss them. **FIX (do this on every new extraction):**
  `python3 scripts/clean-extracted-text.py /tmp/x.txt` — strips NUL + NFKC-normalizes ligatures to ASCII, in place.
  Then plain `grep`/`rg` works (math symbols like `←` are preserved for reading; they don't break grep). The two
  papers above are already cleaned; `python` (`open(...,encoding='utf-8',errors='replace').read()`) also always works
  as a fallback.
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

## 1A. Why the crux is NOT "GI ∈ P, give up" — the carve-out (read before pattern-matching to hopelessness)

It is easy to glance at the crux — *"a primitive small scheme recovers at a bounded base"* — and conclude
"bounded base = bounded WL-dimension = **GI ∈ P**, therefore hopeless, just isolate it." **That inference is
wrong, and it has already misled an onboarding pass. The reasoning is recorded here so it does not recur.**

**The scare, step by step (every step true):** (1) bounded base ⟺ bounded WL-dimension, and bounded WL-dim
canonizes in poly time; (2) WL-dimension is unbounded in general (CFI); (3) ∴ "prove bounded base" *smells like*
"prove GI ∈ P."

**The error is in step (3):** it conflates *bounded base for **the residue*** with *bounded base for **all
schemes***. Only the latter is GI ∈ P. The residue has already had **every known source of unbounded WL carved
out by a separate leg of the seal:**

| Unbounded-WL family | Carved out by |
|---|---|
| CFI / gauge twists | imprimitive gadget structure → **hImprim** (G2-A), or simply not primitive |
| abelian Cayley / circulants (unbounded WL — Wu–Ren–Ponomarenko 2025) | abelian → **leg B** (`AbelianConsumed`) |
| Johnson / Hamming / product action / large almost-simple | *large* → **Cameron** (G3) |
| **hidden Johnson (the genuine wall)** | **Cameron** — this is *precisely why* the seal's last leg is *"or Cameron"* |

After all four carves the residue is **primitive, small, non-abelian, non-Cameron** — and **no known
unbounded-WL scheme lives there**: seven empirical falsifiers returned **0 witnesses**, and the on-target ℤ₄²
amorphic-NLS bullseye *recovers* (WL-depth 2). So the crux is **not GI ∈ P; it is the tame remainder left
after the hardness was quarantined into Cameron.**

**Isolation is the method, applied recursively.** Each row above was *itself* once an "apparent GI ∈ P" that
was dissolved by identifying and walling a sub-case. The crux is the **last** such residue, and the same move
is expected to close it. It is hard *open* math, **not** a proven impossibility — and it was deemed the
*most likely* route to the unconditional seal, which is incompatible with treating it as unclosable.

**The closure angle (what is actually owed).** The route is **separability**: primitive-small-non-Cameron ⟹
bounded `s(C)` ⟹ recovery. This reduces to *"the residue's point extension satisfies Ponomarenko Thm 4.1's
conditions (domination + couple-extensions),"* which the C# probe has already **verified holds** on the
extension (`Theorem41ConditionsProbe`; bare dense `X` fails, the one-point extension `X_α` passes at every µ).
The structural reason to expect it in general is **Cameron's dichotomy** (a primitive group is either
large/classifiable or small/restricted): the *smallness* hypothesis together with *non-Cameron* forces the
bounded-structure regime, where domination holds by counting and separability converts it to recovery. The δ′
forced-triangle closure is the citation-free form of the same content.

**What would mean we are OFF track (the honest falsifier).** A primitive, small, non-abelian, **non-Cameron**
scheme with *unbounded* base — a genuine G2-B witness. That would show the hardness is *not* fully captured by
Cameron, i.e. *"or Cameron"* is the wrong carve and the seal is **false** (a statement change — itself a real
result). The 0-witness record is the standing evidence we are *on* track; equally, Thm 4.1's conditions
*failing* on the residue would be a warning — but the probe shows they hold.

**Discipline that prevents the misperception.** Before invoking "GI ∈ P" about any recovery claim, ask
**"what is still IN the residue?"** If the hard families are already carved into other legs, the claim is about
the tame remainder and GI ∈ P does not apply. The scare comes from forgetting the carve, not from the math.

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
**Treat this as a soundness gate, not a taste choice (sharpened 2026-06-12):** the homogeneous `Separable` is the
*weaker* predicate (fewer partners `Y`), and the transport (B) consumes separability against *extension* alg-isos —
which are exactly the partners the homogeneous quantification omits. Reconcile (prove the homogeneous form equal to /
sufficient for Thm 4.1's conclusion at the point of use, or widen the predicate) **before** Stage 3 invests in proving
it, or the heaviest stage can land a predicate too weak to feed (B).

---

## 3. The mathematics (self-contained)

All from Ponomarenko, *On the separability of cyclotomic schemes over finite field*, **arXiv:2006.13592**
(`docs/papers/p4paper-arxiv-2006.13592.txt`), and Ponomarenko–Vasil'ev, *Cartan coherent configurations*,
**arXiv:1602.07132** (`docs/papers/cartan-arxiv-1602.07132.txt`); foundations in Evdokimov–Ponomarenko, *Separability number and Schurity number of coherent
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
  separability — supplied by the transport (B), not by Thm 2.5. **But note (2026-06-12):** Thm 2.5's *premise* —
  1-regularity of the extension — feeds the seal *directly* through the landed B1–B5 bridge, no transport needed;
  that is Route δ in §6.)
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

### LACKS (the build creates these) — ledger updated 2026-06-12
- ~~A **general (multi-fiber) coherent configuration** type~~ — **LANDED** (`CoherentConfig`,
  `ChainDescent/CoherentConfig.lean`, with the homogeneous coercion `AssociationScheme.toCoherentConfig`).
- ~~The **point extension as a CC** object~~ — **LANDED IN FULL**: the predicate (`IsPointExtension`, universal
  property, complete via the derived fiber coherence `relOf_diag_left_eq`) **and the construction**
  (`pointExtension` + `isPointExtension_pointExtension` + `exists_isPointExtension` + `isPointExtension_unique`,
  `§CC.8`, 2026-06-12). Still open: the **warmRefine↔fiber bridge** — per the direction check, to be stated at
  bases / via the `dimWL` +1 exchange (cells=fibers at arbitrary `T` is FALSE on the bullseye).
- ~~**General-CC `AlgIso` / `Separable`**~~ — **LANDED** (`CoherentConfig.AlgIso`/`Separable`/`SeparablePointed`;
  partner quantifies over all `CoherentConfig n`, resolving the §2 soundness gate by widening).
- ~~The **m-extension on `Ωᵐ`** + m-dim intersection numbers + m-separability~~ — **OBSOLETE (2026-06-12)**: the
  pointed transport (§CC.9/§S-gate2) consumes `SeparablePointed` of the extension directly; no `m=2`, no Ωᵐ.
- ~~**Lemma 2.6**~~ — **OBSOLETE (2026-06-12)** for the same reason (it served only the 2-separability packaging).
- **Theorem 4.1**: ~~statement~~ — **LANDED as the cited `Theorem41Statement`** (hypotheses `Theorem41Hypotheses`
  = exactly the probe's checks; staging-fallback carry). The *proof* (Stage 3, Route β on the extension) is the
  open mathematics.
- ~~The **transport** proof~~ — **LANDED MODULO THE CATCH-UP (2026-06-12, §CC.9 + §S-gate2)**: the citation-free
  pointed core + the seal wiring; the sole carried remainder is `WarmTwinsAreFiberTwins` (the 1-WL↔fiber model
  gap, STATUS item 5).

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
  **✓ DONE (2026-06-12)** — Option H sharpened to the colour-function presentation; decision + rationale in §8;
  skeleton = `ChainDescent/CoherentConfig.lean`.

### Stage 1 — the general-CC substrate (shared prerequisite for A and B)
1. **`CoherentConfig` type** (or the chosen representation) · Stage 0 · **load-bearing.** Fibers, basis relations,
   intersection numbers, the coherence axiom. Provide the homogeneous `AssociationScheme → CoherentConfig` coercion.
   **✓ DONE (2026-06-12)** — `CoherentConfig` + `interNum`/`transposeRel` API + derived fiber coherence
   (`relOf_diag_left_eq`) + `AssociationScheme.toCoherentConfig` (on the seal's `hne`).
2. **The point extension `X_µ` / `X_T` as a `CoherentConfig`** · 1 · **load-bearing.** The smallest CC ≥ X with `T`
   singleton fibers.
   **✓ (a)+(b) DONE (2026-06-12, `§CC.8`)** — (a) the **construction**: `pointExtension X T` = the coherent
   closure as a pair-refinement saturation (`pairStep` on `Setoid (Fin n × Fin n)` with *representative-indexed*
   counts `pairCount` — no quotient/encoding in the iteration; stabilization by the `numClasses` pigeonhole
   within `n²` rounds, the §S-stab pattern on pairs); the four CC axioms read off the fixpoint
   (`stableSetoid_pairCount` = coherence; `pairIter_swap` = transpose; `pairIter_le_init` = diagonal + flags);
   the universal property discharged constructively (`isPointExtension_pointExtension`, via the counting heart
   `pairCount_eq_of_zrel` — `Z.inter_card_eq` summed fiberwise over `Z`'s class pairs, exactly the predicted
   generalization of the §CC.2 argument) ⟹ `exists_isPointExtension` (the `ExtensionSeparable` family is never
   empty). (b) **uniqueness up to relabelling**: `isPointExtension_unique` (mutual refinement from the predicate).
   **OPEN: (c) the warmRefine↔fiber bridge — reshaped by the Stage-2.1 direction check (2026-06-12):** fibers are
   *strictly finer* than 1-WL cells on the ℤ₄² bullseye at `|T|=1` (10 vs 4), so the bridge must NOT be stated as
   cells=fibers at arbitrary `T`. State it at bases, or as the +1 exchange (1-WL at `T`+pt vs fibers at `T` — the
   Chen–Ponomarenko `dimWL` recursion, Stage 2.2(c)). The §S-bridge (B1–B5) remains the template for the
   fiber→1-WL direction where needed.
3. **General `AlgIso` / `Separable` / `m-separable`** · 1 · **load-bearing.** Generalise §S.17 to `CoherentConfig`;
   prove the homogeneous `Separable` (§S.17) is the single-fiber case (reconciliation lemma).
   **◐ DONE except the reconciliation lemma** — `AlgIso`/`InducedBy`/`Separable`/`SeparablePointed` landed (partner
   widened to all `CoherentConfig n`, resolving the §2 soundness gate). The §S.17 reconciliation lemma is now
   **likely unnecessary** (the build targets `ExtensionSeparable` directly, not the homogeneous predicate) — do it
   only if a consumer genuinely needs the §S.17 form; `m`-separable still unstated (needs Stage 1.4).
4. **The m-dim intersection numbers / 2-extension** · 1 · load-bearing *iff* the chosen route needs `m=2` (it does —
   Lemma 2.6 / Thm 1.2). Build `Ω×Ω` only; defer general `Ωᵐ`. **DEFERRED, and possibly avoidable:** Thm 4.1's
   *statement* landed without it (`Theorem41Statement`), and if Stage 2 targets `ExtensionSeparable` directly the
   Lemma-2.6 packaging (the only consumer of `m=2`) may never be needed. Build only when a stage demands it.

### Stage 2 — the transport (B): `Separable ⟹ CellsAreOrbits at T`
Target: `∀ T, SeparabilityTransports S T`. Route (the affine slice `powAffineSeparates_of_twinsAreSemilinear` is the
concrete template; here general). **Status note (2026-06-12): the separability-level input predicate is landed —
`ExtensionSeparable X T` (`CoherentConfig.lean §CC.6`); state the transport against it (and `SeparablePointed`),
not against the homogeneous §S.17 form.**
1. **Twins ⟹ extensions algebraically isomorphic** · Stage 1.2/1.3 · **load-bearing — NOW PROBE-SHAPED
   (2026-06-12, `Probe_Stage21_DirectionCheck_CellsVsFibers`, green; control C₁₇ asserted).** The naive statement
   — ∀T, same-`warmRefine`-cell pair `u,u'` ⟹ `X_{T∪{u}} ≅_alg X_{T∪{u'}}` — is **REFUTED on the residue**:
   on ℤ₄² at `T={0}`, 1-WL cells = 4 but `X_T` fibers = 10 (strictly finer; witness: cell-mates (1,7) are
   fiber-split), and **24/30 same-cell pairs have WL-inequivalent extensions** — i.e. `CellsAreOrbits {0}` is
   genuinely FALSE on the bullseye (the amorphic depth-1 gap, now exhibited rather than inferred). ℤ₂⁴ at
   `T={0}`: cells = fibers (4=4), 30/30 twins equivalent — the gap is specific to the non-elementary-abelian
   bullseye. At every tested `|T| ≥ 2` (both groups, one base per relation class + a size-3): cells = fibers AND
   all same-cell twins extension-WL-equivalent. **What survives:** the gate decls (§2) consume the transport at
   *bases* only, where the data is clean; and the +1 pattern (fibers at `T` ≈ cells at `T`+one point) is exactly
   the Chen–Ponomarenko `dimWL(X) ≤ dimWL(X_α)+1` exchange — state the twin⟹alg-iso step **at bases or via the
   recursion (sub-route (c))**, never at arbitrary `T`. The fiber→1-WL re-bridging tools, if needed, remain the
   B1–B5 / `discrete_of_kRoundRelationSeparates` engines.
2. **Separability of the extension** · Stage 1.3 + Lemma 2.6 · **load-bearing, the crux.** From `Separable X` (the
   §S.17/general predicate) derive separability of the relevant extension. Four sub-routes: (a) prove the inheritance
   `s(X_µ) ≤ s(X)` directly (EP [4]); or (b) use Thm 4.1's **pointed** conclusion (induced `f` controllable on `µ`)
   to skip an explicit inheritance lemma; or (c) **the Chen–Ponomarenko WL-dimension recursion** —
   `dimWL(X) ≤ dimWL(X_α) + 1` (Chen–Ponomarenko, *Coherent Configurations* §4.2 = p4paper ref [3]; already named
   as *the* `b(X) ↔ s(C) ↔ dimWL` bridge theory in `Separability.lean §S.17`'s doc-comment, lines ~1130–1133, but
   absent from this doc until 2026-06-12) — the recursion is stated in the project's native idiom (extension depth),
   so it may be the cheapest *citable* path from `m`-separability to the bounded-base consumer; or (d) prove
   `Separable ⟹` the **joint relation-count separation** the landed `discrete_of_kRoundRelationSeparates` consumes
   directly (the consumer is already built; the doubt — recorded in §7 — is that deriving the count separation from
   a twin still routes through the extension alg-iso, i.e. (d) may be (a)/(b) in disguise). **Pin which before
   investing** — this is the load-bearing uncertainty the transport surfaced.
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
   residue / 2-extension) discharge. This is the genuine new mathematics. **The empirical gate RAN
   (2026-06-12, `Theorem41ConditionsProbe.cs`, green) — ROUTE β VIABLE on the residue.** Checker validated on the
   positive control (cycle schemes under `3ck(k−1) < n`, where §5 *proves* the conditions — PASS, all witnesses
   geometric). On the rank-4 amorphic-NLS Clebsch residue (ℤ₄² bullseye + ℤ₂⁴ anchor): **X itself FAILS both
   conditions** (µ=0; `Δ={0,1,2,3}` undominated — confirms §3.6, the dense scheme is out of direct reach) but the
   **one-point extension `X_α` PASSES both conditions at every µ** (ℤ₄²: all 16 µ; ℤ₂⁴: all µ ≠ α — pick µ in the
   big fiber, or use `X0` where **all** µ pass) and the Lemma-2.5 object `X0 = X_α∖{α}` **passes at every µ on
   both**. Two proof-shaping bonuses: (a) **every (ii)-witness is geometric** (the λ-triangle
   `(r(λ,α),r(λ,β),r(λ,γ))`, `m = r(µ,λ)` — Lemma 5.3's shape; the abstract fallback was never needed), so the
   Lean discharge can *construct* the witness rather than prove bare existence; (b) rank(`X_α`) = 136 (ℤ₄²) / 34
   (ℤ₂⁴) of 256 — the extension is where the dense scheme turns sparse-ish, which is *why* the conditions
   activate. Caveat: this confirms the order-16 instances, not the family — the family-level discharge is still
   Stage 3's mathematics, but it is now probe-backed, not speculative.
3. **Assemble (A)** · 2 + Lemma 2.6 · load-bearing. Either prove `Separable` directly for the residue, or
   `2-separable` via Lemma 2.6 and feed the transport at `m=2`.
4. **Scope note (2026-06-12) — a FAMILY-RESTRICTED Stage 3 suffices; the full general Thm 4.1 is NOT owed.**
   `Theorem41Statement` is carried as a global `∀ n X μ` statement, but the citation checkpoint consumes it only
   at `hcite n E u` for the *specific* extension `E` of the residue at hand. So Stage 3 may land as
   "`Theorem41Hypotheses ⟹ SeparablePointed` *for the residue family's extensions*" (or even per-instance), feed
   the checkpoint through a thin wrapper, and the global cited carry simply retires unused — no statement change
   anywhere in the chain. Plan Stage 3 at the family level, not the full generality of the paper.

### Stage 3 (δ′ route) — the single-base dominator closure (THE recommended route; increment 4 is the open piece)
> **CURRENCY BANNER (2026-06-13): increments 1–4c + the first family closures have LANDED since this section was
> written; the open frontier has moved to the NON-AFFINE residue (concrete route).** Read the STATUS block's
> "CURRENT FRONTIER (2026-06-13)" line and the §8 entries from 2026-06-13 first. The planning insights below
> (cyclic arithmetic, char-2 midpoint, affine-vs-non-affine, "clean sufficient condition" endpoint) are still
> valid and were borne out — but "increment 4 = the single-base closure" now reads as *the affine closure, which
> turned out to be citable / partly imprimitive; the genuine target is the non-affine ℤ₄² amorphic-NLS residue,
> whose closure construction (rainbow-triangle rigidity, depth 3) was extracted by probe (§8).*

**This is the lighter, citation-free Stage 3 and the recommended target** (feeds `reachesRigidOrCameron_viaDominatorClosure`,
not the Thm-4.1 checkpoint). **Landed (increments 1–3, all axiom-clean):** the forced-triangle criterion at three
levels — affine orbit-difference (`affineScheme_interNum_eq_one_of_unique` / `dominatorReachable_affine_step`,
`§S-stage3`), **general any-scheme** (`interNum_eq_one_of_forcedUnique` / `dominatorReachable_step_of_unique`,
`§S-bridge-δ`), and **schurian stabiliser-orbit** (`dominatorReachable_step_of_stab`: pinning ⟺ `Stab(α)·γ ∩
Stab(β)·γ = {γ}`); plus the **closure equivariance** (`dominatorReachable_map` / `dominatorReachable_univ_image`:
complete closure transports across `Aut(S)`-images of the base, so prove at ONE representative).
**OPEN (increment 4, the genuine `s(C)` core): the single-base closure** — exhibit a bounded base `T₀` and prove
`∀ v, DominatorReachable S T₀ v`, i.e. the stabiliser-orbit-intersection condition propagates from `T₀` to all of `V`.
Planning insights for that attack (worked by hand 2026-06-12; **verify before relying**):
- **The cyclic/affine arithmetic reduction.** For `affineScheme (G0pow β)` (so `G₀ = ⟨mul β⟩`, `H := ⟨β⟩ ≤ F_q^×`,
  points `= F_q`): γ is pinned by α, β **iff `∀ h ∈ H, (r + 1 − r·h) ∈ H → h = 1`**, where `r := (γ−α)/(β−γ) ∈ F_q^×`.
  (Derivation: `u−α ∈ H·(γ−α)` ⟹ `u−α = h₁(γ−α)`; the second condition forces `h₂ = 1 + r(1−h₁) ∈ H`; uniqueness
  is `h₁ = 1` only.) This is the **concrete Frobenius/cyclotomic `s(C)` core** — the same arithmetic the retracted
  `PowAffineSeparates` targeted, so closing it is the known-open cyclotomic-separability problem, NOT a quick win.
  - **Char-2 obstruction (carry into any base-selection — verify):** in characteristic 2 (e.g. `F_16`, the Clebsch
    residue) the **midpoint** triangles (`r = 1`, i.e. γ the midpoint of α,β) are **never rigid**: the condition
    `(r+1 − r·h) ∈ H → h = 1` at `r=1` reads `(2 − h) ∈ H → h = 1`, but `2 − h = −h = h ∈ H` always holds, so every
    `h` is admitted and γ is *not* pinned. ⟹ a propagating base over a char-2 residue must be built from
    **non-midpoint (`r ≠ 1`)** triangles; do not expect midpoint-symmetric bases to discretize. (This is exactly why
    the ℤ₂⁴/`F_16` residues sit at WL-depth ≥ 2 empirically — depth-1 midpoint pinning is structurally unavailable.)
- **The stabiliser-orbit form is the right general tool** (`dominatorReachable_step_of_stab`). A base `T₀` has
  `⋂_{t∈T₀} Stab(t) = 1`, so its point-stabiliser orbits must intersect down toward points; the closure question is
  whether the *pairwise* intersections `Stab(t)·γ ∩ Stab(t')·γ = {γ}` cover enough γ to propagate. This is the
  cleanest framing and works for **non-affine** residues too.
- **Strategic — affine vs non-affine (pick deliberately in increment 4).** The affine cyclotomic case is *already
  closed by citation* (`reachesRigidOrCameron_affineSlice`), so an affine δ′ closure only **removes that citation**
  (worthwhile but it re-derives the hard Frobenius arithmetic above). The genuinely-**new** coverage is the
  **non-affine** residue (e.g. the ℤ₄² amorphic-NLS bullseye = `orbitalScheme G`, not `affineScheme`), which the
  **general** step builder (`dominatorReachable_step_of_unique` / `_of_stab`) now reaches — there is no
  `translationScheme`-over-ℤ₄² object needed, just `orbitalScheme` of the right group. **Recommendation:** because
  the full closure is the open `s(C)` research either way, increment 4 should aim for a **clean sufficient
  condition** on the stabiliser-orbit structure (or a family-restricted / structured-base partial result), not a
  full family closure in one step — mirroring how the affine slice landed via the cited `TwinsAreSemilinear`
  predicate. A named clean predicate `DominatorClosesFrom S T₀` carried into a per-family capstone is a legitimate
  honest endpoint if the arithmetic resists.

### Stage 4 — assembly + exceptional cases
1. **Wire (A)+(B) ⟹ seal** · Stages 2,3 + §2 table · mechanical. Instantiate
   `separatesAtBoundedBase_of_separable_of_small` at `orbitalScheme H`, feed `reachesRigidOrCameron_viaPersistentTwinBlock`.
   ~~**⚠️ Keying mismatch to plan for (noted 2026-06-12)**~~ — **RESOLVED (2026-06-12, §S-gate2):** the general-keyed
   gate variants exist (`separatesAtBoundedBase_of_extensionPointed` / `…_of_small` /
   `reachesRigidOrCameron_viaExtensionSeparability`), consuming `SeparablePointed`-of-the-extension directly; the
   homogeneous-keyed `SeparabilityTransports` chain is bypassed entirely (retained for the historical (A)+(B)
   framing, no longer on the critical path).
2. **Exceptional `(p,d)` table** (Thm 1.1, only if the residue includes the cyclotomic/affine instances) · the C# bed
   (`AffineSchemeProbe`/`CatalogueSchemeProbe`) · mechanical. Reproduce the finite exceptions as `decide`-checked
   facts. **The non-affine NLS residue is outside the cyclotomic family, so likely N/A** — confirm per instance.
3. **Assembly-shape note (2026-06-12) — the `_of_small` gate quantifies over ALL `T`; plan a chosen-base variant.**
   `separatesAtBoundedBase_of_extensionPointed_of_small` takes `hsep`/`hcatch` at *every* `T` because the greedy
   base it picks internally (`exists_greedy_base_le_log`) is *some* base, not a chosen one. When the catch-up is
   discharged at specific (probe-validated) bases, assemble through the per-`T` gate
   `separatesAtBoundedBase_of_extensionPointed` with the chosen `T` instead — or land a thin `_of_small` variant
   that accepts a base-selection function. Do not let the ∀-`T` form drive the catch-up discharge wider than the
   assembly needs.

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
- **Route δ — direct 1-regularity at `base+O(1)` points (substrate-cheap, math-risk-identical; added 2026-06-12).**
  Cartan Thm 2.5's *premise* — a 1-regular extension w.r.t. `k` points — feeds the seal **directly**: 1-regularity
  of `X_T` is exactly what the landed B1–B5 bridge (`determined_of_saAdj` / `discrete_of_connectivity` /
  `separatesAtBoundedBase_of_sparseSeparable`) turns into `Discrete`-at-`T` for the sparse case, with **no AlgIso /
  multi-fiber / m-extension substrate at all** (and `m`-separability falls out free via cited Thm 2.5 if wanted).
  The dense-side generalisation is "1-regular w.r.t. `base+O(1)` points" — iterate the `c=1` forced-triangle
  calculus on the extension *after* individualizing the base, where the dense scheme's relations have split.
  **Honest trade-off:** δ is a *direct* attack on the crux (no reduction to checkable local conditions — that
  reduction is exactly what Thm 4.1's (i)/(ii) buys for α/β), so its math risk is the full G2-B; its value is that
  a probe-confirmed partial result lands on already-built homogeneous machinery. Worth a *probe first* (does the
  `c=1` calculus propagate to discreteness on the ℤ₄² Clebsch extension at 2–3 points?) before choosing it over β.
  **THE PROBE RAN (2026-06-12, incidentally to the catch-up gate — `Probe_CatchUpGate_BasesAndDominators`): δ's
  engine is POSITIVE on both residue instances, and stronger than asked** — the `c=1` two-endpoint dominator
  closure discretizes from *every* minimal group base on ℤ₄² and ℤ₂⁴ **at the scheme level** (X's own rank-4
  classes; the extension's classes are not even needed at bases). δ is therefore a live instance-level discharge
  shape (see STATUS item 5 (δ′)); its open content — proving the closure exhausts Ω from a base for the *family* —
  is the same crux as Stage 3's, in citation-free clothing.

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
- **2026-06-12 — onboarding review pass (docs only, no Lean).** Two independent fresh-eyes reviews of the project,
  cross-checked against the Lean source and the paper extracts; the plan survives, with these doc deltas: (1) paper
  extracts **version-controlled** at `docs/papers/` (were `/tmp`-only — reboot-fragile); (2) Stage 2.2's sub-route
  menu widened with **(c) the Chen–Ponomarenko `dimWL(X) ≤ dimWL(X_α)+1` recursion** (named in `Separability.lean
  §S.17`'s doc-comment all along but missing here) and (d) the direct relation-count form; (3) **Route δ** added to
  §6 (direct 1-regularity at `base+O(1)` via the landed B1–B5 bridge — substrate-free, math-risk-identical, probe
  first); (4) Stage 3.2 gated behind a **conditions-(i)/(ii) probe** (the falsifiers only ever tested the
  conclusion); (5) the §2 homogeneous-`Separable` quantification note sharpened to a **soundness gate** (reconcile
  before Stage 3 proves a possibly-too-weak predicate). Also flagged upstream, not in this doc: pin the intended
  `IsLarge` instantiation — the G3 citations (Babai/Sun–Wilmes) kick in at sub-exponential thresholds
  (≈`exp(n^{1/3})`), not super-poly, so "small" in the crux is wider than the `O(log n)`-base prose suggests
  (verify the exact threshold against the sources before relying). Stage 0 remains the next Lean action.
- **2026-06-12 — THE STAGE-3 GATE RAN: Thm 4.1's hypotheses HOLD on the residue's one-point extension — Route β
  VIABLE.** New probe `GraphCanonizationProject.Tests/Theorem41ConditionsProbe.cs` (2 facts, green): a general-CC
  engine (coherent closure on pairs = the point extension; fully-verified intersection numbers; transpose/products)
  + faithful checkers for condition (i) (domination, exhaustive `|Δ|=4`) and condition (ii) (m-extending couples:
  geometric λ-scan per Lemma 5.3 + exhaustive abstract fallback, so FAIL is genuine). **Control:** cycle schemes
  under `3ck(k−1)<n` PASS (the paper proves they must — checker faithful). **Residue (ℤ₄² Clebsch bullseye + ℤ₂⁴
  anchor):** X fails both conditions (dense, as §3.6 says) — but `X_α` and `X0` **pass both conditions at every
  (non-α) µ, with every witness geometric**. Full detail folded into Stage 3.2. Consequences for the plan:
  Stage 0's recommended hypothesis (Option H, Route β) is now *evidence-backed*; the Stage-3 Lean target can be
  stated witness-constructively (the λ-triangle); and the transport (B) should target the *pointed* conclusion at
  the extension (Stage 2.2(b)/(c)) since that is the form the probe-confirmed conditions feed. NEXT: Stage 0.
- **2026-06-12 — STAGE 0 DECIDED + STAGE-1 SKELETON LANDED (`ChainDescent/CoherentConfig.lean`, axiom-clean
  `[propext, Classical.choice, Quot.sound]`, no `sorry`, full build green ~24s; index regenerated).**
  **The Stage-0 decision (Option H, sharpened by the probe):** model the general CC by its **colour function**
  (`relOf : Fin n → Fin n → Fin rank` + four axioms: classes nonempty / transpose well-defined / reflexive classes
  purely diagonal / intersection numbers constant) — the minimal faithful presentation and *exactly* the object
  `Theorem41ConditionsProbe.cs` computes with, so every predicate has a machine-checked finite mirror. Fiber
  coherence is **derived, not axiomatized** (`relOf_diag_left_eq`: a class determines its source fiber — from
  `diag_eq` + `inter_card_eq` alone). The **point extension is a predicate** (`IsPointExtension`, the
  coarsest-coherent-fission universal property — made complete by the derived fiber coherence; `discreteCC`
  witnesses the family nonempty); its construction is deferred to Stage 1.2 (pair-refinement saturation — the
  `Saturation.lean`/`numCells` stabilization pattern, on pairs). **No `Ωᵐ` tower built**: Thm 4.1's hypotheses are
  first-order in intersection numbers (the "m-extension of a couple" is product-membership + uniqueness), so the
  **cited `Theorem41Statement` landed now** — the staging-fallback carry in the G3 pattern. The §2 quantification
  soundness gate is resolved by **widening**: `CoherentConfig.Separable`'s partner ranges over all
  `CoherentConfig n` (multi-fiber), not homogeneous schemes; `SeparablePointed` is Thm 4.1's actual (pointed)
  conclusion, the form the transport wants. Decls: `CoherentConfig` + `repPair`/`interNum`(`_eq`)/`transposeRel`
  (`relOf_swap_eq`, involution) / `relOf_diag_left_eq`/`_right_eq` / `AssociationScheme.toCoherentConfig` (on the
  seal's `hne`) / `AlgIso`/`InducedBy`/`idAlgIso` / `Separable`/`SeparablePointed` / `InComplexProduct`/`Dominates`/
  `DominationCondition`/`IsCoupleExtension`/`CoupleExtensionCondition`/`Theorem41Hypotheses`/`Theorem41Statement` /
  `Refines`(`refl`/`trans`)/`SingletonFiber`/`IsPointExtension`/`ExtensionSeparable` / `discreteCC`(`_refines`/
  `_singletonFiber`). **NEXT (Stage 1.2): the point-extension construction + the warmRefine↔fiber bridge**, then
  Stage 2 (the transport against `ExtensionSeparable`, sub-route (b)/(c) per the probe's pointed-geometric shape).
  Lean gotcha for the log: the micro-sign `µ` (U+00B5) is not a Lean identifier character — use Greek `μ` (U+03BC).
- **2026-06-12 — THE STAGE-2.1 DIRECTION CHECK RAN: the naive twin⟹alg-iso keying is REFUTED at arbitrary `T`;
  bases are clean; transport sub-route (c) favoured.** New fact `Probe_Stage21_DirectionCheck_CellsVsFibers`
  (`Theorem41ConditionsProbe.cs`, green; C₁₇ control asserted — cells=fibers and all reflection twins
  extension-equivalent). Adds a faithful 1-WL vertex refinement (the Lean `warmRefine (schemeAdj S)` mirror) and a
  **canonical** pair-WL (round-wise sorted renaming ⟹ cross-run-comparable stable fingerprints = WL-equivalence of
  extensions). **Findings:** (1) ℤ₄² bullseye, `T={0}`: 4 cells vs **10 fibers** — fibers strictly finer; 24/30
  same-cell pairs give WL-inequivalent one-point-further extensions (first concrete exhibit that `CellsAreOrbits`
  fails at depth 1 on the bullseye — cells ⊋ orbits, the amorphic gap live, consistent with "fails depth-1
  EdgeGenerates, recovers at depth 2"). (2) ℤ₂⁴ anchor, `T={0}`: cells=fibers, 30/30 equivalent (the gap is
  bullseye-specific). (3) ALL tested `|T|≥2` (one 2-base per relation class + a 3-base, both groups): cells=fibers,
  every same-cell twin extension-equivalent. **Consequences:** Stage 2.1 must not be stated over arbitrary `T`
  (false); the gate needs the transport at bases only (clean); the +1 pattern = the Chen–Ponomarenko
  `dimWL(X) ≤ dimWL(X_α)+1` exchange ⟹ **sub-route (c) promoted to favoured — sourcing the monograph §4.2 is now
  the Stage-2 gating action**. Also this turn: the Stage-4 keying-mismatch note added to §5 (the §S-gate decls are
  homogeneous-`Separable`-keyed; Stage 2 targets the general predicates — plan thin general-keyed gate variants).
  NEXT: Stage 1.2(a), the point-extension construction in Lean (route-independent — needed under every transport).
- **2026-06-12 — STAGE 1.2(a)+(b) LANDED: THE POINT-EXTENSION CONSTRUCTION (`CoherentConfig.lean §CC.8`,
  axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full serial build green 26s; index regenerated,
  32 new rows described).** The coherent closure is computed as a saturation on `Setoid (Fin n × Fin n)`:
  `extInitSetoid` (X's classes split by `extFlag` individualization flags) → `pairStep` (split each class by all
  **representative-indexed** intersection counts `pairCount` — reference *pairs* name their classes, so the
  iteration touches no quotient, no multiset encoding) → stabilization by the `numClasses` (= `Nat.card` of the
  quotient) pigeonhole within `n²` rounds (`numClasses_growth` strict monovariant + `numClasses_le_sq` bound +
  the `le_of_numClasses_le` rigidity half ⟹ `exists_pairIter_fixed`; `pairStep_stableSetoid` via
  `Function.iterate_fixed`). The four CC axioms read off the chain: coherence IS the fixpoint property
  (`stableSetoid_pairCount`); transpose = the swap invariant carried through every round (`pairIter_swap` via the
  `pairCount_swap` reindexing); diagonal + `T`-singletons = split-only facts of the start (`pairIter_le_init` +
  `extFlag_eq_of_mem`). **The universal property is discharged constructively** (`isPointExtension_pointExtension`):
  base case reads the flags off a fission `Z`'s classes via the derived fiber coherence (`relOf_diag_left_eq` +
  the singleton hypothesis); the inductive step is the counting heart `pairCount_eq_of_zrel` (`Z.inter_card_eq`
  summed fiberwise over `Z`'s class pairs via `card_eq_sum_card_fiberwise`, with the `s`-conditions constant on
  each fiber — exactly the predicted generalization of the §CC.2 argument). Headlines:
  **`exists_isPointExtension`** (the family `ExtensionSeparable` quantifies over is inhabited for every `(X,T)` —
  the predicate is never vacuous) and **`isPointExtension_unique`** (Stage 1.2(b), mutual refinement). Lean
  gotchas for the log: `open scoped Classical` must be SECTION-wide (an `open … in` on one def leaves later
  lemma sites unable to synthesize `DecidablePred` for setoid filters); `Prod.mk.injEq` is an `=` of Props, use
  `Prod.ext_iff` where an `Iff` is needed; prefer `refine congrArg Finset.card (Finset.filter_congr ?_)` over
  `congr 1` on filter cards (instance-stable); a doc-comment must directly precede its decl (no `open … in`
  between); `simpa [Nat.card_eq_fintype_card]` can rewrite BOTH sides of a `Nat.card` inequality (use `calc`).
  **NEXT (the handoff list): Stage 2 — the transport.** Gating action: source Chen–Ponomarenko §4.2
  (`dimWL(X) ≤ dimWL(X_α)+1`) and decide sub-route (c) vs (b); any 1-WL-twin-keyed statement must be at bases
  only (the direction-check verdict). Then the citation-checkpoint assembly (mind the §5 Stage-4 keying note).
- **2026-06-12 — STAGE 2 LANDED MODULO THE CATCH-UP + THE CITATION CHECKPOINT ASSEMBLED (`CoherentConfig.lean
  §CC.9` + `CascadeAffine.lean §S-gate2`, all axiom-clean `[propext, Classical.choice, Quot.sound]`, full serial
  build green 43s; index regenerated, 11 new rows described).** **Sourcing verdict first:** the recursion (41)
  `dimWL(X) ≤ dimWL(X_α)+1` is Cai–Fürer–Immerman 1992 Thm 5.2, and `separable ⟹ dimWL ≤ 2` is
  Fuhlbrück–Köbler–Verbitsky 2020 Thm 2.1 — both *graph-dimWL* currency (they serve the paper's Thm 1.3), not the
  seal's; so sub-route (c) is an anchor, not a transport. **Sub-route (b) then won outright, citation-free:**
  apply `SeparablePointed` of the extension `E` to the **identity** algebraic isomorphism — a same-fiber pair
  `(u,u')` satisfies exactly the pointed condition, the returned `f` is an automorphism of `E` with `f u = u'`,
  it fixes `T` (singleton fibers) and descends to the scheme (`Refines`). Decls: §CC.9
  `SeparablePointed.exists_aut_of_fiber_eq` / `IsPointExtension.aut_fixes` / `Refines.aut_descends` /
  **`fiberTwin_realized_of_separablePointed`** (the core) / `extension_complete_of_separablePointed` (at a rigid
  base, pointedness on non-singleton fibers forces the extension complete — the fiber-level `b(X) ≤ b(G)`);
  §S-gate2 **`WarmTwinsAreFiberTwins`** (the catch-up, carried per-base) / `isSchemeAut_of_relOfPair_eq` /
  **`twinsRealized_of_extensionPointed`** (the transport into the sink) /
  `separatesAtBoundedBase_of_extensionPointed`(`_of_small`) (the general-keyed gates — Stage-4 keying note
  RESOLVED) / **`reachesRigidOrCameron_viaExtensionSeparability`** (the citation checkpoint: the general
  conditional seal modulo {G3 + `Theorem41Statement` + conditions-on-E at non-singleton fibers + the catch-up +
  a base}). **Two structural consequences:** (1) the homogeneous (A)-obligation DISSOLVES — bare `Separable`,
  Lemma 2.6, m-extensions, and the `Ωᵐ` tower are off the critical path entirely; (2) the non-singleton-fiber
  guard on `hhyp` matches the probe exactly (ℤ₂⁴'s X_α fails conditions only at α — a singleton fiber, exempt).
  **Honest accounting:** at a base with a complete extension the catch-up is equivalent in strength to the
  discreteness conclusion — its value is isolation: it carries no separability/group content, only the
  1-WL↔pair-WL comparison, attackable by the refinement engines (intended: B1–B5 forced-triangle propagation
  from condition (i)'s `c=1` dominators). NEXT: the catch-up discharge (STATUS item 5, probe-gate first), then
  Stage 3 (the genuine open math).
- **2026-06-12 — DOC HYGIENE LANDED + THE CATCH-UP PROBE-GATE RAN: GATE GREEN, ENGINE CONFIRMED AT SCHEME LEVEL,
  `b(X) = b(G)` ON BOTH INSTANCES (`Probe_CatchUpGate_BasesAndDominators`, `Theorem41ConditionsProbe.cs`, all 4
  facts green; no Lean touched, build re-verified green 29s + capstones re-checked axiom-clean).**
  *Hygiene:* 00-START-HERE §4 module table gained `Separability.lean` + `CoherentConfig.lean` rows (+ the
  CascadeAffine §S-gate2 mention); the seal-handoff got a 2026-06-12 banner routing to THIS doc (the 06-11
  module-adjoin pointer was itself stale); §5 gained the **family-restricted-Stage-3-suffices** scope note
  (Stage 3.4: `Theorem41Statement` is consumed only at `hcite n E u` — a family-level proof feeds the checkpoint
  through a thin wrapper, the global carry retires unused) and the **assembly-shape** note (Stage 4.3: the
  `_of_small` gate quantifies `hsep`/`hcatch` over ALL `T` because its greedy base is unchosen — assemble through
  the per-`T` gate at probe-validated bases instead).
  *The probe-gate* (control C₁₇ asserted: |Aut|=34, all 136 pairs are bases, catch-up + discreteness everywhere,
  scheme-closure 17/17): **(a) THE GATE IS GREEN** — exhaustive sweeps against exactly-computed `Aut(X)`
  (backtracking; ℤ₄²: |Aut|=32 = translations×{±1}; ℤ₂⁴: |Aut|=160): catch-up holds at **every** swept `|T| ≥ 2`
  (ℤ₄²: all 120 pairs; ℤ₂⁴: all 120 pairs + all 560 triples), in particular at every minimal base (96/96 resp.
  480/480). ℤ₄²: b(G)=2, the 24 non-base pairs are exactly the involution-difference pairs (`x ↦ −x + 2u`
  stabilizer), and base ⟺ 1-WL-discrete ⟺ extension-complete (32/40 per class, all three); ℤ₂⁴: no size-2 base,
  b(G)=3, all 480 bases discrete + complete. So **`b(X) = b(G)`** (2 resp. 3) and at minimal bases the catch-up
  is *exactly* the discreteness conclusion — the honest-accounting equivalence exhibited, not just argued.
  **(b) THE ENGINE EXISTS, ONE LEVEL CHEAPER THAN PLANNED** — the `c=1` two-endpoint dominator closure (seed
  `Determined = T`; pin δ when some determined pair (µ,λ) has `#{w : r(µ,w)=r(µ,δ) ∧ r(w,λ)=r(δ,λ)} = 1` — the
  landed B3 `determined_of_saAdj` pinning shape) **discretizes from every tested minimal base on BOTH instances
  using only X's own rank-4 classes** (scheme level; E-level closure agrees), with **0 one-WL-soundness
  violations at bases**; at non-bases it stalls (1/16 from `{0}`) and is 1-WL-**un**sound (ℤ₄² `T={0}`: E-closure
  pins 4, of which 3 sit in non-singleton warm cells) — so B3-style lemmas must stay base-keyed, consistent with
  the direction check. **Consequences:** (1) state `WarmTwinsAreFiberTwins` at `IsBase T`; no base+O(1)
  escalation needed on the instances; (2) **Route δ's parked feasibility probe effectively ran POSITIVE** (§6 δ
  updated) — a citation-free discharge shape on the landed homogeneous substrate is live: formalize the
  two-endpoint dominator *closure* (a `Saturation`-pattern wrapper over B3) ⟹ `Discrete` ⟹
  `SeparatesAtBoundedBase`, carrying "closure exhausts Ω from the base" as the named hypothesis; (3) the
  family-level "closure completes" proof is the same open crux as Stage 3's conditions — two interchangeable
  consumption shapes, both probe-backed. NEXT: the Lean increment for item 5 — either (α) the per-base catch-up
  against the checkpoint's keying, or (δ′) the dominator-closure engine (recommended: it is citation-free,
  lands on `Separability.lean`/`CascadeAffine.lean` machinery, and its hypothesis is what Stage 3 proves anyway).
- **2026-06-12 — THE δ′ DOMINATOR-CLOSURE ENGINE LANDED (item 5 discharged as plumbing): a citation-free Lean
  path to the seal (`CascadeAffine.lean §S-bridge-δ` + `§S-gate2`, axiom-clean `[propext, Classical.choice,
  Quot.sound]`, no `sorry`, full serial build green 49s; index regenerated, 6 new rows described).** Following the
  probe-gate's positive verdict, formalized the recommended (δ′) shape. Decls, in dependency order: **B3′
  `determined_of_forcedTriangle`** — the smax-free generalisation of `determined_of_saAdj`, taking the
  intersection-number-`=1` fact directly (the `saAdj` proof always discarded its two `smaxAdj` conjuncts via
  `obtain ⟨_, _, hone⟩`, so the body transfers verbatim); the inductive closure **`DominatorReachable S T`**
  (`base : t ∈ T`; `step : reachable α → reachable β → c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1 → reachable γ`);
  **`determinedAt_of_dominatorReachable`** (induction: base = B2 `determined_of_mem_individualized`, step = B3′);
  **`discrete_of_dominatorClosure`** (`(∀ v, DominatorReachable S T v) ⟹ Discrete (warmRefine … T)`, by reading
  `DeterminedAt` at the target of each pair); **`separatesAtBoundedBase_of_dominatorClosure`** (`+ |T| ≤ bound ⟹
  SeparatesAtBoundedBase` — note **no `IsBase` hypothesis**: discreteness is produced outright, lighter than the
  separability route); and the capstone **`reachesRigidOrCameron_viaDominatorClosure`** (same
  `reachesRigidOrCameron_viaPersistentTwinBlock` plumbing as the extension checkpoint, fed by the dominator
  separation). **Net:** the seal now has *two* conditional checkpoints — the extension-separability one
  (`…viaExtensionSeparability`, carries {G3 + `Theorem41Statement` + conditions-on-E + catch-up + base}) and the
  **citation-free δ′ one** (`…viaDominatorClosure`, carries {G3 + `hImprim` + the single `hclo : ∀ v,
  DominatorReachable S T v`}). The catch-up `WarmTwinsAreFiberTwins` is **off every critical path** — δ′ bypasses
  it. The lone remaining open content is **Stage 3** in its lightest form: prove `hclo` for the residue family
  (the `c=1` forced-triangle closure of a bounded base exhausts Ω — probe-confirmed at every minimal base, the
  genuine family-level mathematics). Lean note for the log: B3′ is a *strict* generalisation, so
  `determined_of_saAdj` could be refactored to call it (deferred — non-load-bearing, and the `saAdj_symm`
  extraction is one line). NEXT: Stage 3 (δ′ target recommended), the genuine open math.
- **2026-06-12 — STAGE 3 INCREMENT 1: THE AFFINE FORCED-TRIANGLE CRITERION (`CascadeAffine.lean §S-stage3`,
  axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full serial build green 36s; index regenerated,
  2 rows described).** Began the δ′ Stage-3 frontier (`hclo : ∀ v, DominatorReachable S T v` for the residue
  family). The first brick is the **coordinate translation**: `affineScheme_interNum_eq_one_of_unique` proves, for
  `affineScheme G₀`, that the dominator premise `intersectionNumber (relOfPair α γ)(relOfPair γ β)(relOfPair α β)
  = 1` holds **exactly when `γ` is the unique point `u` with `u−α` in `G₀·(γ−α)` and `β−u` in `G₀·(β−γ)`** — i.e.
  the `c=1` forced-triangle pins `γ` iff the orbit-of-difference triangle is rigid. Proof is clean (no `card_bij`):
  the forced-triangle filter `{u : r(α,u)=r(α,γ) ∧ r(u,β)=r(γ,β)}` is exhibited as the singleton `{γ}` via
  `intersectionNumber_well_defined` + `affineScheme_rel_iff` + `orbMk_affine_eq_iff` (each membership clause
  unfolds to a `G₀`-orbit-of-difference equation, and `huniq` collapses it). `dominatorReachable_affine_step` is
  the matching builder: two reachable points + the orbit-uniqueness ⟹ `DominatorReachable … γ`, via
  `DominatorReachable.step`. **Net:** the δ′ family argument is now stated purely in `G₀`-orbit-of-difference
  terms — the same idiom as `affineScheme_relOfPair_translation` / `discrete_affineScheme_of_jointSeparates`, so it
  composes with the landed affine machinery. Lean note: `rintro rfl` on `u = γ` (γ a parameter) substitutes γ
  *away*; use `intro hu; rw [hu]` to keep γ in scope. **NEXT (Stage 3 increment 2, the genuine open math): the
  family closure** — pick a bounded base `T` (per the probe, the minimal group base) and prove every `v` is
  `DominatorReachable` by iterated `dominatorReachable_affine_step`, for the residue family (`G0pow β`). This is the
  orbit-combinatorics core: showing the rigid-triangle reachability fills `V` from `T`.
- **2026-06-12 — STAGE 3 INCREMENT 2: THE DOMINATOR-CLOSURE EQUIVARIANCE (`CascadeAffine.lean §S-bridge-δ`,
  axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full serial build green 63s; index regenerated,
  2 rows described).** Structural infrastructure for the δ′ family closure. `dominatorReachable_map`: the dominator
  closure is **scheme-automorphism-equivariant** — for `π` a scheme automorphism mapping base `T` into `T'`,
  `DominatorReachable S T v → DominatorReachable S T' (π v)` (induction over `DominatorReachable`; base = `hT`, step
  invariant because `IsSchemeAut.relOfPair_eq` preserves the forced-triangle intersection-number premise — the same
  one-line `relOfPair`-preservation the seal uses throughout). `dominatorReachable_univ_image`: the payoff —
  **complete closure transports across automorphic base images** (`∀ v, DominatorReachable S T v ⟹ ∀ v,
  DominatorReachable S (T.image π) v`, via `π.symm` + `apply_symm_apply`). **Why it matters:** the residue is
  vertex-transitive (schurian), so `Aut(S)` acts transitively on points and richly on bases; the open single-base
  closure now needs proving at only ONE representative base per `Aut(S)`-orbit, not all bases — exactly the
  reduction the probe's "every minimal base closes" suggested was available. General over any `AssociationScheme`
  (not affine-specific), so it composes with the whole scheme substrate. NEXT (Stage 3 increment 3, the genuine
  open math): the single-base closure for `affineScheme (G0pow β)` — pick `T₀` and prove `∀ v, DominatorReachable`
  by the orbit-of-difference combinatorics, the `s(C)` core.
- **2026-06-12 — STAGE 3 INCREMENT 3: THE GENERAL + SCHURIAN FORCED-TRIANGLE CRITERION (`CascadeAffine.lean
  §S-bridge-δ`, axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full serial build green 94s;
  index regenerated, 3 rows described).** Lifted the affine criterion to its natural generality and surfaced the
  group-theoretic form of the open content. (1) **`interNum_eq_one_of_forcedUnique`** — for ANY `AssociationScheme`,
  `c^{r(α,β)}_{r(α,γ),r(γ,β)} = 1` ⟺ `γ` is the unique `u` sharing `γ`'s `relOfPair`-profile to `α` and `β`
  (forced-triangle filter `= {γ}`; same singleton proof as the affine lemma but with no orbit machinery — pure
  `intersectionNumber_well_defined` + `rel_iff_relOfPair`). (2) **`dominatorReachable_step_of_unique`** — its
  `DominatorReachable` step builder; subsumes `dominatorReachable_affine_step` (the orbit-difference `huniq` is this
  `relOfPair` one unfolded) AND covers non-affine residues (e.g. the ℤ₄² amorphic NLS = `orbitalScheme`, not
  `affineScheme`) the affine lemma could not reach. (3) **`dominatorReachable_step_of_stab`** — the schurian reading:
  `relOfPair`-profile equality is a point-stabiliser-orbit relation (schurian axiom `S.schurian`), so the criterion
  is **`Stab(α)·γ ∩ Stab(β)·γ = {γ}`** — `γ` is pinned exactly when the two point-stabiliser orbits of `γ` meet only
  at `γ`. This is the geometric handle the single-base closure wants: a base `T₀` has `⋂_{t∈T₀} Stab(t) = 1`, so its
  stabiliser orbits must intersect down toward points, and the closure question becomes "do the pairwise
  stabiliser-orbit intersections propagate reachability from `T₀` to all of `V`". **Net:** the open content is now
  framed group-theoretically (stabiliser-orbit intersections), at the right generality (any schurian residue, not
  just affine). NEXT (Stage 3 increment 4, the genuine open math): the single-base closure — exhibit `T₀` and prove
  the stabiliser-orbit-intersection propagation for the residue family. Note: `affineScheme_interNum_eq_one_of_unique`
  is now a special case of (1), left in place (orbit-difference convenience form; non-load-bearing to refactor).
- **2026-06-13 — STAGE 3 INCREMENT 4a: THE ITERATION ENGINE — single-base closure from a pinning rank
  (`CascadeAffine.lean §S-bridge-δ`, `dominatorReachable_of_rank`, axiom-clean `[propext, Classical.choice,
  Quot.sound]`, no `sorry`, full serial build green 198s; index regenerated, 1 row described).** The δ′ toolkit had
  step builders (`dominatorReachable_step_of_unique`/`_of_stab`/`_affine_step`) and the equivariance reduction, but
  **nothing that iterates the step to exhaust Ω** — the actual single-base closure had no engine. `dominatorReachable_of_rank`
  is that brick: given a rank function `rank : Fin n → ℕ` with (i) every rank-`0` point in `T` and (ii) every
  positive-rank `γ` forced-triangle-pinned (the `relOfPair`-profile uniqueness of `interNum_eq_one_of_forcedUnique`)
  by two **strictly-lower-rank** points, strong induction on the rank yields `∀ v, DominatorReachable S T v`. Proof:
  auxiliary `∀ k v, rank v = k → reachable` by `Nat.strong_induction_on` on `k`; rank-0 ⟹ `base`, positive ⟹ obtain
  the two lower-rank pinners, apply the IH to each (their rank `< k` via `hv ▸ hα`), feed `dominatorReachable_step_of_unique`.
  **What it buys:** the family-level open content is now reduced from the global, hard-to-attack "the `c=1` closure
  exhausts Ω" to the **concrete, checkable** "exhibit a pinning rank" — exactly the *clean sufficient condition* the
  δ′ Stage-3 endpoint targets (the rank = number of pinning rounds the stabiliser-orbit intersections take to reach
  each point; a base has `⋂ Stab(t) = 1`). **Net (the open piece is now purely the rank witness):** to close the
  residue family it remains to *define the rank and verify the pinning at each level* — the genuine `s(C)` arithmetic
  (the cyclic `(r+1−r·h) ∈ H → h = 1` core, char-2 midpoints excluded), now cleanly isolated behind a general,
  provable, axiom-clean interface. NEXT (increment 4b, the genuine open math): the affine cyclic arithmetic reduction
  (`affineScheme` pinning ⟺ `∀ h ∈ H, (r+1−r·h) ∈ H → h = 1`) to translate the rank's pinning obligation into pure
  `F_q^×`-coset arithmetic, then exhibit a propagating rank/base for the residue family.
- **2026-06-13 — STAGE 3 INCREMENT 4b: THE AFFINE CYCLIC ARITHMETIC REDUCTION (`CascadeAffine.lean §S-stage3-δ`,
  `fieldOf` / `G0pow_orbit_iff` / `dominatorReachable_G0pow_step`, axiom-clean `[propext, Classical.choice,
  Quot.sound]`, no `sorry`, full serial build green 121s first try; index regenerated, 3 rows described).**
  Translates the cyclotomic family's forced-triangle pinning from `G₀`-orbit-of-difference language into pure
  `F_q`-power arithmetic. (1) **`fieldOf hd x := (efield hd).symm (affineE.symm x)`** — the point→`F_q` coordinate.
  (2) **`G0pow_orbit_iff`** — the core: a `G0pow g = ⟨mul g⟩`-orbit relation between coordinate vectors is exactly
  multiplication by a power of `g` through the field iso (`∃ g₀ ∈ G0pow g, g₀ v = w ↔ ∃ k:ℤ, ↑(g^k)·efield.symm v =
  efield.symm w`); proof = `Subgroup.mem_zpowers_iff` + `sigmaPow_zpow_apply` (`σ_g^k` = `·g^k` through `efield`) +
  `efield` injectivity. (3) **`dominatorReachable_G0pow_step`** — the forced-triangle step builder with `huniq` in
  `F_q` powers (`g^k·(fieldOf u−fieldOf α)=fieldOf γ−fieldOf α`, the symmetric one for `β`), obtained from
  `dominatorReachable_affine_step` by feeding each orbit hypothesis through `G0pow_orbit_iff.mp` + `map_sub`
  (`efield.symm` is linear over the difference). **Net:** the δ′ cyclotomic single-base closure now reasons in pure
  `F_q` arithmetic — define a rank, and for each positive-rank `γ` discharge `huniq` as an `F_q`-power uniqueness — with
  no orbital / intersection-number bookkeeping. **NEXT = increment 4c (the field-division packaging):** the ratio form
  `∀ h ∈ ⟨g⟩, (r+1−r·h) ∈ ⟨g⟩ → h = 1` with `r = (fieldOf γ − fieldOf α)/(fieldOf β − fieldOf γ)` (needs `b ≠ c` and
  unit/nonzero handling) — it divides out the field differences and makes the char-2-midpoint obstruction (`r=1` never
  pins) explicit; then the genuine open piece, the pinning-rank witness for the residue family.
- **2026-06-13 — STAGE 3 INCREMENT 4c: THE RATIO-FORM STEP BUILDER (`CascadeAffine.lean §S-stage3-δ`,
  `dominatorReachable_G0pow_ratio_step`, axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full
  serial build green 115s first try; index regenerated, 1 row described).** The field-division packaging of 4b: the
  cyclotomic forced-triangle step with the two `F_q`-difference equations *divided through*. For distinct field
  coordinates (`fieldOf γ ≠ fieldOf α`, `fieldOf β ≠ fieldOf γ`), `γ` is pinned by `α, β` once the only `h ∈ F_q`
  that is **both** a power of `g` and has `1 + r·(1−h)` a power of `g` — cross-ratio `r = (fieldOf γ − fieldOf α)/
  (fieldOf β − fieldOf γ)` — is `h = 1`. Proof: from `dominatorReachable_G0pow_step`, set `h = (x−a)/(c−a)` for the
  variable `x = fieldOf u` (cond 1 ⟺ `h ∈ ⟨g⟩`, via `eq_div_iff` + `zpow_neg`), compute `(b−x)/(b−c) = 1 + r(1−h)`
  (`field_simp; ring`) so cond 2 ⟺ `1 + r(1−h) ∈ ⟨g⟩`, then `hpin` gives `h = 1 ⟺ x = c ⟺ u = γ` (`fieldOf`
  injective). **This is the `(r+1 − r·h) ∈ ⟨g⟩ → h = 1` reduction of §5 — the closest Lean form to the open
  cyclotomic `s(C)` arithmetic, and it makes the char-2-midpoint obstruction explicit in the Lean statement**
  (`r = 1` ⟹ `1 + (1−h) = 2 − h = h` in char 2 ⟹ every `h` admitted ⟹ nothing pins; char-2 residues need
  non-midpoint triangles). **Net: the δ′ cyclotomic toolkit is complete** — iteration engine (4a) + `F_q`-power
  step (4b) + ratio-arithmetic step (4c). The lone open piece is the **pinning-rank witness**: exhibit a base `T₀`
  and a rank function whose per-level pinning is discharged by `dominatorReachable_G0pow_ratio_step` (the genuine
  open `s(C)` mathematics; the affine slice is cited-closed, so the new coverage target is the non-affine residue,
  where the general/schurian step builders apply instead). NEXT = the rank witness (open math) — or, lower-priority,
  the post-Stage-3 full `hImprim` discharge.
- **2026-06-13 — STAGE 3, THE MATH: FIRST END-TO-END CLOSURE OF A REAL FAMILY (`CascadeAffine.lean §S-bridge-δ` +
  `§S-stage3-δ`; `dominatorReachable_of_basePinsAll`, `fieldOf_injective`, `exists_zpow_neg_one_iff` (private),
  `dominatorReachable_G0pow_neg`, `reachesRigidOrCameron_viaG0powNeg`; all axiom-clean `[propext, Classical.choice,
  Quot.sound]`, no `sorry`, full serial build green ~94–128s, all first try; index regenerated, rows described).**
  The first **actual discharge** of the δ′ seal's open `hclo` for a real `affineScheme` family — not more
  infrastructure, a closure. (1) **`dominatorReachable_of_basePinsAll`** — the clean checkable one-round criterion
  (every non-base point pinned by two base points ⟹ closure; the `rank∈{0,1}` instance of 4a). (2) The genuine
  result **`dominatorReachable_G0pow_neg`**: for `g = -1` (so `⟨g⟩ = {1,-1}`) over **odd characteristic** (`p ≠ 2`),
  *every* point is dominator-reachable from *any* 2-element base `{α,β}`, `α≠β`. Math: the cross-ratio
  `r = (c−a)/(b−c)` of pairwise-distinct points satisfies `r ∉ {0,-1}`, so for the only nontrivial `h = -1 ∈ ⟨g⟩`
  the value `1 + 2r ∉ {1,-1} = ⟨g⟩` (uses `2 ≠ 0`), the pinning antecedent fails, only `h = 1` survives —
  discharged through `dominatorReachable_G0pow_ratio_step`; `fieldOf_injective` carries distinctness, `2 ≠ 0` via
  `CharP.cast_eq_zero_iff`, the field algebra via `linear_combination`. **Char ≠ 2 is essential — exactly the
  documented char-2-midpoint obstruction** (`p = 2` ⟹ `⟨g⟩ = {1}`, the argument collapses). (3)
  **`reachesRigidOrCameron_viaG0powNeg`** feeds (2) into `reachesRigidOrCameron_viaDominatorClosure`: the seal on the
  whole `g = -1` family (rank ≥ 3, i.e. `q ≥ 5`) **with the open `hclo` GONE — proved, not carried**; only the
  standard {G3 + `hne` + `hrank` + `hImprim`} remain. **Significance:** the δ′ route is *not vacuous* — it discharges
  the seal's open mathematical content outright on a genuine family, and removes the cyclotomic citation for the
  `H={±1}` sub-family. **Honest scope:** this is the odd-char `|H|=2` slice (one-round; no multi-round arithmetic);
  the *general* cyclotomic family (larger `H`, and char-2 — the Clebsch residue) and the **non-affine** residue (the
  genuine new-coverage target, via the general/schurian builders) remain the open `s(C)` core. NEXT = larger `H` /
  a multi-round rank witness, or the non-affine residue.
- **2026-06-13 — STAGE 3, MULTI-ROUND: THE SUBFIELD FAMILY `H=K^×` CLOSES IN TWO ROUNDS (`CascadeAffine.lean
  §S-stage3-δ`; `ratio_not_mem_num_out`, `ratio_not_mem_denom_out` (private), `dominatorReachable_G0pow_subfield_step`,
  `dominatorReachable_G0pow_subfield`; all axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, full
  serial build green 108s; index regenerated, rows described).** The first genuinely **multi-round** (`|H|>2`)
  closure. First the necessity check: one-round-from-a-2-base works **iff `|H|≤2`** (as `r` ranges over `F_q∖{0,-1}`,
  `1+r(1-h)` ranges over `F_q∖{1,h}`, so "no triangle blocked" forces `H⊆{1,h}`) — so `|H|>2` genuinely needs
  iteration. The tractable larger-`H` family is **`H=K^×` for a subfield `K⊊F_q`**, with a **size-free** pinning
  rule: `r=(c−a)/(b−c)∉K ⟹ γ pinned` (`dominatorReachable_G0pow_subfield_step`; for `h∈K^×∖{1}`, `1−h∈K^×` ⟹
  `r(1−h)∉K` ⟹ `1+r(1−h)∉K⊇H`). The 2-round closure (`dominatorReachable_G0pow_subfield`) from a base of two
  `K`-points: round 1 pins all non-`K` points by `α,β` (`ratio_not_mem_num_out`), round 2 pins all `K` points by `α`
  and a reached non-`K` point (`ratio_not_mem_denom_out`). Carries `⟨g⟩=K^×` (`hHK`) + a non-`K` witness as field
  facts; instantiation (`K=F_p`, `g=fqGen^{(p^d−1)/(p−1)}`) is field-theory plumbing, no new open math.
  **IMPORTANT HONEST CAVEAT:** the `K^×` family is **IMPRIMITIVE** (`F_p^×` acts as scalars, preserving every
  `F_p`-subspace ⟹ reducible `G₀` ⟹ not primitive) — so it is the **hImprim/G2-A** case, *not* the primitive G2-B
  residue. This is a real multi-round closure that **validates the iteration engine for `|H|>2` and gives a reusable
  size-free subfield pinning lemma**, but the **primitive** larger-`H` case (irreducible `G₀`, field-generating `g` —
  the Clebsch-type / char-2 residue) has no subfield shortcut and remains the genuine open `s(C)` core. NEXT = the
  primitive irreducible multi-round case (no `K` structure — the hard Frobenius/cyclotomic arithmetic), or the
  non-affine residue.
- **2026-06-13 — PROBE: THE NON-AFFINE RESIDUE'S CLOSURE CONSTRUCTION EXTRACTED — it is UNIFORM, MULTI-ROUND,
  and AMORPHIC (`Theorem41ConditionsProbe.Probe_ExtractPinningRank`, green; no production/Lean touched).** Following
  the §1A analysis (the load-bearing claim is the separability content itself, not elementary smallness ⟹ a blind
  general Lean push stalls; extract the concrete construction first), added `DominatorRank` (rank-extracting closure:
  BFS round + pinning pair per point) and the extraction probe. **Findings on the primitive ℤ₄² amorphic-NLS bullseye
  (the genuine G2-B target, n=16):** (1) **96/120 pairs are completing 2-bases**; sample base `{0,1}` closes in
  **depth 3 rounds**, layers `[2,2,6,6]`. (2) **Genuinely multi-round** — intermediate (non-base) pinners are
  required (not one-round-in-disguise). (3) **THE CONSTRUCTION IS UNIFORM AND STRUCTURAL:** every pinning triangle's
  edge-triple `(rel(µ,d),rel(d,λ),rel(µ,λ))` is a **permutation of {1,2,3}** — a **rainbow triangle** (three distinct
  non-diagonal colours) — and all six orderings occur ≈evenly (248/241/225/222/206/202 over all bases); **no triangle
  with a repeated or diagonal colour ever pins.** So the pinning rule is exactly *"rainbow triangle ⟹ rigid (c=1)"* —
  the **amorphic S₃ structure made operational**, which is precisely the mechanism §1A's carve-out predicted would
  drive recovery on the non-Cameron residue. **The char-2 anchor ℤ₂⁴:** **0/120** completing 2-bases (needs a
  ≥3-base) — the midpoint obstruction at the base-size level. **Strategic read:** on-track (clean uniform mechanism,
  no falsifier; the bullseye recovers exactly as predicted). The abstract lemma the construction points to is
  *"rainbow-rigidity (rank-4, rainbow c=1) + a 2-base ⟹ closure in O(1) rounds."* NEXT (the abstraction step):
  formalize the rainbow-rigidity closure — either abstractly (carry rainbow-c=1 + the round-3 geometry as
  hypotheses) or concretely (hard-code the 16×16 colour matrix as a Lean `AssociationScheme`, `decide` the axioms +
  the 16 rainbow-pinning derivations — feasible only with plain `decide`, since `native_decide` violates the axiom
  bar). **CAVEAT:** rainbow-c=1 is special to the Clebsch parameters `(16,5,0,2)`, not automatic for all amorphic
  rank-4, so the abstraction is parameter-scoped, not "all amorphic."
- **2026-06-13 — THE CONCRETE ROUTE LANDED: THE FIRST NON-AFFINE δ′ CLOSURE IN LEAN (`ChainDescent/ClebschConcrete.lean`,
  axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no `native_decide`; in the serial build, the
  module compiles in ~56s; index regenerated, 11 rows).** Took the concrete route from the extraction probe. **Spike
  first:** confirmed plain `decide` can verify the scheme-coherence axiom on the 16×16 matrix (feasible but heavy
  ~66s user, swap-prone under full Mathlib). **Then built it, OOM-managed:** `clebschZ4Scheme : AssociationScheme 16`
  from the hard-coded colour matrix (`clebschZ4ColF`), all four axioms by `decide` — coherence **split per-colour**
  (`fin_cases k`) to quarter the kernel working-set (one giant `decide` OOM-killed the machine; the split + VSCode
  closed fixed it). The closure `clebschZ4_closure : ∀ v, DominatorReachable clebschZ4Scheme {0,1} v` via a local
  **`interNum`-keyed** rank engine `domReach_of_rank_pin` (the Nat-equality `c=1` premise is `decide`-friendly; the
  `relOfPair`-uniqueness form's nested implications have no synthesizable `Decidable`), fed the probe rank
  (`clebschZ4Rank`) + explicit rainbow pinners (`clebschZ4Pin`), with the `relOfPair`→matrix bridge
  (`clebschZ4_relOfPair`) so `decide` checks each rainbow triangle is rigid. Payoff `clebschZ4_discrete`: the ℤ₄²
  Clebsch scheme is **`Discrete` after individualizing `{0,1}`** = `b(X) ≤ 2`, a non-affine
  `SeparatesAtBoundedBase`-grade recovery, fully in Lean. **Significance:** the seal's open `hclo` content is now
  *discharged concretely for a real non-affine primitive G2-B residue* — an existence witness that the δ′ route
  reaches the genuine bullseye, not just the affine/citable corner. **Scope (honest):** one scheme, parameter-scoped
  to Clebsch `(16,5,0,2)`; stays at `AssociationScheme` level (`Discrete`), does **not** feed the seal capstone
  (that needs `SchurianScheme` = the automorphism data, deferred); and it is `decide`-checked, not a general family
  proof. **Lean lessons:** `decide` has no `Decidable (p→q→r)` for nested implications (single `p→q` is fine — that
  is why the `interNum`-form engine was needed); `∃!` has no synthesizable `Decidable` (give the term); split big
  `decide`s with `fin_cases` to bound kernel memory; `native_decide` is BANNED (adds `ofReduceBool`). NEXT = either
  abstract the rainbow-rigidity closure (parameter-scoped family lemma), wire a `SchurianScheme` instance to feed the
  seal, or return to the general/primitive open core.

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

**General-CC substrate (LANDED 2026-06-12, build on these):** `CoherentConfig` / `interNum` / `transposeRel` /
`relOf_diag_left_eq` (derived fiber coherence) / `AssociationScheme.toCoherentConfig` / general `AlgIso` /
`Separable` / `SeparablePointed` / `Dominates` / `DominationCondition` / `IsCoupleExtension` /
`CoupleExtensionCondition` / `Theorem41Hypotheses` / **`Theorem41Statement`** (the cited carry) / `Refines` /
`SingletonFiber` / `IsPointExtension` / `ExtensionSeparable` / `discreteCC` (`CoherentConfig.lean`).
**The §CC.8 construction (LANDED 2026-06-12):** `extFlag` / `extInitSetoid` / `pairCount` / `pairStep` /
`pairIter` (+ `_zero`/`_succ`/`_le_init`/`_swap`) / `numClasses` (+ `_le_of_le`/`le_of_numClasses_le`/`_le_sq`/
`_growth`) / `exists_pairIter_fixed` / `stableSetoid` / `pairStep_stableSetoid` / `stableSetoid_pairCount` /
`pairCount_swap` / `pairCount_eq_of_zrel` (the counting heart) / `zrel_le_pairIter` / `stableEquiv`(`_eq_iff`) /
**`pointExtension`** / `pointExtension_relOf_eq_iff` / **`isPointExtension_pointExtension`** /
**`exists_isPointExtension`** / `isPointExtension_unique` (`CoherentConfig.lean §CC.8`).
**The Stage-2 transport (LANDED 2026-06-12, modulo the catch-up):** `SeparablePointed.exists_aut_of_fiber_eq` /
`IsPointExtension.aut_fixes` / `Refines.aut_descends` / **`fiberTwin_realized_of_separablePointed`** /
`extension_complete_of_separablePointed` (`CoherentConfig.lean §CC.9`); **`WarmTwinsAreFiberTwins`** (the
isolated catch-up) / `isSchemeAut_of_relOfPair_eq` / **`twinsRealized_of_extensionPointed`** /
`separatesAtBoundedBase_of_extensionPointed`(`_of_small`) /
**`reachesRigidOrCameron_viaExtensionSeparability`** (the citation checkpoint) (`CascadeAffine.lean §S-gate2`).
**The δ′ dominator-closure engine (LANDED 2026-06-12, CITATION-FREE — the lighter seal path):**
**`determined_of_forcedTriangle`** (B3′, smax-free) (`CascadeAffine.lean §S-bridge`) / **`DominatorReachable`** /
`determinedAt_of_dominatorReachable` / **`discrete_of_dominatorClosure`** /
**`separatesAtBoundedBase_of_dominatorClosure`** (`CascadeAffine.lean §S-bridge-δ`) /
**`reachesRigidOrCameron_viaDominatorClosure`** (the citation-free checkpoint, carries only
{G3 + `hImprim` + `hclo : ∀ v, DominatorReachable S T v`}) (`CascadeAffine.lean §S-gate2`).
**Stage 3 substrate — the affine forced-triangle criterion (LANDED 2026-06-12, the δ′ family argument runs on
these):** the general (any-scheme) criterion **`interNum_eq_one_of_forcedUnique`** (`c=1` ⟺ filter `={γ}`) /
**`dominatorReachable_step_of_unique`** (the general step builder, subsumes the affine one + non-affine residues) /
**`dominatorReachable_step_of_stab`** (the schurian `Stab(α)·γ ∩ Stab(β)·γ = {γ}` reading — the closure's geometric
handle); the affine specialisation **`affineScheme_interNum_eq_one_of_unique`** (orbit-of-difference uniqueness) /
**`dominatorReachable_affine_step`** (`CascadeAffine.lean §S-stage3`); the closure-equivariance reduction
**`dominatorReachable_map`** / **`dominatorReachable_univ_image`** (complete closure transports across `Aut(S)`-images
of the base — prove at one representative); the **iteration engine `dominatorReachable_of_rank`** (a well-founded
pinning rank ⟹ `∀ v, DominatorReachable S T v` — the brick turning the step builders into a global closure) and the
**one-round criterion `dominatorReachable_of_basePinsAll`** (every non-base point pinned by two base points ⟹ closure)
(`CascadeAffine.lean §S-bridge-δ`); the **cyclotomic arithmetic reduction** **`fieldOf`** (point→`F_q`) /
**`fieldOf_injective`** /
**`G0pow_orbit_iff`** (a `G0pow g`-orbit relation ⟺ multiplication by `g^k` through the field iso) /
**`dominatorReachable_G0pow_step`** (the forced-triangle step builder with `huniq` in pure `F_q` powers) /
**`dominatorReachable_G0pow_ratio_step`** (the ratio form `(r+1−r·h)∈⟨g⟩→h=1`, `r=(c−a)/(b−c)` — divides out the
field differences, exposes the char-2-midpoint obstruction); **the FIRST family closure** —
**`dominatorReachable_G0pow_neg`** (`g=-1`, odd char: any 2-base closes in one round) and the seal capstone
**`reachesRigidOrCameron_viaG0powNeg`** (the seal on the `g=-1` family with `hclo` PROVED, not carried — only
{G3+hne+hrank+hImprim} remain); the **multi-round subfield closure** —
**`dominatorReachable_G0pow_subfield_step`** (size-free `r∉K ⟹ pinned`) / **`dominatorReachable_G0pow_subfield`**
(the `H=K^×` family closes in 2 rounds; **imprimitive — validates the engine, not the primitive residue**) +
private `ratio_not_mem_num_out`/`_denom_out`
(`CascadeAffine.lean §S-stage3-δ`). Open (the genuine `s(C)` core): the **pinning-rank witness** for the
**primitive irreducible** larger `H` (no subfield shortcut), char-2 (Clebsch), and the **non-affine** residue
(new-coverage target) — define `rank` and verify per-level pinning via the general/schurian/`F_q`-power builders.

**The concrete non-affine closure (LANDED 2026-06-13, `ChainDescent/ClebschConcrete.lean` — the FIRST non-affine
δ′ closure in Lean):** **`clebschZ4Scheme`** (the ℤ₄² amorphic-NLS Clebsch scheme as a hard-coded
`AssociationScheme 16`, axioms by `decide`) / **`clebschZ4_closure`** (`∀ v, DominatorReachable clebschZ4Scheme
{0,1} v` — the `hclo` discharged for the real non-affine bullseye) / **`clebschZ4_discrete`** (`b(X) ≤ 2`); built
on `clebschZ4ColF` (the colour matrix) / `clebschZ4_relOfPair` (the bridge) / `clebschZ4Rank` + `clebschZ4Pin` (the
probe rank/pinners) / private `domReach_of_rank_pin` (the `interNum`-keyed rank engine). Axiom-clean, no
`native_decide`. Scope: parameter-scoped to Clebsch `(16,5,0,2)`, `AssociationScheme`-level (does not feed the seal
capstone — needs `SchurianScheme`).

**PV Thm 3.1 `c=1` substrate (reuse heavily):** `saAdj` / `saAdj_symm` / `valency_mul_intersectionNumber` /
`transport` / `transport_step` / `saComp` / `compsOf` / `separatesAtBoundedBase_of_sparseSeparable`
(`Separability.lean §S.1–S.16`); the warmRefine bridge `relOfPair_eq_of_warmRefine_determined` /
`determined_of_saAdj` / `discrete_of_connectivity` / `separatesAtBoundedBase_of_connectivity` /
`warmRefine_refineStep_samePartition` (`CascadeAffine.lean §S-bridge/§S-stab`).

**Papers:** Ponomarenko, arXiv:2006.13592 (**`docs/papers/p4paper-arxiv-2006.13592.txt`**, version-controlled) —
**Thm 4.1** (§4, the target; statement at line ~552 in the extract), **Lemma 2.6** (one-pt ext separable ⟹
2-separable, line ~299), **m-extension** (§2), Thm 1.1/1.2 (cyclotomic). Ponomarenko–Vasil'ev, arXiv:1602.07132
(**`docs/papers/cartan-arxiv-1602.07132.txt`**, version-controlled) — **Thm 2.5** (1-regular `(m−1)`-ext ⟹
`m`-separable, line ~388), base defs (§2.2), **Thm 3.1** (the sparse condition, already formalised). Chen–Ponomarenko,
*Coherent Configurations* (the monograph, p4paper ref **[3]**) — the `b(X) ↔ s(C) ↔ dimWL` theory incl.
`dimWL(X) ≤ dimWL(X_α) + 1` (§4.2; the transport lead, Stage 2.2(c)). Evdokimov–Ponomarenko,
*Separability number and Schurity number of coherent configurations*, EJC 2000 (ref **[4]**) — `s(X)`/`t(X)`
foundations, Thm 4.6(1) (source of Lemma 2.6). Extraction: `pdf2txt`, then **`scripts/clean-extracted-text.py`** or
grep finds nothing (NUL bytes; §0 gotcha). The two papers above are committed cleaned (`docs/papers/README.md`).

**Provenance (do not need to read, but for the curious):** the seal-bridge gate / transport / (C) findings are in
`chain-descent-module-adjoin-plan.md §9`; the seal state in `chain-descent-seal-handoff.md`; the project overview in
`docs/00-START-HERE.md`.
