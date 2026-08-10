# Hard-won steers, dead routes, probe history, and cited-premise corrections (archive)

> **What this is.** The durable, version-controlled home for the cross-session *steers* that used to live in
> `MEMORY.md` (the auto-memory index) — corrections, dead routes, vacuity traps, probe-falsifier records, and
> calibration corrections that save a future session from re-walking a settled dead end. Migrated out of memory
> 2026-06-15 to free memory space (the live frontier + scope are now fully carried by the doc STATUS blocks). Most
> of these are *also* stated in a live doc (cross-referenced); this file is the consolidated, never-lost copy.
> **Consult before re-attempting any route that looks novel — it may be settled here.** Authoritative current
> state is always the doc STATUS blocks + `PublicTheoremIndex.md` + the Lean source, never this archive.

Live-doc homes referenced below: **build doc** = `chain-descent-general-cc-separability.md`; **route doc** =
`chain-descent-a2-potential-route.md`; **cxt-scoping** = `chain-descent-cxt-scoping.md`; **A1** =
`chain-descent-a1-cc-substrate.md`; **exh-obstruction** = `chain-descent-exhaustive-obstruction.md`;
**seal-handoff** = `chain-descent-seal-handoff.md`.

---

## 1. Crux / seal direction

- **The crux is NOT "GI∈P, give up" — do not pattern-match to hopelessness** (full analysis: build doc §1A).
  "bounded base = bounded WL = GI∈P" conflates the RESIDUE with ALL schemes. Every unbounded-WL family is carved
  into a *separate* leg: CFI→`hImprim`, circulants/abelian→leg B, large/Johnson/**hidden-Johnson**→Cameron (this is
  *why* the last leg is "or Cameron"). The residue (primitive, small, non-abelian, non-Cameron) is the **tame
  remainder** — 0 empirical witnesses, ℤ₄² bullseye recovers at depth 2. **Isolation is the METHOD (applied
  recursively), not a surrender;** every carve above was once itself an "apparent GI∈P" that got dissolved, and the
  crux is the last residue — hard *open*, not impossible (it was the *most-likely* closure route). Closure angle =
  **separability** (Thm 4.1 domination+couple conditions, probe-verified on the extension `X_α`; structural reason =
  Cameron's dichotomy → smallness forces the bounded regime). **Off-track falsifier** = a primitive-small-non-abelian-
  non-Cameron scheme with *unbounded* base (⟹ "or Cameron" is the wrong carve, seal false). Discipline: before saying
  "GI∈P" about a recovery claim, ask **"what's still IN the residue?"** (topic file `project_separability_landscape_2026-06-07.md`.)

- **No re-keying of the rigid predicate (`ReachesRigid`) closes the seal.** The abstract capstone carries both
  branch reductions for any keying; closure ⟺ the leaks (G2) are empty ⟺ the self-detection lemma. Stop hunting
  a better rigid predicate (seal-handoff §4.0).

- **`hImprim` (the imprimitive branch / G2-A) is CARRIED undischarged in EVERY capstone — the clean seal needs it
  too, not just G2-B/PotentialDrops.** The docs' "sole irreducible carried content is G2-B" is the *math* claim
  (hImprim reduces to the crux on smaller schurian constituents via the block tower), NOT a Lean fact (no induction
  wires it). Not free: not every residual is primitive, and unconditional block-visibility is DEAD (Shrikhande). Its
  character is *deferred infrastructure on known math*, distinct from the genuine open math. **Two discharge routes**
  (full detail: exh-obstruction §0.7.2 "(3b) RE-CLASSIFIED 2026-06-13"): **(a) the residue-family escape (cheap,
  near-term):** prove `G₀Irreducible ⟹ IsPrimitive` (reverse of landed `isPrimitive_affineScheme_imp_irreducible`)
  ⟹ `hImprim` vacuous on `clebschScheme`/`affineScheme` ⟹ clean seal `modulo {G3 + family crux}` on the family
  (does NOT cover imprimitive residuals). **(b) the full discharge = build (3b)** (re-attempt AFTER the crux closes):
  materialize quotient `S//I` + fiber as smaller `SchurianScheme` (both schurian by the LANDED §11.1 gate
  `schemeBlock_fiber_transitive`/`schemeBlocks_transitive`) → strong induction on scheme size → feed
  `reachesRigid_of_blockVisibleDecomposition`. **(3b) is RE-CLASSIFIED from "DO NOT BUILD" to deferred-re-attempt**:
  two old blockers are stale — `refineStep` is CONCRETE since 2026-05-30 (cross-size transport now statable), and
  the §11.1 schurity gate landed (constituents proved schurian + smaller). The 2026-06-05 "do not build" was right
  for the *conditional* seal only.

- **The block / scheme-congruence route to G2-B is DEAD on the primitive floor.**
  `intraCellRelations_eq_singleton_zero_of_primitive`: a primitive scheme forces the intra-cell block to `{0}`, so
  it only ever discharges the *imprimitive* case (already handled by `hImprim`). Genuine G2-B is a *non-congruence
  amorphic WL-fusion* (the Clebsch `S₃`) no closed-subset object captures ⟹ attack via the **forward/counting** crux
  (base-homogeneous separability gap broken at base+O(1)), NOT a block construction. (Also build doc §1 finding 3 + §7.)

- **Frobenius separation RETRACTED** — the affine-cyclic gap is amorphic-`S₃`, not Galois. The general crux is
  mechanism-agnostic (`PersistentTwinYieldsBlock`), no Frobenius. (The affine slice was then closed via the full
  `ΓL`-adjoin — GL mult-part killed by one individualisation + Galois Frobenius-part by a field-generating set — /
  cited cyclotomic 2-separability; detail in build doc + module-adjoin §9 + topic file
  `project_cartan_2separability_lead_2026-06-11.md`.) **Lesson that generalises: "Frobenius ALONE is only the `Z₂`."**

- **DO NOT anchor the crux on `not_comm_of_orbit_disagree` (C₇ correction).** The concealment is the **separability
  gap** (`¬EdgeGenerates` — can't reconstruct `relOfPair`), NOT group non-abelianness. Symmetric schemes commute
  regardless of group; C₇/D₇ is non-abelian yet recovers via metric. For schurian schemes relations ARE Stab(v)-orbits
  (`vProfile_iff_schemeOrbit`) ⟹ the gap is pure intersection-number determinacy, attackable with NO group detour.
  (Also build doc §7.)

- **The realization half is LANDED** (`schemePartFrom` / `iterSet_refines_schemePartFrom` /
  `discrete_of_kRoundRelationSeparates`); only EXISTENCE of a separating small base is open. **Depth-1 is provably
  insufficient** (cyclotomic + 5 catalogue schemes fail depth-1 `EdgeGenerates` yet recover) — the object is
  multi-base, base+O(1).

---

## 2. A2 frontier — older steers (now mostly in cxt-scoping §5/§6 + build doc + route doc)

- **A2 = `c(X_T),k(X_T)=O(1)` at an O(1) base = bounded WL-dim; OPEN, not citable** (two deep-research passes, M2 +
  A2-research). **Don't re-hunt a citation.** A1's abundance lemma `§CC.18` consumes it via PADDING from a small base
  (`§CC.19` monotonicity) — so A2's deliverable is the bound at ONE small base, not "meet the threshold" (the
  threshold can't hold at non-discrete `X_T`: contrapositive forces `(k−1)c≥|T|`).

- **M1 probe (the target is TRUE).** `c(X_T)` AND `k(X_T)` collapse to O(1) after O(1) points, UNIFORMLY (rank 3/4,
  cyclotomic/amorphic, char 2/odd, n=10-41); **no falsifier**; **char-2 is the hard case** (`k(X₁)~n/2`, `k(X₂)=O(1)`;
  needs 2 pts). Caveat: testing the δ′ closure ON `X_T` AT a base is VACUOUS (discrete there) — the signal is the c/k collapse.

- **hcatch ⟺ 1-WL-discreteness at a complete extension** (`warmTwinsAreFiberTwins_of_warmDiscrete` +
  `discrete_warmRefine_of_extensionComplete`). So for n≥25 `hcatch` IS the open content (`c(X_T)` layer), **NOT cheap
  plumbing**; FREE only where scheme-level δ′ closes (n=16, `warmTwinsAreFiberTwins_of_dominatorClosure`). (Build doc §5.1.)

- **The ladder collapses to the rank-3 base case, NOT a cheap pattern** (A2-research). Every uniform A2 statement is
  the same open theorem; the residue's hard families are carved out, so the open core = "primitive non-conference
  large-motion SRG ⟹ b(X)=O(log n)" (morally known via Babai's quasipoly-GI algorithm + the CGGP `base≤2⟹WL≤4`
  family, but NO portable proof). This is the route doc's **row 4** (the open core of `PotentialDrops`).

---

## 3. Vacuity traps (predicates that look like progress but are trivially true)

- **`SchemeReproduced := ∃ gens, closure = SchemeAutGroup` is TRIVIALLY TRUE** (every finite group is fin-gen);
  ALL orbit-level coverage (hreach / hfiber / CoversOrbits / NoFusion) is vacuous too (orbit-mates are aut-related by
  definition). The genuine "reaches rigid" content is **VISIBLE** (same-warmRefine-cell, refinement-computable)
  realizers — keep predicates keyed there. (The Shatters/PotentialDrops predicate carries the same risk — route doc §6.)

- **The NoFusion / largeness-derivation family was EXCISED** (it was `IsLarge ⟹ IsLarge` once the vacuous coverage is
  stripped). Largeness is now carried honestly as the `LargenessBridge` identity. `IsLargeScheme` stays ABSTRACT —
  **do NOT concretize** (asymptotic citation).

- **TRAP: ClosedSubset (complex-product closure) ≠ EdgeGenerates / isolationStep (pinning closure).** Do NOT argue
  "off-recovery ⟹ proper ClosedSubset ⟹ imprimitive." Off-recovery does NOT imply imprimitive (a primitive scheme
  can fail `EdgeGenerates`: Cameron/Johnson).

- **Do NOT use `Findable` / `FindableWithin` for leg B** — its abelian leg keys on VISIBLE recovery, conflating leg B
  into leg A. Leg B is the L3-keyed `AbelianConsumed` (`not_comm_of_orbit_disagree` makes it non-vacuous).

---

## 4. Dead / do-not-build

- **⛔⛔⛔ A POLY EQUIVARIANT **FULL-ORDER** FRAME SET IS TYPE-IMPOSSIBLE ON A GAUGED INPUT — `seedFrames` and
  `OrderOfEquivariant` are RETIRED** (live homes: `RigidRefine.lean` §9F, `chain-descent-rigid-seal.md` §8.2).
  At a gauge colour-automorphism `σ` (`relabelAdj σ adj = adj`, `transportColouring σ χ = χ`),
  `FramesEquivariant` forces `frames adj χ = (frames adj χ).image (σ * ·)` — closure under **left multiplication
  by the whole gauge group `G`**. Left-mult on a group is a **free** action (`σ * o = o ⟹ σ = 1`), so any
  nonempty invariant set is a union of full `G`-orbits ⟹ **`|frames| ≥ |G| = 2^β`**. The exponential is forced by
  the **TYPE** (`Finset (Equiv.Perm (Fin n))` = full vertex orders), not by a bad choice of set;
  `OrderOfEquivariant` at a gauge fixing a seed forces `σ = 1`, so it holds **only on purely rigid inputs** and is
  target-vacuous. ⚠⚠ **This one bites hard because two docs still advertise it as the live frontier** —
  `00-START-HERE.md` §2's *"FRONTIER: the POLY frame set … ▶ P2 concrete poly seed"* and
  `remaining-work.md` §1's identical line (both now banner-ed, 2026-08-09, after they cost a session real work).
  ⟹ **Do not scope "supply a discretizing equivariant poly frame set".** The escape is §9F's re-typing of the
  aggregate over an abstract base-frame type `(B, act, baseRead)` where the gauge acts **non-freely**
  (`FramesEquivariantB` / `ReadAtEquivariant` / `AggFaithfulB`, all built, with a concrete poly pinning instance).

- **⛔⛔⛔ A GAUGE CAN NEVER MAKE A CELL MIXED — "the cell is mixed due to a linear (gauge) obstruction" is close to
  a contradiction in terms** (measured 2026-08-09, `scratchpad/probe_w2_linear.py` → `.out`; live home:
  `chain-descent-wind-down.md` §2 W2's item-3 block). The gauge (F₂ cycle space) is a **subgroup of `Aut`**, and a
  subgroup only ever **merges** vertices; "mixed" means several `Aut`-orbits, i.e. the **absence** of
  automorphisms. Measured exactly, with every gauge element verified edge-by-edge first: at every CFI root
  **no `Aut`-block is a single gauge-orbit** — gadgets 8 gauge-orbits vs 3 blocks `[12,12,8]`, wires 12 vs 3
  `[12,6,6]`, over `K₄` 4 vs **1**, over `C₆` 12 vs **1**. Since an equivariant key is constant on `Aut`-orbits
  (so it cannot cut *inside* a block) and `rep` merges only within harvest-orbits, the surviving representative
  count is `≥ |block| / |gauge-orbit| ≥ 2` **at every cell of every witness** ⟹ **no key whatsoever — perfect,
  solve-derived, or otherwise — can make a CFI root cell fire on the gauge.** A counting fact, not a missing
  solver. What `Aut` does *beyond* the gauge is **base** automorphism structure, which the linear layer cannot
  see. ⟹ **CFI-over-cubic is NOT an instance of "no stall if the residue contains a linear obstruction"**; that
  claim's home is the **rigid** case (`dim ker = 0`), where `hrigid` *is* the hypothesis and an equivariant order
  provably **exists**. ⚠ Corollary for scoping: the CFI *gauge* is precisely what `kernelSupply` already consumes;
  what remains mixed is the base graph — *"it handles the residue, then hands you back the original graph"*.

- **⛔ "deck MODULO the verified subgroup" is DEAD as a standalone C3b mechanism — measured 2026-07-19
  (`PerformanceTest` §15).** It was the *plan of record* in remaining-work §1C C3 (ii-c) and in the handoff, so it
  looks endorsed in any doc snapshot before that date — it is not. The idea: once `kernelSupply` certifies the gauge
  group `K`, let F2b/F2c propagation force uniqueness only *up to `K`* (candidates unique modulo `K`-orbits), a
  P3b-licensed choice. **Why it fails:** the residual family it was aimed at (`mp7`, the Fano multipede) has
  incidence **girth 6**, and §13 measured that the Z₇-translate seed forces **1 vertex of 42**. Quotienting by `K`
  does not create chaining where there is none — propagation is not the vehicle on this family *at any modulus*.
  ⚠ **Keep the licensing pattern, discard the mechanism:** "force only up to a verified subgroup, absorb the choice
  into `SameOrbits`" is sound and is exactly what the live route uses; it simply had nothing to propagate on.
  **Live replacement = base-graph recovery + lift** (remaining-work §1C C3 ii-c): the missing generator is an
  automorphism of the *base* object `kernelSupply` already extracts (rails = segments, wire supports = checks). Its
  ① license is strictly better — two lifts of one base automorphism differ by a pure gauge element ∈ `K`, and
  **`WordReach` only needs each `v` and `ρ'(v)` connected, so PER-VERTEX gauge elements suffice; no single global
  `k` is required.** That observation is what turns the coset obligation from a graph-dependent assumption into a
  provable statement, and it is the reusable part of this episode.

- **Unconditional A2-iii (block-visibility) is DEAD** — the **Shrikhande graph** refutes it (its own scheme is rank-4
  with a ClosedSubset 1-WL-from-v can't see). Block-visibility is depth-graded, collapses into the WL-dim boundary;
  keep `BlockRefinementVisible` a hypothesis.

- **Don't re-attempt the A2b lockstep discharge — provably futile** (`lockstep_disc_imp_stab_trivial`): the
  discretizing oracle can't harvest a multi-step moved orbit; that symmetry must go cross-branch / Part A. (Topic file
  `project_discretizing_oracle_limit_2026-06-03.md`.)

- **⛔ Orbit-pruning the supply's enumeration is NOT a route to the `d = Θ(log n)` ladder-break — settled by
  construction + measurement, 2026-07-18.** `P3c` is *built and closed* (`PrunedSupply.lean` + `TreePrune.lean`,
  axiom-clean): the first half cut `|table|² → |table|`, the second grows the `(branch, sequence)` space level by
  level as a tree and orbit-prunes each level by a seed group, with the group-closure proof landed
  (`sameOrbits_treeSupply`). **Measured on `C₇`: 399 → 30 rows at `d ≤ 2`, 2800 → 202 at `d ≤ 3`, still recovering
  all 14 of `D₇`.** Both ratios sit just under `|Aut| = 14`, and that is the **structural ceiling, not a tuning
  artifact: pruning by a FIXED group divides the enumeration by at most its order, and per-level growth is
  unchanged** (`30 → 202` is still `≈ n`). A genuine per-level collapse needs the group to *grow* as the level
  deepens — i.e. the **stabilizer chain**, which is separately settled-banned (no iso-invariant within-cell vertex
  pick ⟹ `①b` **and** `①c` fail). ⟹ **Do not re-attempt "make the consume enumeration collapse the ladder" by
  strengthening the pruning, lengthening `wordsOf`, or iterating to a fixpoint** — the win is `|Aut|`-fold in every
  variant. **⚠ And the ceiling is IMPLEMENTATION-INDEPENDENT, so head off the obvious counter-proposal ("prune each
  subtree by the per-node STABILIZER instead of the global group"):** the kept set at level `k` is, at best, one
  representative per `G`-orbit on that level, and by orbit-stabilizer `#orbits ≥ |level| / |G|` — per-node
  stabilizers are just a *way of computing* those orbits, never a way of getting fewer nodes than there are orbits.
  So `≥ |branches| · n^k / |Aut|` survives at every level under **any** group-based pruning scheme. Beating `n^d`
  therefore requires not enumerating all sequences at all — a smarter *choice* of what to individualize, which is
  the selector/force side of the object, not the consume side. The earlier "`n^d` becomes a SUM" projection (handoff §6.2b, pre-2026-07-18) is **retracted**; if a
  regime change exists it is more plausibly force-side (F3/`HolKey`) than a cheaper consume enumeration.

- **`decide`-checking a hard-coded `SchurianScheme` is INFEASIBLE — do not attempt.** The `schurian` axiom is
  `∃`-over-auts `∀`-over-pairs ≈ 8M kernel checks; splitting helps a constant factor, not enough; `orbitalScheme` is
  `noncomputable`. Concrete witnesses stay at `AssociationScheme`/`Discrete` level. (Build doc §7, 2026-06-13.)

---

## 5. Corrections to cited or empirical premises (don't regress to the old claim)

- **"imprimitive ⟹ recovers citably" REFUTED** — E–P's `s(C)≤2` is imprimitive *3/2-homogeneous*-ONLY; general
  imprimitive homogeneous schurian schemes reach UNBOUNDED `s(C)` (circulants) — but those are abelian ⟹ leg B.

- **"circulants have bounded WL-dim (Muzychuk)" is WRONG** — Wu–Ren–Ponomarenko (arXiv:2507.10116, 2025): circulant
  absolute WL-dim is UNBOUNDED (≥c√log n); only PRIME-POWER order is bounded (≤3). So abelian + vertex-transitive does
  NOT force bounded WL (our small empirics were low-prime-factor, hence low-WL).

- **`PrimitiveCCClassification` (G3) / largeness calibration (M2-Q4 2026-06-13).** The poly-`|Aut|`-or-Cameron form is
  solid ONLY at rank 3 (Babai 2014) / rank 4 (Kivva 2023; exceptions Johnson/Hamming); all-rank motion-conjecture
  REFUTED by Eberhard rank-28 (2022); high-rank needs a "Cameron sandwich". General primitive-CC largeness is only
  **SUB-EXPONENTIAL** (Sun–Wilmes `exp(Õ(n^{1/3}))`; Babai's poly conjecture OPEN). **⟹ polynomial canonisation is
  citable ONLY for bounded rank; the residue IS rank 3-4, so poly holds there; claim poly only on bounded-rank,
  sub-exp-base in general.** Group side (citable but only `b(G)≤b(X)`, the `s(X)` gap stays open):
  `b(G)≤2log|G|/logn+24` (HLM), `b(G)≤7` non-standard (Burness), `|G|≤n^5` (Liebeck–Saxl). (Also cxt-scoping §0/§2.)

- **Vocabulary:** `s(C)` = separability number (Evdokimov–Ponomarenko); `s(C)≤m` ⟺ the CC is determined by m-dim
  intersection numbers ≈ WL-dim. The leak = a schurian CC with high `s(C)`.

- **DEAD: the 2-closure / algebraic-gap reframe of G2-B** (topic file `project_2closure_reframe_dead_2026-06-10.md`)
  — 2nd deep-research pass: NO object distinct from `s(C)` bounds recovery depth. Closure-preservation FAILS at k=2/3
  (`AGL_m(2)`: `G⁽³⁾=Sym(2^m)`); minimal-degree is orthogonal; only general WL ceiling is linear (0.15n). G2-B is open
  research, **not a missing citation** — confirmed by two passes. Don't re-hunt a citation shortcut. **REFINED
  2026-06-11** (topic file `project_cartan_2separability_lead_2026-06-11.md`): a third narrow off-chance pass DID find
  a citable `s(C)≤2` for *structured* non-abelian families (Lie-type Cartan schemes, + a general 2-separability
  sufficient condition) — so "no `s(C)` citation exists" is too broad; the genuine gap is *arbitrary small primitive*.

---

## 6. Probe / experiment methodology (C#)

- **MUST use Aut(G)'s OWN orbital scheme** in block-visibility probes — never an a-priori group scheme + a
  non-generating relation (Z₈ + antipodal matching had real Aut `S₂≀S₄ ⊋ Z₈` → 43 spurious straddles, retracted).
  Block systems ≡ closed subsets only for **transitive** Aut ⟹ valid only on vertex-transitive scheme graphs.

- **Brute-force ground truth must be pruned + node-capped** — naive backtracking is EXPONENTIAL on rigid multipedes
  by construction. A multipede is IR-core only when **vertex-coloured** (a raw circulant keeps Dₘ base symmetry; seed
  `VertexTypes` into the descent `P`).

- **SEVEN empirical falsifiers returned 0 G2-B witnesses** (the standing evidence the carve-out is right; a witness =
  statement-change). **Primary home: cxt-scoping §4.3** (the enumerated roster lives there now; this is the backup copy):
  1. the Hanaki–Miyamoto catalogue (2363 schemes, all 481 primitive recover);
  2. the affine `ΓL(1,2^d)` sweep;
  3. the non-solvable `A_n` sweep;
  4. the **non-affine** `PGL(2,p)`-on-2-subsets probe (`NonAffinePrimitiveProbe.cs`, 2026-06-10: 6 primitive
     almost-simple poly-order schemes, orders 28–276, depth 2);
  5. the **Theorem-3.1 density** probe (`CatalogueSchemeProbe.Probe_Theorem31_DensityBoundary`, 2026-06-11);
  6. the **non-affine Latin-square** probe (`CatalogueSchemeProbe.Probe_AmorphicResidue_LatinSquare`, 2026-06-11:
     non-group LS-graphs n≤100, flat depth 2–3);
  7. the **PSL(2,q) exceptional-coset** probe (`CosetSchemeProbe.Probe_PSL2_ExceptionalCosets`, 2026-06-11: 7
     primitive non-affine `orbitalScheme(PSL(2,q)/{A₅,S₄})`, rank 4–9, index 57–620, ALL recover at WL-depth 2–3);
  plus **THE AMORPHIC-NLS BULLSEYE** (`PdsAmorphicSchemeProbe.Probe_AmorphicNLS_Order16`, 2026-06-11): exhaustive
  verified search of rank-4 equal-valency amorphic-NLS partitions (3 interchangeable Clebsch SRG(16,5,0,2)=NL₁(4),
  the amorphic-`S₃` gap) on all order-16 groups — **`ℤ₄²` (non-elementary-abelian) carries the primitive one and it
  RECOVERS at WL-depth 2** (fails depth-1 EdgeGenerates = the amorphic gap, separates at base+O(1)); `ℤ₂⁴` (affine
  anchor) depth 3; `ℤ₄×ℤ₂²`/`ℤ₈×ℤ₂` carry none.

- **Rainbow-rigidity construction is ORDER-16-ONLY** (`Probe_ExtractPinningRank`/`Probe_RainbowRigidFamily`,
  2026-06-13): the `ℤ₄²` bullseye's δ′ closure is "rainbow triangle (3 distinct non-diag colours) ⟹ rigid (c=1)",
  uniform/multi-round (depth 3, layers [2,2,6,6], 96/120 2-bases), but rainbow-`c=1` is special to Clebsch (16,5,0,2)
  and GONE by n=25 ⟹ **don't formalize a parametric rainbow family** — the n≥25 mechanism lives in `X_T`.

- **The `ℤ₄²` (order-16, exp-4) amorphic-NLS Clebsch is the on-target primitive G2-B data point** (recovers depth 2;
  `2·ℤ₄²` involutions scatter ⟹ not a block ⟹ primitive). **NO linear-multiplier Cayley shortcut to a primitive
  residue** (any `M≤GL(m,ℤ₄)` preserves `2·ℤ₄ᵐ` ⟹ block ⟹ imprimitive; DX PDS necessarily non-linear). Equal-valency
  rank-4 NLS needs `v=4^t, 3∣2^t−1` ⟹ next after v=16 is v=256 (search-infeasible); v=64 none.
  `PdsAmorphicSchemeProbe.cs` reusable.

- **The A2 monovariant probe (`A2MonovariantProbe.cs`, 2026-06-15)** — full protocol + correction log in the archived
  probe plan `Archive/ChainDescent/chain-descent-a2-monovariant-probe.md`. Verdict: bounded-drop ⟺ non-geometric,
  geometric = the Cameron carve (route doc §5). Correction: bare 2-rank does NOT separate the cospectral pairs; the
  separator is the geometric/exceptional *structure*, not any single invariant value.

---

## 7. Axiom hygiene

- Project is **custom-axiom-free**. Cited classifications (`CameronClassification`, `PrimitiveCCClassification`,
  Neumaier, CGGP, any EP/Ponomarenko theorem you choose to cite) must be theorem-statement **hypotheses**, NOT fresh
  `axiom`s — keeps the basis clean and the citation visible. **`native_decide` BANNED** (adds `ofReduceBool`, breaks
  the `[propext, Classical.choice, Quot.sound]` bar); the concrete ℤ₄² closure used plain `decide`.
