# Remaining work — the living tracker (the complete-canonizer plan)

> **What this file is.** The single forward-looking tracker: the target, the full gap enumeration, and the
> ordered plan. It carries **no history** — the pre-2026-07-18 blow-by-blow (seal-era modulo set, citation
> tables, node-4 layers, RRU retirement, the 2026-07-13/14 canonizer updates) is archived at
> [`Archive/ChainDescent/chain-descent-remaining-work-archive-2026-07-18.md`](./Archive/ChainDescent/chain-descent-remaining-work-archive-2026-07-18.md);
> do not build on it without checking the current doc its banner names.
> ⚠ **Stale cross-references:** other docs cite this file's OLD sections (§1 modulo set, §2 citation table,
> §3a research core / §3a.1 layered remainder, §6 RRU note) — those all resolve into the ARCHIVE file above,
> same section numbering.
> **State authority stays elsewhere:** what is built = [`chain-descent-handoff-2026-07-14.md`](./chain-descent-handoff-2026-07-14.md)
> (+ module docs, `PublicTheoremIndex.md`); fold/tower = [`chain-descent-fold-tower-plan.md`](./chain-descent-fold-tower-plan.md);
> Route C = [`chain-descent-route-c-plan.md`](./chain-descent-route-c-plan.md); recovery/poly =
> [`chain-descent-recovery-route.md`](./chain-descent-recovery-route.md); rigid/IR =
> [`chain-descent-ir-blindspot-solver.md`](./chain-descent-ir-blindspot-solver.md); citations =
> [`chain-descent-citation-discharge.md`](./chain-descent-citation-discharge.md).

---

## 0. THE TARGET (restated 2026-07-18, user steer — supersedes every "named-residue" done-definition)

**The goal is a COMPLETE canonizer: every input handled, in polynomial time.** A canonizer that flags on a
named residue is the honest *intermediate* — and the final fallback **only if** every identified route to a
gap has been attempted and recorded dead (steers-archive discipline). It is **not** the target, and no plan
or doc may treat a currently-unhandled family as permanently out of scope. ("Polynomial is NOT a wall — it's
the target" has been the standing steer all along; this section makes it the done-definition.)

**The poly-or-flag architecture stays** — it is the scaffold that makes the pursuit honest: ① is unconditional,
② is unconditional-per-node-count with explicit per-mechanism costs, and the flag is the *measurement
instrument* that names each remaining gap (`selNode_stall_iff` = the true mutual stall). Every increment lands
inside it; the residue **deflates monotonically** with no re-proof (`Handled ⟹ HandledS`, `SameOrbits`
transfer). "Complete" = the flag provably never fires.

**The end theorems (the step beyond the algorithm):**
- **Totality:** `canonForm?(record) ≠ none` for every input — assembled as: per-leg `Handled` theorems (one
  per mechanism/family, via the `handled_of_seal`/`_selected` hooks) + the **G3 classification case-split**
  covering the primitive floor (every primitive residue is Cameron → recognition leg / bounded-base → deep
  leg / affine-linear → force+recovery legs) + the `hImprim` consolidation (imprimitive residues reduce to
  the primitive floor through the same firing interfaces).
- **Explicit polynomial cost:** the `SupplyCost` pattern extended to every mechanism (each new supply/key
  lands with its closed-form `c₂`/`keyCost` bound; the end-to-end `descentCost … ≤ costConst · n^costDeg`).
- **Axiom footprint** = `[propext, Classical.choice, Quot.sound]` + at most **{G3}** (citation policy:
  every other citation eventually built in-Lean — register + routes in `chain-descent-citation-discharge.md`).
- Until totality closes, the graded `Publication` shape (①/② + ③a flag ⟹ `¬HandledS` + per-family ③b) is the
  publishable intermediate at every stage.

---

## 1. THE GAP ENUMERATION — everything between the current design and handling every input

Grouped by decision type. Each entry: what it is → the mechanism that should close it → where it is recorded.

### 1C. Consume-side gaps (symmetry present, no built supply certifies it)

- **✅ C1 — mirror∘twisted-matching composite gauges — CLOSED 2026-07-19 (F2c,
  `ChainDescent/Deck2.lean` `deck2Supply`).** Second-seed propagation: the stalled F2b state's own ambiguity
  set (unassigned × viable, equivariantly defined) enumerated as second seeds on the shared stalled state;
  bijectivity gate (`permOf`) + `IsColAut` verify; record capstone `holKey_foldDeck2_selNode_canonizer`.
  Acceptance MET: `ut` end-to-end ANSWERS (~20 min interpreted, `PerformanceTest` §11; `Regression` §14
  gates t3).
- **✅ C2 — wreath-type per-copy gauges (`Z₂ ≀ Z_s`) — CLOSED BY MEASUREMENT 2026-07-19 (no new code).**
  The planned witness was built (`wr3`: 3 copies matched only on mirror-fixed fibers, `Aut ⊇ Z₂³ ⋊ D₃`) and
  the "measure every built supply dead" step FALSIFIED the scope line instead: **`deck2Supply` fires**
  (fold 6 / deck 3 / deck2 → 1; answers end-to-end; `PerformanceTest` §12). Mechanism: the `.getD v`
  identity-default — an *independent* residual ambiguity defaults to identity, and independence is exactly
  what makes that completion an automorphism; verification accepts (and rejects the same default on coupled
  residuals — sound either way). No separate wreath leg is needed.
- **C3 — the general ambiguous-propagation regime — RE-DERIVED 2026-07-19 (the wr3 probe's analysis;
  detail `Deck2.lean` module doc).** Measured deck2 reach: coupled-and-chaining ambiguities (t3) +
  independent gauges (wr3) + every `Z₂`-gauge generated by ≤2-seed-reachable elements (includes all
  sum-zero codes — generated by weight-2 words). **The genuine residual class: gauge = kernel of parity
  checks of arity ≥ 3 with minimum weight ≥ 3** — one assigned wire leaves ≥ 2 candidates at every check
  (pairwise forcing cannot chain) and no weight-≤2 word exists (identity-default invalid) = **CFI
  cycle-space gauges**. Boundary: odd-degree-base CFI already exits via the DEPTH leg
  (`theorem_1_HOR_cfi_oddDeg` ⟹ `deepMatchSupply`); the open witness class is the **symmetric pin-blind
  CFI cover** (multipede-style even-degree base, nontrivial cycle space).
  **✅ (i) WITNESS BUILT + MEASURED 2026-07-19 — `mp7`, the FANO MULTIPEDE (n = 42; `PerformanceTest`
  §13, all `#guard`ed):** 7 foot-pair segments, 7 arity-3 checks = Fano lines (two checks share exactly
  ONE segment — incidence girth 6), 4-vertex CFI gadgets; gauge = ker(incidence) = the [7,3,4] simplex
  code (dim 3, min weight 4 — verified real: the weight-4 flip IS a colour-automorphism). Pin-blind
  (6/42 colours after a pin ⟹ matching supplies structurally dead); fold narrows nothing; deck: the
  gauge seed forces 1 vertex of 42 (girth kills chaining) and even the Z₇-translate seed stalls; deck2:
  689-entry second stage, gauge continuation fails the gate; a THIRD seed (manual deck3) also fails —
  the gadget layer never chains. Force cannot act (single-orbit cells). **TRUE mutual stall of the whole
  stack; the constructor gate is OPEN and the route is DECIDED** (deck_k is dead on this shape at any
  practical k, and growing-weight families kill fixed k in principle).
  **✅ (ii-a) THE KERNEL SUPPLY, TRANCHE 1 LANDED 2026-07-19** (`ChainDescent/KernelSupply.lean`, in
  `build.sh`, compiles clean; wiring gate `Regression` §15, full measured set `PerformanceTest` §14):
  the executable pipeline exactly as designed below, **plus the design lock found during the build —
  the ALL-OR-NOTHING GATE**: a pivot-order-dependent basis with *partial* verification would make the
  emitted subgroup depend on the pivot choice (①c genuinely false); emitting all-or-nothing makes the
  gate ⟺ "every word of `L` verifies" (products of automorphisms) — canonical — so the emitted GROUP
  is a canonical function of `(adj, χ)`. **MEASURED on `mp7`**: rails = exactly the 7 foot pairs;
  basis = dim 3, weights [4,4,4] — *the simplex code recovered from raw structure*; gate passes; root
  gadget cell **28 → 7** (the whole gauge in one supply call); at the pinned node the basis restricts
  to dim 2 = exactly the codewords avoiding the pinned segment; 0 generators on t3/ut/wcyc9.
  **Still open, scoped:**
  - **(ii-b) Tranche 2 — the ① proof stack**: rails/patterns/`flipFunK` transport lemmas; `L` as a
    canonical SUBSPACE (the row span is pattern-determined though rows are not); the
    elimination-correctness lemma `span(kernelBasis) = L` (Gaussian soundness + completeness — the
    largest single proof item, self-contained); the set-level reference supply + its equivariance;
    `SameOrbits`(kernel, reference) via the commuting-flips product argument; capstones through
    `…_of_sameOrbits`. Until it lands, `kernelSupply` stays OUT of the record object.
  - **(ii-c) = C3b, NEW MECHANISM (found at the witness): deck-MODULO-the-verified-subgroup.** The
    kernel certifies the gauge but mp7's translations still stand: deck stalls on them *because* the
    gauge commutes (measured §13) — with the kernel group K known, propagation should force
    uniqueness only up to K (candidates unique modulo K-orbits), a choice licensed the P3b way. This
    is the composition step that turns "gauge certified" into "mp7 answers end-to-end" — the C3
    acceptance moves to C3b.
  **The original design (as built):**
  · *Extraction* (structural, choice-free — trap #7 clean): rail pairs = same-cell non-adjacent pairs
    whose neighborhoods complement inside every shared gadget cluster (and conflict in none); clusters =
    same-cell gadget vertices with equal rail-pair support (the F3a symmetrized-component toolkit).
    Full enumeration; untrusted (junk recognition costs firing, never ①).
  · *Solve*: variables = rail pairs, checks = clusters; F₂ Gaussian elimination ⟹ kernel basis. Poly,
    computable, no proof obligations on the elimination itself.
  · *Emission* per basis word: flip the word's rail pairs; each gadget vertex ↦ its unique same-cluster
    partner matching the flipped adjacency (`uniqueFilter` — no choice); `permOf` gate; `IsColAut`
    verify (soundness free, as always).
  · *① route — NOT `GensEquivariant`*: the basis is pivot-order-dependent (a genuine trap-#7 choice).
    But the GENERATED GROUP is basis-independent, and flips COMMUTE (a kernel word is the symmetric
    difference of basis words = their product) — so ①/②/③ transfer by the **`SameOrbits` reduction**
    against the set-level reference "all kernel flips" (definable and equivariant because the recovered
    code is canonical; reachability = the P3b/`TreePrune` product-license, `wordReach_of_reaches`).
    This is exactly the "any future supply optimization" reuse the P3c machinery was built for.
  · *Cost*: extraction + elimination `O(n³)`, ≤ n emissions at `O(n²)` — explicit flat bill.
  · *Acceptance*: `mp7` root cells narrow to 1 and `mp7` answers end-to-end with the record + kernel
    supply appended; t3/wr3/ut guards unchanged.
  This is the §11.11 "solver kernel feeds de-fused symmetry back" loop landing consume-side (connects
  to `LinearOracle.lean`; F3b-adjacent — the same recovered system, kernel here, coset ordering there).
- **C4 — large-Aut geometric families (Cameron: Johnson/Hamming/Grassmann; the forms graphs).** Symmetry is
  enormous but localisation at bounded depth fails or costs `n^{O(d)}` with growing `d` (forms base
  `O(log n)` ⟹ quasipoly; Steiner/Latin `Θ(√n)`). → **recognition + coordinatization as a SUPPLY**: recover
  the structure (Route C `IFormStructure` engine; Cameron-scheme recognition for the hidden-Johnson atom),
  emit its known automorphisms as candidates, verify. The untrusted-supply discipline makes recognition
  heuristics *safe* — a wrong recovery costs firing, never ①. This is the poly route that **replaces** the
  deep-oracle ladder on every structured family (see §3 note on `d = Θ(log n)`).

### 1F. Force-side gaps (rigid decisions no built key separates)

- **F1 — module-level Smith/CRT coset ordering (= F3b).** Distinguishable-but-WL-merged copy orderings whose
  invariant is coset data: the multipede double's surviving gauge pair (`MultipedeWitness`, measured,
  off-build) + the C# `K_p□K_p` rook-fiber residual (`null`). → the Smith/CRT canonical-coset key (enters as
  a `Force.Key`; ① = `KeyEquivariant`, the F3a pattern) + the C# `SolveOverA`/extended-Smith wired into the
  lex-min. Gate: confirm the witness genuinely needs the module ordering (close to met — cheaper mechanisms
  measured dead on the double). Also the likeliest force-side regime-change lever if a generic depth-collapse
  is ever needed.
- **F2 — rigid non-linear separation** beyond `lookaheadKey`/`holKey`: rigid graphs whose 1-WL-symmetric
  appearance survives pinning (rigid SRG-land). This is the rigid face of the wall (= W2); the ring solver is
  poly by bounded arity and does not cover it. No mechanism exists; routes live in §1W.

### 1W. The wall — the two faces that remain after 1C/1F close

- **W1 — the schurian/affine face: the forms-graph poly program (LIVE, was "parked").** The seal is BANKED at
  quasipoly (`reachesRigidOrCameron_affinePolar` mod {G3}); the **poly** claim runs through **recovery**, not
  WL: target **T0 = bounded branching / poly leaf count** (empirically supported, `Phase0_BranchProfile`;
  weakest sufficient predicate), mechanism = Route C form-recovery (Lean spine assembled; affine-polar +
  alternating instances sealed; half-spin scoped; Suzuki + char-2/Arf track open). Work items, in order:
  (a) **re-base onto the descent object** — the route-c/recovery docs predate `Descend`/`CostM`/`selNode`;
  recovery must enter as a supply/key of the record object with `SupplyCost` bounds, not as the old
  standalone spine; (b) T0 leaf-count formalization against the real cost model; (c) the remaining family
  instances (half-spin, Suzuki, char-2 needs the Arf/trace substrate); (d) the **transport seam** — firing on
  a graph *realizing* the scheme, not on `schemeAdj` (`RouteCTransport.separatesAtBoundedBase_transport`).
- **W2 — the non-schurian / rigid-non-linear face (IR row 4) + D0.** The genuinely-uncited open core:
  unbounded-`s(C)` residues (generic SRG-land) on the symmetric side, rigid SRG-shaped inputs on the force
  side, plus **D0** (is the reached residue faithfully the `orbitalScheme` model — a modelling obligation).
  Attack routes to run to exhaustion, in rough order of promise: (i) the **iterated/rigid solver** on
  recovery interfaces (the hImprim consolidation steer — `chain-descent-seal-handoff.md` §Update 2026-07-16:
  NOT the deep oracle); (ii) **§11.14** — prove "no non-abelian fusion survives into a rigid medium"
  (negative-witness evidence exists; a proof collapses the rigid residual); (iii) recognition reach — how far
  the C4/W1 recognition legs extend into SRG-land (claw-bounded SRGs at `n^{1/3}` are Spielman-citable;
  what recovers *below* that); (iv) the demoted WL-dim independent-math route
  (`chain-descent-cellsareorbits-route.md`) only if a new idea appears. **Probe program in parallel**: hunt a
  constructible witness that survives all built + planned mechanisms; every dead route recorded in the
  steers archive. Only after this exhaustion does any residue framing become final — and then it is carried
  with its recorded route obituaries, not as a design assumption.
- **W3 — where they meet:** `hSmallAutThin` / rigid-GI. Emptied iff W1 and W2 both close. The endgame-spec's
  "two seals, one wall" frame remains the correct *map*; under §0 the wall is a **target**, not a fixture.

### 1T. Theorem-side gaps (proving the canonizer complete, leg by leg)

- **T1 — per-family localisation** (`Handled` population): `∀ T, CellsAreOrbits` or the lighter `_selected`
  hook discharged per sealed family (first: CFI odd-deg via `theorem_1_HOR_cfi_oddDeg`; depth already
  imports via P2b/P2c). Zero families populated today; this is ③'s content and each leg's totality brick.
- **T2 — cost bounds per new mechanism** (`SupplyCost` pattern: closed-form `c₂`/`keyCost` at land time —
  house rule, not a backlog).
- **T3 — citation discharge** per policy (everything but G3; register + M1–M5 playbook in the discharge doc;
  wiring cautions: G3 only at the Sun–Wilmes threshold, FTPG corrected predicate, Payne–Thas narrowed).
- **T4 — D0** (`SchurianScheme` model faithfulness) — see W2.
- **T5 — the totality assembly** (§0): per-leg `Handled` + the G3 case-split + `hImprim` consolidation ⟹
  `canonForm? ≠ none`; `Publication` evolves from the graded shape to totality as legs close.
- **T6 — statement-level audits** at every wiring point (hypotheses instantiable? non-vacuity `#guard`ed?
  statement = intended claim?) — the 2026-07-16 blocker-audit discipline, applied to each capstone the
  Publication wiring consumes. This is where "any piece might be built insufficiently" is discharged.

---

## 2. THE PLAN — near-term queue, then tracks

**Near-term queue (do in this order; each lands green + guarded before the next):**
1. ✅ **C1 / "F2c"** — DONE 2026-07-19 (`Deck2.lean`; `ut` answers end-to-end — see §1C).
2. ✅ **Publication swap SPIKE** — DONE 2026-07-19, better than scoped: `canonForm?` swapped to the real
   record (fused holKey + fold++deck++deck2) and the WHOLE ① trio filled — `canon_sound`/`canon_complete`/
   `flag_iso_invariant` are `[propext, Classical.choice, Quot.sound]`-clean, no `sorryAx`, no citation
   axioms; zero glue needed (all definitional). `canonizer`'s remaining `sorryAx` = ② + ③ + non-vacuity
   exactly. Record pin provisional by construction (one def + one theorem to strengthen). Statements
   untouched (the finalization steer stands).
3. ✅ **C2 witness** — DONE 2026-07-19, outcome inverted: `wr3` built and measured, `deck2Supply` FIRES
   (identity-default mechanism) ⟹ C2 closed with no new code; C3 re-derived precisely (see §1C).
3b. ✅ **C3 witness** — DONE 2026-07-19: `mp7` (Fano multipede) built and measured, full stack + a
   manual deck3 DEAD (`PerformanceTest` §13, guarded); constructor route DECIDED = the kernel supply.
3c. ✅ **C3 constructor tranche 1** — DONE 2026-07-19 (`KernelSupply.lean` in build; mp7's whole gauge
   consumed in one supply call, 28 → 7 at the root; the all-or-nothing gate = the ①c design lock).
3d. **C3 tranche 2 — the ① proof stack** (§1C C3 ii-b): transport lemmas, `L` canonicity, Gaussian
   correctness `span(kernelBasis) = L`, the reference supply, `SameOrbits`, capstones. Gates entry
   of `kernelSupply` into the record object.
3e. **C3b — deck-modulo-verified-subgroup** (§1C C3 ii-c): propagation with uniqueness mod the
   kernel group. Acceptance (moved from 3c): `mp7` answers end-to-end.
4. **T1 first family** — CFI odd-deg localisation through the weakest hook (de-risk on a C₆-style toy
   first). Output: the first real family in `HandledS` at the record = Publication's handled-half witness.
5. **F1 / F3b** — gate review (the witnesses exist; confirm necessity), then the Smith/CRT key + C# wiring.
   Likely prerequisite: the compiled-eval tranche (interpreted `holKeyFast` is out of range at multipede
   scale).
6. **C# parity tranche** (parallelizable with 1–5): the deckSupply port (~80 lines) + feed the harvest into
   the descent's pruning (§11.11 seam) instead of emitting a total copy order. The C# is the falsifier
   engine — parity is what finds the next C1-shaped hole. Then falsifier sweeps.
7. **W1 kickoff** — read `route-c-plan` + `recovery-route` STATUS, then the re-base design note (recovery as
   record-object supply/key + T0 against `CostM`). This is the biggest research arc; start it while 1–6
   proceed.
8. **W2 program** — begins with the probe program + §11.14 attempt once W1 has momentum; runs to exhaustion
   per §1W.

**Track view:** consume completion (C1→C2→C3, then C4 recognition) · force completion (F1, then F2 via W2) ·
the poly program (W1) · the wall (W2/W3) · theorems interleaved throughout (T1 per leg as it lands, T2 at
land time, T6 at wiring; T3/T5 continuous; Publication updated at each stage).

---

## 3. STANDING CONSTRAINTS (unchanged — machine-checked or settled; do not re-walk)

- **⛔ No stabilizer chain as the guarded object** — no iso-invariant within-cell vertex pick exists ⟹ ①b+①c
  fail. Choosing a CELL is canonical; a vertex within one is not.
- **⛔ "X ⟹ GI∈P, therefore X impossible" is banned** (a perfect key IS the target, not a barrier).
- **⛔ Do not re-unify the contract routes under `Covering`** (value-invisible ⟹ re-imports `canonMin`).
- **P3c does not break the ladder** (measured: `|Aut|`-fold only) — do not re-attempt a per-level collapse by
  strengthening pruning. **`d = Θ(log n)` generic ladder-break: no live route** — and under this plan it is
  **not needed**: every named deep family exits via W1 recovery/recognition; a family needing depth `ω(1)`
  with no recoverable structure lands in W2 and is attacked there.
- **Wreath gauges / "WL-blind non-linear residue" are NOT permanent exclusions** — C2 and W2 respectively
  (corrected 2026-07-18; earlier "correctly in the residue" phrasing meant only "outside the linear leg").
- **Vacuity discipline**: every new predicate needs a discharged instance + `#guard`ed witness in the same
  pass; firing stated graded first; supplies stateless; Lean traps #1/#2 (handoff §7).
