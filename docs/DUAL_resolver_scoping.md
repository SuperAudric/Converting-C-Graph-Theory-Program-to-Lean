# The dual resolver — one descent that consumes a symmetry **or** certifies the rigid decision

> ## ▶ STATUS (2026-07-27) — ✅ THE CONSUME→FORCE HOOK IS CLOSED, axiom-clean
>
> **A consume failure now provably makes force FIRE**, at a named node the descent reaches:
> ```
> consume_fail_force_fires :
>   ¬ Discrete χ → ¬ Consume.CellIsOrbit deepenSupply adj χ →
>     ∃ ψ, DescentReach adj χ ψ ∧
>          (narrow (forceBy orbKey) adj ψ).length < (branches ψ).length
> ```
> Three modules, all axiom-clean: `DeepenLocated` (10 thms) → `DeepenKey` (18) → `DeepenExact` (19).
> ⚠ **Superseded as the headline** — see the HANDOFF block below; strict narrowing is not what `②`/`③`
> consume, and `KeyComplete.nodeResolved_of_tinhofer` is the statement that is.
>
> **`①` never depended on any of it.** `keyEquivariant_orbKey` carries no hypothesis, so
> `Force.force_canonizer` / `Composite.composite_canonizer` are applicable as they stand.
>
> **✅ THE POLY GUARD IS ALSO LANDED** (`DeepenGuard`; now 44 thms). §7.1 measures
> that the *obvious* repair is impossible — deepen's own certificate (`Certified`) is **not**
> relabelling-invariant, falsifier included — so §7.2's alternate design was built instead: guard each
> level by `CellIsOrbit S` for a supply that already transports. `keyEquivariant_orbKeyG` needs only
> `SupplyEquivariant S`; instantiated at `deck2Supply`/`deckSupply`, and
> `force_canonizer_orbKeyG_deck2` gives `①a`/`①b`/`①c` + totality with **no hypothesis at all**.
> **⚠ The cost is firing, not soundness** — see §7.2's ⚠ block: the unconditional
> `consume_fail_force_fires` stays over `orbKey`; over `orbKeyG S` the *localization* half is unchanged
> and only *firing* becomes guard-conditional.
>
> ---
>
> ## ▶▶ HANDOFF — the state as of the end of 2026-07-27. START HERE.
>
> **Gate: `bash /workspace/scripts/build.sh` → EXIT 0, 105 modules, no `sorry`, no new `axiom`, every
> theorem `[propext, Classical.choice, Quot.sound]`.** Six modules carry this arc:
> `DeepenCertified` → `DeepenLocated` (10) → `DeepenKey` (18) → `DeepenExact` (19) → `DeepenGuard` (44)
> → **`KeyComplete`** (15). `Regression` §17/§17a and `PerformanceTest` §18 gate the executable
> behaviour.
>
> **The four things that changed on 2026-07-27 (later), in dependency order — detail in §10.1–§10.6:**
>
> 1. **The hook now lands on something.** `consume_fail_force_fires` ends in *strict* narrowing, and
>    **nothing in the project consumes that**; `②`/`③` read `Select.NodeResolved` (`cellNarrow … ≤ 1`).
>    **`nodeResolved_of_tinhofer`** closes the gap at every `Tinhofer` node and
>    **`handledS_of_reached_tinhofer`** is the **first population of `HandledS`** (remaining-work §1T
>    recorded ZERO families). Assembled from `forcedSet_single_orbit` + the **already-landed**
>    `deepen_branch_orbit_iff_aut` — only the assembly was missing. ⚠ NOT reachable via
>    `Cost.CellResolved`: at a mixed node **neither** of its disjuncts holds while the composite still
>    resolves. §10.1.
> 2. **`orbKeyG` is COMPUTABLE and its cost is BILLED.** `Consume.decidableWordReach` (the orbit BFS is
>    the decision procedure) → `decidableCellIsOrbit` → `instDecidableCertPath`; the `Classical.dec`
>    placeholder is gone. `certPathCost` + **`keyCost_orbKeyG_le`** (`≤ n⁴ + n·(n⁴+c₂)`, parametric in
>    the supply bound) make `②` at this key **falsifiable** — the old flat `n⁴` priced the read and
>    nothing of the guard. `orbKey` is NOT repairable this way and stays the theory-side object. §10.5.
> 3. **`reaches_of_descentReach`** bridges `DescentReach` to `Descend.Reaches` (what `HandledS`
>    quantifies over) ⟹ **`consume_fail_locates_resolved`**: the hook with *both* weaknesses removed —
>    a node the canonizer **visits**, resolved to `≤ 1`. §10.5.
> 4. **Guard strength = the UNION** (`guardSupply`), with `①` + totality free. **Measured emergent**:
>    on `t3` all four equivariant supplies are shut on every branch and the union is open on every
>    branch. §10.6.
>
> **⚠⚠ THE ONE CLAIM A FRESH READER MUST NOT INHERIT WRONG.** An earlier draft of §10.2 said
> `KeySeparates` *"globally is the target"*. **False, and corrected in place.**
> `keySeparatesAll_rawKey` proves `KeySeparates` holds **globally for a poly key** (the unguarded read),
> from the unconditional `isColAut_of_readKey_eq`. So separation alone is **cheap**; the GI-hard object
> is **`KeySeparates ∧ Force.KeyEquivariant`**. `rawKey` separates without equivariance;
> `orbKey`/`orbKeyG` buy equivariance with a guard and pay in separation coverage. **⟹ THE GUARD
> PURCHASES EQUIVARIANCE, NOT SEPARATION** — every "guard strength" number must be read that way, and
> coverage work should target the *equivariance* side. §10.2's correction block.
>
> **⛔ Two hunts that are RETIRED — do not run them.** (a) §10.4's falsifier ("a node where the key ties
> a cell with ≥ 2 orbits"): for `rawKey` it provably does not exist, for a guarded key it exists
> trivially wherever both guards are shut. Neither is information. (b) "take `S` deeper" as the
> guard-strength lever (§7.3 item 4 as originally written) — **measured wrong**; the supplies are
> incomparable, not ordered, and the union is the lever.
>
> **▶▶ UPDATE 2026-07-28 — two more landed, and the ledger's shape changed. Gate EXIT 0, 107 modules.**
> · **`ChainDescent/ForcePick.lean` (10 thms) — the exhaustiveness corollary CASHED.** `forceThenPick`
>   is force + `take 1`: no supply, no certificate. `①` rides `CoveringOfAt` at `N = forcedSet` with the
>   automorphism from `forcedSet_single_orbit_of_keySeparatesAt`. **It has no stall channel at all**
>   (totality and the single-path bound carry *no* hypothesis), so `forcePick_record` states the whole
>   package under one conjunction: **an equivariant, separating, poly key is a complete polynomial
>   canonizer.** ⚠ It fires nowhere new today and its instantiations are conditional scaffolds — §10.8.
> · **`DeepenGuard` §9 (5 thms) — `SameOrbits`-licensing, generic half.** `certPath_congr`:
>   the guard reads its supply only through the orbit relation, so `keyEquivariant_orbKeyG_of_sameOrbits`
>   admits a non-equivariant `S` against an equivariant reference. ⚠⚠ **The instance is NOT independent:
>   `SameOrbits deepenSupply Ref` IS R1**, the retired crux (`DeepenR1`, parked) — §10.7.
> · **⚠⚠ NEW LEDGER ITEM 9 — the RECORD OBJECT HAS NO `②` AT ALL.** None of `foldSupplyFast`,
>   `deckSupply`, `deck2Supply`, `kernelSupply` has a `supplyCost` bound and `holKeyFast` has no
>   `keyCost` bound; the two end-to-end cost theorems are at `lookaheadKey`+`prunedSupply`, a different
>   object. ✅ **CLOSED the same day** by `RecordCost.lean` (queue 3f) — see the next update block.
>
> **▶▶ UPDATE 2026-07-28 (later) — `KEY_scoping.md` §0's two defects PAID, and item 9 CLOSED. §10.9.**
> · **The `KeySeparates` duplication is de-silenced**: `KeyComplete.KeySeparates` → **`KeySeparatesAll`**
>   (the bare identifier belongs to F3a's `Hol.KeySeparates`), bridge **`keySeparatesAt_iff_hol`**, and a
>   `⚠` cross-reference in *both* files naming the re-derivation.
> · **`forcePick_record` is no longer claimed for no key**: **`readMin`** (`ForcePick` §8) is
>   `KeyEquivariant` *and* `KeySeparatesAll`, both unconditionally, by indexing the aggregate over
>   `Perm (Fin n)` — an index set that mentions neither `adj` nor `χ`, so equivariance is reindexing by
>   `π ↦ π * σ`. ⚠ Brute force restated, **not** progress on the wall; its job is vacuity insurance plus
>   **`forcePick_open_clause_is_poly`** — the open clause is now provably *poly alone*.
> · **Item 9 CLOSED**: `ChainDescent/RecordCost.lean`, **`descentCostS_selNode_record_le`** — the record
>   object's first `②`, explicit polynomial, no hypotheses.
>
> **▶▶ UPDATE 2026-07-28 (last) — item 7 / queue 3g DONE: `ChainDescent/RecordKey.lean`. §10.10.**
> `pairKey k₁ k₂` = **plain concatenation** of values, summed costs; `keyEquivariant_pairKey` is
> unconditional. **⚠⚠ The encoding this ledger and `remaining-work` both proposed —
> `(len a :: a) ++ (len b :: b)` — is WRONG and must not be re-proposed:** prefixing the length orders
> the first component by **shortlex**, which `lexLeList` is not, so it silently re-orders `holKeyFast`'s
> own narrowing. Correct = plain concatenation under **`ConstLen k₁`** (equal first-component length
> across the branches compared), which every built key satisfies. Under it: separation transfers from
> *either* component, and **`keepMin_pairKey_subset`** proves the tiebreak never *widens* the narrowing.
> **`recordKey := pairKey holKeyFast (orbKeyG guardSupply)`** with `recordKey_canonizer` (`①`) and
> `descentCostS_selNode_recordKey_le` (`②`, explicit poly, no hypotheses). ★ Measured non-vacuous
> (`Regression` §18): on **`G8` the root cell goes 8 → 2** where `holKeyFast` alone keeps all 8;
> `t3`/`wcyc9` are pinned as single-orbit **controls** where firing is *forbidden*.
>
> ---
>
> ## ▶▶▶ WHAT A FRESH READER PICKS UP (2026-07-28, end of arc)
>
> **Everything in the §7.3 ledger is closed except item 1.** Items 2–9 are done; item 7's remainder is
> named below.
>
> **▶ NEXT, in order.**
> 1. **The `Publication` swap — ONE pass, both halves together.** Edit `Publication.canonForm?` from
>    `Hol.holKeyFast` onto **`RecordKey.recordKey`**, *and* reshape
>    `RecordKey.descentCostS_selNode_recordKey_le`'s bound into the **`costConst * n ^ costDeg`
>    monomial** `Publication.canon_poly_or_flag` pins. They are one pass because both touch pinned
>    statements under the finalization steer. `RecordKey.recordKey_canonizer_with_cost` is the input:
>    it already carries `①` + `②` at the composed key, so this is a re-pointing plus arithmetic, not
>    new mathematics. ⚠ `Publication.cost` is still `opaque` and `canon_poly_or_flag` still a `sorry`;
>    that is what this closes.
> 2. **Item 1, restated by the user (2026-07-28):** *the flag is not reached via a stall.*
>    ¬consume⟹force has the free contrapositive ¬force⟹consume, so **no mutual stall occurs in
>    theory**. The dependency is **equivariance** (unproved); what remains after it is **cost**, settled
>    in prose except the **guards** — and the guards' bill is now a theorem
>    (`RecordKey.supplyCost_guardSupply_le` → `keyCost_recordKey_le`), so the remaining half is the
>    equivariance argument, not the arithmetic. ⚠ The honest residual gap:
>    `consume_fail_locates_resolved` resolves a node the descent **reaches**, while `HandledS`
>    quantifies over **every** reached node, so the hook does not by itself prevent a flag at `χ`.
> 3. **Track R P2** — the recover-core read (`chain-descent-rigid-seal.md` §8.2, ~lines 819–847).
>
> **⛔ Do not re-open** (each cost real time and is recorded with its falsifier): the §10.4 falsifier
> hunt · "take `S` deeper" as the guard lever · `SameOrbits`-licensing *as an independent lever* (its
> instance is R1) · the length-prefixed key product · `forceThenPick` instantiated at `orbKey`/`orbKeyG`
> read as a canonizer (§10.8's FORK warning).
>
> Reading order: §1 (the object) → §2 (what is measured) → §3 (what is proved) → **§10 (the current
> state, and the frontier)**. §7 is the guard arc that led here (⚠ its §7.3 ledger is annotated with
> what is now done); §8 is the literature placement;
> **§9 is PROVENANCE — superseded claims, do not read as live.**
>
> ### Where everything is, and how to re-run it
>
> | | |
> |---|---|
> | gate | `bash /workspace/scripts/build.sh` (ABSOLUTE path — it self-`cd`s via `$0`; relative FAILS) |
> | one module | `cd /workspace/GraphCanonizationProofs && lake build ChainDescent.KeyComplete` |
> | axioms | `lake env lean` a file that `import`s the module and `#print axioms <name>` (from `GraphCanonizationProofs/`, or the module prefix is not found) |
> | the arc's Lean, in dependency order | `ChainDescent/Deepen{Certified,Located,Key,Exact,Guard}.lean` → `KeyComplete.lean` → `ForcePick.lean` → `RecordCost.lean` → `RecordKey.lean` |
> | executable guards | `ChainDescent/Regression.lean` §17/§17a/**§18** (**on** the gate, must stay fast; §18 is ~5 s) |
> | expensive measurements | `ChainDescent/PerformanceTest.lean` §18 (**off** the gate by design — `lake build ChainDescent.PerformanceTest`). ⚠⚠ **The "~10 min" estimate is WRONG**: two attempts (2026-07-27 and 2026-07-28) each ran **> 45 min of wall time / > 12 CPU-min on the file itself** without completing, and were stopped. So **§18 has never been confirmed to compile in a finished run** — it is written and believed correct, but unverified. Budget an hour, or split §16 (`mp7`, n = 42) and §18 (`t3` union guard) into separate files before trying again. This does **not** affect the gate: `PerformanceTest` is not in `build.sh`. |
> | what is proved | `GraphCanonizationProofs/PublicTheoremIndex.md` — sections `KeyComplete`, `ForcePick`, `RecordCost`, `RecordKey` and the `Deepen.*` rows. Regenerate with `python3 scripts/GenerateTheoremIndexes.py rewrite` from the repo root, then fill the `—` descriptions it lists |
> | ⚠ after a RENAME | **the regen adds and updates but does not PRUNE** — a renamed theorem leaves a ghost row under its old name (this bit once: `keySeparates_rawKey` survived the rename to `keySeparatesAll_rawKey` and had to be deleted by hand). After renaming, grep the index for the old identifier and delete the stale row |
> | ⚠ counting modules | the gate prints one `✔` per module **plus** a final `✔ serial build complete`, and the top-level module is `ChainDescent` with **no dot** — so `grep -c '✔ ChainDescent'` is the right count (currently **107**), and `grep -c '✔'` over-counts by one |
> | probes (Python) | `probe_orbit_oracle.py` (§2.1/§2.4), `probe_guard_invariance.py` (§7.1), `probe_eqsupply_guard.py` (§7.2), `probe_dualdeepen.py`, `probe_polyloop.py`, `probe_certkey.py`, `probe_strategies.py`, `probe_splitloop.py`, `probe_verdict_invariance.py` — all in `scratchpad/` |
>
> ⚠ **Two traps that cost time in this arc.** (1) Reduce `CertPath` / `leafOf` **only** through their
> equation lemmas (`certPath_none/_nil/_cons`, `leafOf`'s three) — unfolding in place and then
> `cases`-ing on `chooseIdK` descends into its internal `foldl`. (2) A `#guard` that the guard is *open*
> proves nothing on its own: by AKRV's rigid collapse it can hold with **zero levels to certify**.
> **Pin `certPathCost > 0`.** Measured on `G8`: open on 8/8 branches, substantive on only 4.
>
> Probes: `probe_orbit_oracle.py`, `probe_dualdeepen.py` (18 witnesses: mp7/Fano, CFI over C₅ and over
> random cubic bases m=8..14, mixed multipede, circ(5), 6 rigid random multipedes n=34..84),
> `probe_polyloop.py`, `probe_certkey.py`, `probe_strategies.py`, `probe_splitloop.py`,
> `probe_verdict_invariance.py`.

---

## 1. The object, and the one thing that goes wrong with it

`deepen` (`DeepenSupply.lean`; C# `DeepenAnchor` + `ReplayDeepening` + `HarvestTwists`) descends the
**lowest-id non-singleton cell** to a whole-graph-discrete leaf, recording an *iso-invariant* cell-id
sequence `seq`, then replays `seq` from each other representative and colour-matches the leaves
(`twistOf`). Two facts about that pipeline:

* **`chooseIdK` is invariant** (`chooseIdK_transport`) — the *cell* choice transports.
* **The within-cell pick is by vertex index** — `deepen` takes `w :: _` of
  `(finRange n).filter (χc · == cid)`. That does **not** transport.

The leaf is discrete, so it *is* a labelling `π`; `twistOf` builds `π_j⁻¹ ∘ π_1` and gates it with
`IsColAut`. Unfolding that gate:

> **`twistOf` verifies ⟺ `adj^{π_1} = adj^{π_j}`** — the twist is an automorphism exactly when the two
> leaves are the *same relabelled graph*.

So deepen already computes a per-anchor certificate `cert(r) := adj^{π_r}` and throws away every bit of
it except the equality test. The interesting question is what the *negative* branch means.

### 1.1 What a twist failure does and does not prove

**It does not prove the pair is in a different orbit.** Measured per pair against an exact orbit
oracle, with every false negative certified by an explicit verified `IsColAut` — see §2.1.

**The mechanism is exact and exceptionless** (§2.3): cell *ids* transport but the `min`-index member
does not, so if `σ a = b`, `σ` carries `a`'s chosen cell onto `b`'s but not min ↦ min. The two descents
stay aligned through every **single-orbit** cell — a stabiliser element repairs any pick — and break at
the **first cell that is not a single stabiliser orbit**, where they individualize members of
non-corresponding orbits and every surviving isomorphism dies. Hence:

> **a same-orbit twist failure ⟺ deepen's own path crosses a cell that is not a single stabiliser
> orbit, and resolves it inconsistently between the two sides.**

The ⟸ direction is the landed `joint` + `twistOf_of_transport_fixing`; ⟹ is §2.3's traces.

**This is not fusion.** Fusion = the symmetry is not *there* yet at the compared level (it becomes
certifiable only after a rigid decision), and a perfect same-level comparator would decline too. Here
the compared pair **is** in one orbit at the very colouring being compared and the comparator still
fails. The real fusion signature remains Chang-A's `A_stall < A_full`.

### 1.2 Consequence for what can be proved

`¬CellIsOrbit ⟹ RigidObstructionAt at this cell` is **refuted** (§2.1's second falsifier: the cell is a
single orbit, so there is no obstruction in it), and at that node force provably cannot fire either
(`Force.forceBy_no_narrowing_on_orbit`). So:

> **No theorem of the shape "consume fails at `χ` ⟹ force can act at `χ`" can hold.** The obstruction
> must be relocated to a **deeper reachable node**. That is the shape of everything in §3.

---

## 2. What is measured

Exact orbit oracle throughout: `a ~ b ⟺ canon(adj, χ+a) = canon(adj, χ+b)` (the Karp /
Booth–Colbourn reduction of §8.1), with `canon` the min-over-cell exhaustive canonical form.

### 2.1 The harvest is NOT a perfect orbit oracle — two certified falsifiers

| variant | witness | node | fact |
|---|---|---|---|
| **SINGLE anchor** = C# `HarvestTwists(p, part, cell, cell[0])` | **Chang-B**, `n=28` | the **root** (no force step, no deep path) | anchor `a₀=0` has **23** same-orbit partners; the twist verifies for **11** and **FAILS for 12**. Certificate: explicit `σ`, `is_aut ✓`, colour-preserving ✓, `σ(0)=10` |
| **ALL anchors + group closure** = Lean `deepenGens` | **CFI over a random cubic base, m=8**, `n=56` | the `\|C\|=16` cell (one equivariant force-key refinement below the root) | the cell is **ONE true orbit**; the harvest splits it **8+8**. Certificate: explicit `σ`, `is_aut ✓`, colour-preserving ✓, `σ(24)=26` crossing the blocks. Reproduced by two independent implementations |

**Failure mode in both cases is not `replay` bailing out.** Chang-B: replay followed the id sequence in
**12/12** failures. CFI m=8: `replay-null = 0`, `twist-not-aut = 128` of 240 ordered pairs, and **every**
anchor fired the gate. So the negative branch is `cert(a) ≠ cert(b)` in exactly the sense §1 describes,
and it is **not** a separation.

### 2.2 ⚠ The per-pair reading is wrong even where the ORBIT reading is right

`branchOrbit_iff_aut_of_certified` equates the orbit relation with `WordReach` over the *verified
generator set* — the **group generated**, not the individual twist. Chang-B root shows the gap: **12
direct-twist failures, but zero false negatives after generator closure.** The C# already relies on
this (`CoveredByPathFixingAut` BFS-closes over `Automorphisms.Generators`). **Reading a per-pair twist
failure as a separation certificate discards precisely that closure**, and is unsound even on nodes
where the harvest's partition is exact.

### 2.3 The mechanism, traced level by level

`Sigma_k` = the isomorphisms carrying `a`'s pick-sequence to `b`'s; `Sigma_k ≠ ∅` tested exactly as
`canon(a-side) = canon(b-side)`.

```
Chang-B root, pair (0,10):   |Aut| = 96, |Sigma_0| = 4   (same orbit)
  level 0: cell id=1 |C|=12  stabiliser-orbits = 4  <-- MIXED
           a picks min=2, b picks min=1; Sigma-images of 2 = {3,12,15,26}, 1 not among them
           |Sigma| 4 -> 0    *** DIVERGENCE

CFI cubic m=8, |C|=16 node, pair (24,26):  aligned at start (same orbit)
  level 0: |C|=2  orbits=1   a picks 28, b picks 30   aligned
  level 1: |C|=2  orbits=1   a picks 26, b picks 24   aligned
  level 2: |C|=2  orbits=1   a picks 30, b picks 28   aligned
  level 3: |C|=4  orbits=2  <-- MIXED   both pick 32  *** DIVERGENCE
                                        (32 has a different orbit-role on the two sides)
```

### 2.4 Guard conservatism — 1361 nodes, 10 families

Bounded descent sweeps (depth ≤ 2, all reps), `Tinhofer` vs. harvest exactness at every node:

| family | nodes | `Tinhofer` | harvest EXACT | exact but `¬Tinhofer` |
|---|---|---|---|---|
| Chang-A / Chang-B / Chang-C | 365 / 173 / 46 | 364 / 148 / 46 | **365 / 173 / 46** | 1 / 25 / 0 |
| T(8)=J(8,2) · mp7 · MIXED · circ(5) · CFI-C₅ · Shrikhande⊎Rook(4,4) | 365·365·13·11·61·225 | all 100 % | **all 100 %** | 0 |
| C3+C4+C5 (cells provably ≠ orbits) | 37 | 24 | **37** | 13 |
| **total** | **1361** | **1197 (87.9 %)** | **1361 (100 %)** | **164** |

* The all-anchor harvest was **exact at every one of 1361 nodes**, including all 164 `¬Tinhofer` ones.
* `Tinhofer` is **sufficient but far from necessary** — the guard defers on ~12 % of nodes where the
  supply would have been exact. **The firing bottleneck is the GUARD, not the harvest.**
* ⚠ But harvest-transitivity certifies only the `|P| = 1` case. Where the cell has ≥ 2 true orbits the
  guard must certify the **partition**, and that is exactly where the CFI m=8 node lies.
* The anchor-count claim reproduces exactly — CFI cubic m=14, `|C|=56`: **3 anchors → 36 blocks, ALL
  anchors → 14 = TRUE**. And m=8's `(16, harvest 2, true 1)` stall **persists over every anchor**.

### 2.5 `orbKey` fires and is exact at hook nodes — 147/147

Faithful ports of the Lean `indivOne` (`2·χx + [x=v]`), `step`, `leafOf`, `readKey`. At every **hook
node** (`Tinhofer` ∧ branch cell with ≥ 2 orbits — the conclusion of `not_tinhofer_deepest`):

| C3+C4 | C4+C5 | C3+C4+C5 | Shrikhande⊎Rook | Chang-A | Chang-B | MIXED | **total** |
|---|---|---|---|---|---|---|---|
| 1/1/1 | 1/1/1 | 12/12/12 | 0 | 108/108/108 | 24/24/24 | 1/1/1 | **147 / 147 / 147** |

(hooks / `orbKey` fires / fibres == true `Aut`-orbits exactly). **Every leaf discrete** (0 exceptions),
which is what makes the read complete.

A second, earlier sweep counted **100** hook nodes over the same families using a rank-based `indivOne`
ordering instead of the Lean one (`v` lands *before* rather than *after* its cellmates) — a different
descent tree, hence a different but equally valid sample. Both are non-vacuity evidence; they are not
two measurements of one quantity.

### 2.6 Other recorded measurements (`probe_dualdeepen.py`, `probe_polyloop.py`)

**Verdict structure, 18 witnesses** (mp7/Fano, CFI over C₅ and over random cubic bases m=8..14, mixed
multipede, circ(5), 6 rigid random multipedes n=34..84):

| measurement | result |
|---|---|
| **min-over-cell cert invariant under relabelling** | **18/18 TRUE** — the §4.2 fallback's `①`, empirically |
| **greedy index-pick cert (= today's `deepen`) invariant** | **FALSE on 9/18** — mixed multipede, circ(5), all 6 rigid multipedes, CFI-cubic m≥10. TRUE on mp7 and CFI-C₅, which is why mp7 alone cannot detect the problem |
| **cert-ties failing to yield a verified path-fixing automorphism** | **0 of ~150 ties, every witness** — the tie reading is complete; this is §4.1's "two blocks cannot tie", measured |
| **cost, pruned leaves** | 4–29 across all witnesses (CFI cubic m=14, n=98: **29 leaves**; rigid multipede n=84: **4 leaves**) |
| **cost, unpruned leaves** | up to 3584; ratio tracks `\|Aut\|` (mp7: 1344 unpruned = `\|Aut\|` exactly) |
| **consume output** | mp7 `\|Aut\| = 1344` recovered ✓ (matches the C# cross-check) |

**The poly loop per witness** — `bₖ=1` justified by FORCE (a key splits) or CONSUME (certified orbit),
else a STALL. Stall triple = `(|C|, harvest-orbits, TRUE-orbits)`, harvest at 3 anchors:

| witness | levels | FORCE | CONSUME | STALL | stalls |
|---|---|---|---|---|---|
| mp7 Fano | 3 | 0 | **3** | **0** | — |
| circ(5) | 2 | 1 | 1 | **0** | — |
| CFI cubic m=10, m=12 (pl+tw) | 6 | 1 | 5 | **0** | — |
| CFI cubic m=8 pl | 7 | 1 | 4 | 2 | (16, 2, **1**) · (4, 2, 2) |
| CFI cubic m=14 (pl+tw) | 7 | 0 | 6 | 1 | (56, 36→**14** at all anchors, 14) |
| MIXED multipede | 3 | 0 | 2 | 1 | (4, 2, 2) |
| rigid multipedes n=34..84 | 1–2 | 0 | 0 | 1–2 | (4,4,4) · (2,2,2) … |

Two of the three stall kinds are benign: **genuine rigid decisions** (harvest == TRUE > 1 — branching is
forced, and that is force's job) and **anchor-count gaps** (harvest > TRUE, closing with more anchors —
m=14's 36 → 24 → 16 → 14). The third, m=8's `(16, 2, 1)`, is the pick-misalignment witness of §2.1.

### 2.7 ⚠ Probe traps (recorded because both cost real time)

* **Close over the generators.** Compute the harvest's orbit relation as `v ~ g v` for every generator
  `g` and every `v`, never by unioning only the `(anchor, rⱼ)` pairs. The latter manufactured a
  spurious 176-pair "fusion falsifier" at the Chang-A root. (`probe_polyloop.py` does it correctly.)
* **Content-key the canonical-form cache.** Keying on `id(adj)` is wrong — Python recycles ids across
  freed graphs, silently returning another graph's canonical form.
* **Rigid witnesses cannot test a certified-below route.** By §8.4 they certify only vacuously.

---

## 3. What is proved — the landed chain

Every theorem below is `[propext, Classical.choice, Quot.sound]`. ⚠ This section is the 2026-07-27
(earlier) state; **§10 is the current one**.

### 3.1 `DeepenCertified.lean` — `Tinhofer` as a run-time certificate

| | statement | name |
|---|---|---|
| T1 | `CertifiedOrbit ⟹ CellSingleOrbit` — a *checked* transitivity of harvested twists **is** single-orbit-ness | `cellSingleOrbit_of_certifiedOrbit` |
| T2 | `CertifiedPath ⟹ TinhoferPath`, `Certified ⟹ Tinhofer` | `tinhoferPath_of_certifiedPath`, `tinhofer_of_certified` |
| T3 | selector identity `chooseIdK (finRange n) = Descend.targetColour` — deepen's per-level cell **is** the canonizer's branch cell | `chooseIdK_eq_targetColour` |
| T4 | per-level bridge: `Consume.CellIsOrbit` discharges the level's certificate | `certifiedOrbit_of_cellIsOrbit_chooseIdK` |
| T5 | at a certified node, consume failing names a non-automorphic pair **in this branch cell** | `consume_fail_gives_real_decision`, `rigidObstructionAt_branch_of_certified` |
| T6 | **`Tinhofer` transports** — the index-pick obstruction absorbed as in `joint` | `tinhoferPath_transport`, `tinhofer_transport{,_iff}` |
| T7 | guarded supply ⟹ **`①c` with no hypothesis at all** | `deepenSupplyGuarded_canonizer` |

T5's `Certified` hypothesis is **necessary, not an artefact** — §2.1's second falsifier refutes the
unguarded statement.

### 3.2 `DeepenLocated.lean` — locating the obstruction (10 theorems)

| | statement | name |
|---|---|---|
| C1 | `DescentReach` — reachable by *proper* steps (individualize a vertex **with a same-colour partner**, then refine), + `trans` | `DescentReach`, `.trans` |
| C1a | a proper step strictly raises `ncol`; reachability never lowers it | `ncol_lt_step_of_partner`, `ncol_le_of_descentReach` |
| C1b | a `chooseIdK` level's pick has a partner | `partner_of_chooseIdK` |
| **C2** | `¬TinhoferPath ⟹ ∃ ψ` **reachable**, obstruction at `ψ`'s **branch cell** | **`not_tinhoferPath_located`** |
| **C3** | `¬Tinhofer adj χ ⟹ ∃ ψ` reachable with **`Tinhofer adj ψ`** ∧ obstruction at `ψ`'s branch cell | **`not_tinhofer_deepest`** |
| — | the `Tinhofer` (not `Certified`) form of §3.1's T5 | `consume_fail_real_decision_of_tinhofer`, `rigidObstructionAt_branch_of_tinhofer` |
| — | every consume failure is located, one disjunct or the other | `consume_fail_locates` |

C3's point: one node carries **both** hypotheses — consume is exact below it (what an orbit-separating
equivariant key needs) *and* force has a genuine rigid decision at its branch cell. Termination is the
`Descend.ncol` measure, the same one `deepen_succeeds` uses; the base case needs no discreteness lemma
because `¬Tinhofer` itself produces a branch vertex, hence a partner, hence `ncol χ < n`.

**Non-vacuity checked** — nodes that are `Tinhofer` **and** whose branch cell has ≥ 2 orbits, i.e.
inhabitants of C3's conclusion:

| C3+C4 | C4+C5 | C3+C4+C5 | Shrikhande⊎Rook | Chang-A | Chang-B | MIXED | total |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 24 | 1 | 24 | 48 | 1 | **100** |

The conjunction also cannot degenerate: the obstruction requires `targetColour ψ = some cid`, so `ψ` is
**not** discrete and `Tinhofer ψ` is a real constraint, not the vacuous `branches = []` case. And the C3
iteration was validated directly on a measured `¬Tinhofer` node (Chang-B root): two steps, `ncol`
2 → 3 → 10, terminating on `Tinhofer = True` with a 2-orbit branch cell.

### 3.3 `DeepenKey.lean` — `orbKey`, the equivariant force key (18 theorems)

```
orbKey adj χ v := if TinhoferPath adj χ n (step adj χ v)
                  then readKey adj (indivOne χ v) (leafOf adj n (step adj χ v)).col
                  else []                                        -- defer
```

| | statement | name |
|---|---|---|
| — | `Refines` + `trans`; `refines_step`, `refines_indivOne`, `refines_transport` | §1 of the file |
| — | **a colour-automorphism of a FINE colouring fixes every COARSER one** | `transport_eq_of_isColAut_refines` |
| — | `leafOf` + three equation lemmas | §2 of the file |
| **A2** | `TinhoferPath` ⟹ the two **leaves** are related by an accumulated isomorphism `ρ`, and `ρ` acts on any refined-from colouring exactly as `σ` does | **`leafOf_transport_of_tinhoferPath`** |
| A1 | the invariant read + its transport | `readAt/readColAt/readAtIdx/readKey_transport`, `filter_col_transport` |
| A3 | the guard is relabelling-invariant **both ways** | `tinhoferPath_step_transport_iff` |
| **A4** | **`Force.KeyEquivariant orbKey` — no hypothesis** | **`keyEquivariant_orbKey`** |

**Why the guard is not a cheat.** The greedy descent breaks ties by vertex index, which does not commute
with relabelling. `TinhoferPath` is exactly the repair, and it is itself invariant (T6), so the `if`
splits the vertices into two relabelling-stable classes and `KeyEquivariant` survives it.

A2 is `tinhoferPath_transport` with its accumulator `τ * σ` **kept** rather than discarded. The one
thing not anticipated in the plan: a leaf-*adjacency* read alone proves only that the two *uncoloured*
individualized graphs are isomorphic, which is not "same orbit" — so the key must carry the parent
colouring, which needs `τ` to fix it, hence the `Refines` invariant threaded through the induction.

⚠ **Reduce `leafOf` only through its equation lemmas.** Unfolding in place and then `cases`-ing on
`chooseIdK` descends into its internal `foldl` and exposes spurious goals — the recorded `deepen`
match-reduction trap. `simp only [leafOf, h, hf]` is what works.

### 3.4 `DeepenExact.lean` — exactness, and force fires (19 theorems)

| | statement | name |
|---|---|---|
| B0 | leaf colours are ranks (`< n`); the greedy leaf at fuel `n` is **discrete** | `warmRefineR_lt`, `leafOf_lt`, `leafOf_discrete{,_n}` |
| B0a | a discrete class is a **singleton**, so the read is one adjacency entry / one parent colour | `filter_eq_singleton_of_discrete`, `readAt_discrete`, `readColAt_discrete` |
| B0b | key equality ⟹ componentwise (two `map`s ⟹ `List.append_inj` + `List.map_inj_left`) | `readKey_components` |
| **B1** | **equal keys ⟹ SAME ORBIT — no hypothesis** | **`isColAut_of_readKey_eq`** |
| B1a | a discrete colouring with colours `< n` is a permutation; two of them match colour-for-colour | `colEquiv`, `matchPerm`, `matchPerm_col` |
| B3 | `orbKey` **separates** any pair no colour-automorphism links | `orbKey_ne_of_no_aut` |
| B3a | at an `Tinhofer` node with a `RigidObstructionAt`, `forceBy orbKey` **strictly narrows** | `forceBy_orbKey_narrows` |
| **B2** | at an `Tinhofer` node **`orbKey`'s fibres ARE the orbits** (both directions) | **`orbKey_eq_iff_orbit`** |
| **D2** | force narrows the branch cell to a **single orbit** | **`forcedSet_single_orbit`** |
| **D1** | **a consume failure makes force fire at a reachable node** | **`consume_fail_force_fires`** |

**The pivot: the firing direction needs no hypothesis.** B1 is completeness of the encoding — discrete
leaf ⟹ singleton classes ⟹ the read determines the relabelled adjacency *and* the relabelled
`indivOne χ v`; the **odd** values of `indivOne χ u` sit exactly at `u`, so
`transportColouring ρ (indivOne χ u) = indivOne χ w` forces `ρ u = w`, and halving gives `χ ∘ ρ = χ`.
`Tinhofer` is needed only for `①` (§3.3) and for the converse half of B2.

**B2 is also the consistency guard** against `Force.forceBy_no_narrowing_on_orbit`: its `⟸` direction is
the ceiling (`Force.keyV_aut_invariant`, free from `keyEquivariant_orbKey`), so the key is constant on
each orbit and force can never cut *inside* one. It separates orbits and nothing finer — which is what
D2 then says. The landed theorems agree, and §2.5's 147/147 is the same statement empirically.

---

## 4. Cost — where the exponential is, and where it is not

**Cost of any descent = `∏ₖ bₖ`.** Today's `deepen` sets `bₖ = 1` **by fiat** (lowest-index pick). That
is free computationally but not free logically: the leaf it computes is a function of the *labelling*
and is only ever usable through an equality test between two runs — which is labelling-independent
exactly when the picked cell is a single orbit, i.e. **`Tinhofer`**. So deepen is not "poly and
correct"; it is **poly, and correct-when-`Tinhofer`**. Nothing in this track *introduces* an
exponential — it *prices* the assumption deepen was making for free.

`bₖ = 1` is legitimate under either justification:

* **CONSUME** — the cell is certified a single orbit: pick any member.
* **FORCE** — a poly equivariant key *splits* the cell: then we **refine, not branch**; the cell shrinks
  and there is no cost multiplier at all.

So the exponential survives only where both fail, and `cost = ∏(branch factors at stalls)`. Against the
landed chain: `orbKey` supplies the FORCE half wherever its guard is open, and D2 says the forced set is
a single orbit, so consume finishes it. The residual cost question is **how often D1's relocation
recurses** — `DescentReach` + `ncol` bound it by `n` *steps*, but the product over relocations is not
bounded here.

### 4.1 The split loop — the mechanism has no third case

```
loop:  refine
       if discrete: done
       C := target cell;  P := orbit partition of C
       if |P| = 1:  individualize any member          -- CONSUME, branch factor 1, FREE
       else:        order the blocks, refine by rank  -- FORCE, a SPLIT, no branch
```

**Two blocks cannot tie**: `cert(a) = cert(b) ⟺ (adj, χ+a) ≅ (adj, χ+b) ⟺ a, b in the same orbit`, so a
tie contradicts them being distinct blocks. The split therefore always succeeds. **There is no third
outcome** — the `¬HandledS` "true mutual stall" does not exist as a mechanism; it exists only as cost.
Measured, 13 witnesses: `blocks-tied = 0` everywhere, `① = OK` everywhere.

| witness | calls | splits | free | max-nesting | blocks/split |
|---|---|---|---|---|---|
| mp7 Fano | **1** | 0 | 3 | 0 | — (pure consume) |
| MIXED multipede | 3 | 1 | 7 | 1 | [2] |
| circ(5) | 4 | 1 | 4 | 1 | [3] |
| rigid multipedes n=34..84 | 5–15 | 1–6 | 0–1 | 1–2 | [4] … [4,2,2,2,2,2] |
| CFI cubic m=8 / 10 / 12 / 14 | 3 / 9 / 8 / **17** | 1 / 2 / 1 / 2 | 14 / 39 / 43 / **96** | 1 / 2 / 1 / 1 | [2] / [6,2] / [7] / [14,2] |

⚠ **Cost caveat — do not over-read.** These are not the I-R-lower-bound families (Neuen–Schweitzer
odd/expander multipedes, Miyazaki). Random multipedes and CFI over small cubic bases are *easy* for I-R;
the small leaf counts are suggestive, not evidence of polynomiality. The exponential risk is real and
**unmeasured**. What the probes establish is the **verdict structure**, which is labelling-independent
and is the part the design turns on. ⚠ Group completeness is also not independently verified: `|Aut|` is
read off the generators the descent itself discovers; consistency checks pass, but no external oracle
was consulted.

### 4.2 The min-over-cell key — the standing fallback

Replacing the index pick by **min over the cell** gives a key that is `KeyEquivariant`
*unconditionally*, by a much simpler induction than §3.3's (cells transport, and the min of a
transported multiset is equal — no `Tinhofer`, no isomorphism accumulation). Cost is
`∏ₖ (surviving reps at level k)`, i.e. the classical I-R tree. It reaches the same D-level statements
with exponential `keyCost`, so **D is reachable by two independent routes**; `orbKey` buys the *poly*
version wherever its guard is open.

---

## 5. Correction to `CORE_scoping.md` (measured, 2026-07-26)

`CORE_scoping.md` §"Measured" reports *"rigid case R=30 (30/30)"* for the `circ(5)` multipede.
**Measured here: `circ(5)`'s multipede has `|Aut| = 10` (D₅ scheme symmetry), 5 orbits, and
`R(Aut-fixed) = 0` — not 30.** The `R` there was computed from `support(ker H)`, the *linear* handle,
and `circ(5)` is a circulant, so its symmetry is entirely of the **scheme** kind that CORE_scoping's own
2026-07-26 correction says `ker H` misses. Since the R/K plan needs `R` to be *Aut*-fixed (not
`ker H`-fixed), the `circ(5)` witness does not support it; the **MIXED** multipede does (`|Aut| = 8`,
`R = 4` genuinely Aut-fixed), as do the rigid random multipedes (`|Aut| = 1`, `R = n`).

This also names the poly constructor the R/K split was missing: **`K` = the orbits the dual's ties
produce, `R` = what its certified separations leave.**

---

## 6. Strategy assessment — the block-ordering question

* **S1 — the certified-below cert key. ✅ This became `orbKey` (§3.3/§3.4).** If `TinhoferPath` holds
  along `a`'s greedy descent, deepen's single-path leaf cert is iso-invariant; combined with exactness
  it is a poly, equivariant, exactly orbit-separating `Force.Key`, so it **orders the blocks**. Measured
  (`probe_certkey.py`, 9 witnesses): certified-below reps with a non-invariant cert = **0**; every
  non-invariant cert came from an **uncertified** rep (perfect correlation). Now a theorem.
* **S2 — deferred schedule. ✅ effective, ⚠ does not reach "purely rigid".** *"Lowest-id **single-orbit**
  non-singleton cell, else lowest-id"* is an equally legal `targetColour`, and individualizing inside a
  single-orbit cell costs branch factor 1. Measured: forced decisions drop to **0–2 per witness**; MIXED
  and mp7 need **zero**. But at CFI cubic m=8/10/12 the first forced decision still has
  `|Aut| = 512 / 128 / 256` — you run out of *consumable cells* long before you run out of *symmetry*,
  so the whole-node-rigid anchor (rigid-seal 9A–9C, `OrdEquivariant`) does **not** become applicable
  this way. S1 covers it instead, being gauge-tolerant where 9A–9C is not.
* **S3 — order-agnostic block splitting. ❌ refuted on the cheap keys.** Blocks are invariant sets, so
  any invariant set-function is a legal colour — no order needed. Tested `|B|`, the refinement histogram
  after set-individualizing `B`, and that plus `B`'s neighbourhood colours: **0 of 8 forced decisions
  separated** (only circ(5), and only the third variant) — the block-level analogue of the recorded
  `baseReadWL` blindness. Remains a free *pre-filter* wherever it fires.
* **S4 — k-fold branch, non-recursively.** Where S1 is unavailable, branch over one rep per block and
  take the min. Cost `k` at that node, **not exponential unless nested**. Measured nesting: 8/9
  witnesses have a single non-nested decision.

**The residue is not ordering.** It is nodes with an **uncertified** rep — `TinhoferPath` breaks
somewhere below. Measured: rand multipede V=12 W=8 (0/4 reps certified) and CFI cubic m=10 (4/40).
There the response is to resolve the deeper multi-orbit cell first (where S1 *does* apply, by
induction) and re-run — which is exactly what `not_tinhofer_deepest` now proves is possible. So the open
question is the **nesting depth of uncertified levels**, a cost/termination question.

---

## 7. ▶▶ THE FRONTIER — a poly, relabelling-invariant guard

`orbKey`'s guard is `Tinhofer`. It is *decidable* (`IsColAut` has a `Decidable` instance and
`Equiv.Perm (Fin n)` is a `Fintype`), so `orbKey` could be made computable at an `n!` price; it is
declared `noncomputable` rather than pretend that is a cost model. **`①` is unaffected either way** —
what a poly guard buys is a `Publication`-eligible executable.

Two candidate repairs. The first is now closed.

### 7.1 ⛔ CLOSED — deepen's own certificate is NOT relabelling-invariant

`Certified` / `CertifiedOrbit` (T1/T2) is poly and sound, and the open item was its invariance. **It is
not invariant, and this is measured, not conjectured** (`scratchpad/probe_guard_invariance.py`): the all-anchor
harvest's branch-cell partition, recomputed on relabelled copies with the node colouring recomputed
invariantly on each copy —

| node | true orbits | harvest blocks | transports? | block-size profiles seen |
|---|---|---|---|---|
| **CFI cubic m=8 pl, the `\|C\|=16` node** | **1** | 2 | **FALSE** | **`(8,8)` and `(16,)`** |
| Chang-A root | 2 | 2 | TRUE | `(4,24)` |
| Chang-B root | 2 | 2 | TRUE | `(4,24)` |
| MIXED multipede root | 2 | 2 | TRUE | `(2,2)` |
| C3+C4+C5 root | 3 | 3 | TRUE | `(3,4,5)` |

At the m=8 node the harvest **certifies the cell as one orbit under some labellings and splits it 8+8
under others** — so `CertifiedOrbit` is TRUE and FALSE at the same node depending on the labelling.
A guard cannot be built from it: the `if` would itself break `KeyEquivariant`.

Same node as §2.1's second falsifier, same root cause as §2.3 — the certificate is computed *by* the
index-picked descent, so it inherits exactly that descent's labelling dependence. **Proving it
invariant was never a missing lemma; the statement is false.**

⚠ This does not contradict the earlier "partition transports 18/18" measurement
(`probe_verdict_invariance.py`): that was taken at **branch cells of the plain descent**, where the
harvest happens to be exact. Exactness and invariance coincide there; the m=8 node is where they part.

### 7.2 ✅ LANDED — guard by an *equivariant* supply, per level (`ChainDescent/DeepenGuard.lean`)

17 theorems, all `[propext, Classical.choice, Quot.sound]` or a subset; in `build.sh` after
`DeepenExact`.

Guard each level of the greedy path by `Consume.CellIsOrbit S` for a supply `S` already proven
**`GensEquivariant`**, instead of by deepen's own harvest:

```
CertPathS adj : Nat → ColData → Prop
| 0, _        => True
| fuel+1, cur => match chooseIdK (finRange n) cur.col with
    | none     => True
    | some cid => Consume.CellIsOrbit S adj cur.col        -- S's verified gens transitive on the cell
                  ∧ CertPathS adj fuel (step adj cur.col w)
```

* **SOUND** — `CellIsOrbit S adj χc` at the chosen cell ⟹ `CellSingleOrbit adj χc cid`, because `S`'s
  generators are *verified* `IsColAut` and `WordReach` composes. This is T1 verbatim; T1's proof uses
  nothing specific to `deepenSupply`, so it generalizes to any supply.
* **INVARIANT** — from `GensEquivariant S`, plus the same pick-absorption induction as
  `tinhoferPath_transport` (whose per-level input is supplied by SOUND). Needs one new lemma:
  **`CellIsOrbit` transports under `GensEquivariant`** — it does not exist yet and looks routine
  (`WordReach` over a transported generator list).
* **POLY** — if `S` is poly.

**Five supplies already carry `GensEquivariant`**, so the design has ready inputs, not a prerequisite:

| supply | proof |
|---|---|
| `deckSupply` | `DeckSupply.lean:557` |
| `deck2Supply` | `Deck2.lean:400` |
| `foldSupply` | `FoldSupply.lean:396` |
| `foldSupplyFast` | `FoldFast.lean:121` |
| `Consume.matchSupply` | `SupplyTransport.lean:249` |

#### Measured — how much would it actually certify (`probe_eqsupply_guard.py`)

The concern was that these are propagation- and fold-shaped constructors, and `deepen` exists *because*
they are defeated in principle on `mp7` (girth 6 ⟹ a seed forces one vertex and nothing chains). But the
comparison is not at the root cell — the guard only has to certify the cells *along the greedy path*,
which are far finer. Measured with a **depth-0 proxy** for the deck family (seed the pair, individualize
each side, refine; if both leaves are discrete the colour match is forced — build it and verify with
`IsColAut`). This is a **lower bound**: the real `deckSupply`/`deck2Supply` also chain, so they certify
at least this much.

| witness | hook nodes | path cells `TinhoferPath` inspects | certified by the proxy | hook nodes **fully** certified |
|---|---|---|---|---|
| Chang-B | 24 | 48 | **48 (100 %)** | **24 / 24** |
| Chang-A | 108 | 408 | 264 (64.7 %) | **96 / 108** |
| MIXED multipede | 1 | 8 | 4 (50 %) | 0 / 1 |
| C3+C4 · C4+C5 | 1 · 1 | 21 · 27 | 7 · 9 (33 %) | 0 / 1 · 0 / 1 |
| C3+C4+C5 | 12 | 376 | 94 (25 %) | 0 / 12 |
| mp7 Fano | 0 | — | — | — (branch cells are single orbits; pure consume) |

**Verdict: viable but strictly weaker, and the weakness is a firing loss, not a soundness loss.** On the
Chang family the guard would open at **120 of 132** hook nodes even at depth 0; on the disjoint-cycle and
MIXED witnesses it opens at none of them. Where it is shut, `orbKey` returns `[]` and force simply does
not act at that node — `①` is untouched, and `not_tinhofer_deepest` still relocates. So the design is
usable today at a measured cost, and the obvious next lever is depth (the proxy is depth-0; `deck2Supply`
seeds two vertices and chains) rather than a different guard shape.

Two further points on the design space:

* The **union of equivariant supplies is equivariant**, so the guard may use all five at once rather
  than pick one.
* Deepen's harvest can still be used to *fire*, since it is untrusted and re-verified — only the
  **guard** needs invariance. Nothing in §3 changes.

#### What landed

| | statement | name |
|---|---|---|
| — | `WordReach` over a verified list is an automorphism — **for any supply** (`DeepenTinhofer`'s version is `deepenSupply`-specific) | `wordReach_isColAut{,_verified}` |
| **SOUND** | `CellIsOrbit S` ⟹ the branch cell's `CellSingleOrbit`; hence `CertPath S ⟹ TinhoferPath` and `CertifiedG S ⟹ Tinhofer` | `cellSingleOrbit_of_cellIsOrbit`, `tinhoferPath_of_certPath`, `tinhofer_of_certifiedG` |
| **the missing lemma** | `WordReach` and `CellIsOrbit S` **transport** under `SupplyEquivariant S` | `wordReach_transport`, `cellIsOrbit_transport` |
| **INVARIANT** | `CertPath S` transports, both directions | `certPath_transport`, `certPath_step_transport_iff` |
| **①** | **`Force.KeyEquivariant (orbKeyG S)`** from `SupplyEquivariant S` alone | **`keyEquivariant_orbKeyG`** |
| firing | `orbKeyG S` separates a non-automorphic pair; at a `CertifiedG S` node with an obstruction, `forceBy (orbKeyG S)` **strictly narrows** | `orbKeyG_ne_of_no_aut`, `forceBy_orbKeyG_narrows` |
| the hook | localization unchanged; firing conditional on the guard | `consume_fail_force_fires_guarded` |
| agreement | wherever the poly guard is open the two keys are **equal** — `orbKeyG S` is a restriction of `orbKey`, not a different function | `orbKeyG_eq_orbKey_of_certPath` |
| **non-vacuity** | instantiated at `deck2Supply` and `deckSupply`; `①a`/`①b`/`①c` + totality with no hypothesis | `keyEquivariant_orbKeyG_{deck2,deck}`, **`force_canonizer_orbKeyG_deck2`** |

`B1` (`isColAut_of_readKey_eq`) is guard-agnostic — it is completeness of the *read* — so the entire
firing argument transferred verbatim; only "both guards open" changed.

#### ⚠ Exactly what the poly guard costs

`CertPath S ⟹ TinhoferPath`, never the converse. So:

* **Unchanged:** `①` (`keyEquivariant_orbKeyG`), the localization (`not_tinhofer_deepest` never mentions
  a guard), and agreement with `orbKey` wherever the guard is open.
* **Weakened:** the *firing* half. `DeepenExact.consume_fail_force_fires` is unconditional **over
  `orbKey`**; `consume_fail_force_fires_guarded` reaches the same node but discharges firing only under
  `CertifiedG S ψ`. Where the guard is shut the key is constant, force does not act, and `①` is
  untouched — a deferral, not an error.
* **So the two keys coexist by design**: `orbKey` (`Tinhofer` guard, `noncomputable`) carries the
  unconditional theory; `orbKeyG S` (poly guard) is the executable. `orbKeyG_eq_orbKey_of_certPath`
  is the bridge that makes that honest rather than two unrelated objects.

The measured firing rate is §7.2's table above (depth-0 lower bound): **120 of 132** hook nodes on the
Chang family, **0** on the disjoint-cycle and MIXED witnesses. The obvious next lever is depth — the
proxy is depth-0 while `deck2Supply` seeds two vertices and chains — not a different guard shape.

### 7.3 The rest of the open ledger (all `②`, none `①`) — ⚠ items 2, 3, 5, 6, 8 are DONE (§10.5)

1. **Nesting depth.** ⚠⚠ **RESTATED 2026-07-28 (user) — the old wording below was wrong about where the
   difficulty sits, and the correction is a genuine narrowing.**

   > **The flag is not reached via a stall.** *"Consume fails ⟹ force fires somewhere"* has as its free
   > contrapositive *"force fails everywhere ⟹ some consume node fires"* — so in theory **no mutual
   > stall occurs**, and the residue is not a stall channel at all. What the argument depends on is
   > **equivariance**, which is not yet proved; and what remains after it is **cost**: do both
   > resolvers finish in poly-bounded time? That is currently settled *in prose* for everything except
   > the **guards**.

   So this item is not "bound a branching product." Two things follow, and they change what to build:
   * **There is no product to bound in the record object.** `Select.selNode_children_length_le_one` is
     unconditional and `Select.descendS_cost_le_of_le_one` already gives a single path, so nothing
     multiplies. The old wording imported a branching object (§6's S4 `k`-fold move) that the record
     object is not.
   * **The live question is the guards' bill**, and that is now concrete: `keyCost_orbKeyG_le` is
     parametric in the supply's `c₂` (§10.5), and **no record supply has a `c₂` at all** — see item 9.

   ⚠ What is *still* honestly open under the restatement: `consume_fail_locates_resolved` resolves a
   node the descent **reaches**, while `HandledS` quantifies over **every** reached node, so the hook
   does not by itself prevent a flag at `χ`. Under the restatement that gap is the *equivariance*
   dependency named above, not a cost product.
2. ~~**Composite assembly.**~~ **✅ DONE (§10.1)** — and it was mis-scoped here. It does *not* need
   `Consume.CellIsOrbit` on the forced sub-cell: `CellIsOrbit` is a statement about the **whole** branch
   cell and is FALSE at exactly the mixed nodes this is for. The needed fact is the weaker pairwise
   `WordReach` on the forced set, and `Deepen.deepen_branch_orbit_iff_aut` (landed 2026-07-23) already
   supplies it at an `Tinhofer` node. `KeyComplete.forceThenConsume_singleton_of_forcedWordReach` is
   the generalized brick; `nodeResolved_of_tinhofer` is the payoff.
3. ~~**Entry into `Publication.canonForm?`** waits on a decision procedure for `CellIsOrbit S`.~~
   **✅ DONE (§10.5)** — and it was **smaller than billed:** `Consume.orbit` is a computable BFS and `Consume.mem_orbit_iff_wordReach`
   is proved, so `Decidable (WordReach G u w)` is one `decidable_of_iff`, `CellIsOrbit` follows by
   `List.decidableBAll`, and `CertPath` by structural recursion. `leafOf`/`readKey`/`readAt` are already
   computable defs — **only the guard was placeholdered**, so `orbKeyG S` is now computable outright
   (`Consume.decidableWordReach` → `decidableCellIsOrbit` → `Deepen.instDecidableCertPath`).
   (`orbKey` cannot and stays the theory-side object: its `TinhoferPath` guard is an `n!` search.)
   ▶ What still gates `Publication` is the **record-object integration**, item 7.
4. ~~**Guard strength.**~~ **✅ DONE (§10.6)** — the union, `Deepen.guardSupply`. ⚠ **The lever was not
   depth**, as this item originally guessed. The strongest available certifier is `deepenSupply` itself — *exactly* complete at
   `Tinhofer` nodes by `deepen_branch_orbit_iff_aut` — and it is excluded only because it is not
   `GensEquivariant`. That is the problem `kernelSupply` solved via `OrbitPrune.SameOrbits` against an
   equivariant reference, and the congruence machinery exists (`SelectNode.cellNarrow_congr`,
   `handledS_of_sameOrbits`). Guarding by `S` with `SameOrbits S Ref` for equivariant `Ref` looks
   strictly better than depth. ~~**Untried.**~~ **▶ GENERIC HALF LANDED 2026-07-28 (`DeepenGuard` §9)
   — and the instance is NOT independent of a retired route; see §10.7.**
5. ~~**`②` is declarative at both keys.**~~ **✅ DONE (§10.5)** — `certPathCost` + `keyCost_orbKeyG_le`.
   The original diagnosis, kept because it is the reason the fix was needed: `keyCost (orbKeyG S) = n⁴`
   held *by definition*, and the guard
   is currently not computable at all, so the bill prices nothing — the same shape as the 2026-07-14
   "costs are now honest" finding. `SupplyCost` already has the pattern (`keyCost_lookaheadKey_le`).
   remaining-work §1T's recorded debt ("`deepenSupply` has NO formalized cost bound") now extends to
   both keys, and it is the **same work as item 3** — pay them together.
6. ~~**`DescentReach ⟹ Descend.Reaches` is missing.**~~ **✅ DONE (§10.5)** — `reaches_of_descentReach`. `HandledS` quantifies over `Descend.Reaches`; D1
   delivers `DescentReach`. `Descend.Reaches.step` carries *exactly* `DescentReach.cons`'s side
   condition and `step` is `refineV encodeFreeFast ∘ indivOne`, so this is near-definitional — but
   without it D1's `ψ` is not formally a node the canonizer visits.
7. **Neither live track is in the record object.** ✅ **DONE 2026-07-28 (§10.10) except the
   `Publication` edit itself** — `RecordKey.recordKey` is built and carries `①`+`②`; what remains is
   pointing `Publication.canonForm?` at it *together with* the monomial reshape (see the HANDOFF block
   at the top of this doc). Original wording: `Publication.canonForm?` uses `holKeyFast`; no
   `orbKey*` and no rigid-seal key appears. `force_canonizer_orbKeyG_deck2` is `①` for a **force-only**
   canonizer — a different object. Integration needs a key composition (`RigidSeal.compKey`'s
   disjoint-tag pattern is the template) plus a re-proof of `canonForm?_record`.
   ⚠ **Two corrections (2026-07-28).** (a) The `①` half is *smaller* than this reads:
   `Select.selNode_canonizer_of_sameOrbits` is **key-generic**, so swapping the key costs exactly one
   `KeyEquivariant` proof, which `keyEquivariant_orbKeyG_guard` already supplies. What is genuinely
   missing is a **lex-product key combinator** — `compKey`'s disjoint tag is a *case split*, not a
   product. ⚠⚠ **This item's proposed encoding `(len a :: a) ++ (len b :: b)` is WRONG** — it orders the
   first component by *shortlex*, which `lexLeList` is not, so it silently re-orders `holKeyFast`'s own
   narrowing. The correct product is **plain concatenation under `ConstLen`**; see §10.10.
   (b) **Do this AFTER item 9**, or it adds a fifth unbilled component to an object
   that has no cost theorem.
   **✅ DONE 2026-07-28 — `ChainDescent/RecordKey.lean` (§10.10).** `pairKey`, `ConstLen`,
   `keepMin_pairKey_subset`, and `recordKey = pairKey holKeyFast (orbKeyG guardSupply)` with `①`+`②`.
   Measured non-vacuous: on `G8` the cell goes **8 → 2** where `holKeyFast` alone keeps all 8.
   ▶ Still open: editing `Publication.canonForm?` itself, which wants the `②` bound reshaped into the
   pinned `costConst * n ^ costDeg` monomial — do the two together.
8. ~~**No Lean `#guard` for either key.**~~ **✅ DONE** — `Regression` §17/§17a. All firing evidence is Python probes; the project's own vacuity
   discipline asks for a `#guard`ed witness in the same pass. Once item 3 lands, `orbKeyG` is
   `#eval`-able and §2.5's 147/147 can be ported into `Regression`.
9. **⚠⚠ NEW (2026-07-28) — THE RECORD OBJECT HAS NO `②` AT ALL.** This was invisible in the ledger
   because every `②` conversation here was about *this track's* key. Measured by grep, not argued:

   | component of `Publication.canonForm?` | `supplyCost` / `keyCost` bound |
   |---|---|
   | `Fold.foldSupplyFast` | **none** |
   | `Deck.deckSupply` | **none** |
   | `Deck2.deck2Supply` | **none** |
   | `Kernel.kernelSupply` | **none** |
   | `Hol.holKeyFast` | **none** (`keyCost_holKey` is a `@[simp]` *equation*, not a bound) |

   `SupplyCost.lean`'s bounds cover `matchSupply` / `deepMatchSupply` / `partialMatchSupply` /
   `prunedSupply`, and the two end-to-end theorems (`descentCostS_selNode_pruned_lookahead_le`,
   `descentCostS_selNode_match_lookahead_le`) are at **`lookaheadKey` + `prunedSupply`** — *not* the
   record. So the object with `②` proved is not the object of record. There is also no
   `supplyCost_appendSupply` lemma, though it is definitionally `rfl`
   (`appendSupply` sums the costs), so composition is free once the four parts exist.

   This is the direct target of item 1's restatement — "poly-bounded cost for both resolvers, settled
   in prose except the guards" — and it is the T2 house rule ("closed-form `c₂` at land time") not
   having been applied to any record supply. ~~**Do it before item 7.**~~
   **✅ DONE 2026-07-28 — `ChainDescent/RecordCost.lean` (16 thms, axiom-clean).** All five bounds,
   `supplyCost_appendSupply` (definitional), and **`descentCostS_selNode_record_le`**: an explicit
   polynomial on every input, **no hypotheses**. `record_canonizer_with_cost` puts `①` and `②` in one
   place. ⚠ Reshaping it into `Publication`'s `costConst * n ^ costDeg` monomial is the remaining step
   and touches pinned statements — sequence with item 7.

---

## 8. Literature placement (4 subagent searches, 2026-07-26)

### 8.1 The recalled result is real, and sharper than expected

**Booth & Colbourn, "Problems Polynomially Equivalent to Graph Isomorphism", TR CS-77-04, Univ. of
Waterloo, June 1979**, §2.3 (attributed to **Karp**, following Read & Corneil 1977):

> "**THEOREM: Computing the automorphism partition of a graph is isomorphism complete.** … Two vertices
> *x* and *y* are similar … if and only if *G\*x* and *G\*y* are isomorphic."

Turing-equivalent (their §1 collapses Cook/Karp reducibility by fiat). `|Aut|` and Aut-generators are
**Mathon, IPL 8(3):131–132, 1979**. The `G*x` vs `G*y` apex-clique gadget is inherently **pairwise**. So
**an unconditional poly `SameOrbit` puts GI in P — known since 1979.**

**★ The availability caveat is not a caveat.** B&C §2.4 builds `|Aut|` from automorphism-partition calls
on `G_{v₁,…,v_k}` — *individualization-derived graphs, recursively*:

> "the order of the group of *G*_{v₁,…,v_{k−1}} is exactly *d* times the order of the group of
> *G*_{v₁,…,v_k}, where *d* is the size of the similarity class of *v_k* … **This leads to a recursive
> algorithm … whose running time is polynomial in the time required to compute the automorphism
> partition of a graph.**"

The project's oracle profile **is the classical proof's own profile**. Only the base call on `G ⊎ H` sits
outside it. (Decision-only caveat: the bare yes/no gives `|Aut|` and GI; extracting *generators* needs
B&C §2.2's search-to-decision layer.)

### 8.2 ★ Neuen–Schweitzer's exponential lower bound does NOT bind this algorithm

**Neuen & Schweitzer, STOC 2018 (arXiv:1705.03283), §3**, after Prop. 3.1, verbatim:

> "**Likewise would a refinement operator that refines every coloring into the orbit partition under the
> automorphism group** [yield a polynomial-size search tree]. However, we do not know how to compute
> these two examples efficiently. In fact computing either of these is at least as hard as the
> isomorphism problem itself. … it is nonsensical to allow that an individualization-refinement
> algorithm uses a subroutine that already solves the graph isomorphism problem."

**The literature names §4.1's algorithm, grants it a polynomial-size search tree, and excludes it from
the model** — solely because orbits are GI-hard. Theorem 3.2 requires *k-realizability* (`WL_k ⪯ ref`,
i.e. **coarser** than k-WL); orbit-refinement on a rigid multipede is *discrete*, strictly finer, so the
hypothesis fails for every k. Their "all automorphisms free" clause is **vacuous** on their family
(`|Aut| = 1`), so it is not a strengthening that covers an orbit oracle.

⚠ Not a free lunch: there `|P| = 1` never occurs, every cell splits into `|C|` singletons, and they prove
a **linear** number of individualizations is forced. All cost lands on the block-ordering recursion.

### 8.3 Naming — one collision, two matches

| project term | literature |
|---|---|
| `Tinhofer` / `CellsAreOrbits` | **= Tinhofer graph.** AKRV (*comput. complexity* 26(3):627–685, 2017; arXiv:1502.01255) App. A.2: *"G is Tinhofer if and only if, for every F, the orbit partition of A_F coincides with P_F."* Graded: Bhattacharjee–Panse–Sarma arXiv:2605.19702 Thm 1.1. |
| ⚠ **name clash — ✅ RESOLVED 2026-07-27** | AKRV's *own* **"amenable"** means something DIFFERENT (1-WL identifies `G` against all `H`); their hierarchy is `Amenable ⊊ Compact ⊊ Godsil ⊊ Tinhofer ⊊ Refinable`, all strict (Thm 21). The project predicate was renamed `Amenable → Tinhofer` throughout, so the clash is gone. ⚠ **But it is not *literally* AKRV's Tinhofer** — theirs quantifies over ALL `S`, this one only over the cells a single descent selects (§8.5). ⛔ Do not blanket-rename `amenable → tinhofer` again: this row and the one above quote AKRV's terms verbatim and a replaceAll inverts them. |
| the free consume step | **"symmetric choice"** (Gire–Hoang 1998; Dawar–Richerby CSL 2003); with automorphisms supplied as certificates, **"witnessed symmetric choice"** — Lichter & Schweitzer, LICS 2022 (Distinguished Paper) / **J. ACM 71(2), 2024**. Their Thm 1: definable isomorphism ⟹ definable canonization. Their stated motivation is verbatim §3.1's T1: *"it has to be verified that the choice set is actually an orbit and it is not known that orbits can be computed in polynomial time."* |
| the whole split loop | **Gurevich's canonization algorithm**, *From invariants to canonization*, Bull. EATCS 63:115–119, 1997: repeatedly compute a **canonical orbit**, individualize one vertex, repeat. Poly complete invariant ⟺ poly canonization (classes closed under colouring). |

### 8.4 ⚠⚠ The rigid collapse — and what it forbids

**AKRV, immediately after Theorem 21:**

> "It is worth noting that **the hierarchy collapses to Discrete if we restrict ourselves to only rigid
> graphs**, i.e., graphs with trivial automorphism group."

For rigid `G`, `Aut_S = 1` for all `S` ⟹ `Orb(Aut_S)` discrete ⟹ **Tinhofer ⟺ 1-WL already discretizes.**
At a non-singleton cell of a rigid graph, "the cell is a single orbit of the stabilizer" is *impossible*.
Consequence for measurement design: on a rigid graph `TinhoferPath` can only hold **vacuously** (zero
levels to certify), so rigid witnesses cannot be used as evidence that a certified-below route fires.
Measured `descend_cert` level counts confirming it:

```
rand multipede V=6 W=5  (n=34)  levels per rep = [0,0,0,0,0,0,0,0]
rand multipede V=8 W=6  (n=44)  levels per rep = [0,0,0,0]
rand multipede V=10 W=7 (n=54)  levels per rep = [0,0,0,0]
rand multipede V=12 W=8 (n=64)  levels per rep = [1,1,1,1]
CFI cubic m=8 (n=56) levels = 5 ;  m=10 (n=70) levels = 4–6      <- these ARE substantive
```

**★ Where novelty can live — and it is exactly §7.2.** The project's condition is **path-local** (only
the cells actually selected on one descent need be orbits); Tinhofer quantifies over *all* `S`. The
searches found **no named notion for the path-local weakening**, and none for a *poly-decidable* side
condition implying orbit-correctness — recognizing Tinhofer/refinable is P-hard and at least as hard as
GI on vertex-transitive graphs (AKRV Thm 22; arXiv:2605.19702). AKRV's whole hierarchy is over **1-WL**;
a condition over k-WL or coherent-configuration-stable colourings is uncovered.

### 8.5 The frontier, stated in 1983

**Babai & Luks, "Canonical labeling of graphs", STOC 1983, §1**, verbatim:

> "**Does knowledge of Aut(X) lead to a canonical form?** In the canonical form problem the objective is
> to **select, wisely, from the various representations.** If, as is almost always the case, Aut(X) is
> trivial, the number of such representations is n!. **How do we select?**"

Supporting, all verified:

* **Canonization ≤ₚ GI is OPEN**, both forms (`CAN ∈ FP^GI`? `GI ∈ P ⟹ CAN ∈ P`?) — Schweitzer–Wiebking
  arXiv:1806.07466 §1; Grohe–Schweitzer–Wiebking SODA 2021 arXiv:2003.10935 abstract; Lichter–Schweitzer
  arXiv:2205.14003 §1. No separation proved either (Blass–Gurevich 1984 = relativized only;
  Fortnow–Grochow: `CF = Ker` would give NP = UP and probabilistic factoring).
* **Lex-least canonical form is NP-hard** — Babai–Luks Prop. 3.1, *"even if G is restricted to be an
  elementary abelian 2-group"*. The naive block ordering is dead by theorem.
* **★ The concrete lead: Babai–Luks Prop. 3.7** (credited to Galil) — a **canonical reordering of the
  domain** from a canonical structure tree `TREE(G,A)`, making lex-placement solvable in `|A|^{O(d)+c}`
  where `d = cw(G)` = **composition width** (`cw = 1` for solvable). A group-supplied canonical ordering
  of blocks, poly for bounded composition width — i.e. Luks's `Γ_d`, which is precisely the project's own
  W2/solvable-tower route (`GaugeSolvable`, `isSolvable_pi`). Independent arrival at the same boundary.
* Babai's own canonization answer (**STOC 2019**) was to canonify the local-certificate structure, not to
  add an invariant.
* Named culprit for isomorphism-without-canonization results: **coset intersection has no known
  canonization analogue** (Schweitzer–Wiebking §1, citing Codenotti 2011).

**Not Babai's Split-or-Johnson.** That is a "progress-or-Johnson-obstruction" dichotomy with
quasipolynomial multiplicative cost in *both* branches, canonical only relative to arbitrary choices. The
structural match is Babai's **fullness / affected–unaffected** dichotomy in Local Certificates: *full* ⟹
global automorphisms `K(T)` produced (= consume); *non-full* ⟹ explicit obstruction `M(T)`, aggregated
into a canonical relational structure (= force).

**Closest prior theorem to the split loop's architecture:** Arvind–Das–Mukhopadhyay, JCSS
76(7):509–523, 2010 — tournament canonization is poly-time reducible to **tournament isomorphism +
canonization of *rigid* tournaments**. An orbit oracle buys exactly the symmetric part and no more.

---

## 9. ⛔ PROVENANCE — superseded claims. Do not read as live.

Kept so nobody re-derives them. Each line: what was claimed → what is true → where.

1. **"A twist failure certifies that the pair is in a different orbit."** → **False**, two certified
   falsifiers. → §1.1, §2.1.
2. **"`¬CellIsOrbit ⟹ RigidObstructionAt` at this cell (no guard)."** → **Refuted**; the `Certified` /
   `Tinhofer` hypothesis on the located-obstruction theorems is necessary. → §1.2.
3. **"A single anchor suffices for the harvest."** → **Measured false** (the `G8` falsifier in
   `DeepenSupply.lean`): single-anchor branch-cell orbit profiles differ across relabellings
   (`[2,2,2,2,4,4,4,4]` vs `[1,1,2,2,2,2,2,2]`). `deepenGens` loops every anchor. Independently
   falsified per-pair at the Chang-B root. → §2.1.
4. **"The CFI cubic m=8 `(16, 2, 1)` stall is a measured FUSION witness."** → It is a
   **pick-misalignment** witness: the `|C|=16` cell is a single orbit *at that colouring*, with no rigid
   decision needed to expose it. Fusion = symmetry not yet exposed (Chang-A's `A_stall < A_full`). →
   §1.1, §2.3.
5. **"PARTITION = poly and provable; ORDER = the wall"** — i.e. ranking two orbits *is* separating them
   by a poly invariant, so knowing the orbit partition does not help force. → **False.**
   Certified-below ⟹ deepen's single-path cert *is* an invariant separating key, and it orders the
   blocks. Now the theorems `keyEquivariant_orbKey` + `orbKey_eq_iff_orbit`. → §3.3, §3.4, §6 S1.
6. **"All reps certify on the rigid multipedes, so the rigid decision is resolved by a poly key."** →
   **True but EMPTY.** Three of four rigid multipedes discretize after ONE individualization, so
   certified-below held with *zero levels to certify* — and by AKRV's rigid collapse it must be so. The
   CFI results (4–6 levels) stand. → §8.4.
7. **"The remaining open item is proving deepen's poly certificate relabelling-invariant."** →
   **Measured false**, not merely unproved. → §7.1.
8. **"Chang-A leaks — the cascade certifies only order 24 of `|Aut| = 384`."** → **Retracted**; measured
   **complete 384/384**, 17 nodes, 4 leaves, zero starvation. What survives is the **fusion** signature
   `A_stall < A_full`, which costs deferral, not completeness.
9. **Retracted elsewhere, repeated because it recurs:** any *"X ⟹ GI∈P, therefore X impossible"*
   argument is BANNED — a perfect key *is* GI∈P, i.e. the target. Violated once (the "cell orbit
   partition ≡ GI so the supply would be GI∈P" argument) and retracted.

### 9.1 Build sketch, as originally scoped (kept for comparison; the delivered arc differs)

The original plan was `certOf` (min-over-cell) → `keyEquivariant_deepKey` → `Force.forceBy`. What landed
instead is the *guarded greedy* key (§3.3), poly where its guard is open, with min-over-cell retained as
the unconditional fallback (§4.2). The retirement list from that sketch is unchanged and already
actioned: `deepenRefSupply`, `DeepenRefInExec`, R1/R2 are parked out of `build.sh`; `DeepenTinhofer`'s
`joint` survives as the *cost* lemma (`Tinhofer` ⟹ branch factor 1).

---

## 10. ▶▶ THE FRONTIER (2026-07-27, later) — `KeySeparates` and what it does and does not buy

`ChainDescent/KeyComplete.lean`, 7 theorems, all `[propext, Classical.choice, Quot.sound]`, in
`build.sh` after `DeepenGuard`.

### 10.1 ✅ The mixed firing theorem — `NodeResolved` at every `Tinhofer` node

**The gap this closes.** `consume_fail_force_fires` ends in `narrow.length < branches.length`, and
**nothing in the project consumes strict narrowing.** The predicate `②`/`③` read is
`Select.NodeResolved key S adj χ := ∃ c ∈ nonSingletonColours χ, (cellNarrow key S adj χ c).length ≤ 1`.
Strict narrowing does not imply it, so the landed chain terminated one step short of being load-bearing.

**It was one step, and every ingredient was already proved.** At an `Tinhofer` node:

| | |
|---|---|
| force's argmin is one true orbit | `forcedSet_single_orbit` (D2) — or generically, `forcedSet_single_orbit_of_keySeparatesAt` |
| deepen's `WordReach` on the branch cell **IS** the `IsColAut`-orbit relation, **both directions** | `Deepen.deepen_branch_orbit_iff_aut` — **landed 2026-07-23**, not new |
| `rep` constant on the forced set ⟹ dedup is a singleton | `rep_eq_of_wordReach` + `dedup_map_length_one` |

⟹ **`forceThenConsume_singleton_of_tinhofer`**: the composite narrows an `Tinhofer` node's branch cell
to **exactly one** branch ⟹ **`nodeResolved_of_tinhofer`** ⟹ **`handledS_of_reached_tinhofer`**, the
first population of `HandledS` (remaining-work §1T records zero families). **✅ SUPERSEDED 2026-08-04:**
`ChainDescent/TwinFamily.lean` supplies the socket (`handledS_of_noRigidObstruction`), the literature
bridge (`handledS_of_tinhoferGraph`, with `not_tinhoferGraph_of_flagS` as the showcase) and a named
family; §1T is discharged. ⛔ The "rigid-seal §9.1 is the same work" reading is **wrong** — that socket
is pure-consume, so a rigid obstruction *fails* its hypothesis rather than needing rigid work.

⚠ **This is NOT reachable through `Cost.CellResolved`,** and that is a trap worth recording. Its
disjunction is `CellIsOrbit S ∨ (key separates the whole cell)`. At a **mixed** node — cell has ≥ 2
orbits, key ties inside each — **neither** disjunct holds, yet the composite provably resolves. Given
the project's own line that *almost every real residue is mixed*, route to `NodeResolved` directly;
`nodeResolved_of_cellResolved` is a sufficient path, not the general one.

### 10.2 `KeySeparates` — the reduction, and its honest label

> **`KeySeparatesAt key adj χ`** — the key separates every branch pair no colour-automorphism links.
> Contrapositive: *equal keys inside the branch cell ⟹ same orbit*.

`forcedSet_single_orbit_of_keySeparatesAt` proves the argmin is then a single `IsColAut`-orbit — using
**no** property of the key beyond this: no equivariance, no guard, no supply. So keeping one
representative is licensed by an automorphism that **exists but was never computed** (the `CoveringAt`
route, whose witness is `descend_transport` at an automorphism). The consume-side guard stops being a
correctness prerequisite and becomes a *firing accelerator*.

Stated at the node level this says: **under `KeySeparatesAt`, `CellResolved`'s disjunction is
exhaustive** — if the key does not separate the cell, the survivors are semantically one orbit. Granted
globally it gives `ResolvedAll` ⟹ `Handled` ⟹ the flag never fires.

**⚠ Label it correctly: UNIFICATION, not weakening.** What the reduction buys is **one** carried
predicate about an object under construction instead of two coupled ones (`Tinhofer` on consume,
`SolverSeparates` on force). The precedent verdict is `hImprim`'s: *consolidation, not breakthrough.*

#### ⚠⚠ CORRECTION (same day, `keySeparatesAll_rawKey`) — `KeySeparates` alone is NOT the wall

An earlier draft of this block said *"a key with the property globally **is** the target."* **That is
wrong, and the correction sharpens the decomposition rather than weakening it.**

`DeepenExact.isColAut_of_readKey_eq` is **unconditional**: equal reads of two whole-graph-discrete
leaves force a colour-automorphism. So the **unguarded** read never ties a non-automorphic pair, and

> **`KeyComplete.keySeparatesAll_rawKey` — `KeySeparates` holds globally, for a poly (`n⁴`) key, with no
> hypothesis.**

`KeySeparates` on its own is therefore *cheap*. The GI-hard object is the **conjunction**

    KeySeparates key adj  ∧  Force.KeyEquivariant key

and the built keys sit on opposite sides of it:

| key | separates | equivariant | why |
|---|---|---|---|
| `rawKey` | ✅ **unconditionally** (`keySeparatesAll_rawKey`) | ❌ | `leafOf` breaks ties by vertex index |
| `orbKey` / `orbKeyG S` | only where the guard is open | ✅ (`keyEquivariant_orbKey{,G}`) | the guard is exactly the equivariance repair |

**⟹ The guard purchases EQUIVARIANCE, not separation.** That re-reads every "guard strength"
measurement in §7.2/§7.3: the shut-guard nodes are not places where the read fails to see the
difference — the read sees it fine — they are places where the read is not yet known to be
labelling-independent. Coverage work should target the *equivariance* side.

**And it retires §10.4's falsifier hunt as posed.** For a guarded key the falsifier is trivial and
uninformative (any two non-automorphic branches whose guards are both shut tie at the constant `[]`);
for the raw read it provably does not exist. Nothing needs measuring here.

### 10.3 ⛔ The obituaries — this is a REPAIRED dead route, and there are TWO of them

The idea "if nothing resolves, treat the residue as vertex-transitive and consume unverified" was tried
and died. Both obituaries must be read before re-scoping, because **only one of them transfers.**

**A — fusion / Chang-A (2026-07-12).** `chain-descent-cost-model.md` §7a, `endgame-spec` §1a,
`00-START-HERE.md` §2b. Algorithm A flagged on `base > baseMax` and assume-VT-pruned *without verifying
an automorphism*. Verbatim: *"a conditional symmetry fused with a rigid decision (Chang-A) is not
vertex-transitive, so assume-VT-pruning it is unsound, and the guard needed a fusion-mildness theorem
that does not exist."*
▶ **REPAIRED, structurally.** Algorithm A had **no force resolver**, so "unresolved" conflated *VT*
with *fused*. Chang-A's rigid decision is exposed once the symmetry is consumed (`A_stall < A_full`)
and force acts on it — so `KeySeparatesAt` is **false** at that node and the licence never fires there.
The missing fusion-mildness theorem is not needed; the interleaving supplies its content operationally.

**B — vacuity (2026-07-10).** The confinement audit: `ConfinementCitations.hflag` unfolds to *"every
residue of every graph has `|Aut| > n^{log₂ n}`"* and is **machine-checked uninhabited**
(`ConfinementCitations 2 → False`), so all four `descentCanon_showcase*` were vacuously true.
▶ **DOES NOT TRANSFER.** That was a failure of the *citation-bundle shape* — a universally-quantified
`hflag` over all graphs and residues. `KeySeparatesAt` is per-node with measured inhabitants (§3 of the
module: `orbKey` at every `Tinhofer` node, `orbKeyG S` at every `CertifiedG S` node).

### 10.4 ⚠ The surviving objection — the 2026-07-10 audit's FORK

The audit recorded a table that is exactly on point, and its verdict was *"they coincide exactly when
`hSmallAutThin`"*:

| budget keyed on | `flag ⟹ VT` (needed for the prune) | `¬flag ⟹ certified` (needed so deferral never defers a true symmetry) |
|---|---|---|
| greedy **group** base | ✅ definitional | ❌ |
| harvest's **discretizing** depth | ❌ rigid multipede: trivial `Aut`, deep base ⟹ would flag ⟹ prune unsound | ✅ |

`KeySeparatesAt` sits in the same table with *"force did not separate"* in place of *"¬flag"*, and is
informative **only when the key's failure to separate means "no separation exists" and not "the key
deferred."** Concretely: `orbKey` off its guard returns the constant `[]`, so it satisfies the
*negation* vacuously. This is why `KeyComplete` §3's instantiations carry the guard as an explicit
hypothesis and the file does **not** claim any built key satisfies the global `KeySeparates`.

**⚠ RESOLVED by `keySeparatesAll_rawKey` (§10.2's correction) — do not run this hunt.** The FORK's warning
is real but it bites the *guard*, not the read: the read provably never ties a non-automorphic pair, so
a "falsifier" can only be a node where the guard is shut at both branches, which is a restatement of
the guard's coverage and not new information. The paragraph below is retained because its analysis of
the **VT exception** is unaffected and still governs any *structural* VT test.

Two readings of the "VT exception", both landing on the wall:
1. **VT = "the branch cell is a single `Aut(G,χ)`-orbit."** The exception is *vacuous* (no
   non-automorphic pairs there), so the hypothesis is a perfect key = the target.
2. **VT = a structural test** (cell/residue transitive as a scheme). The exception is non-vacuous, and
   the licence "structurally VT ⟹ single orbit" **is Schurian-ness** — D0 / `SchurianScheme`
   faithfulness (remaining-work T4). So `¬force` does not remove the Schurian assumption the earlier
   attempt carried; it relocates it into *which cells the key is excused on*. A 2-orbit cell the
   structural test calls VT is precisely the hole.

**▶ ⚠ The falsifier hunt this section proposed is RETIRED** — see the note above and §10.2's
correction. It was misconceived: the read provably never ties a non-automorphic pair
(`isColAut_of_readKey_eq` is unconditional), so for `rawKey` no falsifier exists, and for a guarded key
one exists trivially wherever both guards are shut. Neither outcome is information.

---

### 10.5 ✅ LANDED — the executable guard, the honest bill, the `Reaches` bridge (gate 878 s, 105 mods)

All axiom-clean. Ledger items 2, 3, 5, 6 and 8 of §7.3 are discharged.

| | statement | name |
|---|---|---|
| **decidable** | `WordReach` is decided by the orbit BFS — `mem_orbit_iff_wordReach` was already proved, so it is one `decidable_of_iff`; hence `CellIsOrbit` (`List.decidableBAll`) and `CertPath` (structural recursion) | `Consume.decidableWordReach`, `Consume.decidableCellIsOrbit`, `Deepen.instDecidableCertPath` (+ `certPath_none/_nil/_cons` equation lemmas) |
| **executable** | **`orbKeyG` is a plain `def`** — the `Classical.dec` placeholder is gone, the key evaluates | `Deepen.orbKeyG` |
| **billed** | the guard's own work, along its own recursion: per level one reachability test **plus one call to `S`**, at the colouring that level visits; bound parametric in the supply's `c₂` | `Deepen.certPathCost`, `certPathCost_le`, **`keyCost_orbKeyG_le`** (`≤ n⁴ + n·(n⁴+c₂)`) |
| **bridge** | `DescentReach ⟹ Descend.Reaches` (same side condition, `step = refineV encodeFreeFast ∘ indivOne`) | `KeyComplete.reaches_of_descentReach` |
| **the hook, repaired** | `consume_fail_force_fires` with **both** weaknesses removed — the located node is one the canonizer *visits*, and the conclusion is `NodeResolved` (`≤ 1`), not strict narrowing | **`KeyComplete.consume_fail_locates_resolved`** |
| **separation is cheap** | `KeySeparates` holds globally for the unguarded read at `n⁴` | **`KeyComplete.keySeparatesAll_rawKey`** (§10.2's correction) |

**⚠ Why `②` at this key was previously unfalsifiable, and is not now.** The key shipped a flat `n⁴`,
which prices the *read* (`leafOf`: `≤ n` warm refinements) and **nothing** of the guard — the 2026-07-14
"`Key`/`Supply` were cost-free" finding recurring. `keyCost_orbKeyG_le` is parametric in the supply's
own bound, so a supply with an exponential `supplyCost` now yields an exponential `keyCost` instead of
disappearing behind a constant.

#### ⚠⚠ MEASURED, and it changes §7.3 item 4's recommendation (`Regression` §17)

The key is now `#guard`-able, so the firing evidence is no longer Python-only. Two findings:

* **A `CertPath = true` guard can be VACUOUS, and the first witness tried was.** By AKRV's rigid
  collapse (§8.4) a guard holds trivially when one individualization already discretizes —
  `chooseIdK` returns `none`, there are **zero levels to certify**. Measured on `G8`: the guard opens
  on all 8 branches but `certPathCost = 0` on **4 of them** and `135168` on the other 4. **So the
  discriminator is `certPathCost > 0`, not `CertPath`** — the `mp7`-fires-totally lesson in its cost
  form, now mechanically checkable. Every OPEN guard in `Regression` §17 pins it substantive.
* **`deck2Supply` is NOT a superset of `deckSupply` at this guard.** `C5` certifies under `deckSupply`
  at every branch (cost 13125 each) and **fails** under `deck2Supply` at branch 0. ⟹ §7.3 item 4's
  "take `S` deeper" is the wrong lever; the **union** of the equivariant supplies is the right one, and
  this is measured rather than argued. (`SameOrbits`-licensing remains the other candidate.)

---

### 10.6 ✅ LANDED — guard strength: the union, and why it is more than a maximum (`DeepenGuard` §8)

**Monotonicity, proved.** More verified generators only make `WordReach` easier, hence `CellIsOrbit`,
hence `CertPath`: `wordReach_mono` → `cellIsOrbit_append_{left,right}` →
**`certPath_append_{left,right}`** → `certifiedG_append_{left,right}`. So a bigger guard admits more
nodes **without weakening what admission means** — `CertPath S ⟹ TinhoferPath` holds for every `S`, so
`①` and soundness are untouched.

**`guardSupply`** = `foldSupplyFast ++ deckSupply ++ deck2Supply ++ matchSupply`, with
`gensEquivariant_guardSupply` / `supplyEquivariant_guardSupply` from the existing `appendSupply`
closure, hence **`keyEquivariant_orbKeyG_guard`** and **`force_canonizer_orbKeyG_guard`** (`①a`/`①b`/
`①c` + totality, no hypothesis). `certifiedG_guard_of_{foldFast,deck,deck2,match}` give firing
dominance over each member. ⚠ `kernelSupply` is deliberately excluded: it is provably **not**
`GensEquivariant` (pivot-order-dependent basis, trap #7), so it cannot sit in a guard whose whole job
is to keep the `if` relabelling-stable. It remains available to *fire*, which needs no invariance.

#### ★★ MEASURED — the union is STRICTLY stronger, and the gain is EMERGENT (`Regression` §17a)

> `CertPath` is a **conjunction over the levels of one greedy path**, and different supplies certify
> different levels. So the union can certify a path **no single member certifies.**

| witness | foldFast | deck | deck2 | match | **union** |
|---|---|---|---|---|---|
| `C5` (5 branches) | — | OPEN 5/5 | **shut 0/5** | — | **OPEN 5/5** |
| **`t3` (3 branches)** | **shut** | **shut** | **shut** | **shut** | **✅ OPEN 3/3** |

`t3` is the headline: **all four equivariant supplies are shut on every branch and the union is open on
every branch** — 0/3 → 3/3 on a witness where every individual supply fails. This is not a maximum over
the members, and no theorem states it (`certPath_append_*` gives monotonicity, not strictness), which is
exactly why it is a `#guard`.

⚠ **The price is real and now visible** — which is what the billed `certPathCost` was for. On `t3` the
union bills `1385216550` against `deckSupply`'s `6176250`, a ~**224×** multiple, because the union's
`supplyCost` is the **sum** of its members'. Under the old flat `n⁴` this trade would have been
invisible. Firing bought at an honest price.

**▶ Remaining on guard strength:** `SameOrbits`-licensing (guard by a non-equivariant `S` with
`SameOrbits S Ref` for an equivariant `Ref` — the `kernelSupply` pattern) is the other candidate and is
**⚠ its generic half landed 2026-07-28 (§10.7) and its INSTANCE IS R1** — the parked crux, so it is not
the independent lever this paragraph implies. It is the only route that could admit `deepenSupply` itself, which
`deepen_branch_orbit_iff_aut` shows is *exactly* complete at `Tinhofer` nodes. ⚠ But note §10.2's
correction: the guard buys **equivariance**, so coverage work should target that side.
**▶▶ Generic half landed 2026-07-28 — and it is NOT an independent lever. See §10.7.**

---

### 10.7 ✅ LANDED — `SameOrbits`-licensing, generic half (`DeepenGuard` §9); ⚠ the instance is R1

Five theorems, all `[propext, Classical.choice, Quot.sound]`:
`cellIsOrbit_congr` → **`certPath_congr`** → `certifiedG_congr` → `keyV_orbKeyG_congr` →
**`keyEquivariant_orbKeyG_of_sameOrbits`**.

The content is that `CertPath` reads its supply **only through the orbit relation**: `CellIsOrbit` is
`WordReach` on `verified`, which is exactly what `SameOrbits` equates, and the path's *shape*
(`chooseIdK`, the cell filter, `step`) never mentions `S`. So `orbKeyG S` inherits `①` from any
equivariant reference `Ref` with `SameOrbits S Ref` — the `kernelSupply` pattern, now available at the
**key** as well as at the resolver. Note only the *value* transfers; `certPathCost` still calls `S`
itself, which is correct — cost carries no `①` obligation.

**⚠⚠ THE CORRECTION THIS SECTION EXISTS FOR.** §7.3 item 4 and §10.6 both call this lever "untried",
which reads as *independent*. It is not. The only supply worth admitting through it is `deepenSupply`,
and **`SameOrbits deepenSupply Ref` for an equivariant `Ref` IS R1** — the crux the whole reference
apparatus was built for and then abandoned (`DeepenRef` / `DeepenRefTransport` / `DeepenR1`, parked out
of `build.sh`; remaining-work's superseded-frontier block records "R1 is THE crux" and that the
all-picks reference is exponential). So the lever inherits R1's open half wholesale. What landed is the
reusable plumbing; what is open is unchanged.

---

### 10.8 ✅ LANDED — `forceThenPick`: the exhaustiveness corollary, CASHED (`ChainDescent/ForcePick.lean`)

Ten theorems, all `[propext, Classical.choice, Quot.sound]`, in `build.sh` after `KeyComplete`.

**The gap it closes.** §10.2 says that under `KeySeparatesAt` *"keeping one representative of the
forced set is licensed by an automorphism that exists but was never computed."* Nothing exercised that
licence — every built resolver still reaches its singleton through consume, i.e. through a **computed**
certificate. `forceThenPick key` is force followed by `take 1`: no supply, no verification, no orbit
BFS. Its `①` rides `Descend.CoveringOfAt` at `N = forcedSet` with the covering automorphism supplied by
`forcedSet_single_orbit_of_keySeparatesAt` instead of by a `verified` list — precisely the third
contract route's intended shape, which no instance had used.

| | statement | hypothesis |
|---|---|---|
| `①a` | `Descend.isCanonicalFormOpt_canonForm?` | — |
| `①b`/`①c` | **`narrowTransport_forceThenPick`** | **`KeyEquivariant` + `KeySeparates`** |
| **the flag never fires** | `narrowProper_forceThenPick` | **none** |
| `②` single path | `resolvedAll_forceThenPick` (`take 1`, structural) | **none** |
| `②` explicit poly | `descentCost_forceThenPick_le` | a `keyCost` bound |
| all three at once | **`forcePick_record`** | the conjunction below |

⟹ the project's target, stated once as a theorem's hypothesis list:

> **an equivariant, separating, poly force key is a complete polynomial canonizer.**

**▶▶ That hypothesis set is SCOPED in its own doc: `scratchpad/KEY_scoping.md` (2026-07-28).** Its four
results, so they are not re-derived here: (i) the obligation restates *exactly* as **"produce a discrete
`ψ` in poly time, canonical up to `Aut(adj, indivOne χ v)`"** — because
`isColAut_of_readKey_eq`'s only hypotheses are `Discrete` + values `< n`, so separation is free for *any*
discretizing map and the whole difficulty is labelling-independence of the *read* (never of `ψ` — that is
`OrdEquivariant`-impossible off rigid inputs); (ii) the **rich / invariant / poly triangle** — every built
and refuted key occupies a corner, and the third clause always fails for a recorded reason; (iii) **the
tie-group ladder**: the exponential in the rich+invariant corner is always "enumerate the group `T` the
read cannot see inside", so a poly key exists exactly where `T` has a poly canonical form — trivial /
Aut-equivalent-picks (`Tinhofer`) / `F₂` (RREF, done) / `Z_{2^k}` (P3-ring) / solvable (L4) / bounded-local
`Γ` (Luks, citable) / **non-solvable = the wall**. ⟹ **the live tracks are RUNGS OF ONE LADDER, not
independent attempts**, and Track R's `②` is the top of the `F₂` rung; (iv) two defects — see below.

**⚠⚠ TWO DEFECTS THE SCOPING FOUND IN THIS ARC (KEY_scoping §0).**
1. **`KeySeparates` exists TWICE.** `Hol.KeySeparates` (`HolKey.lean` §1, F3a, **earlier**) is the same
   predicate per-node in contrapositive form, and `Hol.keepMin_pairwise_aut_of_separates` **duplicates**
   `KeyComplete.forcedSet_single_orbit_of_keySeparatesAt` (`Composite.forcedSet` *is*
   `keepMin … (branches χ)`). Neither file references the other, and the two `KeySeparates` differ only
   in arity. What is *not* duplicated: F3a routes its conclusion back through consume, so
   `forceThenPick` is still the new content. ▶ Add a bridge lemma + rename one.
2. **`forcePick_record`'s hypothesis set is claimed for no key** — the `ConfinementCitations.hflag`
   vacuity shape. ▶ Pay it with the `readMin` anchor (KEY_scoping §4): index the aggregate by
   `Perm (Fin n)` instead of by descent leaves, so the index set mentions neither `adj` nor `χ`;
   equivariance is reindexing by `π ↦ π * σ` (`readKey_transport` + `indivOne_transport`) and separation
   is **unconditional** via `isColAut_of_readKey_eq`. Strictly better as an anchor than
   `keyEquivariant_compKey_readAgg_univ`, whose separation is the carried `AggFaithful`.

**⚠ What this is NOT.** It fires nowhere new today: at a `Tinhofer` node the composite already resolves,
and off its guard `orbKey`/`orbKeyG` return the constant `[]`, which does not separate — so no *built*
key has both conjuncts and every instantiation is the same kind of conditional scaffold as
`deepenSupply_guarded_canonizer_direct`. The gain is that **two** coupled carried predicates
(`Tinhofer` on consume, `SolverSeparates` on force) become **one**. And §10.4's FORK objection applies
with extra force here: a guarded key satisfies the *negation* of `KeySeparatesAt` vacuously off its
guard, and plugged into this resolver that is not merely uninformative but would discard genuinely
different branches — so the hypothesis is carried explicitly and never claimed for a built key. The
module header says this in the same words; do not instantiate at `orbKeyG` and read the result as a
canonizer.

---

### 10.9 ✅ LANDED — the two `KEY_scoping` §0 defects PAID, and the record's `②`

Three pieces, all `[propext, Classical.choice, Quot.sound]`, gate EXIT 0.

**(a) The `KeySeparates` duplication is now visible, not silent (KEY_scoping §0.1).**
`Hol.KeySeparates` (F3a, `HolKey.lean` §1, **earlier**) is this arc's `KeySeparatesAt` in positive
form. Fixed three ways rather than one: the global predicate is renamed
**`KeyComplete.KeySeparates` → `KeySeparatesAll`** (so the identifier `KeySeparates` belongs to F3a
alone, and `keySeparates_rawKey` → `keySeparatesAll_rawKey`); **`keySeparatesAt_iff_hol`** is the
bridge; and both files now carry a `⚠` cross-reference naming the duplication —
`forcedSet_single_orbit_of_keySeparatesAt` **does** re-prove `Hol.keepMin_pairwise_aut_of_separates`,
since `Composite.forcedSet key adj χ` *is* `keepMin key adj χ (branches χ)`. What is **not**
duplicated, and is why the later work still has content: F3a routes its pairwise-`Aut` conclusion back
through **consume**, so `ForcePick.forceThenPick` — discarding on the *uncomputed* automorphism — had
no predecessor.

**(b) `forcePick_record`'s vacuity debt is PAID by `readMin` (KEY_scoping §4).** `ForcePick` §8:
`colOf π` (the discrete colouring of a permutation) → `readSet` (the aggregate indexed by
`Perm (Fin n)`, so the index type mentions **neither `adj` nor `χ`**) → **`readSet_transport`** (the
whole index set is invariant, by the bijection `π ↦ π * σ`) → **`keyEquivariant_readMin`** →
**`keySeparatesAll_readMin`** (unconditional, straight from `isColAut_of_readKey_eq` — whose only
hypotheses, discrete and `< n`, hold for `colOf` by construction) → **`forcePick_readMin`**.

> ⚠ **This is brute force restated, NOT progress on the wall** — `Refine.exhaustive_canonizer` already
> gives an unconditional exponential canonizer. Its value is exactly two things: the hypothesis set of
> `forcePick_record` is now **provably inhabited** (the `ConfinementCitations.hflag` shape does not
> recur here), and the residual difficulty is pinned to the **poly clause alone**, stated as
> **`forcePick_open_clause_is_poly`**.

⚠ Note it is a *better* anchor than the rigid track's exponential object:
`keyEquivariant_compKey_readAgg_univ` gets equivariance at `framesUniv` but its separation is the
**carried** `AggFaithful`; `readMin`'s is unconditional.

**(c) Ledger item 9 / queue 3f — `ChainDescent/RecordCost.lean` (16 thms).** The record object now has
a `②`. `supplyCost_appendSupply` is definitional; the four supplies' closed forms bound out to
`recordSupplyBound`/`recordGensBound`; **`descentCostS_selNode_record_le`** is an explicit polynomial
on every input with **no hypotheses**, and `record_canonizer_with_cost` states `①` and `②` together.
The two facts that were missing rather than hard: `nullBasis` emits one word per **free column**, so
`|kernelGens| ≤ |rails| ≤ n`; and `secondsV` is a `flatMap` of filters of `finRange n`, so
`|deck2Batch| ≤ n²`. ▶ Remaining: reshape into `Publication`'s `costConst * n ^ costDeg` monomial —
statement-side work, sequence it with item 7.

---

### 10.10 ✅ LANDED — item 7 / queue 3g: the lex-product key, and the record's composed force key

`ChainDescent/RecordKey.lean`, 16 theorems, all `[propext, Classical.choice, Quot.sound]`.

**⚠ The combinator's shape is NOT what item 7 predicted, and the correction matters.** This ledger and
`remaining-work` both proposed the length-prefixed encoding `(len a :: a) ++ (len b :: b)` "so that
concatenation is a genuine lex product". **That is wrong.** Prefixing the length orders the first
component by **shortlex**, and `Descend.lexLeList` is *not* shortlex — it compares elementwise and only
falls back on length when one list runs out, so `lexLeList [5] [1,1] = false` while shortlex ranks `[5]`
first. Prefixing therefore silently **re-orders `holKeyFast`'s own narrowing**, which is the one thing
an integration step must not do.

**What is correct: plain concatenation, plus a named side condition.**

> **`ConstLen k₁`** — `k₁`'s value has the same length at every vertex of a node.

Under it, any difference between two branches is decided *inside* the first component and ties fall
through to the second: concatenation is exactly the lex product. Every built key satisfies it
(`constLen_holKeyFast`: `holSigFast` is a `map` over `List.range (n + 1)`), so carrying the condition
costs nothing and keeps the order honest.

| | |
|---|---|
| `①`, **unconditional** | `keyEquivariant_pairKey` — componentwise |
| cost | `keyCost_pairKey_le` — costs add |
| the product determines both components | `keyV_pairKey_inj` (from `ConstLen` + `List.append_inj`) |
| **firing gain** | `keySeparatesAt_pairKey_left` / `_right` — the product separates whatever **either** component does |
| **no strength loss** | **`keepMin_pairKey_subset`** — the tiebreak never *widens* the narrowing (engine: `lexLeList_append_left`) |

**The record's key.** `recordKey := pairKey holKeyFast (orbKeyG guardSupply)`.
**`recordKey_canonizer`** is `①` at the record supply — and it really is *one* `KeyEquivariant` proof,
because `Select.selNode_canonizer_of_sameOrbits` is key-generic (this ledger's item-7 correction (a),
confirmed in the doing). **`descentCostS_selNode_recordKey_le`** is `②`, explicit polynomial, no
hypotheses; it needed one new bound, **`supplyCost_guardSupply_le`**, since `orbKeyG`'s bill is
parametric in its guard supply's — three of `guardSupply`'s four members were bounded in `RecordCost`
and the fourth (`matchSupply`) in `SupplyCost`.

#### ★★ MEASURED — the swap is not a no-op (`Regression` §18, ~5 s)

`keepMin_pairKey_subset` says the product never widens; **nothing proves it ever shrinks**, so that
half is a measurement, exactly as with the union guard.

| witness | cell | `holKeyFast` | **`recordKey`** | reading |
|---|---|---|---|---|
| **`G8`** | 8 | **8** (constant holonomy signature) | **2** | the composed key resolves a cell the record's key leaves untouched |
| `t3` | 3 | 3 | 3 | single orbit — firing is *forbidden* (`forceBy_no_narrowing_on_orbit`) |
| `wcyc9` | 3 | 3 | 3 | same |

The two negative rows are pinned as **controls**: an equivariant key that ever fired inside an orbit
would be a soundness regression, so "no improvement" is the correct result there and a future change
that "improves" it must fail the gate.

**▶ Remaining on item 7: NOTHING — see §10.11.**

---

### 10.11 ✅ LANDED — the `Publication` swap, and `②` discharged (2026-07-28, closes the arc)

`RecordKey` §5 (6 declarations, axiom-clean) + `Publication.lean`. **`Publication` goes from 3 `sorry`s
to 2**, and `#print axioms canon_poly_or_flag` = `[propext, Classical.choice, Quot.sound]`.

| | |
|---|---|
| the object | `canonForm? = Select.canonFormFastS? RecordKey.recordKey RecordCost.recordSupplyFast`; `canonForm?_record` = `recordKey_canonizer` (still zero glue — `canonFormFastS?_eq` is `rfl`) |
| `cost` | no longer `opaque`: `Select.descentCostS` at that object = the `CostM` cost projection of the definition `①` rides on |
| the numerals | `costConst = 57` (53 before `stepCost` was billed, 2026-08-06), `costDeg = 13`, **computed not guessed** — `recordKeyBound_expand` has `ring` check the degree and the coefficient sum |
| `②` | `canon_poly_or_flag`, proved on the **left** disjunct (no flag escape: fan-out `≤ 1` is structural and every component is billed) |

#### ⚠⚠ THE PINNED MONOMIAL WAS WRONG — `n ^ costDeg` → `(n + 1) ^ costDeg`. Do not restore it.

`cost n G ≤ costConst * n ^ costDeg ∨ canonForm? n G = none` is **not provable for this object at any
numerals**, and the flag disjunct does not rescue it:

* `Select.descendS` bills **1** for a leaf, and at `n = 0` every colouring is vacuously `Discrete` — so
  the record object costs **1** and *answers* (`isSome`, measured). But `costConst * 0 ^ costDeg = 0`
  for every `costDeg ≥ 1`.
* `costDeg = 0` degenerates the claim to a constant bound, false at `n = 2` (cost `1162`, measured).

`(n + 1)` is the same polynomial class (`(n+1)^13 ≤ 2^13·n^13` for `n ≥ 1`) and it is *also* what makes
the proof uniform: `pow_le_succ_pow` bounds every `n^k`, `k ≤ 13`, by monotonicity alone, so there is no
`1 ≤ n` case split anywhere. This is a **statement-shape** defect that survived every previous audit
because nothing had ever tried to prove the statement.

#### ★★ MEASURED — the swap is a TOTALITY gain, not only a firing gain

§10.10's table is at the root cell; this is end-to-end on the record supply:

| witness | `holKeyFast` | **`recordKey`** |
|---|---|---|
| **`G8`** (n = 8, regular, not vertex-transitive) | **FLAGS**, 8.7 s | **ANSWERS**, 21.4 s |
| `wcyc9` (n = 9) | answers, 0.34 s | answers, 0.93 s |
| `t3` (n = 15) | answers, 12.0 s | answers, **412.5 s** |

The first row is the point: it is the first **handled/unhandled pair at the record resolvers** —
exactly the witnesses `Publication`'s STATUS block says are still the target for non-vacuity, and the
`constKey`/`emptySupply` witness in `Residue.residue_nonvacuous` does not transfer to this object.

⚠ **The price is real and is interpreted wall-clock, not the cost model:** `t3` is 34×. Consequences:
(a) do **not** put an end-to-end `recordKey` guard on `t3`/`mp7` on the gate; (b) `PerformanceTest`
§11/§12/§14's acceptance numbers were taken at the *previous* key and no longer describe `canonForm?`.

**▶ Worth scoping, not done:** the product bills `orbKeyG`'s union guard on **every** vertex of every
cell. Sequential narrowing (`keepMin k₂` over `keepMin k₁`'s survivors) has the same value under
`ConstLen`, pays the second key only on the argmin (`G8`: 2 vertices, not 8), and removes the `n²·kc`
term that alone drives `costDeg` from 10 to 13. It is a **resolver**-level variant — a `Force.Key` is
per-vertex and cannot express the laziness.

⚠ **One more thing a reader should know about the product, found while auditing it:** `orbKeyG`'s guard
is **per-vertex** (`CertPath S adj n (step adj χ v)`), and `[]` is `lexLeList`-minimal. So at a node
where the guard is open on some branches and shut on others, the **shut** ones sort first — the
tiebreak keeps precisely the branches the orbit key knows nothing about. This is *sound* (`①` rides
`KeyEquivariant` alone) and `keepMin_pairKey_subset` still holds; and `keySeparatesAt_pairKey_right`
correctly demands `CertifiedG` = open on **all** branches. But the firing intent is inverted there, and
a sentinel that sorts the shut case last would flip it — measure before adopting.
