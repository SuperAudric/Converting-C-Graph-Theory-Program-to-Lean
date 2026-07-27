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
> Three modules, gate green (`bash /workspace/scripts/build.sh`, 223 s, 103 modules), every theorem
> `[propext, Classical.choice, Quot.sound]`, no `sorry`, no new `axiom`:
> `DeepenLocated` (10 thms) → `DeepenKey` (18) → `DeepenExact` (19).
>
> **`①` never depended on any of it.** `keyEquivariant_orbKey` carries no hypothesis, so
> `Force.force_canonizer` / `Composite.composite_canonizer` are applicable as they stand.
>
> **▶▶ THE FRONTIER IS §7 — A POLY, RELABELLING-INVARIANT GUARD.** `orbKey`'s guard is `Amenable`,
> which is decidable but by an `n!` search, so `orbKey` is `noncomputable`. **§7.1 measures that the
> obvious repair is impossible**: deepen's own poly certificate (`Certified`) is *not*
> relabelling-invariant — falsifier included. §7.2 gives the alternate design that is left.
>
> Reading order: §1 (the object) → §2 (what is measured) → §3 (what is proved) → §7 (frontier).
> §8 is the literature placement; **§9 is PROVENANCE — superseded claims, do not read as live.**
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

Bounded descent sweeps (depth ≤ 2, all reps), `Amenable` vs. harvest exactness at every node:

| family | nodes | `Amenable` | harvest EXACT | exact but `¬Amenable` |
|---|---|---|---|---|
| Chang-A / Chang-B / Chang-C | 365 / 173 / 46 | 364 / 148 / 46 | **365 / 173 / 46** | 1 / 25 / 0 |
| T(8)=J(8,2) · mp7 · MIXED · circ(5) · CFI-C₅ · Shrikhande⊎Rook(4,4) | 365·365·13·11·61·225 | all 100 % | **all 100 %** | 0 |
| C3+C4+C5 (cells provably ≠ orbits) | 37 | 24 | **37** | 13 |
| **total** | **1361** | **1197 (87.9 %)** | **1361 (100 %)** | **164** |

* The all-anchor harvest was **exact at every one of 1361 nodes**, including all 164 `¬Amenable` ones.
* `Amenable` is **sufficient but far from necessary** — the guard defers on ~12 % of nodes where the
  supply would have been exact. **The firing bottleneck is the GUARD, not the harvest.**
* ⚠ But harvest-transitivity certifies only the `|P| = 1` case. Where the cell has ≥ 2 true orbits the
  guard must certify the **partition**, and that is exactly where the CFI m=8 node lies.
* The anchor-count claim reproduces exactly — CFI cubic m=14, `|C|=56`: **3 anchors → 36 blocks, ALL
  anchors → 14 = TRUE**. And m=8's `(16, harvest 2, true 1)` stall **persists over every anchor**.

### 2.5 `orbKey` fires and is exact at hook nodes — 147/147

Faithful ports of the Lean `indivOne` (`2·χx + [x=v]`), `step`, `leafOf`, `readKey`. At every **hook
node** (`Amenable` ∧ branch cell with ≥ 2 orbits — the conclusion of `not_amenable_deepest`):

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

Gate green (223 s, 103 modules); every theorem below is `[propext, Classical.choice, Quot.sound]`.

### 3.1 `DeepenCertified.lean` — `Amenable` as a run-time certificate

| | statement | name |
|---|---|---|
| T1 | `CertifiedOrbit ⟹ CellSingleOrbit` — a *checked* transitivity of harvested twists **is** single-orbit-ness | `cellSingleOrbit_of_certifiedOrbit` |
| T2 | `CertifiedPath ⟹ AmenablePath`, `Certified ⟹ Amenable` | `amenablePath_of_certifiedPath`, `amenable_of_certified` |
| T3 | selector identity `chooseIdK (finRange n) = Descend.targetColour` — deepen's per-level cell **is** the canonizer's branch cell | `chooseIdK_eq_targetColour` |
| T4 | per-level bridge: `Consume.CellIsOrbit` discharges the level's certificate | `certifiedOrbit_of_cellIsOrbit_chooseIdK` |
| T5 | at a certified node, consume failing names a non-automorphic pair **in this branch cell** | `consume_fail_gives_real_decision`, `rigidObstructionAt_branch_of_certified` |
| T6 | **`Amenable` transports** — the index-pick obstruction absorbed as in `joint` | `amenablePath_transport`, `amenable_transport{,_iff}` |
| T7 | guarded supply ⟹ **`①c` with no hypothesis at all** | `deepenSupplyGuarded_canonizer` |

T5's `Certified` hypothesis is **necessary, not an artefact** — §2.1's second falsifier refutes the
unguarded statement.

### 3.2 `DeepenLocated.lean` — locating the obstruction (10 theorems)

| | statement | name |
|---|---|---|
| C1 | `DescentReach` — reachable by *proper* steps (individualize a vertex **with a same-colour partner**, then refine), + `trans` | `DescentReach`, `.trans` |
| C1a | a proper step strictly raises `ncol`; reachability never lowers it | `ncol_lt_step_of_partner`, `ncol_le_of_descentReach` |
| C1b | a `chooseIdK` level's pick has a partner | `partner_of_chooseIdK` |
| **C2** | `¬AmenablePath ⟹ ∃ ψ` **reachable**, obstruction at `ψ`'s **branch cell** | **`not_amenablePath_located`** |
| **C3** | `¬Amenable adj χ ⟹ ∃ ψ` reachable with **`Amenable adj ψ`** ∧ obstruction at `ψ`'s branch cell | **`not_amenable_deepest`** |
| — | the `Amenable` (not `Certified`) form of §3.1's T5 | `consume_fail_real_decision_of_amenable`, `rigidObstructionAt_branch_of_amenable` |
| — | every consume failure is located, one disjunct or the other | `consume_fail_locates` |

C3's point: one node carries **both** hypotheses — consume is exact below it (what an orbit-separating
equivariant key needs) *and* force has a genuine rigid decision at its branch cell. Termination is the
`Descend.ncol` measure, the same one `deepen_succeeds` uses; the base case needs no discreteness lemma
because `¬Amenable` itself produces a branch vertex, hence a partner, hence `ncol χ < n`.

**Non-vacuity checked** — nodes that are `Amenable` **and** whose branch cell has ≥ 2 orbits, i.e.
inhabitants of C3's conclusion:

| C3+C4 | C4+C5 | C3+C4+C5 | Shrikhande⊎Rook | Chang-A | Chang-B | MIXED | total |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 24 | 1 | 24 | 48 | 1 | **100** |

The conjunction also cannot degenerate: the obstruction requires `targetColour ψ = some cid`, so `ψ` is
**not** discrete and `Amenable ψ` is a real constraint, not the vacuous `branches = []` case. And the C3
iteration was validated directly on a measured `¬Amenable` node (Chang-B root): two steps, `ncol`
2 → 3 → 10, terminating on `Amenable = True` with a 2-orbit branch cell.

### 3.3 `DeepenKey.lean` — `orbKey`, the equivariant force key (18 theorems)

```
orbKey adj χ v := if AmenablePath adj χ n (step adj χ v)
                  then readKey adj (indivOne χ v) (leafOf adj n (step adj χ v)).col
                  else []                                        -- defer
```

| | statement | name |
|---|---|---|
| — | `Refines` + `trans`; `refines_step`, `refines_indivOne`, `refines_transport` | §1 of the file |
| — | **a colour-automorphism of a FINE colouring fixes every COARSER one** | `transport_eq_of_isColAut_refines` |
| — | `leafOf` + three equation lemmas | §2 of the file |
| **A2** | `AmenablePath` ⟹ the two **leaves** are related by an accumulated isomorphism `ρ`, and `ρ` acts on any refined-from colouring exactly as `σ` does | **`leafOf_transport_of_amenablePath`** |
| A1 | the invariant read + its transport | `readAt/readColAt/readAtIdx/readKey_transport`, `filter_col_transport` |
| A3 | the guard is relabelling-invariant **both ways** | `amenablePath_step_transport_iff` |
| **A4** | **`Force.KeyEquivariant orbKey` — no hypothesis** | **`keyEquivariant_orbKey`** |

**Why the guard is not a cheat.** The greedy descent breaks ties by vertex index, which does not commute
with relabelling. `AmenablePath` is exactly the repair, and it is itself invariant (T6), so the `if`
splits the vertices into two relabelling-stable classes and `KeyEquivariant` survives it.

A2 is `amenablePath_transport` with its accumulator `τ * σ` **kept** rather than discarded. The one
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
| B3a | at an `Amenable` node with a `RigidObstructionAt`, `forceBy orbKey` **strictly narrows** | `forceBy_orbKey_narrows` |
| **B2** | at an `Amenable` node **`orbKey`'s fibres ARE the orbits** (both directions) | **`orbKey_eq_iff_orbit`** |
| **D2** | force narrows the branch cell to a **single orbit** | **`forcedSet_single_orbit`** |
| **D1** | **a consume failure makes force fire at a reachable node** | **`consume_fail_force_fires`** |

**The pivot: the firing direction needs no hypothesis.** B1 is completeness of the encoding — discrete
leaf ⟹ singleton classes ⟹ the read determines the relabelled adjacency *and* the relabelled
`indivOne χ v`; the **odd** values of `indivOne χ u` sit exactly at `u`, so
`transportColouring ρ (indivOne χ u) = indivOne χ w` forces `ρ u = w`, and halving gives `χ ∘ ρ = χ`.
`Amenable` is needed only for `①` (§3.3) and for the converse half of B2.

**B2 is also the consistency guard** against `Force.forceBy_no_narrowing_on_orbit`: its `⟸` direction is
the ceiling (`Force.keyV_aut_invariant`, free from `keyEquivariant_orbKey`), so the key is constant on
each orbit and force can never cut *inside* one. It separates orbits and nothing finer — which is what
D2 then says. The landed theorems agree, and §2.5's 147/147 is the same statement empirically.

---

## 4. Cost — where the exponential is, and where it is not

**Cost of any descent = `∏ₖ bₖ`.** Today's `deepen` sets `bₖ = 1` **by fiat** (lowest-index pick). That
is free computationally but not free logically: the leaf it computes is a function of the *labelling*
and is only ever usable through an equality test between two runs — which is labelling-independent
exactly when the picked cell is a single orbit, i.e. **`Amenable`**. So deepen is not "poly and
correct"; it is **poly, and correct-when-`Amenable`**. Nothing in this track *introduces* an
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
transported multiset is equal — no `Amenable`, no isomorphism accumulation). Cost is
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

* **S1 — the certified-below cert key. ✅ This became `orbKey` (§3.3/§3.4).** If `AmenablePath` holds
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

**The residue is not ordering.** It is nodes with an **uncertified** rep — `AmenablePath` breaks
somewhere below. Measured: rand multipede V=12 W=8 (0/4 reps certified) and CFI cubic m=10 (4/40).
There the response is to resolve the deeper multi-orbit cell first (where S1 *does* apply, by
induction) and re-run — which is exactly what `not_amenable_deepest` now proves is possible. So the open
question is the **nesting depth of uncertified levels**, a cost/termination question.

---

## 7. ▶▶ THE FRONTIER — a poly, relabelling-invariant guard

`orbKey`'s guard is `Amenable`. It is *decidable* (`IsColAut` has a `Decidable` instance and
`Equiv.Perm (Fin n)` is a `Fintype`), so `orbKey` could be made computable at an `n!` price; it is
declared `noncomputable` rather than pretend that is a cost model. **`①` is unaffected either way** —
what a poly guard buys is a `Publication`-eligible executable.

Two candidate repairs. The first is now closed.

### 7.1 ⛔ CLOSED — deepen's own certificate is NOT relabelling-invariant

`Certified` / `CertifiedOrbit` (T1/T2) is poly and sound, and the open item was its invariance. **It is
not invariant, and this is measured, not conjectured** (`scratchpad/guardinv.py`): the all-anchor
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

### 7.2 ▶ THE ALTERNATE DESIGN — guard by an *equivariant* supply, per level

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
  `amenablePath_transport` (whose per-level input is supplied by SOUND). Needs one new lemma:
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

| witness | hook nodes | path cells `AmenablePath` inspects | certified by the proxy | hook nodes **fully** certified |
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
not act at that node — `①` is untouched, and `not_amenable_deepest` still relocates. So the design is
usable today at a measured cost, and the obvious next lever is depth (the proxy is depth-0; `deck2Supply`
seeds two vertices and chains) rather than a different guard shape.

Two further points on the design space:

* The **union of equivariant supplies is equivariant**, so the guard may use all five at once rather
  than pick one.
* Deepen's harvest can still be used to *fire*, since it is untrusted and re-verified — only the
  **guard** needs invariance. Nothing in §3 changes.

### 7.3 The rest of the open ledger (all `②`, none `①`)

1. **Nesting depth.** D1 relocates work to a deeper node; the product over relocations is not bounded.
   `DescentReach` + `ncol` bound the number of *steps* by `n`, not the branch factor.
2. **Composite assembly.** `forcedSet_single_orbit` is the exact input
   `Composite.forceThenConsume_singleton_of_cellIsOrbit` wants; wiring it needs `Consume.CellIsOrbit`
   on the *forced sub-cell*, which `Amenable` should supply.
3. **Entry into `Publication.canonForm?`** waits on §7.2.

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
| `Amenable` / `CellsAreOrbits` | **= Tinhofer graph.** AKRV (*comput. complexity* 26(3):627–685, 2017; arXiv:1502.01255) App. A.2: *"G is Tinhofer if and only if, for every F, the orbit partition of A_F coincides with P_F."* Graded: Bhattacharjee–Panse–Sarma arXiv:2605.19702 Thm 1.1. |
| ⚠ **name clash** | AKRV's **"amenable"** means something DIFFERENT (1-WL identifies `G` against all `H`). `Amenable ⊊ Compact ⊊ Godsil ⊊ Tinhofer ⊊ Refinable`, all strict (Thm 21). **Rename the project predicate.** |
| the free consume step | **"symmetric choice"** (Gire–Hoang 1998; Dawar–Richerby CSL 2003); with automorphisms supplied as certificates, **"witnessed symmetric choice"** — Lichter & Schweitzer, LICS 2022 (Distinguished Paper) / **J. ACM 71(2), 2024**. Their Thm 1: definable isomorphism ⟹ definable canonization. Their stated motivation is verbatim §3.1's T1: *"it has to be verified that the choice set is actually an orbit and it is not known that orbits can be computed in polynomial time."* |
| the whole split loop | **Gurevich's canonization algorithm**, *From invariants to canonization*, Bull. EATCS 63:115–119, 1997: repeatedly compute a **canonical orbit**, individualize one vertex, repeat. Poly complete invariant ⟺ poly canonization (classes closed under colouring). |

### 8.4 ⚠⚠ The rigid collapse — and what it forbids

**AKRV, immediately after Theorem 21:**

> "It is worth noting that **the hierarchy collapses to Discrete if we restrict ourselves to only rigid
> graphs**, i.e., graphs with trivial automorphism group."

For rigid `G`, `Aut_S = 1` for all `S` ⟹ `Orb(Aut_S)` discrete ⟹ **Tinhofer ⟺ 1-WL already discretizes.**
At a non-singleton cell of a rigid graph, "the cell is a single orbit of the stabilizer" is *impossible*.
Consequence for measurement design: on a rigid graph `AmenablePath` can only hold **vacuously** (zero
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
   `Amenable` hypothesis on the located-obstruction theorems is necessary. → §1.2.
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
actioned: `deepenRefSupply`, `DeepenRefInExec`, R1/R2 are parked out of `build.sh`; `DeepenAmenable`'s
`joint` survives as the *cost* lemma (`Amenable` ⟹ branch factor 1).
