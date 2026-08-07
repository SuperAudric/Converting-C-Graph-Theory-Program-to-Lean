# PER-CELL HARVEST + PER-CELL GUARD — the plan for getting deepen into `Publication.canonForm?`

**Written 2026-08-06.** Supersedes the "repoint `canonForm?` to the guarded mixed object" proposal,
which was based on a **wrong diagnosis** (recorded in §2 so it is not re-derived).

---

## 1. The core problem, in plain terms

A canonical form must return the same answer for two relabelled copies of one graph.

Deepen finds automorphisms by making arbitrary tie-breaks — *"individualize the lowest-numbered vertex
in this cell"*. Relabel the graph and "lowest-numbered" points at a different vertex, so deepen does
**genuinely different work** on two copies of the same graph. That is not removable: picking a vertex
*inside* a cell is precisely what 1-WL cannot do canonically (the standing ⛔ no-stabilizer-chain steer).

So the design never reasons about **what deepen does**. It reasons about **what deepen produces**, and
rests on one fact: what it produces is the **orbit relation** — a property of the graph, not of the
labelling. Where deepen is provably *complete*, the emitted relation **equals** the true orbit relation,
which conjugates under relabelling, and the arbitrary choices become invisible. That is what
`tinhofer_iff_certifiedG` bought: "deepen is complete here" became a checkable intrinsic condition.

**The catch is the word *where*.** "Provably complete" means **on the branch cell** — the single cell
the descent individualizes (`OrbitComplete`, `exec_recovers_refgen_at`, both requiring
`u ∈ Descend.branches χ`). But `Publication.canonForm?` is the **fused** object
(`Select.canonFormFastS?` → `selNode`), which probes **every** non-singleton cell to commit to the
cheapest one (`selColourV` filters over `nonSingletonColours χ`; `cellNarrowV` maps `rep` over each
`cellList χ c`). So the object consults the orbit relation on cells where deepen's completeness was
never established. **The object asks a question the supply does not answer.**

## 2. ⛔ The wrong diagnosis, recorded so it is not repeated

I first concluded *"the fused object cannot carry deepen; repoint `canonForm?` to the guarded mixed
shape"*. That was wrong, and the error was assuming ① at `selNode` must go through an equivariant
**reference** supply plus a `SameOrbits` bridge (which would have revived the parked R2 apparatus).

It does not. Tracing it: `selNode_canonizer` → `nodeTransport_selNode` → `selColour_transport`, and
`SupplyEquivariant` is consumed there for exactly one purpose — to make `rep (verified S)` transport at
each cell. **If the supply's emitted relation *is* the full `IsColAut`-orbit relation at every
non-singleton cell, that transports by conjugation directly.** No reference, no `SameOrbits`, no R2.

⟹ the fix is a **supply change**, and `Publication.canonForm?` keeps its current object.

## 3. The plan

1. **Per-cell harvest.** `deepenGens` currently harvests on `Descend.branches χ` only. Loop it over
   every non-singleton cell instead. Not a new mechanism — the same anchor/replay/twist code, indexed
   by `nonSingletonColours χ`.
2. **Per-cell guard.** Apply good-or-rigid (`GoodOrIsolated`) at every non-singleton cell rather than
   only the branch cell. Same decidable predicate, wider quantifier. ⚠ See §5 — it must quantify over
   *pairs*, not just cell members.
3. **Restate the two transport lemmas.** `selColour_transport` / `cellNarrow_transport` are currently
   *stated* with `SupplyEquivariant`; restate them against orbit-transport-at-cells. New lemma work,
   but the same shape as `deepen_branchOrbit_transport_guarded` / `_GI`, which are already written:
   open side = the orbit relation, conjugates; shut side = `[]`.
4. **①** at the fused object then goes through unchanged.
5. **③** off the existing `Tinhofer ⟹ no stall` chain, with residue *"some reached node has a cell that
   is neither good nor rigid"*.
6. **②** recompute (`costConst`/`costDeg`), now routine — `Deepen.stepCost` is billed as of 2026-08-06
   and the `ring`-expansion procedure is exercised.

`twinStep`/`pairStep` composes with this and strictly helps: finer cells ⟹ more cells are
good-or-rigid ⟹ the guard opens more often.

## 4. ★ COST — no new exponential, and in the worst case no new factor at all

The concern is fair (*"harvest on every non-singleton cell sounds suspicious"*), so here is the
arithmetic rather than a reassurance.

Per cell of size `m`, deepen's harvest is `≤ m` anchors × (one `deepen` at `≤ n` levels × warm refine
`n³`) + `≤ m` replays each `n⁴` + twists at `n²` ≈ **`m² n⁴`**.

Summing over the cells of a partition:

> **`Σᵢ mᵢ² ≤ (Σᵢ mᵢ)² = n²`**

so the per-cell harvest totals `≤ n² · n⁴ = n⁶` — **exactly the current declared bound**. The current
design's *worst case is already one cell of size `n`* (`Σ m² = n²`); splitting the vertex set into
several cells only **reduces** `Σ mᵢ²`. Per-cell harvest is therefore free at the level of the declared
bound, and is never worse than the single-cell case it replaces.

⚠ Two real caveats, neither exponential:
* The supply is evaluated **once per node** (`selNode`'s shared `sv`/`V`, trap #2), so this does not
  multiply per cell probed. Confirm that sharing survives the change.
* More generators ⟹ more cells collapse to `≤ 1` ⟹ `selColour` may commit to a **different (lower)**
  colour. That is a behaviour change, and it can only *help* branching — but every `Regression` number
  that pins a selected colour must be re-measured, not assumed.

## 5. ⚠⚠ THE PAIR CAVEAT — per-cell reasoning does not always apply to `twinStep`

Recorded because it is easy to miss and it bounds what a per-*cell* predicate can express.

`twinStep`/`pairStep` is indexed by an ordered **pair**, and pairs drawn from the same cell are **not
interchangeable**. `C₆` is the minimal example (`DeepenPair` §C₆): it is vertex-transitive, so all six
vertices are one cell and one orbit — yet

* the **distance-2** pair `(0,2)` shares exactly the vertex between them (`{1,5} ∩ {1,3} = {1}`) and
  `pairStep` discretizes with **zero** further decisions;
* the **adjacent** pair `(0,1)` shares **nothing** (`{1,5} ∩ {0,2} = ∅`) and costs an extra
  individualization.

So a predicate of the form *"this cell is good"* cannot see a distinction that is real and that changes
the descent's depth. The natural index for the pair object is the **orbital**, not the cell — the same
orbits-vs-orbitals seam that separates 1-WL from 2-WL throughout this project.

⟹ **Step 2's per-cell guard must quantify over the pairs inside the cell, not merely over its
members**, or "the cell is good" is ambiguous (open for one pair, shut for another). This does not
block the plan, but a guard written per-member and *assumed* to cover pairs would be unsound-by-omission.

## 6. Status of the pieces

| piece | state |
|---|---|
| `Tinhofer ↔ CertifiedG deepenSupply` | ✅ built, axiom-clean |
| `GoodOrIsolated` equivariant + `①` | ✅ built; **strict win measured** (2/60 cubic, `n=10` verified exhaustively) |
| `pairStep` + inherited `step` interface | ✅ built, blast radius zero |
| `Deepen.stepCost` billed | ✅ built; `costConst` 53 → 57 |
| per-cell harvest | ⬜ not started |
| per-cell guard (pair-indexed) | ⬜ not started |
| `selColour_transport` against orbit-transport | ⬜ not started |
| `②` recompute | ⬜ not started |

## 7. Probe inventory — what has already been measured, so it is not re-run

All in `scratchpad/`. Every one uses the vetted union-find-over-generators orbit reconstruction
(`probe_certkey.true_orbit_partition`), **never** `probe_orbit_oracle` (which is proven wrong).

| probe | what it settled |
|---|---|
| `probe_goodorisolated.py` | `GoodOrIsolated` vs `CertifiedG` on 11 multipede/CFI witnesses — **0 strict wins**, `isol = 0` |
| `probe_isolpower.py` | the above is **not** a weak `inv`: `stepSum`, full colour multiset, and a 2-step signature all give `isol = 0` on the wall families |
| `probe_selector_ceiling.py` | ★ **a better within-cell SELECTOR has ceiling ZERO** — exhaustive over all picks; `chooseIdK` picks the *cell* canonically, a selector only picks a vertex inside it |
| `probe_pairrefine.py` | depth-2 (individualize both) repairs **CFI m=10 4/4**, rigid multipede **0/4** |
| `probe_twinrefine.py` | ★ **`TWIN = BOTH`, 168/168** — the twin refinement **is** `pairStep`; no separate object needed |
| `probe_mixedcell{,2,3}.py` | the `C₃`/`C₄` mixed-cell witness; ⛔ **falsifies `BAD-BIG = 0`** (24-orbit, `good 0/24`) |
| `probe_whychoke.py` | why that witness's twin-hub descent fails: **level 8, a 24-vertex BLOCK cell**, `h₂`/`h₃` still merged — the descent never reaches the hub cell |
| `probe_c8witness.py` | user's interlinked-`C₈` construction — everything good, both guards open; **first firing of `IsolatedBy`** |
| `probe_strictwin.py` | ★★ **2 strict wins in 60 random cubic graphs** |
| `probe_strictwin_verify.py` | ★★★ the `n=10` win **verified exhaustively** (all `10!` perms; no `canon`, no generator harvesting) |

★ **The recipe the failures taught:** a strict win needs a cell whose **bad** anchors are all
`Aut`-**rigid** and `inv`-isolable. `C₃`/`C₄` failed it (bad anchors were *twins* — not rigid, so not
soundly isolable); `C₈` failed it (no bad anchors); **generic rigid-ish regular graphs supply both.**
