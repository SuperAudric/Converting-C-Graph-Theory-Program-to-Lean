# CAO propagation — does refinement preserve `CellsAreOrbits` under individualization?

> ⚠ **NOT the same doc as [`chain-descent-cellsareorbits-route.md`](./chain-descent-cellsareorbits-route.md).**
> That one is the *demoted* forms-graph bounded-WL-dimension route. **This** doc owns the question
> *"start from the orbit partition, individualize one vertex, refine — are the cells still orbits?"*,
> which is the domain hypothesis behind `Tinhofer` / `DeepenTinhofer.lean`.

---

## STATUS (read first)

| level | verdict | witness |
|---|---|---|
| **1-WL** | ⛔ **REFUTED** | `net(Z₄) ≅ CFI[K4]-tw` (n=28); also Shrikhande (n=16, VT), Chang-2 (n=28), `Cay(Z₁₂⋊₅Z₂)` (n=24, VT) |
| **2-WL** | **OPEN — no counterexample, and the evidence is now non-vacuous but thin** | — |
| `VT ⟹ Tinhofer` | ⛔ **REFUTED at 1-WL** by the parallel branch — see [`../scratchpad/HANDOFF_2wl.md`](../scratchpad/HANDOFF_2wl.md) §5 | `Cay(Z₁₂⋊₅Z₂)` |
| `CAO ⟹ Tinhofer` | ⛔ **REFUTED at 1-WL** | `net(Z₄)` |

**The live target is §2's sharpened statement.** It is union-stable, strictly weaker than "schurity of
point extensions", and it isolates the one thing that actually has to happen (§3's coupling principle).

**Why the project cares.** Per [`00-START-HERE.md`](./00-START-HERE.md) §2, *"the SOLE remaining `①c`
condition, `Tinhofer`, IS `CellsAreOrbits`"*, and `deepenSupply` stays out of `Publication.canonForm?`
until that totality is **populated per family (T1)**. This doc is the T1 obligation's evidence base.
Two fragments are **already landed** — do not re-prove them:
`CascadeOracle.cellsAreOrbits_of_discrete` (:292, the discrete end) and
`cellsAreOrbits_of_compl_card_le_two`.

**Everything here was measured with the clean-room machinery in §8, never with
`probe_orbit_oracle` — which is PROVEN BROKEN (§8.2).**

---

## 0. ▶ HANDOFF — start here

**Where the work stands, in a few sentences.** At **1-WL the question is settled: refuted**, four
independent witnesses (§ STATUS). At **2-WL it is open**, no counterexample after a large and
now-non-vacuous search (§6), and §3 explains *why* the search keeps failing. The **reduction is
finished and in Lean**: `ChainDescent/CaoFibring.lean` proves that preservation is equivalent to
*separating orbitals*, with nothing left over (§12.1–12.2). What remains is exactly **one
hypothesis**.

**The remaining obligation has a name.** In `CaoFibring.levelSet_iff_stabOrbit_of_separates`,

```
hsep : ∀ u w, f v u = f v w → SameOrbital adj χ v u v w
```

`f` = any `IsColAut`-invariant pair colouring (a 2-WL closure is one). Discharging `hsep` for the
2-WL closure *is* the theorem; everything else is done. **Do not attack the target in its graph
form** — the graph content is gone after §1's reduction.

**Read in this order.** § STATUS → §1 (the reduction — nothing later makes sense without it) → §2
(the target) → §3 (the mechanism; this is the conceptual core) → §12 (the proof plan). Then §4/§5
before proposing anything, and §7 before investing in anything.

**First actions — ▶▶ THE ORDERED PLAN IS §12.6 (M1–M6); start there.** In one line: **M1** run the
step on its real input class at a population that pays §7.2's entry ticket (⚠ and *fix* the
measurement first — the sharp-Cayley probe silently caps at ~24 inputs, not 729); **M2** is the
separation round count bounded (the only union-stable formalizable shape); **M3** instrument the
feedback loop, not the round number — the actual mechanism ask; **M4** the coupling construction, in
parallel with M3; **M5** reuse the already-built `CoherentConfig.lean` substrate; **M6** the group
bridge. ⚠ **M1 can end the track** — if 2-WL falls, §10.5's selector route (A) becomes the only path.

**Before proposing any new route or invariant, apply §7 in order.** Two proof routes and two
falsifier habitats died to those filters in one session each; they are cheap and they are decisive.

### 0.0 ▶▶ WHY THIS QUESTION IS WORTH ITS COST — the unrecorded reason (added 2026-07-30)

⚠ **This was understood but never written down, and a fresh reader reconstructs the wrong target
without it.** Two readings have now been made and corrected: (a) that this doc serves the *existing*
`Tinhofer` predicate, and (b) that a 2-WL result would feed the **force** resolver. Both are wrong.

**The Lean `Tinhofer` is a 1-WL predicate.** `Deepen.step = Refine.warmRefineVec ∘ Descend.indivOne`,
and `warmRefineVec` iterates `sigKey`, whose `signature` is the multiset of `(χ u, adj v u, P v u)`
over `u ≠ v` — plain colour refinement. `CellSingleOrbit` is stated at `IsColAut adj χc` for that
1-WL `χc`. **So proving §2 (a 2-WL statement) does not discharge `Tinhofer` as it stands**, and it is
not meant to: 2-WL cells refine 1-WL cells, and a 1-WL cell is a *union* of 2-WL cells, so nothing
transfers. Measured on the flagship witness (`net(Z₄)`, n = 28, from the exact orbit partition,
either root-orbit rep): 1-WL → 5 cells, **2 mixed**; 2-WL → 7 cells, **0 mixed**.

**This doc is a probe into a DESIGN CHANGE, not a lemma for the current object.** The question is:
*if the refiner were swapped 1-WL → 2-WL — a direct polynomial cost increase, `n²` → `n³` per round —
does the architecture gain a theorem it provably cannot have at 1-WL?* The chain that would cash it:

> **CAO all the way down ⟹ Layer 1 (`Tinhofer ⟹ R1`) ⟹ the deepen supply is COMPLETE ⟹ consume
> resolves every node.** Force is not fed by this; it is made *unnecessary* on the consume domain.

**Why nothing weaker will do — the obstruction is not about mixed cells.** The recorded refutation
(`scratchpad/DUAL_resolver_scoping.md` §1.2; CFI over a random cubic base, m = 8, n = 56, the
`|C| = 16` node) has the *opposite* shape from what one expects: the cell **is one true orbit**
(explicit σ, `is_aut ✓`, colour-preserving ✓, σ(24) = 26 crossing the harvest's 8+8 split), so consume
fails from **supply incompleteness**, and at a single-orbit cell `Force.forceBy_no_narrowing_on_orbit`
**forbids** force from acting. ⟹ *no theorem of the shape "consume fails at `χ` ⟹ force can act at
`χ`" can hold.* Force is structurally barred from precisely the failure mode that occurs.
`Tinhofer ⟹ R1` closes that mode at its source — with single-orbit cells at every level the
re-relating induction makes the harvest complete, so supply incompleteness cannot arise. **All the
load therefore sits on "every level's cell is a single orbit" = CAO propagation.**

⚠⚠ **"The 1-WL design is provably dead" IS TOO STRONG — walked back 2026-07-30 (user), after
independent verification between iterations.** On the existing VT-non-`Tinhofer`-at-1-WL witnesses
**consume _can_ fire, and measurably does**: the index-min vertex selection usually happens to choose
vertices in the same orbit (this is the same selector luck as §7.5's Shrikhande, and it is why the
force-key tally in limit 2 below finds zero blind cells). What is missing is a **guarantee** — nothing
says the selector is lucky on an antagonistic input, and in particular nothing covers the **root**.
⟹ the honest verdict is **"no completeness theorem at 1-WL", not "dead"**, and there are **two**
routes to one, not one:
- **(A) the SELECTOR route** — see §10.5. Prove index-min (or a better canonical selector) always
  lands on a resolvable cell. Recorded and parked, not dead.
- **(B) the MECHANISM route** — the 2-WL swap, this doc's subject. Plan = §12.6 (M1–M6).

**⚠ TWO SCOPE LIMITS on "revived at 2-WL" — do not overclaim.**
1. **Propagation is the induction STEP; the base case is separate.** A descent starts at the uniform
   colouring, so "root CAO" is *"k-WL computes the orbit partition of the input"* — false at every
   fixed `k` for rigid multipedes. The revival is on the **consume domain** (inputs whose k-WL root
   partition already is the orbit partition); rigid and mixed roots stay Track R's. It makes consume's
   ownership of its domain *complete*, not the whole design safe.
2. **The known 1-WL witnesses do NOT exhibit a concrete stall.** Measured 2026-07-30
   (`probe_stall.py`/`probe_stall3.py`/`probe_stall4.py`): across **all four** recorded witnesses —
   `net(Z₄)`, Shrikhande, Chang-2 and the named VT witness `Cay(Z₁₂⋊₅Z₂)` — **13 manufactured mixed
   cells, and the force key separates the true `Aut_v`-orbits at every one of them**: lookahead depth 1
   (which *is* `lookaheadKey`'s non-discrete branch) on 10, depth 2 on 3 (one size-3 `net(Z₄)` cell and
   the two size-2 cells of the VT witness). **Zero blind cells.** 2-WL splits all 13 at depth 0.
   ⟹ **the death is the missing theorem, not a failing run.** Do not cite these graphs as "the design
   dies here" exhibits. ⚠ This does *not* rescue 1-WL: bounded lookahead depth is not a theorem either,
   and "some bounded depth always suffices" is the WL-dimension question in another costume.

**▶ And the stakes of the negative branch.** If CAO propagation fails at *every* `k`, the design
cannot be made viable by refiner strength and needs deeper structural change. The reason to expect
otherwise is §5's **self-limiting** lesson, which has never been connected to this question: the CAO
hypothesis *excludes* the standard "no bounded `k` works" constructions — rigid ⟹ discrete orbit
partition ⟹ vacuous kills the multipede/Lichter family, and CFI is excluded separately (it is about
distinguishing two graphs, not orbit recovery within one; its large gauge group keeps orbits coarse
enough that even 1-WL matches). A "fails at every `k`" witness would have to be simultaneously
non-rigid, orbit-coarse, and closure-deficient **at the same cell pair** — §3's coupling requirement,
which no falsifier has ever met. **That branch currently has no candidate witness at all.**

### 0.1 How to reproduce anything here

*Probes* — pure Python 3 stdlib, **no dependencies** (no networkx/sympy/nauty; none are installed).
Every probe that another probe **imports** is `__main__`-guarded, so importing it does not run its
sweep (verified — the import graph was checked and the two stragglers fixed). Leaf drivers are not
guarded; they are meant to be run directly. ⚠ If you add a probe that imports another, re-check
(§9: this trap fired three times in one session):

```bash
cd /workspace/scratchpad && python3 -u probe_cao_cleanroom.py     # the core witnesses
python3 -u probe_cao_provenance.py                                # 11 known |Aut| values + the broken-oracle proof
```

Long sweeps write logs; **do not pipe them through `tail`** (§9). Run them detached and read the log.

*Lean* — the gate is the **absolute** path (it self-`cd`s via `$0`; a relative path fails):

```bash
bash /workspace/scripts/build.sh          # full serial gate, ~220 s, 108 modules
cd /workspace/GraphCanonizationProofs && lake build ChainDescent.CaoFibring   # this module alone
lake env lean /workspace/scratchpad/CaoFibringAxioms.lean                     # #print axioms, all 18 decls
```

⚠ bare `lake build` builds a **partial** 14-module subset and omits this cluster — always use
`build.sh`. Lean probe files live **outside** the package root so they cannot enter any build.

---

## 1. The question, stated three ways

**Graph form.** Let `χ` be the exact `Aut(G)`-orbit partition (so `CellsAreOrbits` holds by
construction, *however obtained* — the hypothesis does not require refinement to have found it).
Individualize `v`, take the `k`-WL closure. Is every cell still a single `Aut(G, v)`-orbit?

**CC form (the useful one).** Under CAO the start cells *are* `Aut`-orbits, so for cells `D ∋ v` and
`C`, transitivity on `D` puts the `Aut_v`-orbits on `C` in bijection with the **`Aut`-orbitals inside
`D × C`**. Hence

> **`k`-WL preserves `CellsAreOrbits` ⟺ the one-point extension separates the orbitals between
> fibres ⟺ the class of *fibre-schurian* coherent configurations is closed under one-point extension.**

No graph, CFI or gauge content survives the reduction. **Do the reduction before attempting anything** —
it is what makes §3 and §4 visible.

**⚠ Do not conflate these.**

```
CAO propagation (∀ inputs)   ⟹   CAO at every node of a descent from a CAO root   ⊋   Tinhofer
```
The first two are equivalent along a descent from a CAO root (propagation applied inductively); the
universal form is stronger only in that it quantifies over all inputs. **The strict gap is the last
one:** `Tinhofer` (`DeepenTinhofer.lean`) inspects **only the `chooseIdK`-selected** cell at each
level, so CAO may break at a node — even on a cell the descent will later visit — and the graph can
still be `Tinhofer` (Shrikhande does exactly this, §7.5). **Proving CAO propagation is proving
strictly more than the chain needs**; check whether the weaker statement suffices before starting.

⚠⚠ **The ladder above holds at a FIXED WL level and does NOT cross levels.** The built `Tinhofer` is
**1-WL** (`step = warmRefineVec ∘ indivOne`); this doc's target (§2) is **2-WL**. Since 1-WL cells are
unions of 2-WL cells, the 2-WL statement implies nothing about the 1-WL one — measured, `net(Z₄)`:
2-WL 0 mixed cells, 1-WL 2 mixed. **A proof of §2 is a result about a 2-WL-refined descent, i.e. about
a proposed design change, not about the object in `build.sh`.** See §0.0 for why that change is the
point rather than a defect.

---

## 2. ▶▶ THE LIVE TARGET

> **If individualizing `v ∈ D` splits `C` (i.e. `Aut_v` is intransitive on `C`), then the 2-WL
> extension separates the `D–C` orbitals.**

Why this phrasing and not another:
- **union-stable by construction** (stated per cell pair) — it survives the stress test in §7.1 that
  killed two earlier formulations;
- **strictly weaker** than "schurity of point extensions" — it only asks about orbitals the group
  actually splits;
- it states the coupling requirement (§3) explicitly, which is what every falsifier attempt missed.

**Counterexample design implied by it:** find `D, C` with `Aut` transitive on both, `Aut_v`
**intransitive** on `C`, and two `D–C` orbitals still algebraically fused **in the extension**.

**▶ The proof plan for this statement is §12.** Steps 1–2 there are free and already discharge
~99% of instances; the crux is isolated in §12.3.

---

## 3. ★ THE MECHANISM, AND THE COUPLING PRINCIPLE

**Exactly what individualization does to other orbits.** Individualizing `v ∈ D` changes cell `C`'s
orbits **only** by fibring `C` over the `Aut`-orbitals inside `D × C`: orbital `O` contributes
`{u ∈ C : (v,u) ∈ O}`, of size `|O|/|D|`. **Nothing else can happen.** Therefore

- if `Aut_v` is still transitive on `C`, nothing changes there and CAO is **trivially safe**;
- `k`-WL detects the change iff its closure **separates** those orbitals; the blind spot is a
  **fusion** of ≥ 2 orbitals into one class.

> ### ⟹ A CAO failure needs the GROUP-CHANGE and the CLOSURE-DEFICIENCY at the **same** cell pair `D × C`.

This one principle explains every negative result on record (all measured, `probe_cao_mechanism2.py`):

| construction | group-change | deficiency | outcome |
|---|---|---|---|
| `G ⊔ G` | copy A | copy B | **all 144 fused pairs are BB**; copy B's `Aut_v`-orbits are `[16]` = one orbit ⟹ safe |
| non-rigid multipede | everywhere (\|Aut\|=2) | none — the CAO start hands WL the labelling | 1-WL discretizes |
| CFI over big bases | none (`Aut_v` stays transitive) | gauge parity | propagates even at 1-WL |
| **`net(Z₄)` at 1-WL** | **same place** | **same place** | **the one that works** |

**Fusion structure at deficient roots** (merged orbitals, valencies from one point): Shrikhande `[3,6]`;
`net(Z₄)` four classes `[3,6] [3,6] [4,8] [1,2]` (ratio 1:2 = the `Z₄` order-2-vs-order-4 signature);
Chang-2 two classes `[4,4]`. ⟹ **fusions occur at both equal and unequal valency, so no valency
argument can shortcut this.**

**Why 2-WL is different in kind from 1-WL (not merely stronger).** The gap to close is the orbital
structure on `D × C` — a *pair-level* object. 1-WL is a vertex-level tool aimed at a pair-level gap: a
**type mismatch**, which is why 1-WL counterexamples are easy. 2-WL computes the coarsest invariant
approximation *of that very object*. This is a reason, not a guarantee.

---

## 4. ⛔ DEAD PROOF ROUTES — with the reason each died

**4.1 Coset transfer — CIRCULAR.** `u,w` in one extension cell ⟹ CAO gives `τ ∈ Aut` with `τu = w`;
you need `σ ∈ Aut_v`. That holds iff `τ⁻¹(v) ∈ Aut_u·v` — and the `Aut_u`-orbits on `D` are the
orbitals in `C × D`, **the transpose of what is being proved**. This is the recorded 1-WL sketch's
defect one dimension up. ⟹ **CAO alone can never close the gap.**

**4.2 No purely counting/local proof can exist.** `k`-WL computes only structure constants;
"an automorphism exists" is not a counting statement. A proof needs a Schur–Wielandt-style
classification of the algebraic automorphisms, or a genuine restriction of the class.

**4.3 The bounded-shattering-depth route — killed by `G ⊔ G`.** `Discrete ⟹ CAO` is free and already
proved (`CascadeOracle.cellsAreOrbits_of_discrete`), so a bound "the descent discretizes within `d`
individualizations" would give CAO propagation with no schurity theorem. But **depth is linear in the
number of components**: Shrikhande ×1/×2/×3 → **3/6/9**, while VT and CAO hold throughout. The target
property is union-closed; a depth bound is not. ⟹ **usable only as a per-family statement (§10.4).**

**4.4 "Full schurity" as the induction invariant — killed by the same construction.** Measured law
*"non-schurity occurs only at depth 0 and the first individualization destroys it"* is **FALSE**:
Shrikhande ⊔ Shrikhande has root CAO ✓ and depth-1 CAO ✓ but full schurity fails at **both** — one
individualization lands in one copy and the other still carries the whole deficient scheme.

**4.5 Proving the stronger "schurian CCs are closed under point extension".** Not available: the
fibre hypothesis is doing real work, and any route that would also prove the unrestricted version is
doomed. (Also: it fails §7.1.)

---

## 5. ⛔ DEAD FALSIFIER HABITATS — do not re-sweep

| habitat | why it cannot work | measured |
|---|---|---|
| **CFI over any base** | CFI is about *distinguishing two graphs*, not orbit recovery inside one; the gauge group is huge, so orbits stay coarse and WL matches them | twisted over prism, K3,3, Q3, cubic8, K5, Petersen (treewidth ≤ 4) propagate **even at 1-WL**; only `CFI[K4]-tw` fails, and that graph *is* `net(Z₄)` |
| **rigid multipedes** | theorem `Cascade.recoverableAt_base_iff_discrete`: rigid ⟹ orbit partition discrete ⟹ CAO start is discrete ⟹ vacuous | — |
| **non-rigid multipedes** | the loophole, and it is closed: F₂ kernel = ⟨all-ones⟩ ⟹ \|Aut\|=2, CAO start = all 2-element orbits, `\|Aut_v\|=1` so *any* non-singleton cell would be a hit | 10 instances, W=6–10, n=52–114: **1-WL already discretizes** |
| **abelian Cayley, generalized dicyclic** | `x ↦ x⁻¹` fixes `e` ⟹ `\|Aut_e\| ≥ 2`, no GRR exists (⚠ a *GRR-hunt* exclusion only — these remain legitimate 2-WL inputs, and the Schur-ring sweep uses them) | 3681/3681, 1312 resp. — parallel branch, `HANDOFF_2wl.md` §3 |
| **group-derived generally** (Cayley, Johnson, Kneser, Paley, rook, nets over abelian groups) | tend to be schurian outright ⟹ the sharp case never arises | see §6 vacuity ledger |

**★ The general lesson from all five rows:** these all fail for the *same* reason — they separate the
group-change from the deficiency (§3). **The CAO hypothesis is self-limiting**: a small group means a
fine start, which hands WL the entire labelling; a large group means a coarse start but coarse orbits
too. Every "shrink the group" design dies on this.

---

## 6. THE EVIDENCE LEDGER — weighted honestly

**⚠ Read the discounts. Two of these numbers were once quoted at face value and were worth nothing.**

| evidence | strength |
|---|---|
| **S-ring sweep, COMPLETE**: 38 verified groups, orders 8–32, **66,888 connection sets · 62,147 non-discrete S-rings · 729 NON-SCHURIAN (genuine entry tickets) · 0 counterexamples** | **the strongest evidence on record.** The entry ticket actually occurs here |
| Parameter-determined SRGs (T(8) + 3 Chang graphs, nets, Paley, Johnson/Kneser) | moderate; Chang-2 is a real 1-WL failure repaired exactly by 2-WL |
| **2-WL recovers the `Aut_v`-orbits EXACTLY on the named VT witness** `Cay(Z₁₂⋊₅Z₂)` (n=24, \|Aut\|=48, \|Aut_v\|=2): `same_partition(2-WL diag, Aut_v-orbits) = True`, while 1-WL = `False` with **all 6** non-singleton cells mixed (2026-07-30, `probe_stall4.py`) | **strong, and sharp.** The input class is known-capable — this is the graph that refutes `VT ⟹ Tinhofer` at 1-WL — so the §7.2 entry ticket is paid, unlike the worthless 21-object sweep |
| VT voltage covers (`Z₂`/`Z₃`/`Z₄` over 9 VT bases): 122 covers, 0 failures | moderate — imprimitive, blocks of size 2–4, not circulant-dominated |
| Descent instrumentation: 11 objects, **16,048 nodes**, fibre-schurian everywhere | ⚠ **DISCOUNT HEAVILY** — only **364** of those nodes still have a cell of size ≥ 3; the rest are near-discrete where schurity is trivial. **The honest figure is 364, not 16k** |
| The original 2-WL sweep (21 objects) | ⛔ **WORTHLESS** — 0/21 had a non-schurian one-point extension, so it could not possibly have found a counterexample. The recorded vacuity failure |
| The old 498 + 313 VT pins | ⛔ **UNSOUND** — produced by the broken oracle (§8.2), which errs by *merging* ⟹ false "ok"s |

**Why the descent numbers collapse:** max cell size drops per level (Shrikhande 16→6→4→2→1;
T(8) 28→15→10→6→4→2→1). Descents are over in 4–6 levels, so almost every node is trivially schurian.

---

## 7. ★ STANDING FILTERS — apply these before investing in anything

**7.1 The `G ⊔ G` stress test.** The target is closed under disjoint union. **Any proposed invariant
or proof route must be union-stable, or be applied component-wise.** It is nearly free and it killed
two routes in one call (§4.3, §4.4). Run it *first*.

**7.2 The vacuity / entry-ticket check.** A 2-WL vertex-level failure **requires a non-schurian
one-point extension** (if the extension is schurian the diagonal classes *are* the orbits).
`probe_2wl_vacuity.py` decides both root- and extension-schurity for any candidate in one call.
**Run it on any candidate family before sweeping it.** ⚠ Necessary, **not sufficient** — non-schurity
can live entirely off-diagonal (`G ⊔ G` is exactly that).

**7.3 The Lagrange certificate.** Orbit sizes divide `|Aut_χ|`, so a cell of size `c` with `c ∤ |Aut_χ|`
is **automatically mixed** — no orbit oracle needed. This found every 1-WL counterexample. Extremal
form: trivial stabiliser with a non-discrete colouring.

**7.4 Aim for the convention-independent falsifier.** ⚠ *Naming collision: the parallel handoff calls
these "T1/T2"; that is unrelated to the project's **T1** = the per-family `CellsAreOrbits` totality
obligation. Avoid the T1/T2 labels here.*
- *selector-dependent* (weak): "`chooseIdK` picks a mixed cell" — depends on the colour-id convention,
  so it needs the Lean `#eval` cross-check of §8.3 to be believed;
- ★ *convention-independent* (aim here): **"every non-singleton cell is mixed at a reachable node"** —
  needs no id convention and kills backtracking selectors too. Structural form: *the descent reaches a
  node whose stabiliser is too small for any of its cells*; extremal case, a trivial stabiliser with a
  non-discrete colouring. Note the node need not be at depth 1 — along a legal descent every picked
  cell is a full orbit, so `|Aut_χ|` divides by the cell size each step and shrinks fast.

**7.5 `Tinhofer` is a (graph, SELECTOR) property.** Shrikhande carries a genuine `RigidObstructionAt`
at a node the descent visits, yet **is** `Tinhofer` because `chooseIdK` looks elsewhere — twice.
Measured EXISTS-Tinhofer = True, FORALL-Tinhofer = False. ⟹ **any proof of a `… ⟹ Tinhofer` lemma
must use the concrete `chooseIdK` + `warmRefineVec` id numbering; a selector-free proof cannot exist.**

---

## 8. TOOLING

### 8.1 Sound machinery (validated)
- `probe_cao_cleanroom.py` — own CFI/net construction, own 1-WL, `all_isos` = complete I-R leaf
  enumeration with **every accepted leaf re-verified as a permutation automorphism**.
- `probe_cao_vtcover.py::iso_exists` — early-exit pairwise search. Agrees with `all_isos` on orbits.
- **Validation** (`probe_cao_provenance.py`): 11 independently known `|Aut|` values — K4 24, C6 12,
  K3,3 72, Q3 48, Petersen 120, Kneser(5,2) 120, Kneser(6,2) 720, Paley(13) 78, Heawood 336,
  rook4×4 1152, Shrikhande 192. All match.
- ⚠ `iso_exists` returns `None` on budget exhaustion. **Treat only `is True` as same-orbit and only a
  completed `False` as different-orbit** — conflating `None` with `False` manufactures counterexamples.

### 8.2 ⛔⛔ BROKEN — never use
`probe_orbit_oracle.orbit_partition` (= `canon` **with automorphism pruning** + `leafcap`). Proved on
`multipede[6x5]` (n=30, `|Aut| = 8`, *not* rigid): true orbit partition has **15** blocks; the oracle
returns **11** at the root and **6** when handed the correct partition. **It errs by MERGING** ⟹ it
yields **false "ok"s, never false counterexamples** ⟹ every "0 counterexamples" verdict it ever gave
is unsound, including the 498 + 313 VT pins.

### 8.3 The Lean cross-check pattern
`#eval` on `chooseIdK` / `step`, file placed **outside the package root** so it cannot enter any build;
no `native_decide`. Example: `scratchpad/ShrikhandeTinhoferProbe.lean`.
⛔ **Do NOT hand-reason the colour-id order** from `indivOne χ v = 2·χv + 1`: the `2χ+1` makes `v`
largest, but `sigKey`'s **Cantor-paired** tuples reverse the cell order. This was gotten wrong twice;
only `#eval` settles it. (Irrelevant if you aim for T2 — another reason to.)

### 8.4 Cheap computational identities worth reusing
- For a Cayley graph the **root** closure is translation-invariant, hence the **Schur ring** ⟨S⟩ —
  computable on `G` in `O(n²)` per round from the structure constants, a ~1000× filter versus an `n³`
  pair colouring. ⚠ **But the S-ring is the ROOT closure only**: individualizing `e` destroys
  translation-invariance and the real extension refines **strictly past** it (measured:
  `[1,1,2,4,4,4] → [1,1,2,2,2,4,4]`). Sound as a necessary-condition filter, **never as the verdict**.
- `Aut(G ⊔ G) = Aut(G) wr S₂` — build it programmatically from `Aut(G)`; orbits/orbitals by union-find
  **from generators** (exact, no enumeration). Makes n=32 with `|Aut| = 73728` instant.
- Under CAO, **one representative per cell suffices** when descending: the cell is one orbit, so other
  representatives give conjugate children.

---

## 9. PROCESS TRAPS (each cost real time)

- **Importing a probe module re-runs its module-level sweep.** `__main__`-guard everything. *(Hit three
  times across two sessions — including once while writing the fix for it.)*
- **`pkill -f <script>.py` matches your own launcher's command line** ⟹ self-kill, exit 144. Kill by PID.
- **`str.replace`-based edits silently no-op.** Assert the marker is present and assert the edit landed.
- **Piping a long background command through `tail` buffers everything** — you see nothing until exit,
  and nothing at all if it is killed. Write to a log file.
- **Wrap `all_isos` budget exceptions.** An unguarded `RuntimeError` killed a sweep at its last stage.
- Connection-set / voltage enumerations blow up combinatorially. Cap, and **log what you skipped**.

---

## 10. OPEN ITEMS

> ✅ **Closed since this doc was written:** the reduction (Steps 1–2 of the proof plan) is proved and
> gated — `ChainDescent/CaoFibring.lean`, §12.1–12.2. The open items below are what is left.

1. **The live target (§2), unproven — and it is now a single named hypothesis**, `hsep` in
   `CaoFibring.levelSet_iff_stabOrbit_of_separates` (§0). Treat it as a genuine question of algebraic
   combinatorics — the schurity of one-point extensions — not a lemma to discharge. The practical
   route is a **per-family certificate** (§12.4 R2/R3), matching the project's carried-obligation
   pattern; note `ChainDescent/Separability.lean` and `ChainDescent/CoherentConfig.lean` already
   carry `Separable` / `SeparablePointed` / `ExtensionSeparable`, which is R2's vocabulary.
2. **Not yet run:** the `E1/E2` descent instrumentation over the **sharp Cayley inputs** (the 729
   non-schurian S-rings). The section exists in `probe_cao_induction.py` but its first attempt died on
   an unguarded budget exception; the guard is now in place and it has not been re-run. **This is the
   cheapest remaining measurement.**
3. **The coupling construction (§2, §3).** Nobody has yet tried to *build* an object with the
   group-change and the deficiency at the same cell pair. That is the falsifier design, and it is the
   only one not already excluded by §5.
4. **Per-family route.** The project's hard families (forms graphs, Cameron) have known classical
   groups, so their orbitals are computable and schurity is provable *per family* — no general theorem
   needed. Related but distinct: the node-4 families reportedly shatter under ≤ 4 individualizations.
   ⚠ Bounded depth is **not** union-stable (§4.3), so it can only ever be a per-family statement.

5. **★ THE SELECTOR ROUTE (A) — RECORDED AND PARKED, not dead (2026-07-30, user).** The alternative to
   the whole 2-WL swap. **Measured fact it rests on:** on every recorded VT-non-`Tinhofer`-at-1-WL
   witness, consume *does* fire, because index-min selection happens to pick vertices in one orbit.
   (§7.5's Shrikhande is the same phenomenon; limit 2 of §0.0 is the force-side tally). 
   Disjoint antagonistic copies of VT graphs can be made to fail comparisons between them,
   but some consumable comparisons survive. **The target:**
   *prove the lowest-index selector — or a better canonical one — always lands on a resolvable cell.*
   User's concrete variant: **lowest index, with priority to vertices shared under both descents.**
   - **⚠ Do NOT kill this with the `⛔⛔ NO STABILIZER CHAIN` steer — it does not apply.** That steer
     forbids an *iso-invariant within-cell vertex pick* as the guarded object. Here (i) choosing a
     **cell** is canonical (`targetColour` transports), and (ii) `deepen`'s within-cell pick is already
     non-canonical and is legitimised downstream by the all-anchors quantification + the verification
     gate, not by canonicity of the pick. A *better* pick is therefore legal where a *canonical* one is
     not.
   - **The obstruction to state plainly:** "pick a single-orbit cell if one exists" is not a selector a
     refinement can compute — orbit membership is the thing being decided. The realistic form is
     **resolver-level, not selector-level**: try cells, keep one where the supply certifies
     transitivity (poly: ≤ n cells × one supply call). That is a `Select`-layer change, and it converts
     the question from "is the selector lucky" into "does *some* cell resolve", which is strictly
     weaker and matches `Select.NodeResolved`'s shape.
   - **⚠ The gap the user named and it is the load-bearing one:** no guarantee at the **root**, where
     there is no parent structure to exploit and an antagonistic input has the most freedom. Any
     attempt should attack the root case first — if it fails there, the route is over cheaply.
   - **⚠ Selector claims are convention-dependent** (§7.4, §8.3): anything proved here must be pinned
     against the concrete `chooseIdK` + `warmRefineVec` id numbering by Lean `#eval`, never by
     hand-reasoning the colour order (gotten wrong twice).

---

## 11. FILE INDEX

**Falsifier hunts** — `probe_cao_propagates.py` (the original 1-WL hit) · `probe_cao_bases.py`
(CFI over many bases) · `probe_cao_net.py` (the `net(G)` family + the `CFI[K4] ≅ net` identification) ·
`probe_cao_vtcover.py` (VT voltage covers) · `probe_2wl_sring.py` (the 66,888-set Schur-ring sweep) ·
`probe_2wl_chang.py` (T(8) + Chang) · `probe_2wl_multipede.py` (non-rigid multipedes).

**Instrumentation / calibration** — `probe_2wl_vacuity.py` (entry-ticket check, §7.2) ·
`probe_cao_2wl.py` (1-WL vs 2-WL side by side) · `probe_cao_net2wl.py` · `probe_cao_induction.py`
(fibre- and full-schurity at every descent node) · `probe_cao_coarse.py` (the discount in §6) ·
`probe_cao_union.py` (the `G ⊔ G` stress test) · `probe_cao_mechanism.py` (the `CFI[K4]` twisted-vs-
untwisted dissection: wire-pairs as a block system, and the `|Aut|` 192-vs-576 accident) ·
`probe_cao_mechanism2.py` (the coupling / fused-orbital measurements of §3) · `probe_cao_rounds.py` (§12.3: the round at which the extension separates fused orbitals — 3 for Shrikhande/Chang-2, 4 for `net(Z₄)`) ·
**★ `probe_cao_cause.py`** (§12.6 M3 — the cause-chain instrument: witness triangle types at the
separating round, birth-round trace, recursive explanation. **The uniform depth-3 chain**) ·
**`probe_cao_diameter.py`** (§12.3 convention box, term 1: Johnson recovers `Aut_v`-orbits at round
⌈diam/2⌉ — the construction refuting a constant bound on the *total* count) ·
**`probe_cao_diam_deficient.py`** (term 2: Shrikhande □ `C_m`, a **deficient** root at growing
diameter — the Doob-graph shape — fused orbitals separate at round **3** at diameters 3/4/5, removing
the diameter-2 confound) ·
**`probe_stall.py` / `probe_stall2.py` / `probe_stall3.py` / `probe_stall4.py`** (§0.0 limit 2 — at each
1-WL *manufactured* mixed cell, the minimum lookahead depth at which the force key separates the true
`Aut_v`-orbits; depth 1 = `lookaheadKey`'s own non-discrete branch. `probe_stall4.py` is the named VT
witness `Cay(Z₁₂⋊₅Z₂)` — ⚠ its connection-set search is slow (~2048 masks × `all_isos` at n = 24), so
run it detached per §9; **result recorded at `probe_stall4.out`**).
Shared machinery lives in `probe_cao_cleanroom.py` (§8.1); most files import it, so they are
`__main__`-guarded — keep them that way (§9).

**Provenance** — `probe_cao_provenance.py` (§8.1/§8.2).

**Lean (this doc's own results)** — `ChainDescent/CaoFibring.lean` (Steps 1–2, in `build.sh`; all 18 decls in `PublicTheoremIndex.md`) · `scratchpad/CaoFibringAxioms.lean` (the `#print axioms` check) · `scratchpad/ShrikhandeTinhoferProbe.lean` (the `chooseIdK` `#eval` cross-check of §8.3). The two Lean files sit **outside** the package root by design (§8.3).

**Parallel branch (1-WL VT hunt, succeeded)** — [`../scratchpad/HANDOFF_2wl.md`](../scratchpad/HANDOFF_2wl.md),
`probe_vt_witness.py`, `VTNotTinhoferProbe.lean`.

**Lean definitions this doc is about** — `ChainDescent/DeepenTinhofer.lean` (`CellSingleOrbit`,
`RigidObstructionAt`, `TinhoferPath`, `Tinhofer`), `ChainDescent/DeepenSupply.lean` (`chooseIdK`,
`step`), `ChainDescent/Refine.lean` (`warmRefineVec`, `keyOf`, `refineRound`).

---

## 12. ▶▶ PROOF PLAN for the live target (§2)

**Setup.** `X` = the 2-WL closure of `(G, χ_orb)`, whose fibres are the `K`-orbits (CAO), `K = Aut(G)`,
`v ∈ D`, and `X_v` = the coherent closure of `X` with `v` individualized. Target: the fibres of `X_v`
on `C` are the `K_v`-orbits on `C`.

### 12.1 Step 1 — the fibring lemma  ✅ **LANDED** (`ChainDescent/CaoFibring.lean`, in `build.sh`)

> `K` is transitive on `D` ⟹ the map `O ↦ {u ∈ C : (v,u) ∈ O}` is a bijection from the `K`-orbitals
> inside `D × C` onto the `K_v`-orbits on `C`.

Pure group theory (no WL, no graphs). It converts the target into orbital separation and is the
reason §3's mechanism table is exhaustive. Axiom-clean (`[propext, Classical.choice, Quot.sound]`),
no `sorry`, stated in the project's own `IsColAut` / `CellSingleOrbit` idiom so it composes with
`DeepenTinhofer.lean`:

| name | content |
|---|---|
| `isColAut_one` / `_mul` / `_inv` | `IsColAut adj χ` is a group (needed: the argument composes and inverts) |
| `SameOrbital` / `SameStabOrbit` | the 2-orbit relation and the point-stabilizer orbit relation, + refl/symm/trans for both |
| `sameStabOrbit_iff_sameOrbital_row` | on `v`'s row the two coincide — the statement Step 2 consumes |
| **`exists_row_transport`** | **every orbital meets `v`'s row**; the surjectivity half, and *the only place transitivity on `D` is used* |
| `sameStabOrbit_of_transports` | the row transport is well defined up to `K_v` |
| **`sameOrbital_iff_sameStabOrbit_of_transport`** | the row transport is a **complete invariant** of the orbital class ⟹ with `exists_row_transport`, the bijection. Needs **no** hypothesis — `CellSingleOrbit` is required only for *existence* of transports |

⚠ **Not** formalized: the size statement `|O| = |D| · |fibre|`. It needs `Finset` cardinality work and
nothing downstream uses it; the logical content Steps 2–3 consume is complete without it.

### 12.2 Step 2 — reduction to the FUSED classes  ✅ **LANDED** (same module, §4)

> If `X` already separates the orbitals inside `D × C`, the target holds automatically.

*Proof.* The `X`-colour of the pair `(v,u)` is an invariant `X_v` inherits, and by Step 1 its level
sets are exactly the `K_v`-orbits. ∎

Formalized for an arbitrary `IsColAut`-invariant pair colouring `f` (`PairInvariant`) — which is what
any 2-WL closure supplies, so the statement is independent of the refinement's details:
- `pairInvariant_eq_of_sameOrbital` — **soundness**: `f` is constant on orbitals, i.e. its classes
  are *unions* of orbitals. This is why refinement can never split an orbit.
- **`levelSet_iff_stabOrbit_of_separates`** — if `f` merely *separates the orbitals in `v`'s row*
  (`hsep`), then `u ↦ f v u` has level sets **exactly** the `K_v`-orbits.

⟹ preservation reduces to orbital separation **with no remainder**, and `hsep` is precisely the open
crux of §12.3 — now isolated as a single named hypothesis rather than diffused through the problem.

> ### ⚠ CORRECTION + ✅ FIX — Step 2 did not literally apply to the real object (`CaoRound.lean`, 2026-07-30)
> `levelSet_iff_stabOrbit_of_separates` asks for `PairInvariant adj χ f` = invariance under **all** of
> `IsColAut adj χ`. But the colouring the algorithm builds is the closure of the configuration with `v`
> **individualized**, which is invariant only under the **stabilizer of `v`**. So the landed Step 2 was
> a true theorem about an abstract `f` that the real closure did not satisfy.
> **Fixed and gated — `ChainDescent/CaoRound.lean` (11 theorems, axiom-clean):**
> - **`PairInvariantAt`** — invariance under `{σ ∈ IsColAut adj χ : σ v = v}`, exactly the group
>   `SameStabOrbit` is about; **`levelSet_iff_stabOrbit_of_separatesAt`** = Step 2 at it. Nothing is
>   lost — the `←` direction only ever used a `σ` fixing `v`, because it *comes from* `SameStabOrbit`.
> - **`pairInvariantAt_ext0`** (individualizing `v` keeps stabilizer-invariance) +
>   **`sig_congr`**/**`pairInvariantAt_roundBy`**/**`pairInvariantAt_iterRoundBy`** (a refinement round
>   preserves it — the content is that `σ` may be absorbed into the intermediate point, since it
>   permutes the universe) ⟹ **`step2_closure`**: start from any invariant root colouring,
>   individualize `v`, take **any** number of rounds — if the result separates the orbitals in `v`'s
>   row, its level sets there are exactly the `K_v`-orbits. **Step 2 now applies to the real object,
>   with `hsep` the only thing left.**

⟹ **all content is confined to `X`-classes that fuse ≥ 2 orbitals meeting `v`'s row.** This is not a
cosmetic reduction: in the completed Schur-ring sweep only **729 of 62,147** non-discrete instances
(≈ 1.2%) had a non-schurian root at all, and §6's other families are mostly schurian outright. Steps
1–2 therefore discharge the overwhelming majority of inputs with no new mathematics, and they extend
the free territory well beyond the two landed fragments (`cellsAreOrbits_of_discrete`,
`cellsAreOrbits_of_compl_card_le_two`).

### 12.3 Step 3 — the crux, and why it cannot be local

Remaining case: a fused class `R = O₁ ⊎ O₂ ⊎ …  ⊆ D × C` meeting `v`'s row in ≥ 2 orbitals. Show
`X_v` separates them.

> **⛔ THE ROUND-1 BARRIER — ✅ NOW MACHINE-CHECKED** (`CaoRound.round1_barrier`, axiom-clean; it was
> prose until 2026-07-30, and per the project's own steer a pinned statement nobody has tried to prove
> can be false — this one is not). Coherence is stated in the form that actually says it: a coherent
> colouring is a **fixpoint** of the round (`CaoRound.Coherent`). The proof splits the signature at the
> base point: the flags contribute the *same single term* to both sides, and the remaining multisets are
> equal by coherence + multiset cancellation. Its positive companion **`witness_ne_base`** is the other
> half of what M3 measures: if a round *does* separate `(v,u)` from `(v,w)` while they share a colour,
> the difference provably lives in the intermediate points **`x ≠ v`** — so *the marking must leave `v`
> and come back* is a theorem, not an observation. The round-1
> refinement of the pair `(v,u)` is the multiset over `x` of `(col(v,x), col(x,u))`, and by
> **coherence** that count is the intersection number `p^k_{ij}` with `k = X`-class`(v,u)` —
> *identical for every `u` in the same `X`-class*. **The base point learns nothing directly.**

So the marking must travel: a far pair `(a,b)` acquires its **triangle type**
`(X`-class`(a,v), X`-class`(v,b))`, that splits the far classes, and only the feedback from those
splits reaches `(v,u)`. **Measured** (`probe_cao_rounds.py`): separation first occurs at
**round 3** (Shrikhande `[3,6]`; Chang-2 `[4,4]`, both classes) and **round 4** (`net(Z₄)`, both
classes) — never earlier, exactly as the barrier predicts. **Any proof is a statement about this
feedback loop, not about the base point.**

> ### ⚠⚠ ROUND-COUNT CONVENTION — the "3/3/4" above is a CONFLATED figure (corrected 2026-07-30)
> `probe_cao_rounds.py` counts from the **raw** colouring, so its figure is the sum of two terms
> that behave completely differently:
>
> **`rounds_total = rounds_to_BUILD X  +  rounds_of_the_EXTENSION from X`**
>
> - **Term 1 grows with DIAMETER and is unbounded** — refinement carries information ~2 hops per
>   round. Measured (`probe_cao_diameter.py`): Johnson `J(m,k)` recovers its `Aut_v`-orbits at round
>   **⌈diam/2⌉** exactly — `J(6,2)/J(6,3)/J(8,4)/J(10,5)` → **1/2/2/3** at diameters 2/3/4/5. **So no
>   constant bounds `rounds_total`, by construction** (user, 2026-07-30: any VT family of growing
>   diameter does it).
> - **Term 2 is the one §12.3 and M2 are about**, and it is measured **constant 3** across every
>   deficient root on record — including at growing diameter (`probe_cao_diam_deficient.py`):
>   Shrikhande □ `C₃`/`C₅`/`C₇`, diameters 3/4/5, **all fused classes separate at round 3**, while
>   term 1 goes 3/3/3 and 4 at diameter 6.
>
> ⚠ **The old figures were also CONFOUNDED**: all three original deficient roots (Shrikhande,
> `net(Z₄)`, Chang-2) have **diameter 2**, so the count had no room to vary. The □`C_m` family
> removes that confound — and it is the **Doob-graph shape** (distance-regular, *not*
> distance-transitive), so the deficiency is real at every diameter; it simply stays localized in the
> Shrikhande factor, so separating it never needs long-range information.
> ⟹ **State which term you mean.** A bound on term 1 is refuted; a bound on term 2 is live and now
> has evidence at diameter > 2.

### 12.4 Candidate resolutions, ranked

| route | content | gap |
|---|---|---|
| **R1 triangle-type / `v`-profile** (most promising — it is what the measurement points at) | define a pair's `v`-profile `(X`-class`(a,v), X`-class`(v,b))`; the target becomes *two orbitals in one `X`-class have different `v`-profile distributions* | why must they differ? This is where the CAO hypothesis has to bite, and it is the one place it plausibly can — CAO is what forces the fibres to be full orbits, hence the profiles to be group-theoretically meaningful |
| **R2 separability** (the standard tool, and the right Lean pin) | if `X` is *separable* — every algebraic isomorphism is induced by a combinatorial one — the extension is schurian and the target follows | separability is **not** implied by fibre-schurity; it must be proved per class. ⟹ **carry it as a per-family certificate**, matching the project's existing obligation pattern |
| **R3 classification ladder** | free for schurian roots (§12.2) · S-rings over cyclic groups (schurian by classification) · families with known classical groups (forms graphs, Cameron — orbitals computable) · general = open | each rung is a separate piece of work; mirrors `KEY_scoping`'s tie-group ladder |
| **R4 ⛔ excluded** | coset transfer (circular, §4.1) · pure counting (structure constants only, §4.2) · bounded depth (not union-stable, §4.3) · full-schurity invariant (killed by `G ⊔ G`, §4.4) | — |

### 12.5 Honest assessment

Steps 1–2 are real, free, and formalizable now, and they reduce the problem to ≈1% of instances.
**Step 3 is a genuine open question of algebraic combinatorics** (schurity of one-point extensions
under a fibre hypothesis), not a lemma to be discharged by effort. The practical route is therefore
R2 + R3: pin the crux as a per-family certificate and prove it for the families that matter.

### 12.6 ▶▶ THE PLAN for route (B) — the mechanism track (2026-07-30, user-directed)

**What "the mechanism" means, and how much of it is already settled.** The question is *how
individualizing `v` changes the other cells' orbits, and whether 2-WL's classes coincide with that
change*. **The first half is DONE and formalized**: §3's fibring — individualizing `v ∈ D` changes
`C`'s orbits **only** by fibring `C` over the `K`-orbitals inside `D × C`, and **nothing else can
happen** (`CaoFibring.exists_row_transport` +
`sameOrbital_iff_sameStabOrbit_of_transport`). So the whole remaining question is the **second** half:

> **when does a 2-WL class properly contain ≥ 2 orbitals meeting `v`'s row?** (= `hsep` = §12.3)

**The organising fact for the plan.** The target is an *induction along the descent*, so its step is
applied where the input **arose from individualization** — a strictly wider class than "orbit
partitions of plain graphs", which is the only class ever swept. Every step below is chosen against
that.

| # | step | cost | what it DECIDES |
|---|---|---|---|
| **M1** | **Run the step on its real input class, at a population that pays the entry ticket** (= the old §12.6(1)/§10.2, but *fixed* — see the ⚠ below) | hours | whether "no 2-WL counterexample" survives a population where §7.2's ticket is genuinely paid. **If it falls, route (B) ends** and §10.5's selector route (A) becomes the only path |
| **M2** | **Is the EXTENSION round count bounded?** ⚠ **RESTATED 2026-07-30** — see §12.3's convention box. The *total* count is **refuted** by any VT family of growing diameter (Johnson, measured ⌈diam/2⌉); only **term 2**, the rounds *after* coherent `X`, is the live quantity. Measured **constant 3** on every deficient root incl. Shrikhande □ `C₃`/`C₅`/`C₇` at diameters 3/4/5 | hours | pursue a **bounded-extension-round** theorem, or drop it. Still the only shape that is *both* union-stable (unlike bounded depth, §4.3) *and* formalizable. **▶ The falsifier to hunt: a deficiency that is inherently LONG-RANGE** — in a Cartesian product the fusion stays factor-local, which is why □`C_m` does not refute it |
| **M3** | **★ Instrument the FEEDBACK LOOP, not the round number** — the actual mechanism ask, and new work | days | supplies R1's missing *"why must the `v`-profile distributions differ?"* |
| **M4** | **The coupling construction** (§10.3) — build an object with group-change and deficiency at the **same** cell pair | open-ended | kills the track cheaply, or its principled failure *is* the mechanism. Run **in parallel with M3** — same question from opposite sides |
| **M5** | **Lean: reuse the CC substrate that already exists** (see below — it is not referenced anywhere in this plan and should be) | days | turns R2's "carry a per-family certificate" from a plan into a deliverable |
| **M6** | the group-identification bridge (`IsColAut` of a refined colouring ↔ the point stabilizer) | hours | needed by **any** consumer of `CaoFibring`, at either WL level |

**⚠ M1 — the measurement is not what §10.2 says it is.** `probe_cao_induction.py`'s
sharp-Cayley section iterates **8 groups of order 16 only** and `break`s at `hits > 3` per group ⟹ at
most ~24 sharp inputs, **not** "the 729 non-schurian S-rings" (which came from 38 groups of orders
8–32). Remove the cap, extend to the full population, and **log what was skipped** (§9's discipline —
a silent cap reads as full coverage). Until then the "729" figure describes the *hunt*, not the
*instrumentation*.

**★ M3 — what to actually record.** §12.3's round-1 barrier is proved: coherence makes the round-1
count of `(v,u)` an intersection number, identical across the class, so **the base point learns
nothing directly**; the marking must travel — a far pair `(a,b)` acquires its triangle type
`(X`-class`(a,v), X`-class`(v,b))`, that splits far classes, and only their feedback reaches `(v,u)`.
Measured round 3 / 3 / 4 confirms it. **Nobody has measured *which* far split does the work.** Per
round, record: (a) how many orbital-fusions remain; (b) which triangle types were newly created;
(c) the **minimal cause chain** — the specific far class whose split, on removal, leaves the target
pair fused. Output is the mechanism *in the form a proof consumes*: "the marking travels via `X`, and
`X` is forced to exist because `Y`". This is the one step that attacks the crux rather than
characterising it.

#### ★★ M3 — FIRST RESULT (2026-07-30, `probe_cao_cause.py`): the cause chain is UNIFORM

Built and run on every deficient root on record (Shrikhande, `net(Z₄)`, Chang-2 — **7 fused classes**,
all counted from the coherent `X`). The instrument extracts, at the round `r*` where `(v,u)` and
`(v,w)` first separate, the **triangle types** `(c1, c2) = (class of (v,x), class of (x,u))` whose
multiplicity differs — literally §12.3's object — then traces each witness class to its **birth
round** and recursively explains the later-born one. **Every chain has the same shape and the same
depth 3:**

```
r0   v's flag           — the only new information in the extension
r1   FAR classes split  — witness = a triangle type of two r0 classes, ≥1 of them v-ROW / v-COL
r2   deeper FAR split   — witness = a triangle type of two r1 FAR classes
r3   THE TARGET SEPARATES — witness = (v-ROW class born r0,  FAR class born r2)
```

**Three things this pins down, and they are what a proof needs.**
1. **The barrier is confirmed constructively, not just by counting**: the target pair is never
   separated by anything on `v`'s row alone — the returning half of every final witness is a **far**
   class, and one that did not exist before round 2.
2. **The final witness is always the SAME SHAPE** — `(v-ROW born r0, FAR born r2)`. Never two far
   classes, never two `v`-row classes. So the feedback returns through **exactly one** twice-refined
   far class, and R1's *"two orbitals in one `X`-class have different `v`-profile distributions"* is
   the right statement: the profile that differs is a count of one triangle type.
3. **The chain always grounds at `v`'s flag** in 3 steps, on every witness, at every diameter tested
   (§12.3's convention box: Shrikhande □ `C_m` also separates at round 3, diameters 3–5).

⟹ **The target for R1 is now concrete:** show that the round-2 far class `c2` *must* split, and that
its split *must* register unequally on the two fibres. The first half is caused by round-1 splits
that are directly caused by `v`'s flag — a two-step chain, not an unbounded induction. ⚠ Still open,
and this is measurement not proof: 7 witnesses, all with `|fibres| ∈ {[3,6], [4,4], [6,12], [1,2]}`.
**▶ Next for M3:** (a) the **ablation** — merge `c2` back and confirm the target stays fused (proves
minimality rather than inferring it); (b) run the instrument over M1's population to see whether
depth 3 and the `(r0 v-ROW, r2 FAR)` witness shape survive a real population, or are an artifact of
the diameter-2 SRG witnesses.

**★ M5 — the substrate is already built and gated, and this plan never mentions it.**
`ChainDescent/CoherentConfig.lean` (in `build.sh`, axiom-clean) carries: **`IsPointExtension X T Y`**
(the coarsest coherent fission with `T` singled out — *the object of Step 3*), the **construction**
`pointExtension` via `pairStep`/`pairIter`/`stableSetoid` with the universal property discharged
(`isPointExtension_pointExtension`, `exists_isPointExtension`, `isPointExtension_unique`),
`AlgIso`/`AlgIso.InducedBy`, **`Separable`/`SeparablePointed`**, **`ExtensionSeparable`** (= R2's
statement, verbatim), and **`Theorem41Statement`** — Ponomarenko arXiv:2006.13592 Thm 4.1 as a
citation-carrier, whose hypotheses a probe found **hold precisely on the one-point extension and fail
on the residue itself**. §12.4 ranks R2 as "must be proved per class" without noting that a cited
route to it is already in-build. ⚠ Two honest gaps before it closes anything: **`Separable ⟹
schurian`** (standard, must be cited or proved — it is what converts R2 into the target) and the
**D0/T4 modelling seam** (`CoherentConfig` is abstract; connecting it to graphs is the faithfulness
obligation W2 already tracks).

**▶ Order:** M1 + M2 first (cheap, and M1 can end the track). Then M3 and M4 in parallel — they are
the same question from both sides. M5 is the Lean deliverable and can start once M1 has not falsified.
M6 anytime.

**▶ If 2-WL falls (M1 turns up a counterexample).** Re-run M1/M2 at **3-WL** before concluding
anything: the same measurements decide whether this is a ladder that continues or whether refiner
strength cannot fix the design at all — and only the second warrants the structural change. ⚠ Note
§0.0's negative branch: a "fails at every `k`" witness has **no candidate** today, because §5's
self-limiting lesson excludes every standard unbounded-WL family from the CAO hypothesis.

> *(The former §12.6, "the two measurements that would most inform Step 3", is absorbed into §12.6's
> **M1** and **M2** above — with the correction that the sharp-Cayley instrumentation does **not**
> currently cover the 729. Old cross-references to "§12.6(1)/(2)" resolve to M1/M2.)*
