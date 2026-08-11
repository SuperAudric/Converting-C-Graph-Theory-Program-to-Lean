# The splitter — a sound negative from matched descents

> ## ▶▶ STATUS (2026-08-11) — a DIAGNOSIS, a THEOREM, and a MEASURED probe. Nothing is built in Lean.
>
> **What this is.** The rigid-side complement to consume, built from the *same* descent
> computation that [`chain-descent-divergence-lift.md`](./chain-descent-divergence-lift.md) measured
> and refuted — used in the **opposite soundness direction**. That inversion is the whole content:
> the failure modes that kill a symmetry *detector* are free for a *splitter*.
>
> **The theorem (§1).** The matched-descent relation `~_d` **contains** `SameOrbit`, unconditionally.
> Hence `¬(u ~_d w) ⟹ u,w in different orbits` — a sound negative — and `~_d`'s classes are a sound
> **coarsening** of the orbit partition. **Over-merging is harmless here; only over-splitting is fatal,
> and the exhaustive relation provably cannot over-split.**
>
> **Measured (§2, `scratchpad/probe_holonomy_split.py` → `.out`, 7 witnesses / 9 root cells):**
> * **S — 0 soundness violations**, at `d = 1, 2`, for both the exhaustive and the certified-path form.
> * ★ **`~_2` computes the Chang-2 orbit partition EXACTLY** (`[4,24]`), the habitat that decided
>   against the divergence lift. **This is the first non-vacuous equivariant splitter measured in this
>   area** — contrast `Linked`, vacuous on all 9 of its witnesses.
> * ★★ **The certified-path collapse is EXACT: `C_d = ~_d` on 18/18 rows.** Collapsing a
>   single-orbit level to one pick loses nothing — measured, not assumed.
> * ★★ **The CAO hypothesis is LOAD-BEARING and the price is measured.** The cheap single-path read
>   `^_d` **over-splits on 4 of 7 witnesses** (27–60 same-orbit pairs separated; on CFI(K4)-twisted it
>   splits a genuine 12-orbit into `[6,6]`). Where no level is mixed it is sound and costs `|C|·d`.
> * ⚠ **Only TWO posed instances.** Seven of the nine cells are single orbits — controls where firing
>   is *forbidden* (and correctly does not). One posed instance solved exactly, one
>   (`rook4x4 ⊔ Shrikhande`, orbits `[16,16]`) **not** solved at `d ≤ 2`. Read §2.1 before quoting
>   strength.
>
> **What it depends on.** Exactly one thing: **that a single pick per level suffices**, i.e. 2-WL CAO
> propagation, or a back-trace with a failsafe. §4 states the two discharge routes and prices the
> failsafe. ⛔ Until then the cheap form is **unsound**, and the probe says by how much.
>
> **How to use this doc (user steer, 2026-08-11).** It is written to be **harvested**: §5's table marks
> each piece *usable by the rigid route today* or *blocked on the grounding*. If the grounding lands,
> §3 **becomes** the rigid route rather than feeding it.
>
> **Read first:** [`chain-descent-force-refinement-channel.md`](./chain-descent-force-refinement-channel.md)
> (the delivery channel and why `keepMin` cannot carry this) and `chain-descent-divergence-lift.md` §3
> (the governing principle, which this doc re-uses unchanged).

---

## 1. The inversion — the load-bearing theorem

Fix a graph, a colouring `χ`, a cell `C`. A **descent from `u`** individualizes `u`, refines, then makes
`d` further picks. Its **footprint** is the sequence of `(target cell id, canonical 1-WL signature)`
produced along the way — every entry canonical, no vertex names.

> ### `u ~_d w  :=  the depth-d footprint SETS of u and w intersect`

**Theorem (soundness).** `SameOrbit ⊆ ~_d`, for every `d`, with no hypothesis.

*Proof.* Let `σ` be a colour-automorphism with `σu = w`. For any descent `p` from `u`, the image `σ(p)`
is a legal descent from `w`, and signatures are permutation-invariant, so the two footprints are equal.
Hence the footprint sets coincide, a fortiori intersect. ∎

**Three consequences, and they are the design.**

1. **`¬(u ~_d w)` is a sound "different orbits" verdict** — the deliverable the rigid side has never had.
2. **`~_d`'s classes refine nothing they shouldn't.** They are *coarser* than the orbit partition, so
   using them to split a cell can never split a true orbit. Iso-invariance is not an obligation to be
   discharged later; it is the direction the error runs.
3. ★★ **`NOAUT` is free.** Divergence-lift §4.3 — a descent reaching a discrete leaf with a matching
   comparison whose induced map is *not* an automorphism — is fatal for a symmetry detector (it
   over-merges) and **harmless here** (over-merging is the safe direction). Likewise §4.1's false
   positives and §4.2's direction flip are statements about an *ordered* read; `~_d` is unordered.

⚠ **What is NOT free: truncation.** `~_d` is sound because the footprint set is exhaustive over picks.
Any restriction of the pick set *shrinks* the footprint sets, which can only *destroy* intersections —
i.e. **over-split**. Every cheapening of this relation is a soundness risk, and §4 is about the one
cheapening that is provably safe.

## 2. What was measured

`scratchpad/probe_holonomy_split.py` → `probe_holonomy_split.out`. Clean-room: own 1-WL, own exact
colour-preserving automorphism enumeration (no `probe_orbit_oracle` — it is proven wrong, it errs by
merging). Three forms per cell:

| form | picks per level | cost | sound? |
|---|---|---|---|
| `~_d` | **all** (exhaustive) | `|C|^{d+1}` | ✅ theorem §1 |
| `C_d` | all at **mixed** levels, one at certified single-orbit levels | `|C| · Π_{mixed} |cell|` | ✅ (the collapse is exact — see below) |
| `^_d` | **one** (min index) at every level | `|C| · d` | ⛔ **not** a priori — this is what CAO buys |

| witness (root cell) | true orbits | `~_2` | `C_2` | `^_2` over-splits | branch levels |
|---|---|---|---|---|---|
| **Chang-2**, n=28 | `[4, 24]` | **`[4,24]` exact** | `= ~_2`, 732 refines | **44–45 pairs** | 64 |
| `rook4x4 ⊔ Shrikhande`, n=32 | `[16,16]` | `[32]` (vacuous) | `= ~_2` | 0 | 16 |
| Shrikhande | `[16]` | `[16]` ✅ | `= ~_2` | **60 pairs** | 64 |
| net(Z₄) cell 1 | `[12]` | `[12]` ✅ | `= ~_2` | **27 pairs** | 12 |
| net(Z₂×Z₂), both cells | `[16]`,`[12]` | ✅ | `= ~_2`, **24 refines** | 0 | **0** |
| CFI(K₄) untwisted, both cells | `[16]`,`[12]` | ✅ | `= ~_2`, **24 refines** | 0 | **0** |
| CFI(K₄) twisted cell 1 | `[12]` | `[12]` ✅ | `= ~_2` | **36 pairs** (`[6,6]`) | 12 |

**Four readings.**

- **S.** Zero soundness violations anywhere, for `~_d` and `C_d`, at both depths. The §1 theorem is not
  doing anything the code disagrees with.
- ★★ **The collapse is exact — `C_d = ~_d` on every one of the 18 rows.** This is the design's central
  claim, and it is now measured rather than assumed: *at a level whose cell is a single orbit, taking
  one pick yields the same footprint set as taking all of them.*
- ★★ **The cost is linear exactly when no level is mixed.** `branchlevels = 0 ⟹ refines = |C|·d`
  (net(Z₂×Z₂) cell 1: `d=1 → 12`, `d=2 → 24`, `|C| = 12`). That is the CAO regime, and it is the whole
  cost argument: `cost = |C| · Π over MIXED levels of |cell|`, so **the exponent is the number of mixed
  levels on the path, and nothing else.**
- ★★ **`^_d`'s over-splits track mixed levels**, exactly as divergence-lift §3 predicts — every witness
  with `branchlevels = 0` has `^_d` sound; three of the four with `branchlevels > 0` have it unsound.
  ⟹ **§3's principle is the correct governing statement in the split direction too**, and the CAO
  hypothesis is precisely the claim that the mixed-level count is 0 below the root.

### 2.1 ⚠ Vacuity discipline — read before quoting strength

Divergence-lift §6 records **three probe generations that measured nothing**. Applying its test here:
seven of the nine cells are **single orbits**, so they pose no question — they are *controls* where
firing is forbidden, and they are valuable only as soundness evidence. **There are two posed
instances**: Chang-2 (solved exactly at `d = 2`) and `rook4x4 ⊔ Shrikhande` (**not** solved at `d ≤ 2` —
`~_2` stays `[32]`). One-for-two is a beachhead, not a result.

⚠ The union habitat is the honest limit case: separating those `[16,16]` blocks requires telling two
1-WL-equivalent non-isomorphic SRGs apart, which the footprint cannot do at depth 2. **Depth is the
resource, and depth is what the grounding pays for.**

## 3. The design

Four layers. Only L3 is new engineering; L0–L2 are assembly of things the project already has.

| | piece | content |
|---|---|---|
| **L0** | the descent produces footprints | already what `deepenSupply` / the C# `HarvestTwists` compute (replay a deepening, compare footprints) |
| **L1** | **certify levels with consume** — a level whose cell consume proves transitive is collapsed to one pick | poly (one consume call per level), stall-free, and **equivariant by construction**: every collapsed level carries a *verified* automorphism, and verification is labelling-independent ⟹ **this dodges R1** |
| **L2** | at an uncertified level, **branch** (pay `|cell|`) or **solve** — see §6 | the cost exponent lives here and nowhere else |
| **L3** | deliver the `~`-partition through **`RigidRefine.refineBy`**, never through `keepMin` | `refEquivariant_refineBy` is proved and needs `ReadEquivariant read` **alone** |

**Delivery, and the naming wall.** `~` gives a *partition* of the cell, not a colouring. To enter `χ`
the blocks must be named by invariants (block size; then 1-WL on the quotient). ⚠ The recorded wall —
*naming a class without an order* — still bites, but here it bites **softly**: blocks with identical
invariants stay merged, which is coarser and still sound. Contrast `readAggB`, where the ≤ 8-value cap
makes `AggFaithfulB` **provably false** at any cell with ≥ 9 pairwise non-automorphic branches. A soft
loss of strength is a different object from a proved impossibility. (On the one posed instance the
blocks are `[4,24]` — distinct sizes, so it delivers.)

**⛔ The `≤ 1` bar is not negotiable.** `Select.lean:22-23`'s fan-out `≤ 1` is what buys `②`'s single
path of `≤ n+1` nodes. The split must arrive as *refinement* — cell becomes cells, each handed to
consume — never as `k > 1` survivors. Split-then-consume keeps fan-out at 1; a `k`-way commit restores
the tree and turns `②` back into a product.

**Costs to price up front** (same list as the force-channel doc §3): `Refiner n` is cost-carrying and
`②` is re-billed at `|C|·d` refines per probed cell; a new refiner is a **new `Reaches`**, so `HandledSC`,
`③`'s population and the `Tinhofer` results do not transfer for free (the three-layer inheritance trap);
and ⛔ trap #1 — never a bare `… → Colouring n`, go through `Refine.ColData` + rfl-twins.

## 4. ▶▶ THE GROUNDING — what exactly is owed, and the two ways to pay it

The design is sound at `~_d` and poly at `^_d`. **The gap between them is one statement:**

> **(G) One pick per level suffices** — the footprint set is invariant under which vertex is picked at
> each level below the root.

`(G)` is *exactly* 2-WL CAO propagation restricted to what this design consumes, and the probe shows it
is not decorative: without it, `^_2` separates 27–60 same-orbit pairs on four of seven witnesses.

**Route A — prove it.** 2-WL CAO propagation is a conjecture with **no counterexample found in this
project, including after literature passes** (`chain-descent-cao-propagation.md`; ⚠ its "known false"
wording is *not* a located citation — the closure stands, the refutation wording does not). ⚠ Carried as
a hypothesis it is a second carried obligation on the object, alongside `ForcingModel.bridge`. ⚠⚠ And it
is a **2-WL** statement while the Lean `Tinhofer`/`CellSingleOrbit` are **1-WL**: 1-WL cells are unions
of 2-WL cells, so *nothing transfers* — this needs a 2-WL refiner and its own `Reaches`.

**Route B — back-trace with a failsafe.** Do not assume `(G)`; **detect** its failure. L1 certifies what
it can; at the first uncertified level, either branch (paying `|cell|`) or stop and report the cell as
the located mixed cell. This is the **failsafe for "no parent mixed cell"**: the design never asserts a
split it has not paid for, and the flag stays honest. Price, measured: `cost = |C| · Π over mixed levels
|cell|` — poly iff the mixed-level count is bounded. ⚠ Multipedes are the specification here, not a
warning: Neuen–Schweitzer says no IR-invariant pruning bounds that count, so **Route B alone cannot be
complete**, and the non-IR content must come from §6's solve.

★ **The two routes are not exclusive.** Route B is buildable *now* and its measurements are exactly the
evidence Route A needs: *how many mixed levels actually occur on the families of interest.*

## 5. ▶ WHAT THE RIGID ROUTE CAN DRAW TODAY

| piece | usable now? | why |
|---|---|---|
| **§1's soundness theorem** (`SameOrbit ⊆ ~_d`) | ✅ **yes, unconditionally** | no CAO, no 2-WL, no extraction. It is the missing *negative* certificate the rigid side lacks, and it is a five-line proof over existing definitions |
| **`~`-classes as a `refineBy` read** | ✅ yes, at `~_d` for fixed `d` | poly for fixed `d`, equivariant, no order chosen. **Not capped at 8 values** and **not indexed by a `2^β` frame family** — it evades both recorded obstructions of `readAgg`/`readAggB` |
| **L1, the consume-certified collapse** | ✅ yes | poly, stall-free, equivariant by construction ⟹ **dodges R1**, which is why `deepenSupply` sits outside `Publication` |
| **the cost identity** `cost = |C| · Π_{mixed} |cell|` | ✅ yes | it converts "is this poly?" into one measurable integer per family |
| **`^_d`, the cheap single-path read** | ⛔ **no** | over-splits on 4/7 witnesses. Blocked on §4's grounding |
| **the whole design as a route** | ⛔ not yet | becomes the rigid route if `(G)` lands; until then it is a source of pieces |

★ **Where it is strictly better than the current rigid route**, in the record's own terms:
`readAggB` is `encode ∘ sort` of a read valued in `{0,1,2}` ⟹ ≤ 8 values on any input ⟹ `AggFaithfulB`
is **provably false** at every rigid multipede cell of interest, and `RigidRefine`'s own banner concludes
*"richness has to come from the READ, not the frame set"*. A partition is not an encoded read and has no
such cap. And `readAgg` is correct but exponential because a `FramesEquivariant` set of full orders is
closed under a free gauge action (`|frames| ≥ 2^β`); `~_d` aggregates over **descents from the cell**,
an equivariant index set of poly size. **That is the structural difference — not a repaint.**

★ **Where it is the same wall:** both need faithfulness of whatever is extracted. See §6.

## 6. ▶ THE SOLVE — what "solvable" actually gates (correcting an earlier framing)

Recorded here because the natural reading is wrong. *"Pass through a mixed level iff the residual is
abelian/solvable"* mis-locates the gate. From
[`chain-descent-w2-solvability-route.md`](./chain-descent-w2-solvability-route.md):

1. **Flatness** — free after refinement (`localExchange_of_equitable`).
2. **Recovery / faithfulness** — the gauge `Γ` must be *extracted from the graph* as an explicit system.
   This is **R-b** (`faithful` ≈ `ForcingModel.bridge`) at F₂ and **L4** per derived layer beyond it.
   Carried, unbuilt. ★ **This is the gate.**
3. **Only then does solvability enter, and it is nearly free**: recovered `Γ ≤ G₀^m` for a fixed local
   gadget group forces `Γ ∈ Γ_{μ(G₀)}` (`μ = 2` for CFI/Lichter) ⟹ genuine Luks poly, not a hedge.
   `GaugeLayer` L1–L3 + `of_solvable_tower` reduce solvable ⟹ a bounded tower of per-coordinate linear
   solves; the F₂/abelian case is **built** (`kerF2`, `rigid_unique_solve`).
4. **The wall** is a *growing non-solvable* `Γ` (Aₙ/PSL) — zero constructible witnesses, a separate
   conjecture, not implied by L4.

⟹ **Solvability governs the cost of computing `Γ`-orbits once `Γ` is in hand; it does not let you cross
a mixed level.** And note `GaugeComplex` already *names* this doc's deliverable:
`HolonomyNontrivial := LocallyFlat ∧ ¬SameOrbit` with `holonomyNontrivial_iff_diff_orbit` — ⚠ read that
honestly, it is a **definitional restatement**, not a decision procedure. The content is
`GaugeBridge.holonomy_iff_gauge`, and it carries `faithful`.

★ **The connection worth building.** Both existing rigid routes stall on *getting the system out of the
graph*. A descent-with-replay that harvests footprints **is a measurement of the forcing relation** —
which is what `deepenSupply` and the C# `HarvestTwists` already do. So this design is best positioned as
**constructive content for R-b**, not as a competitor to the gauge track.

⚠ **Direction of error, and it differs by layer.** `~_d` errs by *over-merging* (safe, §1). A **recovered
`Γ` that is too small** errs by *over-splitting* (`Γ_rec ⊊ Γ_true ⟹ finer orbits ⟹ a true orbit split`),
which is **fatal**. Consume's errors are caught by an `O(n²)` edge check; a recovered gauge's are caught
by nothing. **Faithfulness is not a technicality here — it is the missing verifier.**

## 7. ⛔ Traps and falsifiers

* ⛔ **Do not truncate the pick set** to cheapen `~_d` (except by L1's certified collapse, which is
  measured exact). Every other truncation over-splits — that is `^_d`, and the probe quantifies it.
* ⛔ **Do not read a direction off this.** The divergence-lift refutations are all about an ordered read;
  re-introducing one re-imports every one of them.
* ⛔ **Do not widen success to `k > 1` survivors** to "use" the partition. `Select.lean:22-23`.
* ⚠ **Apply the standing union filter** to anything added here: test `G ⊔ G` first. It has already killed
  two routes in one call, and the union habitat is where `~_2` is currently vacuous.
* ⚠ **Root-only is not a pass.** Falsifiers live at reached nodes; the probe measures the root cell and
  the certified-depth walk only. Extending `~_d` to every reached node is owed before any claim.
* ⚠ **Rigid multipedes are not automatically a 1-WL-blind habitat** — the recorded probe shows 1-WL
  *discretizing* one at n = 68. Check the witness is not degenerate before citing it.
* **Falsified if:** `~_d` stays vacuous on a widened posed-instance set (currently 1 of 2); or the
  certified collapse `C_d = ~_d` fails on any witness (it would refute divergence-lift §3 in the split
  direction); or the mixed-level count is unbounded on every family of interest, which makes Route B
  useless and puts the whole weight on Route A.

## 8. Files

| file | what it does |
|---|---|
| `scratchpad/probe_holonomy_split.py` | this doc's measurements: `~_d` / `C_d` / `^_d`, soundness, non-vacuity, exactness, over-split counts, certified depth. Clean-room; reusable — point it at a new witness and it answers in seconds |
| `scratchpad/probe_holonomy_split.out` | the run of 2026-08-11, 7 witnesses / 9 root cells |
| `scratchpad/probe_dir_flip.py` | the verified helpers it imports (`refine`, `indiv`, `all_auts`, `orbits_of`, `net`, `shrikhande`, `t8_chang`, `disjoint`) |
| `scratchpad/probe_w2_asymbase.py` | the descent walk + edge-verified gauge, for the reached-node extension |
