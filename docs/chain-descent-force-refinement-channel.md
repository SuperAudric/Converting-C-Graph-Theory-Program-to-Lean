# FORCE HAS NO REFINEMENT CHANNEL — the missing foundation under W2

> # ⛔⛔⛔ 2026-08-10 (later) — **§6'S PROBE RAN. METHOD 2 IS REFUTED AT THE BUILT EXTRACTION.**
> `scratchpad/probe_w2_linked.py` → **`probe_w2_linked.out`**, 9 witnesses. Read this before §4/§6.
>
> **The identity that makes `Linked` cheap also predicts it, and both were verified.** `H` symmetric
> ⟹ `rowspace H = ker(H)^⊥`, so
> **`Linked u v ⟺ x_u = x_v for every x ∈ ker H`** — *"the kernel cannot tell `u` from `v`"*. Checked
> against independent Gaussian-elimination span membership on `CFI(K₄)`, every pair.
>
> ⟹ **Two degenerate regimes and nothing in between:**
> | regime | witness | `dim ker_F₂(adj)` | `Linked` | classes |
> |---|---|---|---|---|
> | rigid | `G8` | **0** | rowspace is everything ⟹ the **TOTAL** relation | **1** |
> | gauged | CFI(K₄) · CFI(Frucht) · CFI(cubic m=8) · `mp7` · MIXED · circ(5) · rand multipede | 12 · 28 · 20 · 22 · 14 · 12 · 16 | essentially **EQUALITY** | 28/28 · 84/84 · 56/56 · 42/42 · 24/30 · 22/30 · 26/34 |
>
> ⟹ ⛔ **Every legal read is vacuous, measured on all 9 witnesses.** Class size (the cheapest
> σ-invariant of a class) and the **steelman** — 1-WL on the 2-relation `adj ∪ Linked`, strictly
> stronger and still order-free — each leave the non-singleton cells **`k → k` with identical sizes**,
> on every witness. Not one cell split.
>
> ⛔⛔ **And the tempting fix is the old trap wearing a new costume.** Reading the kernel *signature*
> `sig v := (x¹_v,…,x^k_v)` over a basis discretizes everything — including **`CFI(K₄)`, where `Aut`
> merges all 16 gadget vertices into ONE block**. §8's falsifier #2 fired, and the probe's own
> read-equivariance check localizes it: **144 / 1152 / 768 / 6912 direct violations** of
> `read (σ·) (σv) = read v` against **edge-verified** gauge automorphisms. Choosing a kernel basis
> **is** choosing a pivot/column order — *`OrdEquivariant` is unsatisfiable* (S3 correction 1), again.
> ⟹ *"the row space is gauge-blind"* is true and **not enough**: gauge-blindness was never the
> obstacle; **naming a class without an order** is, and a relation does not dodge it — it only moves
> the order from the labelling to the *class indexing*.
>
> **▶ WHAT SURVIVES.** §1's diagnosis (force has no refinement channel) is **untouched** — it was
> verified at source and is independent of §4. §3's **Method 1 is untouched as a channel** but now has
> **no reader to put through it**: `Linked` was the proposed `read`, and it is empty. §5's reduction
> and ceiling are untouched. ⟹ **Method 1 is a mechanism in search of an invariant; finding the
> invariant is the whole problem, and it is the same one S3 bottoms out on (`AggFaithfulB`,
> per-family).** ⛔ Do not build the refiner plumbing until a reader is measured to split something.
>
> ★ **AND ONE THING §1 UNDERSTATES, checked at source** ([Select.lean:22-23](../GraphCanonizationProofs/ChainDescent/Select.lean#L22)):
> the `≤ 1` in `NodeResolvedC` is **not an oversight — it is what buys `②`.** *"Fan-out `≤ 1` **by
> construction** — the single path of `≤ n+1` nodes"* is the reason `cost ≤ 69·(n+1)^13` holds with no
> flag disjunct. ⟹ ⛔ **Never "fix" the missing partial-success rung by letting a node commit to `k > 1`
> survivors** — that restores the tree and the cost becomes a product again, which is the one thing
> chain descent exists to avoid. A **refinement** channel is the only shape that adds information
> without branching, which is why §3 is the right idea even though §4 failed to feed it.

> ## ▶▶ STATUS (2026-08-10) — a DIAGNOSIS + three ranked methods. **Nothing here is built yet.**
>
> **The finding, verified against source:** in the published object the force key's value **never
> enters a colouring**. Force's only channel is *selection inside one cell* (`Force.keepMin`), so a
> force key that cleanly separates a mixed cell into three orbit-blocks **accomplishes nothing** — the
> argmin block is kept and the information that the other two were *different* is discarded.
>
> ⟹ **"Force separates mixed-orbit cells" — force's core job — is not expressible as success in the
> object as built.** Every W2 dead end of 2026-08-08/09 is a symptom of that, not an independent wall.
>
> **▶ The live proposal: give force a refinement channel** (§3), fed by an **order-free, gauge-blind
> relation** read off the row space (§4). Both rest on pieces that already exist and are proved.
> **▶ STEP 0 IS A PROBE (§6) AND IT MUST RUN FIRST** — the relation's *strength* is unmeasured, and
> vacuity is this project's recurring failure mode.
>
> ⚠ **Read [`chain-descent-wind-down.md`](./chain-descent-wind-down.md) §2 W2 first** for what is
> already refuted (four routes + S3's six corrections). This doc does not repeat them; it explains why
> they were all the same mistake.

---

## 1. The diagnosis

Three source facts, each checked this session:

| # | fact | where |
|---|---|---|
| D1 | `cellNarrowC key S adj χ c = ((keepMin key adj χ (cellList χ c)).map (rep V)).dedup` — force picks the argmin class, then `rep` must collapse it to one representative | [SelectNode.lean:205](../GraphCanonizationProofs/ChainDescent/SelectNode.lean#L205), [SelectCell.lean:70](../GraphCanonizationProofs/ChainDescent/SelectCell.lean#L70) |
| D2 | the published resolver's children are `kept.map (fun v => (v, refineV rf adj (indivOne χ v)))` — the child colouring comes from `indivOne` + the **refiner**, and the key touches only *which* `v` (via `kept = cellNarrowC …`), never the colouring | [SelectCell.lean:107-113](../GraphCanonizationProofs/ChainDescent/SelectCell.lean#L107) (`selNodeC`); same shape in `Select.blindNode` |
| D3 | success is `NodeResolvedC key S adj χ := ∃ c ∈ nonSingletonColours χ, (cellNarrowC key S adj χ c).length ≤ 1` — one cell down to **one** representative, or nothing | [SelectCell.lean](../GraphCanonizationProofs/ChainDescent/SelectCell.lean) §1 |

⟹ There are exactly two ways to succeed, and they are the two extremes:

* **consume**: the whole cell is **one** orbit (`CellOrbitAt`) — `rep` collapses it;
* **force**: the key is **injective** on the cell (`CellSeparatedAt`) — `keepMin` is already a singleton.

**There is no notion of partial success.** A cell that force splits into `k` genuine orbit-blocks,
`1 < k < |cell|`, is exactly what force is *for*, and it registers as failure.

⚠ Note this is **not** a defect of the disjunctive socket (`SelectCell` §9a). `CellResolvedAt` is
stated on the `keepMin` survivors and does admit the **mixed** case — key cuts between orbits, supply
certifies the survivor. What is missing is one rung further out: a split that the *supply cannot
finish* is still progress, and the object has nowhere to put it.

## 2. What the diagnosis explains (three "walls" that were one wall)

1. **The ≤ 8-value cap on `baseReadPin`** (wind-down §2 W2, S3 correction 3). `readAggB` is
   `encode ∘ sort` of a read valued in `{0,1,2}`, so it takes ≤ 8 values on any input and cannot be
   injective on a cell of ≥ 9 pairwise non-automorphic vertices. ★ That is a cap on a **standalone
   key**. `refineBy` pairs the read *with χ* and the next refinement round propagates it — the cap is
   an artifact of the channel, not of the reader.
2. **`hrigid` in every rigid firing lemma** (`RigidGen.nodeResolved_compKey_genOfRef`,
   `nodeResolved_compKey_readAgg`, `…readAggB_faithful`) demands **every** branch pair be
   non-automorphic. That is not conservatism: with only the `keepMin` channel, whole-cell injectivity
   is the *only* force success available, so the hypothesis is forced by the interface.
3. **The Frucht measurement** (`scratchpad/probe_w2_asymbase.out`, item 3b). CFI over the Frucht
   graph: the root gadget cell is **12 `Aut`-blocks, and each is already a single gauge-orbit**
   (12 = 12; wires 18 = 18). Force does **not** need to be injective there — it needs to **split**,
   after which consume clears each block. There is no channel for a split, so the node stalls.

⟹ ★★ The three are one problem seen from three sides. Chasing a stronger *reader* (S3) or a CFI
coverage theorem on top of this interface is building on a foundation that cannot express the goal.

## 3. METHOD 1 — give force a refinement channel *(highest value; this is the foundation)*

**The pieces exist and their obligations are already discharged at the general interface.**

| piece | statement | status |
|---|---|---|
| `RigidRefine.refineBy read adj χ v = Nat.pair (χ v) (read adj χ v)` | refine χ *by* a per-vertex reader | ✅ built |
| `RigidRefine.refEquivariant_refineBy` | `RefEquivariant (refineBy read)` from **`ReadEquivariant read` alone** | ✅ proved |
| the refiner is a **parameter** | `Select.canonFormS? (rf : Refiner n) …`, `descentCostS rf …` | ✅ by construction |
| `Descend.RefineEquivariant` is the refiner's *only* `①` obligation | [Descend.lean:930-933](../GraphCanonizationProofs/ChainDescent/Descend.lean#L930) | ✅ at source, verbatim: *"it needs **no** refiner hypothesis: `RefineEquivariant` is used only to **establish** `NarrowTransport` (in the two sufficient conditions) **and to transport the root colouring**"* — so a refiner swap owes exactly those two, not a re-proof of the spine |

★★ **Why this dissolves the value cap rather than working around it.** As a refiner the read is paired
into the colour and then **propagated by the next 1-WL round** — the same reason individualizing *one
vertex* (one bit of information) discretizes a graph. A 3-valued read is not weak in this channel; it
is a seed.

★★ **And it needs NO new notion of success.** After the split each block is a single gauge-orbit
(measured at every reached node on a resolved base), so consume clears it and `NodeResolvedC` fires
with the predicate that already exists. Force separates, consume clears — with a wire between them.

### ⚠ Costs and traps, stated up front

* **`Refiner n` is cost-carrying** (`rf adj χ : Colouring n × Nat`; `descentCostS` bills
  `(rf adj (indivOne χ v)).2`). `RigidRefine.RefEquivariant` is on the plain
  `AdjMatrix → Colouring → Colouring` shape — the composite needs a cost and a bridge between the two
  equivariance predicates. Mechanical, but not free.
* **It changes `Reaches`.** `HandledSC`, `③`'s population and the `Tinhofer` results are all stated
  over `Descend.Reaches (Refine.encodeFreeFast …)`. A new refiner is a **new reached set**, so those
  do not transfer for free. This is the same three-layer inheritance trap that cost `③` ~150 lines.
* **It re-bills `②`.** The refiner's cost enters `descentCostS` directly.
* **⛔ Trap #1 applies**: never a bare `… → Colouring n`; go through `Refine.ColData` + rfl-twins, or
  function-typed rounds compound exponentially under `Function.iterate`.
* **Executability.** `forcedVal` is `noncomputable` only because it decides `Submodule.span`
  membership; see §4 — the relation form is decidable by Gaussian elimination, so the channel need not
  cost the object its `#eval`.

## 4. METHOD 2 — the automorphism-blind solver: use the row space **relationally**

> ⛔⛔ **REFUTED 2026-08-10 at the built extraction — read the block at the top of this file.**
> Everything below is a correct derivation of a **vacuous** object: `Linked` is the total relation
> when `dim ker = 0` and the equality relation when `dim ker > 0`, so no equivariant read comes out of
> it. The section is kept because the *identity* it establishes (`Linked u v ⟺ ∀ x ∈ ker H, x_u = x_v`)
> is the useful residue and is now verified.

**The row space is already gauge-blind.** `R := rowspace H = ker(H)^⊥` is a canonical function of
`(adj, χ)` — no order, no pivot, no basis is chosen — and **`RigidRefine.rowspace_transport` is
proved** ([RigidRefine.lean:87](../GraphCanonizationProofs/ChainDescent/RigidRefine.lean#L87)).

⟹ ★★★ **The stall was never gauge-blindness. It was that the stack tried to extract a vertex
*labelling* from `R`, which needs a column order — and an equivariant order is unsatisfiable** (S3
correction 1: `OrdEquivariant` forces `σ = 1` at the empty graph with the constant colouring). **A
relation needs no order:**

> ### `Linked u v  :=  e_u + e_v ∈ R`   —   *"the difference between `u` and `v` is determined"*

| property | why |
|---|---|
| **equivalence relation** | `R` is a subspace: `0 ∈ R`; symmetry is `+` commuting; `(e_u+e_v)+(e_v+e_w) = e_u+e_w` |
| **equivariant** | `transportVec σ (e_u + e_v) = e_{σu} + e_{σv}` (`transportVec_e`) + `rowspace_transport` + the extraction transport, which is **proved** for the adjacency instance (`refExtractEquivariant_adj`) |
| **gauge-blind** | it is defined from `R` alone, and `R = ker^⊥` is exactly the slack-free part |
| **decidable** | membership in an F₂ row space is Gaussian elimination — no `Submodule.span`, so a computable Lean version is available |

★ **It is the rail detector, stated intrinsically.** `Kernel.kernelSupply`'s rails are found by a
heuristic ("same colour, non-adjacent, disjoint neighbourhoods, each the other's unique such
partner"); `Linked` is the same notion as a property of the system, with no choice and no pivot. Its
classes are precisely where slack has been removed — which is the hand-off point the architecture
wants: **consume removes slack from `ker`, force reads `R`; same system, opposite sides.**

▶ **As method 1's `read`**: take a σ-invariant of `v`'s `Linked`-class (class size is the cheapest;
iterating refinement is the strong version). Order-free, gauge-blind, decidable.

⚠ **Its strength is UNMEASURED.** With the concrete built extraction (`extractOf rowAdj witChi`),
`R` is the **F₂ row space of the adjacency matrix**, so `Linked u v` ⟺ `e_u + e_v ∈ rowspace(adj)`.
Whether that is informative on CFI graphs and multipedes is exactly §6's probe. Note the CFI wire
pairs have *disjoint* neighbourhoods by construction, so the condition is non-trivial there — but
**do not assume it fires. Measure it.**

## 5. METHOD 3 — know the reduction, and the ceiling, before spending

On a CFI graph the gauge is the base's **cycle space**, whose circuits are the base's cycles, so
coordinate-refinement of that code **is** edge-refinement of the base.

⟹ **The linear layer reduces CFI cell-separation to BASE edge-separation.** That is a *reduction*
theorem — honest and publishable — rather than a coverage claim, and it is what item 3b's numbers
literally say (Frucht: 12 blocks ↔ 12 base vertices).

⟹ **And it fixes the ceiling.** On a base *with* automorphisms the blocks are merged by `Aut`, so an
equivariant invariant provably cannot split them (the (F1) ceiling: an equivariant key is constant on
`Aut`-orbits). **No method in this family will ever fire a CFI root over a symmetric base.** That is
the honest scope sentence to publish with any of this.

## 6. ▶▶ STEP 0 — THE PROBE, BEFORE ANY LEAN

> ✅ **IT RAN (2026-08-10): `scratchpad/probe_w2_linked.py` → `probe_w2_linked.out`.** All three rows
> below plus six more witnesses. **Row 2 (`K₄`) fired the falsifier** for the signature read, and rows
> 1 and 3 came back **vacuous** for every legal read. Verdict block at the top of this file. The probe
> is reusable: it carries exact F₂ nullspace/rowspace, the `Linked` identity check, a
> **read-equivariance** check against edge-verified gauge automorphisms, and the refine-to-fixpoint
> measurement — point it at a **new** extraction and it answers in seconds.

Compute `Linked` and the refinement it induces on witnesses already characterized, and ask whether it
**splits** the mixed cells. Three rows, and the middle one is a soundness check, not a hope:

| witness | question | what the answer means |
|---|---|---|
| **CFI over Frucht** (asym base, 1-WL coarse) | does it separate the **12** blocks? | ✅ ⟹ methods 1+2 are the whole answer for CFI over an asymmetric base |
| **CFI over `K₄`** (symmetric base) | it **must NOT** separate | `Aut` merges those blocks, so an equivariant invariant *cannot*. A separation here means the probe is unsound — the same built-in check that validated `probe_w2_keysplit` |
| **rigid multipede** (`dim ker = 0`) | does it separate? | this is the Neuen–Schweitzer family, the only place the headline claim lives |

Reuse: `probe_w2_asymbase.py` has the CFI construction, exact `Aut(base)`, verified gauge orbits and
the **descent walk**; `probe_w2_linear.py` has `cycle_space`/`gauge_perm`. ⚠ **Root-only is not a
pass** — carry the walk over.

⚠ Also worth measuring in the same run, because it decides whether §3's cost is worth paying: after
refining by `Linked`, is each remaining non-singleton cell a **single gauge-orbit**? If yes the
consume half closes with the *shipped* supply (`Kernel.kernelSupply` is inside
`RecordCost.recordSupplyFast`, and `Select.CellOrbitAt` carries **no guard**).

## 7. ⛔ WHAT NOT TO RE-DERIVE

* The four refuted W2 routes and S3's six corrections — wind-down §2 W2. In particular: `seedFrames`
  is **type-impossible**, `OrdEquivariant` is **unsatisfiable for `n ≥ 2`**, `readAggB`'s `①` is
  **already closed and poly**, and the only concrete `baseRead` is **capped at 8 values**.
* *"A gauge can never make a cell mixed"* — true, and it is why "mixed by a linear obstruction" is a
  misnomer under the gauge reading. ⚠ But *"no key of any kind can fire a CFI root cell"* is
  **over-strong**: it needs `Aut > gauge`, i.e. base symmetry (item 3b).
* Narrowing `Publication`'s residue to `SomeCellResolved` is **not** a re-point —
  `unhandledResidue_nonvacuous` goes back in play.
* ⛔⛔ The banned argument stays banned: *"X ⟹ GI ∈ P, therefore X is impossible"*. A perfect key **is**
  the target. The legitimate use of that observation is **calibration**: an order-free poly
  coordinate-separating read for an F₂ code is permutation code equivalence, which GI reduces to — so
  `AggFaithfulB`-style faithfulness must be proved **per family**, never in general.

## 8. What would falsify this arc

* `Linked` is constant on the mixed cells of all three §6 witnesses ⟹ method 2's concrete instance is
  vacuous at the adjacency extraction, and the read has to come from a CFI-specific extraction (which
  reopens the *emitted* obligation on `KernelSupply.lean`, a module with **zero theorems**).
* `Linked` separates on **`K₄`** ⟹ the probe is unsound; stop and find the bug.
* The composite refiner's `②` bill moves `costDeg` ⟹ the numerals in `Publication.lean` move, and the
  pinned statements must be recomputed (`RecordDeepenCell.recordDeepenBound_expand`'s `ring` check).
