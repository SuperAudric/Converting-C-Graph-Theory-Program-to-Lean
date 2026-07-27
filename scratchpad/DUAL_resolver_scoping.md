# The dual resolver: one descent that consumes a symmetry **or** certifies the rigid decision

Probe: `scratchpad/probe_dualdeepen.py` (18 witnesses: mp7/Fano, CFI over C₅ and over random cubic
bases m=8..14, mixed multipede, circ(5), 6 rigid random multipedes n=34..84).

---

## 1. Why the two sides don't unify today (the mechanism disconnect, precisely)

`deepen` (`DeepenSupply.lean` / C# `DeepenAnchor`+`ReplayDeepening`+`HarvestTwists`) descends the
**lowest-id non-singleton cell** to a whole-graph-discrete leaf, recording an *iso-invariant* id
sequence `seq`, then replays `seq` from each other rep and colour-matches the leaves (`twistOf`).

Two facts about that pipeline, both already in the record:

* **`chooseIdK` is invariant** (`chooseIdK_transport`) — the *cell* choice transports.
* **The within-cell pick is by vertex index** — `deepen` takes `w :: _` of
  `(finRange n).filter (χc · == cid)`. That does **not** transport. This is exactly the §1.1 `G8`
  falsifier, and it is why `①c` needs `Amenable` at all.

The leaf is discrete, so it *is* a labelling `π`. `twistOf` builds `π_j⁻¹ ∘ π_1` and gates it with
`IsColAut`. Unfolding that gate:

> **`twistOf` verifies ⟺ `adj^{π_1} = adj^{π_j}`** — the twist is an automorphism exactly when the
> two leaves are the *same relabelled graph*.

So deepen already computes a per-anchor certificate `cert(r) := adj^{π_r}` and then **throws away
every bit of it except the equality test**. When the twist fails, the code returns "no candidate,
sound over-split" — but the *reason* it failed is `cert(r₁) ≠ cert(r_j)`, which is a **separation**,
i.e. precisely what force wants. The disconnect is not mathematical; it is that the negative branch
discards its own evidence. What blocks reading it as a certificate is only the index-pick: with a
non-invariant pick, `cert(a) ≠ cert(b)` may be an artifact of the labelling rather than a fact about
the graph.

## 2. The fix (one line): replace the index pick by **min over the cell**

```
cert(χ):                                  -- χ a colouring of adj
  χ := refine χ
  if discrete χ:  return (adj^χ, parent^χ)              -- the leaf certificate
  C := lowest-id non-singleton cell of χ
  return MIN over v ∈ C of cert(indiv χ v)              -- no index tie-break
```
plus the standard pruning: skip `v ∈ C` covered by an already-**verified**, path-fixing automorphism.
Pruning only removes members whose subtree certs are provably equal, so **min-over-pruned =
min-over-all**.

This is `deepen`'s own descent with the one non-invariant step removed. Cost is no longer one path —
it is `∏ₖ (surviving reps at level k)`.

### The two readings of the one object

| | test | consumer |
|---|---|---|
| **CONSUME** | `cert(a) = cert(b)` | `π_b⁻¹π_a` is an automorphism — the existing `twistOf` gate verifies it; feeds `deepenGens` |
| **FORCE** | `cert(a) ≠ cert(b)` | `cert` **is** a `Force.Key`; `forceBy` keeps the min-key branches |

Same computation, opposite branch of one equality. That is the dual resolver.

## 3. What becomes free, and what stays carried

**Free (mechanical Lean, no carried hypothesis):**

* **`KeyEquivariant deepKey`** by well-founded induction on colour count: cells transport, so `C ↦ σC`;
  child certs transport by IH; the **min of a transported multiset is equal**. Base case = a discrete
  leaf's relabelled adjacency, structural. **No `Amenable`, no rigidity, no uniqueness.**
  ⟹ `Force.force_canonizer` gives `①` immediately (it needs `KeyEquivariant` and nothing else).
* **`①c` for the consume side**: the emitted orbit relation is the fibre relation of an equivariant
  key, hence invariant. The whole `deepenRefSupply`/R1/R2/`SameOrbits` apparatus is not needed —
  it exists only to repair the index pick.
* **No third outcome.** At every node the cell partitions into cert-classes; ties give a *verified*
  generator, differences give a *certified* separation. The "mutual stall" residue cannot occur as a
  **mechanism**.

**Carried — and this is the whole of it:** `∏ₖ (surviving reps)` is the classical I-R tree size, i.e.
worst-case exponential. Nothing here makes GI easy.

**The relocation (the actual prize).** `Amenable` today is a **soundness** hypothesis on `①c`
(`deepenSupply_guarded_canonizer_direct` takes `hAmen : ∀ adj χ, Amenable adj χ`, which is *false on
rigid graphs* — the STATUS block already calls it a conditional scaffold). In the dual it becomes a
**cost** statement and nothing else:

> `Amenable` at a node ⟺ surviving reps = 1 ⟺ the descent is a single path there.

A non-`Amenable` node is no longer unsound — it is merely *expensive*, and lowering its cost is
exactly the rigid solver's job (supply a key that splits the cell instead of branching over it).
The flag stops being a mechanism flag (mutual stall) and becomes a **budget** flag.

## 4. Probe results (`probe_dualdeepen.py`)

| measurement | result |
|---|---|
| **① min-over-cell cert invariant under relabelling** | **18/18 witnesses TRUE** |
| **① greedy index-pick (= today's `deepen`) invariant** | **FALSE on 9/18** — mixed multipede, circ(5), all 6 rigid multipedes, CFI-cubic m≥10. TRUE on mp7 and CFI-C₅ (reproduces §1.1: *mp7 cannot detect this*) |
| **DUALITY: cert-ties failing to yield a verified path-fixing automorphism** | **0 out of ~150 ties, on every witness** — the tie reading is complete; no stall |
| **cost, pruned leaves** | 4–29 across all witnesses (CFI cubic m=14, n=98: **29 leaves**; rigid multipede n=84: **4 leaves**) |
| **cost, unpruned leaves** | up to 3584; ratio tracks `\|Aut\|` (mp7: 1344 unpruned = `\|Aut\|` exactly) |
| **consume output** | mp7 `\|Aut\| = 1344` recovered ✓ (matches the C# cross-check) |
| **rigid verdict non-vacuous** | CFI cubic m=14: root cell `\|C\|=56` → **14 cert-classes, 13 singletons** = 13 certified rigid decisions at the root of a WL-hard graph. Mixed multipede: root cell 4 → 2 classes |

⚠ **Cost caveat — do not over-read.** These are not the I-R-lower-bound families (Neuen–Schweitzer
odd/expander multipedes, Miyazaki). Random multipedes and CFI over small cubic bases are *easy* for
I-R; the small leaf counts are suggestive, not evidence of polynomiality. The exponential risk is
real and **unmeasured**. What the probe does establish is the **verdict structure** (① and duality),
which is labelling-independent and is the part the design turns on.

⚠ **Group completeness not independently verified**: `|Aut|` is read off the generators the descent
itself discovers (nauty-style). Consistency checks pass (unpruned leaf counts track `|Aut|`), but no
external oracle was consulted.

## 5. Correction to `CORE_scoping.md` (measured, 2026-07-26)

`CORE_scoping.md` §"Measured" line reports *"rigid case R=30 (30/30)"* for the `circ(5)` multipede.
**Measured here: `circ(5)`'s multipede has `|Aut| = 10` (D₅ scheme symmetry), 5 orbits, and
`R(Aut-fixed) = 0` — not 30.** The `R` there was computed from `support(ker H)`, the *linear* handle,
and `circ(5)` is a circulant, so its symmetry is entirely of the **scheme** kind that CORE_scoping's
own 2026-07-26 correction says `ker H` misses. The correction is stated in that doc but its measured
numbers were not re-run. Since the R/K plan needs `R` to be *Aut*-fixed (not `ker H`-fixed), the
`circ(5)` witness does not support it; the **MIXED** multipede does (`|Aut| = 8`, `R = 4` genuinely
Aut-fixed), as do the rigid random multipedes (`|Aut| = 1`, `R = n`).

This also names the poly constructor the R/K split was missing: **`K` = the orbits the dual's ties
produce, `R` = what its certified separations leave.** The split stops being an oracle.

## 6. Where the exponential enters — and how much of it is avoidable

Probe: `scratchpad/probe_polyloop.py` (faithful ports of `deepen`/`replay`/`twistOf`/`lookaheadKey`).

### 6.1 Deepen's polynomiality and its `Amenable` hypothesis are the SAME FACT

Cost of any descent = `∏ₖ bₖ`. Today's `deepen` sets `bₖ = 1` **by fiat** (lowest-index pick). That is
free computationally but not free logically: the leaf it computes is a function of the *labelling*, and
is only ever usable through an equality test between two runs — which is labelling-independent exactly
when the picked cell is a single orbit, i.e. **`Amenable`**. So deepen is not "poly and correct"; it is
**poly, and correct-when-`Amenable`**. The dual does not *introduce* an exponential — it *prices* the
assumption deepen was making for free. Where `Amenable` holds, the dual has `bₖ = 1` too and is exactly
as poly as deepen.

`bₖ = 1` is legitimate — no branching at all — under either justification:

* **CONSUME** — the cell is certified a single orbit (harvest transitive on it): pick any member.
* **FORCE** — a poly equivariant key *splits* the cell: then we **refine, not branch** — the cell
  shrinks and there is no cost multiplier whatsoever.

**Exponential survives only at STALL nodes (both fail).** `cost = ∏(branch factors at stalls)`.

### 6.2 `Amenable` never needs to be ASSUMED — deepen witnesses it from below

`CellSingleOrbit adj χc cid := ∀ u w in the cell, ∃ σ, IsColAut adj χc σ ∧ σ u = w`
(`DeepenAmenable.lean:198`). Every harvested twist **is** an `IsColAut` (`twistOf_isColAut`, landed), and
`IsColAut` is closed under composition — so **transitivity of the harvested twists on the cell is a
verified witness for `CellSingleOrbit`**. It is decidable and poly (deepen's own harvest computes it).

⟹ The globally-false `hAmen : ∀ adj χ, Amenable adj χ` in `deepenSupply_guarded_canonizer_direct` can be
replaced by a **per-level run-time certificate**, making the capstone unconditional. `joint` /
`step_rerelate` are already exactly the lemmas that consume it — they need `CellSingleOrbit` per level,
which is what the certificate supplies. The certificate is **one-sided** (failure ⇏ rigid), which is
correct: failure means "not certified", and the response is branch / force / flag, never a wrong answer.

### 6.3 Measured — the poly loop on 18 witnesses

| witness | levels | FORCE | CONSUME | STALL | stall (\|C\|, harvest-orbits, TRUE-orbits) |
|---|---|---|---|---|---|
| mp7 Fano | 3 | 0 | **3** | **0** | — |
| circ(5) | 2 | 1 | 1 | **0** | — |
| CFI cubic m=10, m=12 (pl+tw) | 6 | 1 | 5 | **0** | — |
| CFI cubic m=8 pl | 7 | 1 | 4 | 2 | (16, 2, **1**) · (4, 2, 2) |
| CFI cubic m=14 (pl+tw) | 7 | 0 | 6 | 1 | (56, 36→**14**, 14) |
| MIXED multipede | 3 | 0 | 2 | 1 | (4, 2, 2) |
| rigid multipedes n=34..84 | 1–2 | 0 | 0 | 1–2 | (4,4,4) · (2,2,2) … |

**Stall triage** — comparing the harvest's orbit count on the cell against the TRUE `Aut`-orbit count
(computed independently by the min-over-cell canonical form) separates *forced* branching from *fixable*:

1. **Genuine rigid decisions** (harvest == TRUE > 1): rigid multipedes (4,4 / 2,2), MIXED (2,2),
   and CFI m=14's residual 14. Branching here is **forced** — no harvest improvement helps. This is
   exactly force's job, and the rigid reader belongs here as a **stall-branch-factor reducer**, not as
   a separate resolver.
2. **Anchor-count gaps** (harvest > TRUE, closes with more anchors): CFI m=14 gives
   **36 (3 anchors) → 24 (6) → 16 (12) → 14 (ALL) = TRUE**. A quantitative confirmation of §1.1
   ("all anchors are required"); the all-anchor supply is *exactly* complete there.
3. **★ A measured FUSION witness** (harvest > TRUE, does NOT close with all anchors): CFI cubic m=8,
   the `|C| = 16` cell has **TRUE orbits = 1** — it *is* a single orbit — yet the harvest stalls even
   over every anchor. Traced level by level: `AmenablePath` breaks **4 levels deeper**, at a cell with
   **2 orbits**. This is precisely `not_amenablePath_imp_rigidObstruction`'s claim (a stall exposes a
   force-actionable rigid pair *deeper* than the compared pair, which is itself automorphic = fusion).
   The deepen doc §4 records this witness as *still missing*; it is here, on a CFI cubic base.

### 6.4 Answer: avoidable at two of three scopes

* **`Amenable` nodes — avoidable entirely and unconditionally.** `bₖ=1` with a *verified* witness; no
  hypothesis; same cost as today's deepen. The dual is a conservative extension of deepen, not a
  replacement with worse cost.
* **Force-separable nodes — better than avoidable.** The key shrinks the cell; no multiplier at all.
* **Genuine stalls — not avoidable in general.** `∏` over stall nodes is the honest cost and it is the
  wall, unmoved. But it is now a **cost multiplier at nodes you can point at**, with a *correct*
  fallback (branch), instead of a soundness hypothesis that is false on the graphs of interest.

## 7. ★ CORRECTION — the exponential is in neither resolver; it is in ORDERING, not separating

§6's framing put the exponential in "stall branching". That mislocates it. Neither resolver is
exponential, and the dual does not make one so. Redone properly:

### 7.1 The strong link is real, and it is provable from landed pieces

`Descend.targetColour = (nonSingletonColours χ).min` and `Deepen.chooseIdK (finRange n)` are the **same
object** — lowest-id non-singleton cell. So the canonizer's descent path *is* deepen's descent path.
That makes "deepest failure along the path" well-defined, and gives:

> **CERTIFIED-BELOW EXACTNESS.** Let `C` be a branch cell whose descent certifies `CellSingleOrbit` at
> **every level strictly below** (§6.2's poly witness). Then the all-anchor harvest's partition of `C`
> is **exactly the true `Aut`-orbit partition of `C`**.
>
> *Proof from landed pieces.* ⊆: every twist is verified (`twistOf_isColAut`), so each harvest block sits
> inside a true orbit. ⊇: certified-below **is** `AmenablePath`, so `joint` + `twistOf_of_transport_fixing`
> say an automorphic pair *does* produce a verifying twist. Hence equality. ∎

This is strictly stronger than the link in use today. `not_amenablePath_imp_rigidObstruction` says a
consume failure *exposes an obstruction somewhere*. The above says: **at a certified-below failure, the
cell's exact orbit partition has been computed, in polynomial time, and its non-blocks are certified
non-automorphic.** That is the user's "a cell with the properties needed to force" — and it is a
proof-form gap, not new mathematics.

Measured (`probe_verdict_invariance.py`, all-anchor harvest at the **branch cell**, 18 witnesses):

* **exact = 18/18** — harvest partition == true `Aut`-orbit partition, on every witness
  (mp7 28→1 block, CFI cubic m=14 56→14 blocks, rigid multipedes 4→4, MIXED 4→2).
* **partition transports under relabelling = 18/18.**

### 7.2 Why the earlier m=8 counterexample does not contradict this

The `(16, 2, 1)` stall of §6.3 was at a node **not** certified-below (`AmenablePath` breaks 4 levels
deeper, at a 2-orbit cell). Exactness is not claimed there, and its verdict is provably unusable — not
merely measured so: `Force.forceBy_no_narrowing_on_orbit` says an **equivariant** key cannot split a
single-orbit branch cell. That cell is a single orbit and the harvest splits it 2 ways, so that verdict
**is not an equivariant key**, full stop. The scheduling consequence is the existing interleaving:
force acts at the deeper exposed cell first, the colouring refines, consume retries. Rounds are ≤ n
(each force step strictly refines), so the *loop* is poly.

### 7.3 Where the exponential actually lives

A branch cell with `k > 1` true orbits leaves the descent exactly two moves:

* **rank the orbits** by an invariant and `keepMin` — this is `forceBy`; or
* **branch over them** and take the min canonical form — cost multiplier `k`.

And **ranking two orbits *is* separating them by a poly invariant** — the two are the same thing
(`forceBy`'s power is exactly its key, and `forceBy_no_narrowing_on_orbit` says a key can act only
between orbits). So:

> Knowing the orbit partition **exactly** — which §7.1 now gets in poly time — still does not give
> force a key. Force needs a **poly invariant ORDER on the certified-rigid blocks**. Absent it, the
> only sound move is branching, and *that* is the exponential. It is the fallback for a missing order,
> not a property of either resolver.

So the split is: **PARTITION = poly and (per §7.1) provable; ORDER = the wall.** That is independently
exactly the rigid-seal frontier wording ("canonical column order on the rigid residue", the recover
core) and CORE_scoping's "main blocking feature = the poly iso-invariant order on R". The dual work
does not move that wall — but it *does* deliver R/K with a poly, exact, certified constructor, which is
what the R/K plan was missing.

## 8. ★★ §7.3 WAS WRONG — ranking is NOT the wall. Strategy assessment.

§7.3 claimed "ranking the blocks == separating them by a poly invariant == the wall". That is false,
and the refutation is deepen's own object. Probes: `probe_certkey.py`, `probe_strategies.py`.

### S1 — the certified-below cert key ✅ CONFIRMED, and it is the route

> **Claim.** If `AmenablePath` holds along `a`'s greedy descent (certified-below), then deepen's
> **single-path leaf cert** `cert(a) = adj^{π_a}` is **iso-invariant**.
>
> *Proof.* Run the descent from `a` in `adj` and from `τa` in `τ·adj`. Cell ids match
> (`chooseIdK_transport`). The min-index picks differ, `w` vs `w'`. `AmenablePath` says the chosen cell
> is a single orbit of `IsColAut adj χ_cur`, so ∃`ρ` with `ρ w = τ⁻¹ w'`; then `τ∘ρ` is again an
> isomorphism `adj → τ·adj` carrying pick to pick. Induct. At the discrete leaf the two are related by
> an isomorphism, so the relabelled adjacency is **equal**. ∎
>
> This is `joint` with an **isomorphism between two graphs** in place of an automorphism of one — the
> project's standard transport generalization, and its atoms (`step_transport`, `chooseIdK_transport`,
> `cellSingleOrbit_transport`) are all landed.

Combined with §7.1 exactness (`cert(a) = cert(b) ⟺ same orbit`), `cert` is a **poly** (one greedy path
per rep), **equivariant**, **exactly orbit-separating** `Force.Key` — so it **ORDERS the blocks** and
`force_canonizer` fires. No min-over-cell, no branching, no wall. It is also **gauge-tolerant**
(automorphic pairs tie by construction), so it does not need whole-node rigidity.

**Measured (`probe_certkey.py`, 9 witnesses):** certified-below reps with a non-invariant cert =
**0**. Every non-invariant cert came from an **uncertified** rep (perfect correlation). `exact = Y` on
8/9. On the **rigid multipedes** — the case I said was walled — all reps certify, and `cert` separates
all 4 orbit blocks invariantly. The rigid decision is resolved by a poly key.

### S2 — deferred schedule ✅ effective, ⚠ but it does NOT reach "purely rigid"

Single-orbit-ness is invariant, so *"lowest-id **single-orbit** non-singleton cell, else lowest-id"* is
an equally legal `targetColour`. Individualizing inside a single-orbit cell costs branch factor 1 and
is free. Measured: forced decisions drop to **0–2 per witness**; **MIXED and mp7 need ZERO**.

⚠ **But the node is not purely rigid when the first decision arrives.** At CFI cubic m=8/10/12 the
first forced decision has `|Aut| = 512 / 128 / 256`. Every cell carries ≥2 orbits while the graph is
still highly symmetric — you run out of *consumable cells* long before you run out of *symmetry*. So
"defer until truly rigid, which is already handled" does not materialize, and the whole-node-rigid
anchor (9A–9C, `OrdEquivariant`) does **not** become applicable this way. S1 covers it instead,
because S1 is gauge-tolerant where 9A–9C is not.

### S3 — order-agnostic block splitting ❌ refuted on the cheap keys

Blocks are invariant sets, so any invariant set-function is a legal colour — no order needed. Tested
`|B|`, the refinement histogram after set-individualizing `B`, and that plus `B`'s neighbourhood
colours: **0 of 8 forced decisions separated** (only circ(5), and only the third variant). The
block-level analogue of the already-recorded `baseReadWL` blindness. Not a route on its own — though
it remains a free *pre-filter* wherever it does fire.

### S4 — k-fold branch, non-recursively

Where S1 is unavailable, branch over one rep per block and take the min. Cost `k` at that node,
**not exponential unless nested**. Measured nesting: 8/9 witnesses have a single non-nested decision.

### The actual residue (and it is not ordering)

Nodes with an **uncertified** rep — i.e. `AmenablePath` breaks somewhere below (fusion). Measured:
rand multipede V=12 W=8 (0/4 reps certified) and CFI cubic m=10 (4/40). There `cert` is genuinely
non-invariant and S1 does not apply; the response is to resolve the deeper multi-orbit cell first
(where S1 *does* apply, by induction) and re-run. So the open question is the **nesting depth of
uncertified levels**, not the ordering of blocks. That is a cost/termination question, and it is a
different question from the one the rigid-seal frontier is currently phrased around.

## 9. ★★★ THE SPLIT LOOP — the mechanism has no third case (validated)

Probe: `probe_splitloop.py`. The algorithm, exactly as stated:

```
loop:  refine
       if discrete: done
       C := target cell;  P := orbit partition of C
       if |P| = 1:  individualize any member          -- CONSUME, branch factor 1, FREE
       else:        order the blocks, refine by rank  -- FORCE, a SPLIT, no branch
```

**Two blocks cannot tie**: `cert(a) = cert(b) ⟺ (adj, χ+a) ≅ (adj, χ+b) ⟺ a, b are in the same
orbit` — so a tie contradicts them being distinct blocks. The split therefore *always* succeeds.
**There is no third outcome.** The `¬HandledS` "true mutual stall" does not exist as a mechanism;
it exists only as cost.

**One computation gives both verdicts.** Compute `cert(a)` for `a ∈ C`: its **fibres are the orbits**
(consume) and its **values order them** (force). No separate harvest is needed — deepen's harvest
becomes an *optimization*: where it certifies the cell is a single orbit, skip the certs entirely and
take the free step.

**Measured, 13 witnesses:** `blocks-tied = 0` everywhere; `① = OK` everywhere.

| witness | calls | splits | free | max-nesting | blocks/split |
|---|---|---|---|---|---|
| mp7 Fano | **1** | 0 | 3 | 0 | — (pure consume) |
| MIXED multipede | 3 | 1 | 7 | 1 | [2] |
| circ(5) | 4 | 1 | 4 | 1 | [3] |
| rigid multipedes n=34..84 | 5–15 | 1–6 | 0–1 | 1–2 | [4] … [4,2,2,2,2,2] |
| CFI cubic m=8 / 10 / 12 / 14 | 3 / 9 / 8 / **17** | 1 / 2 / 1 / 2 | 14 / 39 / 43 / **96** | 1 / 2 / 1 / 1 | [2] / [6,2] / [7] / [14,2] |

CFI cubic m=14 (n=98, WL-hard): **96 free consume steps, 2 splits, 17 recursive calls.**

### What this settles, and what it leaves

* **Settled — the mechanism.** Every cell is consumed or split; the split cannot fail; the result is
  iso-invariant. `①` is unconditional for the whole algorithm (a canonical form is equivariant, and
  `force_canonizer` needs only `KeyEquivariant`). The mixed-cell route (`CoveringOfAt`) collapses into
  "split by the orbit partition, order by the key" — not a separate resolver.
* **Left — the cost, and only the cost.** `calls = ∏` over a root-to-leaf chain of mixed cells of
  (#blocks) = the **fully `Aut`-pruned I-R tree**. Measured 1–17 with nesting ≤ 2. In general this is
  the object with known exponential lower bounds (Neuen–Schweitzer multipedes over expanders,
  Miyazaki) — those families are *not* in this witness set, so the small numbers are suggestive only.
* **Where force's key removes the cost entirely.** The recursion exists *only* to order the blocks. A
  poly equivariant block-ordering key collapses it to depth 0 (`calls = 1 + #splits`, poly). So
  "force handles ordering rigid cells" is exactly the hypothesis that makes the whole loop poly — the
  model is right, and the wall is now located precisely at **"a poly key that orders the blocks of one
  mixed cell"**, nothing else.
* **And S1 is such a key at nesting 1.** Certified-below ⟹ deepen's single-path cert orders the blocks
  in poly time. So **nesting ≤ 1 ⟹ poly, unconditionally** (measured: 9/13 witnesses).

⚠ **Probe idealisation.** `orbit_map` uses a true canonical form as the partition oracle. In the real
algorithm the partition comes from the same `cert` computation (fibres), so this is faithful — but it
means the poly *fast path* (deepen's harvest instead of certs) is only available where the harvest is
exact, i.e. certified-below (§7.1, measured 18/18 there).

## 10. ✅ LANDED — `ChainDescent/DeepenCertified.lean` (block 1 of the forcibility proof)

Gate green (`bash /workspace/scripts/build.sh`, 197 s); all 9 theorems
`[propext, Classical.choice, Quot.sound]`. In `build.sh` after `DeepenAmenable`.

**The target chain** for *"consume failing hands force a forcible node"*:

| | statement | status |
|---|---|---|
| **T1** | `CertifiedOrbit ⟹ CellSingleOrbit` — a *checked* transitivity of harvested twists **is** single-orbit-ness | ✅ `cellSingleOrbit_of_certifiedOrbit` |
| **T2** | `CertifiedPath ⟹ AmenablePath`, `Certified ⟹ Amenable` | ✅ `amenablePath_of_certifiedPath`, `amenable_of_certified` |
| **T3** | selector identity `chooseIdK (finRange n) = Descend.targetColour` — deepen's per-level cell **is** the canonizer's branch cell | ✅ `chooseIdK_eq_targetColour` |
| **T4** | per-level bridge: `Consume.CellIsOrbit` discharges the level's certificate | ✅ `certifiedOrbit_of_cellIsOrbit_chooseIdK` |
| **T5** | **located failure**: at a certified node, consume failing names a non-automorphic pair **in this branch cell** | ✅ `consume_fail_gives_real_decision`, `rigidObstructionAt_branch_of_certified` |
| **T6** | **`Amenable` transports** — the index-pick obstruction absorbed as in `joint` | ✅ `amenablePath_transport`, `amenable_transport`, `amenable_transport_iff` |
| **T7** | guarded supply ⟹ **`①c` with no hypothesis at all** | ✅ `deepenSupplyGuarded_canonizer` |

**What T1–T4 buy.** `Amenable` was unobservable — `CellSingleOrbit` quantifies over the true `IsColAut`
group. T1 shows it does not need to be *assumed*: deepen's harvest emits only *verified* automorphisms
(`twistOf_isColAut`) and `IsColAut` is composition-closed, so a checked transitivity **is** a proof of
single-orbit-ness. T3 is what makes that check *achievable* — it identifies the cell `AmenablePath`
names with the cell `deepenGens` actually harvests, so the consume side's own `CellIsOrbit` discharges
each level (T4).

**What T5 buys — "forcible", not merely "exposed".** `not_amenablePath_imp_rigidObstruction` gives
`∃ χc cid, RigidObstructionAt adj χc cid`: an obstruction *somewhere*, possibly far below, with no
control over which colouring or cell. At a certified node the failure is **located** — two named
branch vertices linked by no colour-automorphism, at *this* colouring and *this* branch cell. That is
the strengthening asked for.

**What T6/T7 buy — the hypothesis is gone.** `AmenablePath`'s per-level pick is by vertex index and so
does not commute with a relabelling; that is the obstruction this track keeps meeting, and it is what
forced `deepen_branchOrbit_transport` to carry a *global* `∀ adj χ, Amenable adj χ`. It is absorbable
exactly as in `joint`: the level's cell **is** a single orbit (that is what `AmenablePath` says), so a
stabilizer element carries `σ wₐ` to `w_b` and the relating isomorphism accumulates. With `Amenable`
transport-stable, a supply that simply *defers* where `Amenable` fails is equivariant unconditionally
(good side: §5 transports; bad side: both emit nothing). So **`deepenSupplyGuarded_canonizer` carries
no hypothesis at all**, where `deepenSupply_guarded_canonizer_direct` carried a globally-false one.
Soundness no longer rests on anything; only *firing* is reduced, and the guard is precisely where the
rigid side takes over.

Note that T3 (the selector identity) turned out load-bearing for T6 too: with
`Descend.targetColour_transport` it gives `chooseIdK_finRange_transport` in one line, so the
`List.map σ` mismatch in `chooseIdK_transport` never has to be dealt with.

⚠ **Still open.** The guard is a `Prop` test, so `deepenSupplyGuarded` is `noncomputable`. Which
*poly, relabelling-invariant* check to use in the executable is open: `Certified` (§2) is poly and
sound, but its own invariance is **not** established — `deepenGens` is index-dependent. This is the
same index-pick issue one level up, and it is where the min-over-cell / split-loop redesign (§9)
would apply.

## 11. ★★★ LITERATURE PLACEMENT (4 subagent searches, 2026-07-26)

### 11.1 The recalled result is real, and sharper than expected

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

### 11.2 ★ Neuen–Schweitzer's exponential lower bound does NOT bind this algorithm

**Neuen & Schweitzer, STOC 2018 (arXiv:1705.03283), §3**, after Prop. 3.1, verbatim:

> "**Likewise would a refinement operator that refines every coloring into the orbit partition under the
> automorphism group** [yield a polynomial-size search tree]. However, we do not know how to compute
> these two examples efficiently. In fact computing either of these is at least as hard as the
> isomorphism problem itself. … it is nonsensical to allow that an individualization-refinement
> algorithm uses a subroutine that already solves the graph isomorphism problem."

**The literature names §9's algorithm, grants it a polynomial-size search tree, and excludes it from the
model** — solely because orbits are GI-hard. Theorem 3.2 requires *k-realizability* (`WL_k ⪯ ref`, i.e.
**coarser** than k-WL); orbit-refinement on a rigid multipede is *discrete*, strictly finer, so the
hypothesis fails for every k. Their "all automorphisms free" clause is **vacuous** on their family
(`|Aut| = 1`), so it is not a strengthening that covers an orbit oracle.

⚠ Not a free lunch: there `|P| = 1` never occurs, every cell splits into `|C|` singletons, and they prove
a **linear** number of individualizations is forced. All cost lands on the block-ordering recursion.

### 11.3 Naming — one collision, two matches

| project term | literature |
|---|---|
| `Amenable` / `CellsAreOrbits` | **= Tinhofer graph.** AKRV (*comput. complexity* 26(3):627–685, 2017; arXiv:1502.01255) App. A.2: *"G is Tinhofer if and only if, for every F, the orbit partition of A_F coincides with P_F."* Graded: Bhattacharjee–Panse–Sarma arXiv:2605.19702 Thm 1.1. |
| ⚠ **name clash** | AKRV's **"amenable"** means something DIFFERENT (1-WL identifies `G` against all `H`). `Amenable ⊊ Compact ⊊ Godsil ⊊ Tinhofer ⊊ Refinable`, all strict (Thm 21). **Rename the project predicate.** |
| the free consume step | **"symmetric choice"** (Gire–Hoang 1998; Dawar–Richerby CSL 2003); with automorphisms supplied as certificates, **"witnessed symmetric choice"** — Lichter & Schweitzer, LICS 2022 (Distinguished Paper) / **J. ACM 71(2), 2024**. Their Thm 1: definable isomorphism ⟹ definable canonization. Their stated motivation is verbatim §10's T1: *"it has to be verified that the choice set is actually an orbit and it is not known that orbits can be computed in polynomial time."* |
| the whole split loop | **Gurevich's canonization algorithm**, *From invariants to canonization*, Bull. EATCS 63:115–119, 1997: repeatedly compute a **canonical orbit**, individualize one vertex, repeat. Poly complete invariant ⟺ poly canonization (classes closed under colouring). |

### 11.4 ⚠⚠ THE RIGID COLLAPSE — and a vacuity in §8's rigid measurement

**AKRV, immediately after Theorem 21:**

> "It is worth noting that **the hierarchy collapses to Discrete if we restrict ourselves to only rigid
> graphs**, i.e., graphs with trivial automorphism group."

For rigid `G`, `Aut_S = 1` for all `S` ⟹ `Orb(Aut_S)` discrete ⟹ **Tinhofer ⟺ 1-WL already discretizes.**
At a non-singleton cell of a rigid graph, "the cell is a single orbit of the stabilizer" is *impossible*.

**Re-checked §8's rigid measurement against this — it was vacuous.** `descend_cert` level counts:

```
rand multipede V=6 W=5  (n=34)  levels per rep = [0,0,0,0,0,0,0,0]
rand multipede V=8 W=6  (n=44)  levels per rep = [0,0,0,0]
rand multipede V=10 W=7 (n=54)  levels per rep = [0,0,0,0]
rand multipede V=12 W=8 (n=64)  levels per rep = [1,1,1,1]
CFI cubic m=8 (n=56) levels = 5 ;  m=10 (n=70) levels = 4–6      <- these ARE substantive
```

Three of four rigid multipedes **discretize after ONE individualization**, so certified-below held with
*zero levels to certify*. §8's "all reps certify on the rigid multipedes" is TRUE but EMPTY. The CFI
results (4–6 levels) stand. This is the already-flagged "not the I-R-lower-bound families" caveat, now
with a theorem saying why it *must* be so.

**★ Where novelty can live — and it is exactly §10's open item.** The project's condition is
**path-local** (only the cells actually selected on one descent need be orbits); Tinhofer quantifies over
*all* `S`. The searches found **no named notion for the path-local weakening**, and none for a
*poly-decidable* side condition implying orbit-correctness — recognizing Tinhofer/refinable is P-hard and
at least as hard as GI on vertex-transitive graphs (AKRV Thm 22; arXiv:2605.19702). AKRV's whole
hierarchy is over **1-WL**; a condition over k-WL or coherent-configuration-stable colourings is
uncovered. §10's ⚠ ("which poly, relabelling-invariant check to use for the guard") is therefore not a
loose end — it is the one genuinely unclaimed spot.

### 11.5 The frontier, stated in 1983

**Babai & Luks, "Canonical labeling of graphs", STOC 1983, §1**, verbatim:

> "**Does knowledge of Aut(X) lead to a canonical form?** In the canonical form problem the objective is
> to **select, wisely, from the various representations.** If, as is almost always the case, Aut(X) is
> trivial, the number of such representations is n!. **How do we select?**"

That is §9's remaining question verbatim. Supporting, all verified:

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
* Babai's own canonization answer (**STOC 2019**, a separate paper three years after the isomorphism
  test) was to canonify the local-certificate structure, not to add an invariant.
* Named culprit for isomorphism-without-canonization results: **coset intersection has no known
  canonization analogue** (Schweitzer–Wiebking §1, citing Codenotti 2011).

**Not Babai's Split-or-Johnson.** That is a "progress-or-Johnson-obstruction" dichotomy with
quasipolynomial multiplicative cost in *both* branches, canonical only relative to arbitrary choices. The
structural match is Babai's **fullness / affected–unaffected** dichotomy in Local Certificates: *full* ⟹
global automorphisms `K(T)` produced (= consume); *non-full* ⟹ explicit obstruction `M(T)`, aggregated
into a canonical relational structure (= force).

**Closest prior theorem to §9's architecture:** Arvind–Das–Mukhopadhyay, JCSS 76(7):509–523, 2010 —
tournament canonization is poly-time reducible to **tournament isomorphism + canonization of *rigid*
tournaments**. An orbit oracle buys exactly the symmetric part and no more.

## 12. Build sketch (if this is taken up)

**Smallest first step (§6.2 — does not need the min-over-cell descent at all):**

1. `CertifiedOrbit adj χc cid : Bool` := harvested twists act transitively on the `cid`-cell.
2. `certifiedOrbit_imp_cellSingleOrbit` — from `twistOf_isColAut` + `IsColAut` composition-closure.
   A few lines; both ingredients landed.
3. Guard `deepen` on the certificate per level ⟹ `AmenablePath` holds **by construction** along the
   taken path ⟹ `joint` applies ⟹ drop `hAmen` from `deepenSupply_guarded_canonizer_direct`.
   This alone converts the conditional scaffold into an unconditional (flagging) capstone.

**Then the dual proper:**

4. `DualDescent.lean` — `certOf` (min-over-cell, fuel = colour count), `deepKey`, pruning by the
   verified-generator accumulator. Data-typed throughout (`Refine.ColData`, trap #1).
5. `keyEquivariant_deepKey` — the induction of §3. Mechanical; no new predicate.
6. Feed `Force.forceBy deepKey` ⟹ `force_canonizer` gives `①` unconditionally.
   Ties ⟹ `deepenGens'`; reuse `twistOf_isColAut` verbatim as the verification gate.
7. Cost: `keyCost` = leaves explored. `②` becomes a bound on `∏(stall branch factors)`, which is where
   the rigid reader (`structReadAt` / RREF-column) plugs in — as a **cell splitter that removes
   branching**, not as a separate resolver.
8. Retire on success: `deepenRefSupply`, `DeepenRefInExec`, R1/R2, and `Amenable`-as-soundness
   (`DeepenAmenable`'s `joint` survives as the *cost* lemma: `Amenable` ⟹ branch factor 1).

## 13. ★★★ MEASURED — the harvest is NOT a perfect orbit oracle (2026-07-27)

Probe: `scratchpad/probe_orbit_oracle.py`. Tests the hypothesis *"a harvest failure on `(a,b)` is a
proof that `a`,`b` are in different orbits"* **directly, per pair**, against an exact orbit oracle
(`a ~ b ⟺ canon(adj, χ+a) = canon(adj, χ+b)`, the Karp/Booth–Colbourn reduction of §11.1), and
certifies every false negative by exhibiting an **explicit verified `IsColAut` automorphism**.

### 13.1 The two falsifiers (both certified, not inferred)

| variant | witness | node | fact |
|---|---|---|---|
| **SINGLE anchor** = C# `HarvestTwists(p, part, cell, cell[0])` | **Chang-B**, `n=28` | the **root** (no force step, no deep path) | anchor `a₀=0` has **23** same-orbit partners; the twist verifies for **11** and **FAILS for 12**. Certificate: explicit `σ`, `is_aut ✓`, colour-preserving ✓, `σ(0)=10` |
| **ALL anchors + group closure** = Lean `deepenGens` | **CFI over a random cubic base, m=8**, `n=56` | the `\|C\|=16` cell (reached by one equivariant force-key refinement; = §6.3's `(16,2,1)` stall) | the cell is **ONE true orbit**; the all-anchor harvest splits it **8+8**. Certificate: explicit `σ`, `is_aut ✓`, colour-preserving ✓, `σ(24)=26` crossing the blocks. Reproduced by two independent implementations |

**Failure mode in both cases is the same, and it is not `replay` returning `none`:**
Chang-B — replay followed the id sequence in **12/12** failures, the colour-match simply was not an
automorphism. CFI m=8 — `replay-null = 0`, `twist-not-aut = 128` of 240 ordered pairs, and **every**
anchor fired the gate. So the negative branch is `cert(a) ≠ cert(b)` in exactly the sense §1 describes,
and it is **not** a separation.

**Mechanism (not luck).** Cell *ids* transport (`chooseIdK_transport`); the per-level `min`-index member
(`w :: _`, C# `sub2[0]`/`members[0]`) does not. If `σ a = b`, `σ` carries `a`'s chosen cell onto `b`'s but
not min↦min, so the descents diverge unless a stabiliser element repairs the pick — which *is*
`CellSingleOrbit` at that level. All three measured failure nodes (Chang-A root, Chang-B root, CFI m=8)
are **`¬Amenable`**, matching `branchOrbit_iff_aut_of_certified`'s hypothesis exactly.

### 13.2 ⚠ The per-pair reading is wrong even where the ORBIT reading is right

`branchOrbit_iff_aut_of_certified` equates the orbit relation with `WordReach` over the *verified
generator set* — the **group generated**, not the individual twist. Chang-B root shows the gap
concretely: **12 direct-twist failures, but `FN(all) = 0` after generator closure.** The C# already
relies on this (`CoveredByPathFixingAut` BFS-closes over `Automorphisms.Generators`). **Reading a
per-pair twist failure as a separation certificate discards precisely that closure**, and is unsound
even on nodes where the harvest's partition is exact.

⚠ Also a probe trap worth recording: a first version of the sweep unioned only the `(anchor, rⱼ)` pairs
instead of `v ~ g(v)` for every generator, and manufactured a spurious 176-pair "fusion falsifier" at the
Chang-A root. **Always close over the generators.** (`probe_polyloop.py` does this correctly.)

### 13.3 How much of the guard's conservatism is real — 1361 nodes, 10 families

Bounded descent-tree sweep (depth ≤ 2, all reps), `Amenable` vs. harvest exactness at every node:

| family | nodes | `Amenable` | harvest EXACT | exact but `¬Amenable` |
|---|---|---|---|---|
| Chang-A / Chang-B / Chang-C | 365 / 173 / 46 | 364 / 148 / 46 | **365 / 173 / 46** | 1 / 25 / 0 |
| T(8)=J(8,2) · mp7 · MIXED · circ(5) · CFI-C₅ · Shrikhande⊎Rook(4,4) | 365·365·13·11·61·225 | all 100 % | **all 100 %** | 0 |
| C3+C4+C5 (cells provably ≠ orbits) | 37 | 24 | **37** | 13 |
| **total** | **1361** | **1197 (87.9 %)** | **1361 (100 %)** | **164** |

* The all-anchor harvest was **exact at every one of 1361 nodes**, including all 164 `¬Amenable` ones.
* `Amenable` is therefore **sufficient but far from necessary** — the guard defers on ~12 % of nodes
  where the supply would have been exact. **The firing bottleneck is the GUARD, not the harvest.**
* ⚠ But transitivity of the harvested group certifies only the `|P| = 1` case. Where the cell has ≥ 2
  true orbits the guard must certify the **partition**, and that is exactly where the CFI m=8 node lies
  (harvest says 2 blocks, truth is 1). A `CertifiedOrbit`-style guard (T1/T4) fixes the single-orbit
  half and **not** the multi-block half.
* ★ Also measured: §6.3's anchor-count claim reproduces exactly — CFI cubic m=14, `|C|=56`:
  **3 anchors → 36 blocks, ALL anchors → 14 = TRUE**. And m=8's `(16,2,1)` stall **persists over every
  anchor** — it is the genuine fusion residue, not an anchor-count artifact.

### 13.4 Consequence for the dual-resolver design

The FORCE reading of §2/§9 (`cert(a) ≠ cert(b)` ⟹ separation) is **only** available where `cert` is
invariant, i.e. certified-below (S1, §8) — never from today's index-picked descent as it stands. Nothing
here touches ①: the harvest is untrusted and `Consume.verified` re-checks everything, so all three
failures cost *firing*, never soundness. What they refute is the stronger reading the negative branch was
about to be given.

### 13.5 ★★ THE MECHANISM, TRACED — misaligned picks at the first MIXED cell below

The failures of §13.1 are **not fusion**. Fusion = the symmetry is not *there* yet at the compared level
(it becomes certifiable only after a rigid decision), and a perfect same-level comparator would decline
too. Here the compared pair **is** in one orbit at the very colouring being compared, and the comparator
still fails. Traced level by level (`Sigma_k` = the isomorphisms carrying `a`'s pick-sequence to `b`'s;
`Sigma_k ≠ ∅` tested exactly, as `canon(a-side) = canon(b-side)`):

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

**The pattern is exceptionless and it is the ONLY mechanism.** Single-orbit cells never break alignment
(a stabiliser element repairs any pick); the descent stays aligned until the **first mixed cell**, where
the two sides individualize members of non-corresponding orbits and every surviving isomorphism dies.
That direction is not merely measured — it is the contrapositive of a landed theorem: `AmenablePath`
along `a`'s descent ⟹ an automorphic pair *does* produce a verifying twist (`joint` +
`twistOf_of_transport_fixing`, §7.1). So

> **a same-orbit twist failure ⟺ deepen's own path crosses a cell that is not a single stabiliser orbit,
> and resolves it inconsistently between the two sides.**

**⚠ Correction to §6.3 item 3.** The CFI cubic m=8 `(16,2,1)` stall is labelled there *"★ A measured
FUSION witness"*. That label is wrong by the above: the `|C|=16` cell is a single orbit **at that
colouring**, with no rigid decision needed to expose it. It is a pick-misalignment witness. (The real
fusion signature remains Chang-A's `A_stall < A_full`.)

**Does this block the mixed resolver? No — provided the failure is read as a POINTER, not a verdict.**
* ✅ *Sound as-is.* The harvest is untrusted; a failure is a sound over-split, and
  `not_amenablePath_imp_rigidObstruction` still applies — the divergence cell **is** a
  `RigidObstructionAt`, so force is genuinely handed something to act on. It is also **locatable**: the
  first level at which the harvest is non-transitive on its own chosen cell is a poly, one-sided detector
  for it (`CertifiedOrbit`, T1).
* ⛔ *But the failure must never separate the COMPARED cell.* At the CFI node the compared cell is one
  orbit and the harvest splits it 8+8. By `Force.forceBy_no_narrowing_on_orbit` an equivariant key cannot
  split a single-orbit cell — so that verdict is **provably not an equivariant key**, and using it as one
  breaks `①c`. The current design defers instead of separating, which is exactly why it is not blocked.
  This is the concrete bound on the §2 "read the negative branch as a `Force.Key`" proposal: legal only
  where the path below is certified single-orbit at every level.

## 14. ★★★ THE CONSUME→FORCE HOOK — target ladder and tractability (2026-07-27)

**Brief:** find the strongest *feasible* statement of "consume fails only where force can succeed",
better than `not_amenablePath_imp_rigidObstruction`'s `∃ χc cid, RigidObstructionAt adj χc cid`.

### 14.0 ⛔ FIRST — the literal target is FALSE, not merely unproved

`DeepenCertified` §4 states the located form only under `Certified`
(`rigidObstructionAt_branch_of_certified`). That hypothesis is **necessary**, and §13's CFI witness is
the counterexample to dropping it:

> CFI cubic m=8, the `|C| = 16` node. `¬Consume.CellIsOrbit deepenSupply adj χ` **holds** (the all-anchor
> harvest splits the cell 8+8) while `RigidObstructionAt adj χ (targetColour χ)` is **FALSE** (the cell is
> a single `Aut`-orbit; explicit verified `σ`, `σ(24) = 26`).

So `¬CellIsOrbit ⟹ RigidObstructionAt at this cell` is refuted. Worse for the naive hope: at that node
force **provably cannot fire either** (`Force.forceBy_no_narrowing_on_orbit` — the cell is one orbit). Any
target of the form *"consume fails at χ ⟹ force succeeds at χ"* is therefore dead. **The statement must
relocate the force step to a REACHABLE DEEPER node.** That is the shape of everything below, and §13.5's
trace says exactly which node: the first cell on the descent that is not a single stabiliser orbit.

### 14.1 The ladder

| | statement | status |
|---|---|---|
| **L0** | `¬AmenablePath ⟹ ∃ χc cid, RigidObstructionAt` | ✅ landed, force cannot use it |
| **L1** | at a `Certified` node, the obstruction is at **this** branch cell | ✅ landed, hypothesis provably necessary (§14.0) |
| **L2** | **first-failure localization**: the obstruction sits at a colouring **reachable by the descent's own individualizations**, at *its* branch cell | ▶ target, easy |
| **L3** | **deepest-failure**: that node is *also* `Amenable` — consume-exact below **and** force-actionable at the same node | ▶ target, moderate |
| **L4** | at an `Amenable` node an **equivariant key exists whose fibres are exactly the orbits** ⟹ force **strictly narrows** | ▶ target, moderate (one risky lemma) |
| **L5** | `forceThenConsume` narrows that cell to **one branch** | ▶ target, follows from L4 |
| **L6** | all of the above with a **poly** key | ⚠ open — the §10 executable-guard item |

**L3 + L4 is the deliverable**: *consume failing at `χ` ⟹ there is a descent-reachable `χ*` at which
force provably fires, and at which consume is simultaneously exact below.* That is "consume fails only
where force succeeds", relocated to the node where it is true.

### 14.2 Workstream A — `orbKey`, the key force hooks to

`Force.Key n := AdjMatrix n → Colouring n → Fin n → CostM (List Nat)`; the **only** `①` obligation is
`KeyEquivariant`. Define the **per-vertex-guarded greedy leaf cert**:

```
orbKey adj χ v := if AmenablePath adj χ n (step adj χ v)
                  then encode (leaf-relabelled adj, leaf-relabelled χ)   -- deepen's own discrete leaf
                  else []                                                 -- defer
```

* **A1** encode the leaf as `List Nat` (`Vector`-materialised, trap #1). *Easy.*
* **A2 ★ the one technical core** — `amenablePath_transport_iso`: strengthen the **landed**
  `amenablePath_transport` ([DeepenCertified.lean:391](GraphCanonizationProofs/ChainDescent/DeepenCertified.lean#L391))
  so it *returns* the accumulated relating isomorphism, not just the transported `AmenablePath`:
  ```
  AmenablePath adj χp fuel cur_a → cur_b.col = transportColouring σ cur_a.col →
    ∃ ρ, relabelAdj ρ adj = relabelAdj σ adj ∧ leaf_b.col = transportColouring ρ leaf_a.col
  ```
  **The existing proof already builds `τ * σ` level by level** (lines 447–462) — this threads that
  accumulator into the conclusion. A strengthening of a proved induction, not a new one. *Moderate; the
  only real risk in the plan.*
* **A3** guard invariance — from A2 / `amenablePath_transport`, both directions (apply at `σ` and `σ⁻¹`).
  *Easy.*
* **A4** `KeyEquivariant orbKey` from A2+A3. *Easy given A2.*
  ⟹ `Force.force_canonizer` and `Composite.composite_canonizer` apply **with no further hypothesis**.

**Free corollary (no work):** `Force.keyV_aut_invariant` then says `orbKey`'s fibres are **unions of
orbits** — the key can never split an orbit, so it sits exactly at the `forceBy_no_narrowing_on_orbit`
ceiling by construction.

### 14.3 Workstream B — firing and exactness

* **B1 (UNCONDITIONAL, and it is the firing direction)** `orbKey u = orbKey w` with both certified ⟹
  `∃ σ, IsColAut adj χ σ ∧ σ u = w`. Equal certs *reconstruct* the automorphism (`π_w⁻¹ ∘ π_u`), exactly
  as `twistOf_isColAut` reconstructs the twist. **Contrapositive: different orbits ⟹ different keys.**
  *No `Amenable` needed.* *Moderate, structural.*
* **B2** at an `Amenable` node the fibres on the branch cell are **exactly** the orbits (⊇ is A2). *Easy
  given A2+B1.*
* **B3** `Amenable adj χ` ∧ `RigidObstructionAt adj χ (targetColour χ)` ⟹ `forceBy orbKey` **strictly
  narrows** — one line from B1 + `Force.forceBy_narrows_of_key_ne`. *Easy.*
* **B4** with B2, force narrows to exactly one orbit block and consume finishes it ⟹
  `forceThenConsume` narrows to **one branch** (`Composite.forceThenConsume_singleton_of_cellIsOrbit`
  on the forced set). *Moderate — needs "consume exact on the forced sub-cell".*

### 14.4 Workstream C — localization (independent of A/B; do this first)

* **C1** `DescentReach adj χ χ'` — an inductive "reachable by individualize+refine along the descent".
  *Easy.*
* **C2 (L2)** strengthen `not_amenablePath_imp_rigidObstruction` to return the **failing level's
  colouring** plus `chooseIdK (finRange n) χ' = some cid`. The landed proof already reaches that level
  and returns `⟨cur.col, cid, …⟩`; it just discards the reachability and the selector fact. With **T3**
  (`chooseIdK_eq_targetColour`, landed) the obstruction is at `χ'`'s **branch cell**. *Easy.*
* **C3 (L3) — the deepest-failure theorem.**
  ```
  ¬Amenable adj χ → ∃ χ*, DescentReach adj χ χ* ∧ Amenable adj χ*
                          ∧ RigidObstructionAt adj χ* (targetColour χ*)
  ```
  *Proof:* C2 gives a reachable `χ'` with an obstruction at its branch cell. If `Amenable χ'`, done; else
  recurse. Each step strictly raises the colour count (`Descend.ncol_lt_indivOne_of_partner` +
  `ncol_le_refine`, both landed — the same measure `deepen_succeeds` already uses), bounded by `n`; a
  discrete colouring has `branches = []` so `Amenable` holds vacuously and the recursion must stop.
  *Moderate; all atoms landed.*

### 14.5 Workstream D — the headline, and E — cost

* **D1** = C3 + B3: `¬Consume.CellIsOrbit deepenSupply adj χ ⟹ ∃ χ*` descent-reachable at which
  `forceBy orbKey` strictly narrows. *One line once C3 and B3 exist.*
* **D2** = C3 + B4: at `χ*` the composite narrows to **one** branch.
* **E1** `Amenable` is **decidable** (`IsColAut` already has a `Decidable` instance — `twistOf` uses
  `decide`; `Equiv.Perm (Fin n)` is a `Fintype`), so `orbKey` is *computable*, merely exponential in the
  guard. **`①` therefore closes outright and the whole `Amenable` question becomes `②` (cost) — exactly
  the relocation §3 wanted.** *Easy but watch elaboration cost.*
* **E2** swap the guard for the poly `CertifiedPath` (`amenablePath_of_certifiedPath`, landed). The one
  remaining gap is the **invariance of the certificate boolean** — note this is now weaker than what §10
  asked for: a *Boolean* (does the harvest act transitively?), not the emitted partition.

### 14.6 Order, risk, fallback

**Do C1→C2→C3 first** — independent of the key, and C3 alone already replaces L0 with a genuinely
force-actionable statement. **Then A2** (the single risky lemma), then B1→B3→D1, then B2/B4→D2, then E.

**Fallback if A2 stalls.** The min-over-cell key `certMin` (§2/§9) has an *unconditional*
`KeyEquivariant` by a much simpler induction — cells transport, and the **min of a transported multiset
is equal**; no `Amenable`, no isomorphism accumulation. It reaches the same D-level statements with
exponential `keyCost`. So **D is reachable by two independent routes and A2 is not a single point of
failure**; A2 only buys the *poly* version.

**Explicitly out of scope:** none of this touches the block-**ordering** wall of §7.3/§8. `orbKey` orders
blocks only where `Amenable` holds; where it does not, D relocates the work deeper rather than ordering
it. That is the honest boundary.

## 15. ✅ LANDED — workstream C (`ChainDescent/DeepenLocated.lean`), 2026-07-27

Gate green (`bash /workspace/scripts/build.sh`, **211 s**); in `build.sh` after `DeepenCertified`. All
**10** theorems `[propext, Classical.choice, Quot.sound]`; no `sorry`, no new `axiom`.

| | statement | name |
|---|---|---|
| C1 | `DescentReach` — reachable by *proper* descent steps (individualize a vertex **with a same-colour partner**, then warm-refine) + `trans` | `DescentReach`, `DescentReach.trans` |
| C1a | one proper step strictly raises `ncol`; reachability never lowers it | `ncol_lt_step_of_partner`, `ncol_le_of_descentReach` |
| C1b | a `chooseIdK` level's pick has a partner (from `chooseIdK_mem`) | `partner_of_chooseIdK` |
| **C2 (L2)** | `¬AmenablePath ⟹ ∃ ψ` **reachable**, with `Descend.targetColour ψ = some cid` ∧ `RigidObstructionAt adj ψ cid` — the obstruction is at a **reachable node's BRANCH CELL** | **`not_amenablePath_located`** |
| **C3 (L3)** | `¬Amenable adj χ ⟹ ∃ ψ` reachable with **`Amenable adj ψ`** ∧ obstruction at `ψ`'s branch cell | **`not_amenable_deepest`** (+ `_aux`) |
| — | the `Amenable` (not `Certified`) form of `DeepenCertified` §4 | `consume_fail_real_decision_of_amenable`, `rigidObstructionAt_branch_of_amenable` |
| **D-entry** | every consume failure is located: *either* a decision in **this** cell (node `Amenable`) *or* at a reachable node carrying **both** hypotheses | **`consume_fail_locates`** |

**What changed relative to L0.** `not_amenablePath_imp_rigidObstruction` returns `∃ χc cid` naming no
reachable colouring and no branch cell — force cannot act on it, since `forceBy` fires *at a node*. C2/C3
return a node the descent stands on, with the obstruction at the cell `Descend.targetColour` selects
there (via the landed selector identity `chooseIdK_eq_targetColour`), and — the point of C3 — a node that
is **simultaneously `Amenable`**, which is what an orbit-separating equivariant key needs (§14.2/§14.3).

**Termination** is `Descend.ncol`, the same measure `deepen_succeeds` uses: each `DescentReach` step is
*proper*, so `ncol` strictly rises and is capped by `n`. The base case needs no discreteness lemma —
`¬Amenable` itself produces a branch vertex, hence a partner, hence `ncol χ < n`.

### 15.1 ⚠ Non-vacuity — CHECKED, per the standing steer

The conclusion is a conjunction (`Amenable ψ` **and** a mixed branch cell at `ψ`) and could have been
empty. It is not. Bounded descent sweeps (`scratchpad/probe_orbit_oracle.py`), counting nodes that are
`Amenable` **and** whose branch cell carries ≥ 2 `Aut`-orbits — i.e. inhabitants of C3's conclusion:

| C3+C4 | C4+C5 | C3+C4+C5 | Shrikhande⊎Rook(4,4) | Chang-A | Chang-B | MIXED multipede | **total** |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 24 | 1 | 24 | 48 | 1 | **100** |

Note also that the conjunction cannot degenerate: the obstruction requires `targetColour ψ = some cid`,
so `ψ` is **not** discrete and `Amenable ψ` is a real constraint, not the vacuous `branches = []` case.

**The C3 iteration validated directly** on a measured `¬Amenable` node (Chang-B root):

```
start : Amenable=False, branch-cell orbits=2   (ncol=2)
step 1: Amenable=False, branch-cell orbits=4   (ncol=3)
step 2: Amenable=TRUE , branch-cell orbits=2   (ncol=10)   <- the hook node
```
Two steps, `ncol` strictly rising exactly as the termination measure predicts, terminating on a node with
both properties.

### 15.2 Next

**Workstream A** (`orbKey` + `KeyEquivariant`) is now the only thing between C3 and D1
(`forceBy_narrows_of_key_ne` at `ψ`). A2 — threading `amenablePath_transport`'s accumulated `τ * σ` into
the conclusion — remains the one risky lemma, with the min-over-cell key as the stated fallback (§14.6).
