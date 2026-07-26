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

## 9. Build sketch (if this is taken up)

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
