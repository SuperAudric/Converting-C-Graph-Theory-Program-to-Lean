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

## 6. Build sketch (if this is taken up)

1. `DualDescent.lean` — `certOf` (min-over-cell, fuel = colour count), `deepKey`, pruning by a
   verified-generator accumulator. Data-typed throughout (`Refine.ColData`, trap #1).
2. `keyEquivariant_deepKey` — the induction of §3. Mechanical; no new predicate.
3. Feed `Force.forceBy deepKey` ⟹ `force_canonizer` gives `①` unconditionally.
4. Ties ⟹ `deepenGens'`; reuse `twistOf_isColAut` verbatim as the verification gate.
5. Cost: `keyCost` = leaves explored. `②` becomes a bound on `∏ surviving reps`, which is where the
   rigid reader (`structReadAt` / RREF-column) plugs in — as a **cell splitter that removes
   branching**, not as a separate resolver.
6. Retire on success: `deepenRefSupply`, `DeepenRefInExec`, R1/R2, and `Amenable`-as-soundness
   (`DeepenAmenable`'s `joint` survives as the *cost* lemma: `Amenable` ⟹ branch factor 1).
