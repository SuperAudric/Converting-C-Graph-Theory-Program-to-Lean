# CAO carrier/payload falsifier constructions — the record

> **What this is.** Three related *designed* attacks on CAO propagation, raised from outside the
> project (2026-08-12) and measured here. **Construction B is a genuine 1-WL CAO-propagation
> counterexample** — the first one on record that was built to order rather than found by sweeping.
> **Construction C is the 2-WL attempt**; its first payload (Shrikhande/rook) is measured dead, the
> **scheme is not** — and at rung 1 it runs end to end, with **100 mixed cells** and the ensemble
> measured **passive** (§6). This doc owns the constructions, the measurements and the reusable filters.
>
> ⚠ Companion, not replacement: [`chain-descent-cao-propagation.md`](./chain-descent-cao-propagation.md)
> owns the *question*. Read its §1 (the hypothesis), §3 (the coupling principle) and §14 (the anatomy
> and the arity ladder) before this. ⚠ The research phase is closed
> ([`chain-descent-wind-down.md`](./chain-descent-wind-down.md)); this is a **record**, not a live track.

---

## 0. The hypothesis being attacked — get this right first

From the CAO doc §1, verbatim in force:

> Let `χ` be the **exact `Aut(G)`-orbit partition** (so `CellsAreOrbits` holds by construction,
> *however obtained*). Individualize `v`, take the `k`-WL closure. Is every cell still a single
> `Aut(G, v)`-orbit?

**The start is the orbit partition, not the `k`-WL stable colouring.** Every failed attempt below
failed by forgetting that. It is *not* a vertex-transitivity hypothesis — §2's counterexample design
asks only for `Aut` transitive on the two cells `D` (containing `v`) and `C`, which is CAO restated.

Two necessary conditions follow, and they are the whole design space:

| | condition | why |
|---|---|---|
| **N1** | the automorphism fusing `u, w ∈ C` must **move `v`** | `u, w` share an `Aut_v`-orbit **iff** `(v,u)`, `(v,w)` share an `Aut`-orbital (CAO doc §3). A gadget whose attachment set *determines* `v` can never produce two distinct orbitals. |
| **N2** | the distinguishing relation must be **uniform at the root** | individualization converts a uniform fact into a partition (§14.3). If the split pre-exists, the CAO start hands it to WL for free. |

---

## 1. Construction A — the Q₃ carrier. ⛔ DEAD, and the death is instructive

**Spec.** 3-cube of "positions"; each edge direction `i` replaced by a distinct gadget (a `K_i` joined
to both endpoints) so the frame is rigid. Three copies `A,B,C`; a central vertex `m_v` joined to
`A_v,B_v,C_v`. Individualize `m_0`; residual group = diagonal `S₃`. Carriers attach to a triple
`{x₁,x₂,x₃}`, one corner at each of the three positions adjacent to `0`, with one copy doubled —
e.g. `g₁ = {A1,A2,B3}` vs `g₂ = {A1,B2,A3}`.

**⛔ Why it dies (proof, no computation needed).** If `α ∈ Aut(G)` has `α(g₁)=g₂` then `α` maps
`N(g₁)` to `N(g₂)`, so it fixes the position set `{e₁,e₂,e₃}` setwise, hence fixes their **unique**
common neighbour `0`, hence fixes `m₀`. So `α ∈ Aut_{m₀}`. Dichotomy with no third branch:

* **no such `α`** (the actual build — the gadgets that rigidify the corners also make directions 2 and
  3 permanently inequivalent) ⟹ `g₁,g₂` are different `Aut`-orbits, the CAO start already separates
  them, **nothing is tested**;
* **such an `α` exists** (frame symmetrised) ⟹ it fixes `m₀`, so `g₁,g₂` share an `Aut_{m₀}`-orbit and
  1-WL's merge is **correct**.

⚠⚠ **The conditional is sound; do not over-generalize it.** *"A carrier whose attachment set determines
`v` is dead"* is a theorem. *"Attachment sets must determine `v`"* is **false** — Construction B breaks
exactly that premise. This over-generalization was made and corrected in-session.

**Also fails N2**: "which direction is the odd one out" is a root-level invariant, not a uniform fact.

---

## 2. Construction B — the Q₄ complementary-pair carrier. ✅ **A REAL 1-WL COUNTEREXAMPLE**

### 2.1 The idea that makes it work

In `Q_c`, `p` and its complement `p̄ = p ⊕ 1…1` differ in **every** direction, so the pairing `p ↔ p̄`
is invariant under all direction permutations and is therefore **compatible with a rigid frame**. They
share a distance sphere around the base point only when their weights `w` and `c − w` agree, i.e.

> ### ★ `c` must be EVEN. `Q₄` is minimal — this is impossible in `Q₃`.

At weight 2 in `Q₄` the six positions form three complementary pairs, and the quadruple
`Q₀ = {1100, 0011, 1010, 0101}` is a coset of the Klein group `V = {0000, 1111, 0110, 1001}`.
`Q₀`'s common-distance-2 set is `V` itself — **four** candidates, so the attachment set does **not**
pin `m₀`, and N1 is satisfiable.

### 2.2 Spec (as built and measured)

* positions `F₂⁴`; direction `i` (0–3) replaced by a gadget clique on `i+1` vertices joined to both
  endpoints ⟹ frame rigid, `Aut` on one copy = the 16 translations, acting **regularly**;
* three copies `A,B,C`; central vertex `m_v ~ A_v,B_v,C_v`;
* **carriers**: for each coset `R` of `V`, `R` splits into two complementary pairs; a carrier attaches
  to one corner at each of `R`'s four positions, with one copy **doubled on one whole pair** and the
  other two copies on the other pair. 12 patterns per coset × 4 cosets = **48 carriers**.

`n = 352` — 16 centrals, 48 corners, 240 gadget middles, 48 carriers.

### 2.3 Measured — `scratchpad/probe_cao_hypercube.py`

```
Aut-orbits at the root : centrals [16]  corners [48]  carriers [48]   <- CAO start is coarse
g1, g2 same Aut-orbit  : True
   witness             : translation by 0110, sends m_0000 -> m_0110  (it MOVES the base point)
exact CAO start        : carr 48, centre 16, corner 48, mid 24/48/72/96
after individualizing m_0000:
   corner cells        : 16 x [3]   = exactly the Aut_v-orbits
   carrier cells       : 4 x [12]   each splitting [6,6] under Aut_v
   MIXED CELLS         : 4
g1,g2 same 1-WL cell True | same Aut_v-orbit False
```

with `g₁ = {A1,A1',B2,C2'}`, `g₂ = {B1,C1',A2,A2'}` in the reader's notation
(`1=1100, 1'=0011, 2=1010, 2'=0101`).

**Soundness of the two directions** — neither is a bare computation:

* *same root orbit* is witnessed by an **explicitly verified** automorphism (every generator is checked
  to be an adjacency-preserving bijection before use);
* *different `Aut_{m₀}`-orbits* needs an **upper** bound on the stabilizer, which is a proof: any `α`
  fixing `m₀` preserves the 16 position-cells (measured: those are the cells), gadgets exist only
  within a copy, and the position graph is connected ⟹ the copy permutation is constant ⟹
  `Aut_{m₀}` acts on corners and carriers exactly as the **diagonal `S₃`**;
* the start is the **true** orbit partition (centrals/corners/carriers are each a single orbit
  already; only the middles needed merging, per direction, which is their true orbit);
* the comparison group must include the **gadget-internal clique permutations** — they are in the
  stabilizer, and without them the middles report as spurious mixed cells.

### 2.4 2-WL repairs it exactly — `scratchpad/probe_cao_hypercube_2wl.py`

Reduced model (gadget → edge colour, 112 vertices), calibrated against the 352-vertex verdict first:

```
CALIBRATION 1-WL : corner 16x[3]  carrier 4x[12]  g1,g2 same cell True   (matches n=352)
2-WL (4 rounds)  : corner 16x[3]  carrier 8x[6]   separates g1,g2 True
```

⛔ **Why it cannot be lifted, and why the whole family is capped at 1-WL.** The hidden fact is
**binary** — *the two attachments at `p` and `p̄` lie in the same copy* — and 2-WL is the tool that
reads binary facts. It can read it because same-copy is 2-WL-visible: corners in one cube are joined by
gadget paths, corners in different cubes only through centrals. Raising `c` or `k` changes nothing;
a ternary coincidence is a conjunction of pairwise ones. **To beat 2-WL the copy relation itself would
have to be invisible — which is a CFI gauge**, and that is Construction C.

### 2.5 Standing worth

⚠ **The ledger does not move.** 1-WL CAO propagation was already refuted four times (CAO doc §STATUS:
`net(Z₄)`, Shrikhande n=16, Chang-2, `Cay(Z₁₂⋊₅Z₂)`, plus CFI over a random cubic base). B is the
**fifth**, at `n = 352`. Its value is that it is **designed and parametrized**: it answers a question
the doc never asked — *a 1-WL CAO failure can be built to order, with the mechanism chosen in advance*.

---

## 3. Construction C — the gauge/payload ensemble (the 2-WL attempt)

### 3.1 What it is, in one line

**A CFI construction with a `Z₂⁴` gauge group per slot.** The cubes are the gauge (translation acts
regularly on corners), the payload copies are indexed by gauge choices, the central vertices *are* the
gauge, and individualizing one fixes the gauge globally — which is what turns "which corner" into an
absolute **edge type**. The combinatorial explosion is the gauge orbit, not decoration.

**Spec.** A `K_n` payload (`n = 16` for the Shrikhande/rook attempt). Each of the `C(n,2)` slots owns
cubes; a copy attaches its label-`i` and label-`j` vertices to a corner pair of slot `{i,j}`, and the
corner pair read *after individualization* is the edge type (connected / disconnected). All copies are
present, so **every graph on the label set is carried simultaneously**.

### 3.2 ★ The gauge-invariance condition — check this before building anything

Translating a cube shifts the corner positions at **both** ends of its slot by the same `t`, so the
gauge-invariant of a slot is

```
δ = p ⊕ p'          (positions of the two attached payload vertices)
```

> **The root is one orbit ⟺ `δ_connected = δ_disconnected`, i.e. `1 ⊕ 1' = 2 ⊕ 2'`.**

If they differ, `δ` is a gauge invariant, the two payload copies sit in different `Aut`-orbits at the
root, and **CAO fails at the root** — Construction A's death, one level up. If they are equal, a single
cube's gauge move flips one slot's type, the gauge acts transitively on all colourings, and the root
genuinely is one orbit. Using complementary pairs (`X` and `X'` opposite corners) satisfies it by
construction, since every complementary pair has `δ = 1…1`.

### 3.2a ★ THE GADGET REDUCTION — one cube per slot, and what the doubling was really for

**Reduction (reader, 2026-08-12, verified here).** The two cubes per slot — present so the encoding
is reversible (`1→1'` vs `1'→1`) — halve to **one cube**, by attaching **both** payload endpoints to
**both** corners of the pair. Symmetric in `i, j` by construction.

Verified in two parts.

**(a) The frame algebra still works** (`scratchpad/probe_cao_gadget_check.py`): the `Q₄` gauge is
**transitive on the 8 unordered complementary pairs** (stabilizer `{0000, 1111}`, order 2, so
`16/2 = 8` types), and `δ = p ⊕ p'` is **constant `1111`** across every complementary pair. ⟹ the
root stays one orbit, and ★ **§3.2's `δ` condition becomes AUTOMATIC** — using complementary pairs,
which the `Q₄` parity insight already forced, discharges it. It stops being a design obligation.

**(b) What the doubling was actually load-bearing for** — and it is **not** root symmetry
(`scratchpad/probe_cao_gadget_variants.py`, small ensemble, `L = 4`):

| frame shape | gauge is an aut | transposition is an aut | it fixes `m(0)` | |
|---|---|---|---|---|
| **both-to-both** (one cube) | ✓ | ✓ | ✓ | **PASS** |
| one cube, ordered, `m` holds one corner | ✓ | ✗ | — | **FAIL** |
| two cubes, opposite orientations (the original) | ✓ | ✓ | ✓ | **PASS** |

> ### ★★ The real obligation: `m` must hold exactly ONE corner per cube — that is what makes it a
> gauge choice — and the label transposition must still be an automorphism **fixing `m`**, or
> `Aut_m` loses its transpositions and **T4 fails**.
> The original doubling buys that by letting the transposition **swap the cubes**. Both-to-both buys
> it more cheaply: the transposition then fixes the frame **pointwise**, so it fixes every `m(g)`
> outright. ⟹ the reduction is not a convenience — it makes T4 nearly trivial.

⚠⚠ **A modelling trap, hit here:** the first run reported the two-cube original as **FAIL**. That was
wrong — the transposition there must **swap the cubes**, not swap the ends within a cube, and mapping
ends breaks `m`. Do not re-derive "the original design was broken"; it was the model that was.

### 3.3 What the construction reduces to

`Aut = gauge ⋊ (label symmetries)`; after individualizing `m` the gauge dies and `Aut_m` is the label
group, so **`Aut_m`-orbits of copies = isomorphism classes of graphs on the label set**. Hence

> ### CAO propagation fails at `k`-WL ⟸ encoded-`k`-WL is not a complete isomorphism invariant on graphs over the label set.

Because the ensemble carries every payload, **you never have to choose the payload**: if *any* two
non-isomorphic graphs are fused, CAO fails. Since no fixed WL level is a complete invariant (CFI),
this is the strongest form of the program, and **nothing measured here refutes it.**

### 3.4 Sizing — you do not need `16^240`

The copy set only has to be closed under the gauge, and you only have to gauge the slots where the two
target graphs differ: gauge `d = |E(G) △ E(H)|` slots ⟹ `2^d` copies. For `C6` vs `2C3` (labelled
`12,23,34,45,56,16` vs `12,13,23,45,46,56`) the symmetric difference is `{34,16,13,46}`, so `d = 4` →
**16 copies**, a ~142-vertex test object.

⚠⚠ **But restricting the gauge is exactly the leak the design guards against** — a gauge that touches
only some corners is visible pre-individualization. Preserving *every* symmetry costs `16^{C(n,2)}`
copies and is untestable at any `n`. **The frozen-frame abstraction (§4) is the way out of that bind**,
and it is what the only decisive test used.

---

## 4. ⛔ The Shrikhande/rook payload is DEAD — measured

### 4.1 The premise, checked — `scratchpad/probe_cao_payload_pair.py`

```
A. 2-WL, plain graphs              : equivalent = True     <- the pair IS 2-WL-blind
B. 2-WL, one vertex individualized : equivalent = False
     Shrikhande extension cells [1, 3, 6, 6]
     rook 4x4   extension cells [1, 6, 9]
```

★ **The payload property that matters is not "2-WL-blind" but "2-WL-blind under the encoding".**
One individualized vertex is enough to separate the bare pair — those are §14.1's numbers.
Construction C individualizes the **gauge**, not a payload vertex, so B does not by itself kill it;
it sets the bar: **no payload vertex and no payload label may become pinned.**
⚠ The subdivided cases (C/D) in that probe were **never run** — the job was killed. Do not cite them.

### 4.2 The triangle-frame test — `scratchpad/probe_cao_triangle_frame.py`

`K16` + a frame vertex on **every** pair, coloured **only** by edge type (never given an identity of
its own — the faithful abstraction of the shared, ensemble-symmetric frame). 272 vertices, no component
marker, so separation has to be earned.

| model | frame constraint | control (S vs S) | Shrikhande vs rook |
|---|---|---|---|
| disjoint | none | not separated | **separated** (5 rounds, 217 colours) |
| disjoint | frame-frame pairs frozen, orbit-level | not separated | **separated** (3 rounds) |
| disjoint | frame-frame frozen, **minimal** | not separated | **separated** (5 rounds, 75 colours) |
| shared frame | none | not separated | **separated** (5 rounds, 1408 colours) |
| shared frame | frozen, orbit-level | not separated | **separated** (4 rounds, 352 colours) |
| shared frame | frozen, **minimal** | not separated | **separated** (5 rounds, 246 colours) |

★ The **minimal** rows are the load-bearing ones: there the frame-frame pairs know only their two
types — no same-cube, no share-a-label — which is strictly **coarser** than the `Aut_m`-orbit partition
of those pairs, so that model hands 2-WL strictly *less* than the real object can. It still separates.

⚠ The orbit-level freeze produced *more* colours than no freeze (16398 vs 217) because its atom is
finer at round 0 (it hands over "share a label" immediately). It is therefore neither uniformly
stronger nor weaker; the **minimal** rows are the ones to quote.

### 4.3 The mechanism, and it is not a modelling artefact

> ### ★★ 2-WL cannot distinguish Shrikhande from rook 4×4, but it CAN distinguish their triangle-extended versions.

Promoting edges to vertices is what does it: a **pair** of frame vertices is a pair of edges, hence up
to **four** payload vertices, so 2-WL on the extension carries a 4-vertex window on the payload.
Shrikhande and rook differ exactly at four vertices — measured:

```
K4 count   Shrikhande 0    rook 4x4 8   (4 rows + 4 columns)
```

⛔ **The skip-recolouring rule cannot repair this.** That rule constrains the frame's *vertex* cells;
the information lives in *pair* colours. Frame-frame pairs were frozen completely and it still
separated, so the channel is the **payload-frame** pairs — which cannot be frozen without deleting the
encoding itself, since they are what carries the edge type.

---

## 5. ★★★ THE PAYLOAD ADMISSION TEST — what the frame hides, and what it cannot

**The design intent** (reader, and it is the right frame for the whole scheme): the edge vertices are
built to obscure as much as possible of the fact that they *are* edges. Their 1-WL content is forced
static; their 2-WL+ content is still computed, but the only place it can say anything is **inside the
payload's own edge set** — stepping outside lands either in the full ensemble (every graph present, so
symmetric by construction) or in the cube (symmetric by construction). So the extra strength available
to 2-WL is exactly *2-WL on the edge-bisected payload*. Hence:

> ### ▶ A candidate payload pair must be 2-WL-resistant **after edge-bisection**, not before.
> ⚠ **Stated as a NECESSARY condition, and only that direction is supported.** *Fails the test ⟹
> dies* is what §4.2/§4.3 measure, and it is the direction that makes it a useful filter — apply it to
> any candidate **before** building anything around it. **The converse (*passes ⟹ survives*) is a
> design conjecture, not a theorem**: it assumes the ensemble contributes nothing (§6), and there is no
> theorem here bounding what the encoded closure can compute. Do not quote this as an `iff`.

**The measured calibration is consistent with that account, and rules out the simpler readings:**

| payload pair | bare | triangle-extended | gain |
|---|---|---|---|
| `C6` vs `2C3` | 1-WL blind | 1-WL **still blind** | **0 levels** |
| Shrikhande vs rook | 2-WL blind | 2-WL **separates** | **≥ 1 level** |

(control `C6` vs `C6` extended: not separated, so the rung-1 negative is real.)

⚠⚠ **The cost is NOT a constant — an earlier "the encoding hands WL exactly one extra level" is
RETRACTED.** At `k = 1` the encoding buys nothing: 1-WL's state is a single vertex and its aggregation
is a multiset, so it can see an edge but cannot correlate two of them. At `k = 2` the state is a pair
of frame vertices = four payload vertices, and that is where the gain appears. The cost scales with `k`
because a `k`-tuple of frame vertices spans up to `2k` payload vertices.

⚠ **`≥ 1` is a lower bound only.** Shrikhande/rook falls to 3-WL anyway, so it cannot exhibit a gain
larger than one level even if the extension delivers more. **Nothing here bounds the cost above.**
Budget generously: *"a payload that beats 4-WL to beat 2-WL"* is a safe floor, not a target. Pinning
the number needs calibration against CFI pairs of known WL-hardness — not yet done.

**One assumption inside the admission test**: that the ensemble contributes nothing. ✅ **Measured
TRUE at rung 1** (§6 — the full `2^15`-copy ensemble separates `C6` from `2C3` no better than the
two-copy model). ⚠ Assumed, not measured, at rung 2.

### 5.1 ▶ CFI PAYLOADS — the first candidates that pass anything

`scratchpad/probe_cao_cfi_frame.py`. Both CFI pairs are checked 2-WL-blind **bare** first, so the
test is not vacuous: `CFI[K4]` (`n = 28`) and `CFI[K5]` (`n = 60`), plain vs twisted, **equivalent =
True**. ★ `CFI[K4]` already suffices — base treewidth 3 > 2 — so the payload costs `n = 28`, **not**
the `n = 60` of `K5`.

| payload | encoding | union `|V|` | control | 2-WL separates? |
|---|---|---|---|---|
| `CFI[K4]` | subdivision (edges only) | 152 | clean | ⭕ **No — survives** |
| `CFI[K5]` | subdivision (edges only) | 440 | clean | ⭕ **No — survives** |
| `CFI[K4]` | full, ⚠ **non-faithful variant** (see below) | 812 | clean | ⛔ Yes — separates, diverging at **round 2** |
| **`CFI[K4]`** | **full, faithful** (clique payload) | **812** | **clean** | ⛔⛔ **YES — SEPARATES**, diverging at **round 3**, 1848 colours vs the control's 567 |
| `CFI[K5]` | full | 3660 | — | ⛔ out of reach (`n³` time, `n²` signatures) |

> ### ⛔⛔ VERDICT: `CFI[K4]` FAILS the payload admission test.
> The full all-pairs frame cracks a pair that is 2-WL-blind bare, so **encoded-2-WL ≥ bare-3-WL** on
> this pair. `CFI[K4]` is out as a payload, and subdivision was indeed the weak encoding: the same
> pair survives it (row 1) and dies here.

⚠⚠ **THE FAITHFULNESS DEFECT IN ROW 3 — found after that run, kept only as provenance.** It retained
the payload's **own edges** alongside the typed frame vertices; Construction C makes the copy a
**complete** graph with adjacency living *only* in the types (as `probe_cao_triangle_frame.py` does).
So it handed 2-WL the adjacency **twice** — atomically at round 0 *and* through the frame. Fixed in
`encode`; row 4 is the verdict. ★ **The two rows agree and the fix behaved exactly as predicted**: the
faithful model diverges one round *later* (3 vs 2) and reaches the same 1848 colours, which is what
removing a duplicated round-0 signal should do. Raw output kept at `scratchpad/cfi_frame_unfaithful.out`.

### 5.2 ▶ WHERE THE CALIBRATION NOW STANDS — and the one measurement that would settle it

| pair | bare WL dimension | encoded, tested at | result |
|---|---|---|---|
| `C6` / `2C3` | 2 (1-WL blind) | 1-WL | survives ⟹ **gain 0** |
| Shrikhande / rook | 3 (2-WL blind) | 2-WL | separates ⟹ **gain ≥ 1** |
| `CFI[K4]` | 3 (2-WL blind) | 2-WL | separates ⟹ **gain ≥ 1** |
| **`CFI[K5]`** | **4 (3-WL blind)** | **2-WL** | **▶ NOT RUN — the decisive cell** |

Both rung-2 points give `≥ 1` and **neither bounds the gain above**, so the two live readings are
still open: *"costs exactly one level"* (⟹ `CFI[K5]` is the payload, and the programme is sound but
huge) versus the **doubling** reading, *encoded-`k`-WL ≈ bare-`2k`-WL* (⟹ `CFI[K5]` dies too and the
payload must be 4-WL-blind, i.e. CFI over a treewidth-5 base). A 3-WL-blind pair tested at encoded
2-WL separates them, and `CFI[K5]` full at `n = 3660` is the only instance in hand.

**▶ To make that run possible**, one of: (a) a C implementation of the counting-signature 2-WL —
`n³ ≈ 4.9×10^10` simple ops per round is ~2–3 min/round in C against ~4 h in Python; (b) a
**smaller 3-WL-blind pair** than `CFI[K5]`'s 60 vertices, which would shrink `C(n,2)` quadratically
and is the higher-leverage search; (c) an algorithmic 2-WL (partition-refinement rather than
recolour-everything). ⛔ Do **not** attempt it in the current Python prober.

⚠⚠ **The two ⭕ rows are NOT the admission test being passed.** They use **subdivision**; Construction
C types **every pair**, edges and non-edges alike — that is the `full` row, and the same `CFI[K4]`
that survives subdivision **dies** there. ⟹ **subdivision is the weak encoding, and measuring it
answers a different question.** Keep the rows only as the contrast that establishes it.

---

## 6. ✅ THE ENSEMBLE IS PASSIVE AT RUNG 1 — RAN 2026-08-12

**The worry.** With every colouring present, WL gets the whole **Hamming structure on colouring
space** as a reference frame: two copies differing in a single slot agree at all the others, and that
relation is WL-visible. §3.3's reduction and §5's admission test both silently assume this contributes
nothing. It is the only unproved step in the scheme, so it was measured.

**Object** — `scratchpad/probe_cao_ensemble.py`, Construction C at rung 1 with **nothing restricted**:
6 labels, 15 slots, gauge `Z₂` per slot, **all `2^15` copies and all `2^15` central vertices**.
`|V| = 229,406`, `|E| = 1,966,095`.

```
CAO start cells : payload 196608 | frame 30 | centrals 32767 | m(0) individualized
1-WL            : stabilized in 4 rounds -> 292 payload cells
Aut_v = S_6     : 544 true orbits on the payload
MIXED CELLS     : 100        (orbits fused per cell, top 10: 9 9 8 8 8 8 7 7 7 7)
C6 copy cells [218] | 2C3 copy cells [218]
   share a 1-WL cell: True   |   share an Aut_v-orbit: False
```

> ### ▶ VERDICT: the full ensemble gives 1-WL **nothing** beyond the two-copy model.
> The two-copy model did not separate `C6` from `2C3` (§5) and neither does the ensemble — they land
> in the *same* cell 218 while sitting in different `Aut_v`-orbits. ⟹ **§5's admission test's ensemble
> assumption HOLDS at rung 1**, measured. ⚠ Rung 1 only; this is evidence for the rung-2 case, not a
> proof of it, and the Hamming structure is genuinely richer at higher WL levels.

★★ **And it is a second designed 1-WL CAO-propagation counterexample — Construction C's machinery
working end to end**, with the payload *chosen* rather than inherited from the frame, and 100 mixed
cells rather than 4.

**Both group facts are proved, not assumed, and the orbit count is independently cross-checked.**
The CAO start is exactly three cells because the gauge `(Z₂)^15` and the label group `S₆` are jointly
transitive on each kind and the kinds cannot merge (degrees 10 / ~49k / 15); `Aut_{m(0)} = S₆`
**exactly**, because a stabilizing `α` preserves `m(0)`'s neighbourhood hence types, "two slots share a
label" is recoverable (disjoint slots have no common payload neighbour), `Aut(T(6)) = S₆`, and the slot
permutation then determines the action on every copy. **Burnside cross-check** of the union-find:
`156` iso classes of 6-vertex graphs (known value) and `544` orbits on (graph, marked vertex) — both
match exactly.

**▶ What it leaves.** Rung 2 is now purely a **payload-budget** question: CFI over a treewidth-4 base
(`CFI[K5]`, 60 vertices) is the natural candidate, putting the frame at `C(60,2) = 1770` slots and the
ensemble at `2^1770` copies. Untestable — but that is a **size** problem, not a soundness problem, and
the two things that could have made it a soundness problem (the frame leaking, §4; the ensemble
leaking, here) are now one measured-dead and one measured-clean.

---

## 7. Reusable filters extracted (apply before building)

1. **N1 / N2** (§0) — the fusing automorphism must move `v`; the distinguishing relation must be
   uniform at the root.
2. **The attachment-set test** (§1) — if the carrier's attachment set determines `v`, it is dead.
   ⚠ Conditional only; `Q₄` complementary pairs break its premise.
3. **The parity test** (§2.1) — complementary-pair carriers need `c` **even**.
4. **The `δ` test** (§3.2) — `1 ⊕ 1' = 2 ⊕ 2'` or the root is not CAO. ✅ **Discharged automatically**
   by complementary-pair corners (§3.2a); keep the test only for non-complementary designs.
4b. **The transposition-fixes-`m` test** (§3.2a) — for any frame shape, check that a label
   transposition is an automorphism *and* fixes the individualized central vertex. It is the cheapest
   way to catch a frame that silently loses T4, and it is what separates the three shapes.
5. **The payload admission test** (§5) — 2-WL-resistant *after edge-bisection*, not before.
   ⚠ **Necessary only** — a cheap kill for any design that encodes payload adjacency as vertices
   (Shrikhande/rook fails it); passing it is **not** a survival guarantee.
6. **The binary-coincidence test** (§2.4) — if the hidden fact is a pairwise coincidence, 2-WL reads it.

---

## 8. Files and reproduction

| file | what it does | runtime |
|---|---|---|
| `scratchpad/probe_cao_hypercube.py` | Construction B at `n = 352`; verified generators, true CAO start, mixed-cell verdict | < 1 s |
| `scratchpad/probe_cao_hypercube_2wl.py` | reduced 112-vertex model; 1-WL calibration + the 2-WL repair | ~5 s |
| `scratchpad/probe_cao_payload_pair.py` | Shrikhande/rook: 2-WL plain vs one-point extension (⚠ cases C/D never ran) | ~1 s for A/B |
| `scratchpad/probe_cao_triangle_frame.py` | the triangle-frame kill, 6 variants + controls; `disjoint`/`shared`, `freeze` ∈ `False`/`True`/`'minimal'` | ~1–3 min |
| `scratchpad/probe_cao_ensemble.py` | §6 — Construction C at rung 1, full symmetry, `n = 229406`; 100 mixed cells | ~2 min |
| `scratchpad/probe_cao_gadget_check.py` | §3.2a(a) — gauge transitive on the 8 complementary pairs; `δ` constant | < 1 s |
| `scratchpad/probe_cao_gadget_variants.py` | §3.2a(b) — the three frame shapes vs the transposition-fixes-`m` test | < 5 s |
| `scratchpad/probe_cao_cfi_frame.py` | §5.1 — CFI payloads through the frame; `<m> <sub\|full>` | 152/440 fast; 812 ~1 h |

**Lean.** `GraphCanonizationProofs/ChainDescent/CaoEnsemble.lean` — the index-level skeleton
(`gact_transitive` = T1, `gact_eq_self_iff` + `lact_base` = T2⁻, `Propagates` +
`not_propagates_of_merge` = the target and the bridge the probes instantiate). Builds clean, all
declarations `[propext, Classical.choice, Quot.sound]`, no `sorry`, no custom axiom. ⚠ **Not in
`scripts/build.sh`'s `MODULES` list** — the gate is a hand-maintained enumeration, so this is
unbuilt by the gate until someone adds it. ⛔ It contains **no graph, no adjacency and no refiner**:
T2⁺ (`Aut_m` is *exactly* the label group, needing `Aut(T(n)) = Sym n`) and T3 (the frame's cells are
the position classes) are **not** in it.

⛔ **Two process traps hit while producing this, both already in the CAO doc §9 — do not repeat.**
(a) `pkill -f probe_...` **matches your own launcher** ⟹ self-kill, exit 144; kill by PID.
(b) A 1-WL stop condition of the form `len({(old,new)}) == len(set(new))` is **always true** (the new
colouring always refines the old), so the loop returns after one round; compare
`len(set(new)) == len(set(old))` instead. This produced a wrong `[3,45]` corner split before it was
caught.

⚠ Run the 272-vertex and 128-vertex jobs **one at a time** — running them concurrently thrashed memory
badly enough to stall a 32-vertex job to > 120 s.

---

## 9. Provenance

Measured (this doc): §2.3, §2.4, §3.2a, §4.1 A/B, §4.2, §4.3 K4 counts, §5's calibration table,
§5.1's two subdivision rows, §6.
Proved, not measured: §1's dichotomy, §2.3's and §6's `Aut_v` upper bounds, §2.1's parity requirement,
§3.2's `δ` condition, §3.3's reduction. Cross-checked: §6's 544 orbits (Burnside, plus the known 156).
Machine-checked: T1 and T2⁻ in `ChainDescent/CaoEnsemble.lean` (axiom-clean; ⚠ not gate-listed).
▶ **Outstanding: §5.2's `CFI[K5]`-full cell — the only measurement that separates "costs one level"
from "doubling", and out of reach of the Python prober.**
Argued, not established: §5's admission test — ⚠ **necessary direction only**; its ensemble assumption
is measured at **rung 1** (§6) and *assumed* at rung 2. Also the claim that the 4-vertex window is
*the* separating mechanism in §4.3 — consistent with the numbers, not isolated by ablation.
