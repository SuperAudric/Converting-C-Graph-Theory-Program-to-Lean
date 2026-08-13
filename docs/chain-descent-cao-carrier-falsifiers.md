# CAO carrier/payload falsifier constructions — the record

> **What this is.** Three related *designed* attacks on CAO propagation, raised from outside the
> project (2026-08-12) and measured here. **Construction B is a genuine 1-WL CAO-propagation
> counterexample** — the first on record built to order rather than found by sweeping. **Construction
> C is the 2-WL attempt**: its machinery runs end to end at rung 1 (**100 mixed cells**, §6), and both
> payloads tried — Shrikhande/rook (§4) and `CFI[K4]` (§5.1) — separate under the two-copy model.
>
> ⛔⛔⛔ **AUDITED 2026-08-13 (§6a, §6b), and the picture changed.** That two-copy model is **not the
> construction**: the real ensemble's 1-WL sees only the degree sequence, so it is far coarser
> (**292 cells / 100 mixed** vs the model's **538 / 6**), and §6's *"the ensemble is passive"* is
> **withdrawn** — its witness was degree-regular and could not have detected the gap. ⟹ **neither
> payload is established dead for Construction C.** What *is* established, proved and measured on the
> real object, is sharper than either kill: **2-WL reads an edge encoded as a typed common neighbour,
> so the frame hides the payload COMPLETELY at 1-WL and NOT AT ALL at 2-WL** (§6b). The scheme is not
> refuted; it is blocked on **tooling that can run 2-WL on a shared-frame object**.
>
> ⚠ Companion, not replacement: [`chain-descent-cao-propagation.md`](./chain-descent-cao-propagation.md)
> owns the *question*. Read its §1 (the hypothesis), §3 (the coupling principle) and §14 (the anatomy
> and the arity ladder) before this. ⚠ The research phase is closed
> ([`chain-descent-wind-down.md`](./chain-descent-wind-down.md)); this is a **record**, not a live track.

---

## ▶▶ HANDOFF — start here

**Where it stands, in five sentences.** The CAO-propagation hypothesis starts from the *exact orbit
partition* (§0) — forget that and you will build something that fails at the root instead of at
propagation, which is how Construction A died (§1). A `Q₄` complementary-pair carrier **is** a 1-WL
counterexample (§2, `n = 352`, 4 mixed cells), and the gauge-ensemble Construction C is a second one
at rung 1 (§6, `n = 229,406`, 100 mixed cells) — so at 1-WL the design programme **works**. At 2-WL
everything turns on a payload surviving the frame encoding; the two tried both separate under the
**two-copy model** (§4, §5.1) — ⚠ but that model has since been measured **unfaithful** (§6a), so
those are not yet verdicts about Construction C. What *is* settled about the real object is worse
for the programme than either kill: **2-WL reads the encoded adjacency directly, no matter how
symmetric the frame** (§6b, proved and measured).

**Reading order.** §0 (the hypothesis + N1/N2) → §7 (the filters — cheapest thing in the doc) →
§2 (the construction that works) → §3 incl. **§3.2a** (the gadget reduction) → §5 + **§5.2** (the
payload bar and the calibration) → §6, **§6a, §6b** (the ensemble, the model audit, the theorem) →
§8 (files) → §9 (what is proved vs measured vs argued).

> ### ▶ IF YOU DO ONE THING
> **Read §6a before quoting any 2-WL verdict in this doc.** The two-copy private-frame model that
> every 2-WL row is measured in has been shown to disagree with the real ensemble at the one level
> where both are computable (1-WL: **538 cells / 6 mixed** vs the ensemble's **292 / 100**), and at
> 2-WL the two are **incomparable**, not merely one-sided. §5.2's `CFI[K5]` cell is still the open
> *calibration* measurement, but it calibrates the model, not the construction.

> ### ⛔ WHAT NOT TO DO
> * Do **not** quote §5's admission test as an `iff` — only *fails ⟹ dies* is supported (§5, §9).
> * Do **not** quote §4 or §5.1 as *"Construction C cannot use this payload"*. They are statements
>   about the two-copy model. §6a is why. (What *does* transfer to the real object is §6b.)
> * Do **not** repeat §6's inference *"the ensemble is passive"*. It is **withdrawn** (§6a): the
>   ensemble is far coarser than the model, and the witness pair could not have detected it.
> * Do **not** measure **subdivision** and conclude anything about the construction: `CFI[K4]`
>   survives subdivision and dies under the real all-pairs encoding (§5.1).
> * Do **not** re-derive *"the original two-cube design was broken"* — that was a modelling error of
>   mine, corrected in §3.2a.
> * Do **not** attempt `CFI[K5]`-full in `probe_cao_cfi_frame.py`; it is ~4 h/round (§5.2).
> * Do **not** assume `Aut_v` is the group you compared against — every mixed-cell count here needs
>   a proved **upper** bound on the stabilizer (§2.3, §6), and only T2⁻ is machine-checked (§8).

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

## 4. ⛔ The Shrikhande/rook payload dies IN THE TWO-COPY MODEL — measured

> ⚠⚠ **Heading corrected 2026-08-13.** It read *"is DEAD"*. The measurement is real and reproduces,
> but it lives in the two-copy private-frame model, which **§6a shows is not the construction**. Read
> §6a before carrying this row anywhere.

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

> ### ★★ 2-WL cannot distinguish Shrikhande from rook 4×4, but it CAN distinguish their frame-encoded versions.
> ⚠ "Triangle-extended" throughout §4 means the **full** encoding — a frame vertex on *every* pair,
> clique payload. It does **not** mean subdivision, and §5.1 shows the two are not interchangeable.

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
to 2-WL is exactly *2-WL on the encoded payload*. Hence:

> ### ▶ A candidate payload pair must be 2-WL-resistant **after the FULL frame encoding**, not before.
> **"Full" is load-bearing and is not edge-bisection.** The encoding is: payload copy = a **clique**,
> a **typed frame vertex on every pair** (edges *and* non-edges), adjacency carried only by the types.
> ⛔⛔ **Subdivision is NOT a proxy for it** — `CFI[K4]` survives subdivision and dies under the full
> encoding (§5.1). The criterion was first phrased as *"still 2-WL-resistant after edge-bisection"*;
> that phrasing is what motivated the test, but the measurement showed the two encodings disagree, so
> **only the full form is the criterion.**
> ⚠ **Stated as a NECESSARY condition, and only that direction is supported.** *Fails the test ⟹
> dies* is what §4.2/§4.3 and §5.1 measure, and it is the direction that makes it a useful filter —
> apply it to any candidate **before** building anything around it. **The converse (*passes ⟹
> survives*) is a design conjecture, not a theorem**: it assumes the ensemble contributes nothing (§6),
> and nothing here bounds what the encoded closure can compute. Do not quote this as an `iff`.

**▶ The measured calibration is §5.2's table — read it there, not here.** Two facts about it belong
with the test itself:

⚠⚠ **The cost is NOT a constant — an earlier "the encoding hands WL exactly one extra level" is
RETRACTED.** At `k = 1` the encoding buys nothing: 1-WL's state is a single vertex and its aggregation
is a multiset, so it can see an edge but cannot correlate two of them. At `k = 2` the state is a pair
of frame vertices = four payload vertices, and that is where the gain appears. The cost scales with `k`
because a `k`-tuple of frame vertices spans up to `2k` payload vertices.

⚠ **Every measured gain is a lower bound only.** A pair that falls to `(k+1)`-WL bare cannot exhibit
a gain larger than one level however strong the encoding is, and both rung-2 pairs on record
(Shrikhande/rook, `CFI[K4]`) are exactly that. **Nothing measured bounds the cost above.** Budget
generously: *"a payload that beats 4-WL to beat 2-WL"* is a safe floor, not a target.

**⛔⛔ THE ASSUMPTION INSIDE THE ADMISSION TEST HAS FAILED ITS AUDIT — §6a, 2026-08-13.** The test
assumes the two-copy private-frame model stands in for the ensemble. It does not: at 1-WL the model
gives **538 cells / 6 mixed** where the ensemble gives **292 / 100**, and at 2-WL the two are
**incomparable** (each has a channel the other lacks — §6a.1). §6's *"measured TRUE at rung 1"* is
withdrawn; its witness `C6`/`2C3` is 2-regular and so could not have detected the disagreement.
⟹ **everything below this line in §5 is a statement about the model, not about Construction C.**
The part of the admission test that survives without any model is the weaker clause proved in §6b:
*a payload pair separated by **bare** 2-WL is dead.*

### 5.1 ⛔ CFI PAYLOADS — `CFI[K4]` TESTED, and dead IN THE MODEL (⚠ §6a)

`scratchpad/probe_cao_cfi_frame.py`. Both CFI pairs are checked 2-WL-blind **bare** first, so the
test is not vacuous: `CFI[K4]` (`n = 28`) and `CFI[K5]` (`n = 60`), plain vs twisted, **equivalent =
True**. `CFI[K4]` is the cheapest pair that is 2-WL-blind at all (base treewidth 3 > 2), which is why
it was tried first — ⚠ **and it does not survive; see the verdict below.** An earlier version of this
section read *"`CFI[K4]` already suffices, so the payload costs `n = 28`"* — **that is REFUTED**, and
the surviving content of it is only that `K4` is where to *start* testing, not where to stop.

| payload | encoding | union `|V|` | control | 2-WL separates? |
|---|---|---|---|---|
| `CFI[K4]` | subdivision (edges only) | 152 | clean | ⭕ **No — survives** |
| `CFI[K5]` | subdivision (edges only) | 440 | clean | ⭕ **No — survives** |
| `CFI[K4]` | full, ⚠ **non-faithful variant** (see below) | 812 | clean | ⛔ Yes — separates, diverging at **round 2** |
| **`CFI[K4]`** | **full, faithful** (clique payload) | **812** | **clean** | ⛔⛔ **YES — SEPARATES**, diverging at **round 3**, 1848 colours vs the control's 567 |
| `CFI[K5]` | full | 3660 | — | ⛔ out of reach (`n³` time, `n²` signatures) |

> ### ⛔⛔ VERDICT: `CFI[K4]` FAILS the payload admission test **as modelled**.
> The full all-pairs frame cracks a pair that is 2-WL-blind bare, so **model-2-WL ≥ bare-3-WL** on
> this pair, and subdivision was indeed the weak encoding: the same pair survives it (row 1) and dies
> here. ⚠⚠ **Corrected 2026-08-13: this is a statement about the two-copy private-frame model, not
> about Construction C** (§6a). `CFI[K4]` is not established dead as a payload.

**✅ The premise of this section is now reproducible** — `scratchpad/probe_cao_cfi_bare.py`. It was
asserted here and measured only ad hoc, which left the whole section unfalsifiable: if the pair were
not 2-WL-blind bare, the frame separating it would mean nothing. Measured:
`CFI[K4]` `n=28` stable after 3 rounds at 14 pair colours, `CFI[K5]` `n=60` after 3 rounds at 19 —
**both plain ~ twisted equivalent = True**.

⚠⚠ **THE FAITHFULNESS DEFECT IN ROW 3 — found after that run, kept only as provenance.** It retained
the payload's **own edges** alongside the typed frame vertices; Construction C makes the copy a
**complete** graph with adjacency living *only* in the types (as `probe_cao_triangle_frame.py` does).
So it handed 2-WL the adjacency **twice** — atomically at round 0 *and* through the frame. Fixed in
`encode`; row 4 is the verdict. ★ **The two rows agree and the fix behaved exactly as predicted**: the
faithful model diverges one round *later* (3 vs 2) and reaches the same 1848 colours, which is what
removing a duplicated round-0 signal should do. Raw output kept at `scratchpad/cfi_frame_unfaithful.out`.

### 5.2 ▶ WHERE THE CALIBRATION NOW STANDS — and the one measurement that would settle it

| pair | bare WL dimension | encoded, tested at | encoding | result |
|---|---|---|---|---|
| `C6` / `2C3` | 2 (1-WL blind) | 1-WL | ⚠ full **+ payload edges** | survives ⟹ **gain 0** |
| Shrikhande / rook | 3 (2-WL blind) | 2-WL | full | separates ⟹ **gain ≥ 1** |
| `CFI[K4]` | 3 (2-WL blind) | 2-WL | subdivision | survives — ⚠ weak encoding, not comparable |
| `CFI[K4]` | 3 (2-WL blind) | 2-WL | **full** | separates ⟹ **gain ≥ 1** |
| `CFI[K5]` | 4 (3-WL blind) | 2-WL | subdivision | survives — ⚠ weak encoding, not comparable |
| **`CFI[K5]`** | **4 (3-WL blind)** | **2-WL** | **full** | **▶ NOT RUN — the decisive cell** |

Every row has a same-pair-against-itself control that came out unseparated, so no row is a machinery
artefact. The `full` encoding is the construction's own (**clique** payload, a typed frame vertex on
every pair); `subdivision` is edges-only and is kept only for the contrast in §5.1.

⚠ **The `C6`/`2C3` row used the same non-faithful variant as §5.1's row 3** (frame on every pair, but
the payload keeping its own edges instead of being a clique). **Its conclusion is safe anyway, and
only because it is a survival**: that model is strictly *stronger* than the construction's, so failing
to separate there means failing to separate under the faithful encoding a fortiori. ⛔ The same
reasoning does **not** rescue a separation — which is exactly why §5.1's row 3 had to be re-run and
row 4 is the verdict. **If you re-derive the rung-1 row, use the clique payload.**

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

## 6. THE RUNG-1 ENSEMBLE — RAN 2026-08-12. ⚠ Its verdict is WITHDRAWN by §6a

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

> ### ⛔⛔ VERDICT WITHDRAWN 2026-08-13 — see §6a.
> It read: *"the full ensemble gives 1-WL **nothing** beyond the two-copy model"*, inferred from the
> two landing in the same cell 218. The inference is **void**: the ensemble gives 1-WL not *the same
> as* but **far less than** the two-copy model, and the witness pair is degree-regular so it could not
> have told the two apart. The **numbers above are correct and reproduce**; only the inference drawn
> from them is withdrawn.

★★ **It is still a second designed 1-WL CAO-propagation counterexample — Construction C's machinery
working end to end** — with 100 mixed cells rather than 4. ⚠ But §6a shows the payload was *not*
effectively chosen: at 1-WL this object cannot see a payload at all, so any two 6-vertex graphs with
a common degree sequence and different iso type would have served equally.

**Both group facts are proved, not assumed, and the orbit count is independently cross-checked** —
this part is untouched by §6a, and without it the 100 is unfalsifiable. The CAO start is exactly
three cells because the gauge `(Z₂)^15` and the label group `S₆` are jointly transitive on each kind
and the kinds cannot merge (degrees 10 / ~49k / 15); `Aut_{m(0)} = S₆` **exactly**, because a
stabilizing `α` preserves `m(0)`'s neighbourhood hence types, "two slots share a label" is recoverable
(disjoint slots have no common payload neighbour), `Aut(T(6)) = S₆`, and the slot permutation then
determines the action on every copy. **Burnside cross-check** of the union-find: `156` iso classes of
6-vertex graphs (known value) and `544` orbits on (graph, marked vertex) — both match exactly, and
`544` is independently reproduced by `probe_cao_ensemble_audit.py`.

---

## 6a. ⛔⛔ THE TWO-COPY MODEL IS UNFAITHFUL — AUDITED 2026-08-13

`scratchpad/probe_cao_ensemble_audit.py`, `probe_cao_ensemble_exact.py`.

**The finding, in one line.** The rung-1 ensemble's 1-WL payload partition is **exactly**

```
colour(c, i)  =  (degree sequence of G_c,  deg_{G_c}(i))
```

— verified **elementwise** against the real 229,406-vertex object, not inferred from matching counts.
It reproduces all three of §6's numbers: **292** cells, **544** orbits, **100** mixed.

**Why, structurally — and the reason is level-independent, not an artefact of rung 1.** The frame is
**shared**: 30 frame vertices carry all `2^15` copies. `S₆` is transitive on slots and `m(0)` marks
type 0, so a frame **vertex** can hold exactly **two** colours, for ever. A payload vertex `p(c,i)`
sees five clique neighbours — *all* of them, so adjacency is invisible there — plus one frame
neighbour per slot contributing only a **count of type-0**, which is `deg(i)`. Iterating adds the
multiset of the other five colours. That is the whole fixpoint.

**What that does to the two-copy model.** The admission test (§5) is calibrated on
`probe_cao_triangle_frame.py`'s `disjoint` shape, where each copy owns a **private** frame vertex per
pair — and those *do* accumulate copy-specific data. Same question, same rung, measured:

| model | payload cells | mixed cells | vs the 544 true orbits |
|---|---|---|---|
| the **real ensemble** (shared frame, all `2^15` copies) | **292** | **100** | far coarser |
| the **two-copy `disjoint` model** (private frame) | **538** | **6** | nearly exact |

> ### ⛔ The two-copy model separates ~94 orbit-fusions the real construction does not.
> It is not a conservative abstraction of the ensemble; it is a **much stronger object**.

**⚠⚠ And §6's witness could not have detected this.** `C6` and `2C3` are both **2-regular**, so they
are identical under the weakest invariant there is. A validation whose witness is degree-blind cannot
distinguish *"the ensemble equals the model"* from *"the ensemble sees only degrees"* — and it was
the second. **A single agreeing data point is not a validation of an abstraction; compare the
partitions.**

### 6a.1 At 2-WL the two are INCOMPARABLE — so neither direction transfers

⚠ Do **not** patch this by saying *"the model is stronger, so its survivals are sound"*. That rule
(§8(c)) applies to a coarser **colouring of the same graph**; the ensemble and the two-copy model are
**different graphs**, and WL power is not monotone across that. At 2-WL each has a channel the other
lacks:

| channel | two-copy model | real ensemble |
|---|---|---|
| frame–frame pairs = a 4-payload-vertex window (§4.3's stated mechanism) | **present**, copy-specific | **absent** — a frame pair is shared by *every* copy, so it cannot carry copy-specific data |
| the `2^{C(n,2)}` **central** vertices | **absent entirely** — no 2-copy model has them | **present**: `(p(c,i), m(g))` counts `#{k ∋ i : g_k = c_k}`, so a pair of payload vertices can be correlated *through a central* — §6's own "Hamming structure" worry, real at 2-WL and still unmeasured |

⟹ **neither survivals nor separations transfer rigorously.** Both 2-WL kills (§4, §5.1) carry an
open faithfulness question, and so does any future `CFI[K5]` row.

### 6a.2 ⚠ §4.3's stated mechanism does not survive its own evidence

§4.3 blames the separation on *"a pair of frame vertices = a pair of edges = four payload vertices"*.
Two facts already in this doc contradict that being the channel:

* **subdivision** also makes pairs of frame vertices span four payload vertices, yet `CFI[K4]`
  **survives** subdivision and dies under `full` (§5.1);
* the **minimal-freeze** rows (§4.2) kill the frame–frame channel outright and **still separate**.

So the 4-subset window is not the mechanism, or not the only one. §9 already flagged this as *"not
isolated by ablation"* — it is now actively **counter-indicated**, and the honest reading is that the
surviving channel is **payload–frame** pairs (a 3-subset window `{x, i, j}`), which is also the one
channel that *does* survive frame-sharing.

---

## 6b. ★★★ WHAT DOES TRANSFER: 2-WL READS THE ENCODED EDGE — proved, and measured on the real object

This is the one 2-WL statement in the doc that needs no model.

> ### ★★★ In the ensemble, `p(c,i)` and `p(c,j)` have `f({i,j}, c_{ij})` as a **common neighbour**, and after `m(0)` is individualized that vertex's type is **absolute**. An edge encoded as a typed common neighbour is exactly what 2-WL counts. ⟹ 2-WL recovers the adjacency of **every** copy at round 1, however shared and however symmetric the frame is.

**Measured — `scratchpad/probe_cao_ensemble_2wl.py`, and it is the first 2-WL measurement anywhere in
this doc on the real shared-frame, full-gauge object** (`L = 4`, `n = 332`: 256 payload, 12 frame,
64 central; the `L = 6` object is 229k and out of reach at 2-WL):

```
round 1: 27 -> 82   round 2: 82 -> 3614   round 3: 3614 -> 5344   round 4: stable
payload-pair colours on type-1 slots 20, on type-0 slots 20, overlap 0
==> 2-WL RECOVERS every copy's adjacency: True
payload vertex cells 20 | true Aut_m = S_4 orbits 20 | MIXED CELLS 0
```

**Consequences, and they are the load-bearing ones:**

1. **`encoded-2-WL ≥ bare-2-WL`, unconditionally and in the real object.** The design intent — *"the
   edge vertices obscure that they are edges"* — **fails at 2-WL by construction**. It succeeds
   completely at 1-WL (§6a: the payload is invisible), and that gap is exactly why the programme
   works at rung 1 and stalls at rung 2.
2. **§5's admission test keeps its necessary direction without the model.** *A payload pair that
   `bare-2-WL` separates is dead* is now a theorem, not a measurement in an unfaithful abstraction.
   ⚠ It is the *weaker* necessary condition than §5's; the stronger form (2-WL-resistant after the
   full encoding) still rests on the two-copy model and inherits §6a.
3. ⚠ **It does not kill the programme.** The payload pairs of interest are 2-WL-blind *bare*, so
   clause 1 does not touch them. What it removes is any hope that the frame *hides* a payload from
   2-WL — the payload must carry the whole burden itself.
4. ▶ It is the natural next **Lean** target: it needs a refiner in the Lean layer (T3's dependency)
   and it is a statement about one round, not a fixpoint.

**▶ What §6 + §6a + §6b leave.** Rung 2 is **not** settled either way, and the reason has changed.
It is *not* that the frame leaks and the ensemble does not (§6's reading — withdrawn). It is that
**at 1-WL the frame hides the payload completely** (§6a) and **at 2-WL it hides nothing at all**
(§6b), so the entire question is whether a payload can carry the burden alone, against an encoding
whose extra strength over bare 2-WL is **still unmeasured on the real object**. Every number bearing
on that extra strength (§4, §5.1, §5.2) comes from an abstraction now known to disagree with the
ensemble. ⟹ the binding constraint is **tooling that can run 2-WL on a shared-frame object**, not a
bigger payload.

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
5. **The payload admission test** (§5) — 2-WL-resistant *after the **full** frame encoding* (clique
   payload + typed frame vertex on **every** pair), not before, and ⛔ **not** after mere subdivision.
   ⚠ **Necessary only**, and ⚠⚠ **measured in a model that failed its audit (§6a)** — treat a failure
   here as a reason to look harder, not as a kill. The clause that is model-free is 5′.
5′. **The typed-common-neighbour test** (§6b) — ★ *if bare 2-WL separates the pair, it is dead*, and
   this one is a **theorem about the real object**: an edge encoded as a typed common neighbour is
   exactly what 2-WL counts, so no amount of frame-sharing or gauge symmetry hides it.
6. **The binary-coincidence test** (§2.4) — if the hidden fact is a pairwise coincidence, 2-WL reads it.
7. ★ **The partition-comparison rule** (§6a) — when validating an abstraction against the object,
   **compare the whole partitions, not one witness pair**. §6 validated on `C6`/`2C3`, which are
   2-regular and therefore agree under *every* candidate invariant; the abstraction was off by
   538 vs 292 cells and the test could not see it.

---

## 8. Files and reproduction

| file | what it does | runtime |
|---|---|---|
| `scratchpad/probe_cao_hypercube.py` | Construction B at `n = 352`; verified generators, true CAO start, mixed-cell verdict | < 1 s |
| `scratchpad/probe_cao_hypercube_2wl.py` | reduced 112-vertex model; 1-WL calibration + the 2-WL repair | ~5 s |
| `scratchpad/probe_cao_payload_pair.py` | Shrikhande/rook: 2-WL plain vs one-point extension (⚠ cases C/D never ran) | ~1 s for A/B |
| `scratchpad/probe_cao_triangle_frame.py` | the triangle-frame kill, 6 variants + controls; args `<disjoint\|shared> <none\|orbit\|minimal>`. ⚠ `freeze` was **not wired to argv** until 2026-08-13, so only the two `none` rows of §4.2 were reproducible from the committed file | ~1–3 min |
| `scratchpad/probe_cao_ensemble.py` | §6 — Construction C at rung 1, full symmetry, `n = 229406`; 100 mixed cells | ~2 min |
| `scratchpad/probe_cao_ensemble_audit.py` | **§6a** — the ensemble's 1-WL = (degree sequence, own degree); the 538/6 vs 292/100 comparison against the two-copy model | ~3 min |
| `scratchpad/probe_cao_ensemble_exact.py` | **§6a** — the same claim **elementwise** against the real 229406-vertex object, not by matching counts | ~2 min |
| `scratchpad/probe_cao_ensemble_2wl.py` | **§6b** — 2-WL on the REAL shared-frame ensemble, `L=4`, `n=332`; adjacency recovered, 0 mixed cells. The only 2-WL run in this doc on the real object | ~2 min |
| `scratchpad/probe_cao_cfi_bare.py` | **§5.1's premise** — `CFI[K4]`/`CFI[K5]` are 2-WL-blind bare. Was asserted but never checked in | ~1 min |
| `scratchpad/probe_cao_gadget_check.py` | §3.2a(a) — gauge transitive on the 8 complementary pairs; `δ` constant | < 1 s |
| `scratchpad/probe_cao_gadget_variants.py` | §3.2a(b) — the three frame shapes vs the transposition-fixes-`m` test | < 5 s |
| `scratchpad/probe_cao_cfi_frame.py` | §5.1 — CFI payloads through the frame; args `<m> <sub\|full>`. Outputs kept: `cfi_frame_full.out` (faithful), `cfi_frame_unfaithful.out` (row 3, provenance) | 152/440 fast; 812 ~1 h |

**Lean.** `GraphCanonizationProofs/ChainDescent/CaoEnsemble.lean` — the index-level skeleton
(`gact_transitive` = T1, `gact_eq_self_iff` + `lact_base` = T2⁻, `Propagates` +
`not_propagates_of_merge` = the target and the bridge the probes instantiate). Builds clean, all
declarations `[propext, Classical.choice, Quot.sound]`, no `sorry`, no custom axiom. ⚠ **Not in
`scripts/build.sh`'s `MODULES` list** — the gate is a hand-maintained enumeration, so this is
unbuilt by the gate until someone adds it. ⛔ It contains **no graph, no adjacency and no refiner**:
T2⁺ (`Aut_m` is *exactly* the label group, needing `Aut(T(n)) = Sym n`) and T3 (the frame's cells are
the position classes) are **not** in it.

⛔ **Traps hit while producing this — do not repeat.** (a) and (b) are already in the CAO doc §9.
(a) `pkill -f probe_...` **matches your own launcher** ⟹ self-kill, exit 144; kill by PID.
(b) A 1-WL stop condition of the form `len({(old,new)}) == len(set(new))` is **always true** (the new
colouring always refines the old), so the loop returns after one round; compare
`len(set(new)) == len(set(old))` instead. This produced a wrong `[3,45]` corner split before it was
caught.
(c) ⚠⚠ **THE MODEL-FAITHFULNESS TRAP, and it cost a whole 812-vertex run.** In the `full` encoding the
payload copy must be a **clique** with adjacency carried *only* by the frame types. Keeping the
payload's own edges as well hands 2-WL the adjacency **twice** — atomically at round 0 *and* through
the frame. It is a *stronger* model than the object, so **survivals under it are still sound but
separations are not**. Check which side of that asymmetry your result is on before quoting it.
(d) ⚠ Two modelling errors of the same family, both caught only by cross-checks: the `Aut_v`
comparison group must include the **gadget-internal clique permutations** (§2.3) or middles report as
spurious mixed cells; and a relabelling of the two-cube frame must **swap the cubes**, not the ends
(§3.2a), or the original design reads as broken.

(e) ⚠⚠ **1-WL colours are only comparable ACROSS COMPONENTS if every component is refined for the
SAME number of rounds.** Refining a disjoint union component-by-component with a shared intern table
is legitimate — but stopping each component at *its own* fixpoint returns colours from different
rounds, which are different namespaces. That bug made §6a's control read **520** instead of **538**
on its first run, and it is silent: the numbers look plausible and the partition looks well-formed.
Run a fixed `≥ n` rounds instead.
(f) ⚠⚠ **Validating an abstraction on one witness pair is not validating it** — §7's filter 7, and it
is what let §6's wrong inference stand for a day.

⚠ **Run the big 2-WL jobs one at a time.** Concurrent 812- and 128-vertex runs thrashed memory badly
enough to stall a *32*-vertex job past 120 s — which looked like a hang in the small job, not the big
one. 2-WL here is `n³` time with `n²` signatures; the counting signature in `probe_cao_cfi_frame.py`
is what makes `n = 812` fit at all.

---

## 9. Provenance

**Measured — on the REAL object.** §2.3, §2.4, §3.2a, §6's three numbers, **§6a** (elementwise, at
`n = 229406`), **§6b** (`L = 4`, `n = 332`).

**Measured — IN THE TWO-COPY MODEL, which §6a shows is not the construction.** §4.2, §4.3's `K4`
counts, §5.1 (all rows), §5.2's table. Every separation has a same-object control that came out
unseparated, so none is a *machinery* artefact — but each is a *modelling* claim.

**Proved, not measured.** §1's dichotomy · §2.3's and §6's `Aut_v` **upper** bounds (without these the
mixed-cell counts are unfalsifiable) · §2.1's parity requirement · §3.2's `δ` condition · §3.3's
reduction · **§6b's typed-common-neighbour argument**, which is the only 2-WL claim here that is both
proved and about the real object.

**Cross-checked.** §6's 544 orbits, by Burnside, together with the known 156 iso classes — and
independently re-derived in `probe_cao_ensemble_audit.py`. §6's 292/100 re-derived from a closed
formula and then compared **elementwise**.

**Machine-checked.** T1 and T2⁻ in `ChainDescent/CaoEnsemble.lean`; re-verified 2026-08-13 — builds
clean, all seven declarations `[propext, Classical.choice, Quot.sound]` or a subset, no `sorry`, no
custom axiom. ⚠ **not gate-listed.**

**Argued, not established.** §5's admission test — ⚠ **necessary direction only**, and ⚠⚠ its
ensemble assumption is now **refuted at rung 1** (§6a), not merely unmeasured at rung 2. §4.3's
4-vertex-window mechanism is **counter-indicated** by two facts already in the doc (§6a.2).

**Superseded, listed so the retractions are not silently re-inherited.**
*"The encoding hands WL exactly one extra level"* (→ not constant, §5) · *"a carrier's attachment set
must determine `v`"* (→ false, §1) · *"`CFI[K4]` suffices as a payload"* (→ refuted, §5.1) ·
*"the two-cube original fails the transposition test"* (→ my modelling error, §3.2a) · the `iff` form
of the admission test (→ necessary only, §5) · *"rung 2 is purely a budget question"* (→ §6) ·
⛔⛔ **2026-08-13:** *"the ensemble is passive / contributes nothing beyond the two-copy model"*
(→ §6a — it is far **coarser**, and the witness was degree-blind) · *"the Shrikhande/rook and
`CFI[K4]` payloads are DEAD"* (→ §4, §5.1 — dead **in the model**; not established for Construction C)
· *"rung 2 is a payload question, not a scaffolding question"* (→ §6a — the scaffolding is exactly
what is unresolved).

> ### ▶ OUTSTANDING, in priority order — REORDERED 2026-08-13
> 1. ★★★ **Re-establish or discard the two 2-WL kills against a faithful object.** They are the only
>    reason the programme looks blocked, and they are now model claims (§6a). The obstacle is that
>    2-WL on a shared-frame ensemble needs `n` in the thousands. **Cheapest honest route: add the
>    missing channel to the model rather than growing the object** — a 2-copy *shared*-frame test
>    that also carries the `2^d` **central** vertices (§6a.1's second row), which is what no current
>    variant has. ⛔ Do not simply re-run `disjoint`.
> 2. ★★ **§6b in Lean** — it is the one 2-WL statement that is proved and about the real object, it
>    is a **single-round** claim rather than a fixpoint, and it forces the refiner into the Lean layer
>    that T3 needs anyway. Better first target than T2⁺.
> 3. **§5.2's `CFI[K5]`-full cell** — still the calibration of *"costs one level"* vs *doubling*, but
>    ⚠ it now calibrates **the model**, so it dropped below (1). ★ Prefer hunting a **3-WL-blind pair
>    under 60 vertices** over brute-forcing `n = 3660`.
> 4. **T2⁺ in Lean** (`Aut_m` is *exactly* the label group) — makes every mixed-cell count here
>    unconditional; `Aut(T(n)) = Sym n` is the whole content.
> 5. **T3 in Lean** (frame cells = position classes) — needs a refiner in the Lean layer.
> 6. Decide whether `CaoEnsemble.lean` joins `scripts/build.sh`'s `MODULES` list.
