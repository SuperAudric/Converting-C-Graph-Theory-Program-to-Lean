# CAO carrier/payload falsifier constructions — the record

> **What this is.** Three related *designed* attacks on CAO propagation, raised from outside the
> project (2026-08-12) and measured here. **Construction B is a genuine 1-WL CAO-propagation
> counterexample** — the first one on record that was built to order rather than found by sweeping.
> **Construction C is the 2-WL attempt**; its first payload is measured dead, the scheme is not.
> This doc owns the constructions, the measurements, the reusable filters, and the one open experiment.
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

> ### ▶ A candidate payload pair survives Construction C **iff** it is still 2-WL-resistant after edge-bisection.
> Shrikhande vs rook **fails** this test (§4.2/§4.3), which is why it dies. Apply the test to any
> candidate **before** building anything around it.

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

**One assumption inside the admission test, and it is the open item**: that the ensemble contributes
nothing. See §6.

---

## 6. ▶ THE ONE OPEN EXPERIMENT — is the ensemble passive?

The ensemble is not obviously a passive container. With every colouring present, WL gets the whole
**Hamming structure on colouring space** as a reference frame: two copies differing in a single slot
agree at all the others, and that relation is WL-visible. Whether encoded-WL-on-the-full-ensemble is
still bounded by any fixed level on the payload is the unproved step, and §3.3's argument silently
assumes it.

**It is answerable at rung 1, and the answer is sharp either way:**

* **two-copy model** — measured (§5): 1-WL does **not** separate `C6` from `2C3` extended;
* **full ensemble** — 6 labels, 15 slots, all `2^15` copies, `2^15` central vertices, 30 frame
  vertices ≈ **230k vertices, ~2M edges**. 1-WL is linear, so this runs in minutes.

If the full ensemble separates them, the ensemble is doing work no bounded-level argument covers and
the scheme needs rethinking. If it does not, there is a *designed* 1-WL CAO failure with a chosen
payload, and rung 2 becomes purely a payload-budget question — where CFI over a treewidth-4 base
(`CFI[K5]`, 60 vertices) is the natural candidate, putting the frame at `C(60,2) = 1770` slots and the
ensemble at `2^1770` copies. Untestable, but that is then a **size** problem, not a soundness problem.

---

## 7. Reusable filters extracted (apply before building)

1. **N1 / N2** (§0) — the fusing automorphism must move `v`; the distinguishing relation must be
   uniform at the root.
2. **The attachment-set test** (§1) — if the carrier's attachment set determines `v`, it is dead.
   ⚠ Conditional only; `Q₄` complementary pairs break its premise.
3. **The parity test** (§2.1) — complementary-pair carriers need `c` **even**.
4. **The `δ` test** (§3.2) — `1 ⊕ 1' = 2 ⊕ 2'` or the root is not CAO.
5. **The payload admission test** (§5) — 2-WL-resistant *after edge-bisection*, not before.
   Shrikhande/rook fails; it is a cheap kill for any design that encodes payload adjacency as vertices.
6. **The binary-coincidence test** (§2.4) — if the hidden fact is a pairwise coincidence, 2-WL reads it.

---

## 8. Files and reproduction

| file | what it does | runtime |
|---|---|---|
| `scratchpad/probe_cao_hypercube.py` | Construction B at `n = 352`; verified generators, true CAO start, mixed-cell verdict | < 1 s |
| `scratchpad/probe_cao_hypercube_2wl.py` | reduced 112-vertex model; 1-WL calibration + the 2-WL repair | ~5 s |
| `scratchpad/probe_cao_payload_pair.py` | Shrikhande/rook: 2-WL plain vs one-point extension (⚠ cases C/D never ran) | ~1 s for A/B |
| `scratchpad/probe_cao_triangle_frame.py` | the triangle-frame kill, 6 variants + controls; `disjoint`/`shared`, `freeze` ∈ `False`/`True`/`'minimal'` | ~1–3 min |

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

Measured (this doc): §2.3, §2.4, §4.1 A/B, §4.2, §4.3 K4 counts, §5's calibration table.
Proved, not measured: §1's dichotomy, §2.3's `Aut_{m₀}` upper bound, §2.1's parity requirement,
§3.2's `δ` condition, §3.3's reduction.
Argued, not established: §5's admission test (its ensemble assumption is §6), and the claim that the
`4`-vertex window is *the* separating mechanism in §4.3 — consistent with the numbers, not isolated by
ablation.
