# The divergence lift — a concept doc

> **STATUS (2026-08-02): RECORD, not a plan.** The research phase closed 2026-08-01
> ([`chain-descent-wind-down.md`](./chain-descent-wind-down.md)); this design was proposed and probed
> afterwards, and is recorded because it is unlikely to be resolved before retirement.
> **Do not open it as a track.**
>
> **Verdict in one line:** the design as proposed is **refuted by measurement** (a single mixed-cell pick
> flips its verdict, Chang-2, n=28, reproducible) — but it has an exactly-characterised sound core,
> §5, which is poly, stall-free, and equivariant *by construction*. That core is the usable residue.
>
> **Entry:** §1 (the design) → §3 (the principle that decides it) → §4 (the refutations) → §5 (what survives).
> §6 is the vacuity record: **three probe generations measured nothing before the question was posed** —
> read it before trusting any negative run in this area.

---

## 1. The design as proposed

Run the symmetry detector as usual. Given `u, w` in one 1-WL cell:

1. individualize `u` in one instance and `w` in another; 1-WL each;
2. repeatedly take the shared cell (matched by canonical colour id), individualize a vertex in **each**
   instance, 1-WL, and compare the two instances **edgewise over the vertices selected so far**;
3. terminate either when the comparison differs (**divergence**) or when the descent runs to the end
   (**a symmetry to consume**).

Steps 1–3 are the existing consume/`deck` shape. **The proposed modification is step 4:**

4. on divergence, 1-WL has an opinion about which of `u, w` comes first. Rather than backtracking
   (nauty's response), **lift that opinion up the chain** and apply it as a decision — consuming a
   symmetry, or splitting a cell in the direction a higher-`k` WL would have chosen.

The claim under test: this is polynomial and cannot stall, leaving iso-invariance as the only
remaining obligation.

**Refinement of the target (user, 2026-08-02).** The lift destination is *not* in general the root: it is
the level of the *selected descent* at which the decision was really made. The clear case is a disjoint
component prepended to the selection — picks made inside it are irrelevant to a comparison elsewhere, so
the opinion transports up past them. The sharp question then becomes:

> ▶ when several **mixed-orbit** cells were individualized before identification, can that flip the
> direction of the comparison to one inapplicable to the correct pair?

§4.2 answers **yes**, and one mixed pick suffices.

---

## 2. What is genuinely free (do not re-derive these as problems)

- **The positive branch costs nothing to trust.** An automorphism is verified in `O(n²)` regardless of how
  it was found, so every arbitrary pick made on the way to a *found* symmetry is harmless. This is why the
  consume side has never carried an equivariance obligation for its successes.
- **★ The tiebreak read was measured invariant when the pair is genuinely separated.** C3/C4's overmerged
  14-cell (a C3-vertex vs a C4-vertex: same 1-WL colour, different orbits) returned the **same direction on
  400/400 relabellings at every beam width**. So given a certificate that `u ≁ w`, reading the direction off
  the 1-WL divergence signature is not the difficulty. **The entire difficulty is on the false-negative
  side** — divergence firing on a pair that is in fact one orbit.

---

## 3. ★ THE PRINCIPLE — the lift distance is the `CellSingleOrbit` suffix

This is the load-bearing statement; every measurement in §4 is an instance of it.

The verdict transports up past level `i` **iff it is invariant under which vertex was picked at level `i`**.
A sufficient — and essentially necessary — condition is that the cell individualized at level `i` is a
**single orbit of the stabiliser at that node**: then all choices there are related by an automorphism, so
nothing below can depend on which was taken. That condition is `CellSingleOrbit`, the per-level content of
`Tinhofer`. Hence:

> **The 1-WL opinion lifts soundly from the divergence point up through the maximal contiguous suffix of
> `CellSingleOrbit` levels, and must stop at the first mixed cell.**

Three consequences.

**(a) Certifying the lift costs what the lift costs.** Verifying choice-independence at one level costs
`|C|` subtree re-runs; over `d` levels it is the **product** of the cell sizes. So *lift one level with
certification = nauty*; *lift to the root with certification = the whole search tree*. **There is no free
middle.**

**(b) The disjoint-component case is free but illusory.** It works because component decomposition is
canonical — the irrelevance is certified structurally, not searched for. But canonical per-component
preprocessing already delivers that gain *without* the lift, so it is not evidence that the lift generalises.

**(c) The mixed cells are exactly the boundary.** At a mixed cell the two branches are genuinely
non-equivalent, so a later divergence may be an artifact of which side was taken. The user's sharpened
question is therefore posed precisely at the point where the principle predicts failure — and §4.2 confirms it.

---

## 4. The refutations (all measured clean-room, no orbit oracle)

⚠ `probe_orbit_oracle` is **proven wrong** (it errs by merging — see
[[project_vt_test_and_divergence_2026-07-29]]). Nothing below uses it. Orbits come from exact
colour-preserving automorphism enumeration (`all_auts`, cross-checked against recorded `|Aut|` values) or,
for the unions, from hand-known component transitivity.

### 4.1 Lifting to the root splits an orbit — `Cay(Z₁₂⋊₅Z₂)`, n = 24

`scratchpad/probe_root_lift.py`. The VT/T2 witness; VT ⟹ the pair `(0,1)` is provably **one orbit**.
200 random relabellings of the *same abstract graph*, beam width `W` (W = 1 is the deterministic
no-stall version; larger `W` is bounded backtracking):

| W | verdicts |
|---|---|
| 1 | `LT: 97` / `SYM: 103` |
| 2 | `LT: 48` / `SYM: 152` |
| 4 | `SYM: 200` |
| 32 | `SYM: 200` |

At W = 1 the emitted root order is a function of the **labelling**, and it splits an orbit — which no
iso-invariant colouring can do, since colour classes are unions of orbits. Width repairs *this* family only
because all 20 recorded witnesses sit at ambiguity depth 1 / `|Aut_v| = 2`; nothing bounds `W` in general,
and the recorded construction target (VT ∧ T2 ∧ ambiguity depth ≥ 2) is exactly what defeats it.

**★ And on a VT graph k-WL has no root opinion for any `k`** — its colouring is Aut-invariant, hence
constant. So *"the deep 1-WL opinion agrees with what higher k-WL would have preferred"* has no referent on
exactly the hard cases: the order is **manufactured, not recovered**. That part is a proof, not a probe.

### 4.2 ⛔ A mixed pick flips the direction — `Chang-2`, n = 28 (**the decisive result**)

`scratchpad/confirm_chang.py` (+ `probe_dir_flip4.py`). Chang-2 = C8 switching of `T(8)`; `|Aut| = 96`;
1-WL root is **one cell of 28** with orbit sizes `[4, 24]`, so the root cell is already mixed. Pair `(0,3)`,
verified **different orbits**. Scheme run exactly as described in §1 — independent picks in each instance,
divergence = first mismatch of (edge vector to the selected sequence, 1-WL signature):

| seed | verdicts (1000 trials) | divergence depth | mixed picks before verdict |
|---|---|---|---|
| 3 | `GT: 62` / `LT: 938` | `{0: 993, 1: 7}` | ≥ 1 in every run |
| 11 | `GT: 57` / `LT: 943` | `{0: 985, 1: 15}` | ≥ 1 in every run |
| 101 | `GT: 54` / `LT: 946` | `{0: 985, 1: 15}` | ≥ 1 in every run |

Same graph, same labelling, same pair — **the direction is a function of the pick.** Two sharpenings:

- **The minimal form suffices.** It does not take a long chain of muddy choices: divergence lands at depth
  0–1, so **one** mixed-cell pick already flips it.
- ⚠ **The flip is a ~6% minority** — worse than a coin flip, not better. It survives casual testing and
  surfaces later as a rare, non-reproducible canonical form.

⚠ `mixedPicksBefore` is a sound **lower** bound: it is counted against the node's orbit partition, which is
coarser than the deeper stabiliser's, and coarse-mixed ⟹ fine-mixed.

### 4.3 ⛔ A fourth outcome the trichotomy omits — `rook4×4 ⊔ Shrikhande`, n = 32

`scratchpad/probe_dir_flip5.py`. Both components are SRG(16,6,2,2) ⟹ 1-WL-equivalent and non-isomorphic
⟹ one 1-WL cell of 32 with orbits `[16,16]`. 300 trials per pair:

| pairs | verdicts |
|---|---|
| (0,16), (0,18), (1,16), (1,18) | `LT: 211` / `GT: 55` / **`NOAUT: 34`** |
| (0,17), (1,17) | `LT: 205` / `GT: 72` / **`NOAUT: 23`** |

`NOAUT` = the descent **ran to a discrete leaf with the edgewise comparison matching the whole way**, yet
the induced map is not an automorphism — and cannot be, since the components are non-isomorphic.

> ⟹ **"reach the end and you have a provable symmetry" is FALSE as stated.** Vertices that become
> singletons through *refinement* are never selected, so they are never edge-compared.

Cure: verify the leaf map (`O(n²)`, cheap). But the repaired state then yields **no selected-vertex
opinion** — the direction must be read off the full leaf certificates instead. Left untreated it is a
**stall**, at ~8–11%, in the one design that claimed to have none.

### 4.4 Not universal

`net(Z₄) ⊔ net(Z₂²)` (= CFI[K4] twisted + untwisted, n = 56, cells `[24,32]`, each two orbits) returned
`GT` **200/200 on every pair in both cells**. The flip tracks mixedness of the *picked* cells, not anything
global — consistent with §3.

---

## 5. ★★ THE USABLE RESIDUE — the consume-certified lift

§3 does not say the idea fails; it says the lift needs a certificate, and names one that the project
already produces.

> **At each level of the descent, run `consume` on the target cell. If it returns verified generators
> acting transitively on that cell, the level is certified `CellSingleOrbit` and the lift passes through
> it. Stop at the first level where it does not.**

Properties, in the project's own terms:

- **Poly** — one consume call per level, on a supply already billed (`deepenSupply` at `n⁶`).
- **No stall** — the lift always terminates; it just may lift zero levels.
- **★ Equivariant by construction, not as a later obligation** — every level it passes through carries a
  *verified automorphism*, and verification is labelling-independent. This is the structural difference
  from the proposed design, where equivariance was deferred to "the third pillar".
- **Strength becomes quantitative,** not binary: *how deep does consume certify, on which families?* That is
  a measurable question, unlike the original all-or-nothing claim.

⚠ **What it does not do.** It cannot certify a level whose cell is mixed, and detecting mixedness is the
orbit question itself. The cheap certificate runs one way only: the **Lagrange test** (a cell of size `c`
with `c ∤ |Aut_χ|` is automatically mixed) refutes cleanliness cheaply — all four recorded 1-WL CAO
counterexamples were found with it — but proving a cell *is* a single orbit is the hard direction.

**If anyone ever pins this in Lean**, the statement to aim at is the §3 principle, not the design:
*a verdict computed below a contiguous run of `CellSingleOrbit` levels is invariant under the picks made
at those levels.* That is pure group theory over the existing `CellSingleOrbit` predicate, it needs no new
WL machinery, and it is the honest general theorem in the area.

---

## 6. ⚠⚠ VACUITY RECORD — read before trusting any negative run here

**Three probe generations measured nothing.** Recorded so the "0 counterexamples" lines are not cited as
evidence:

- `probe_dir_flip.py` and its v2 returned **0 posed instances** across net(Z₄), net(Z₆), Shrikhande,
  Chang-2 at depth 1, Shrikhande ⊔ Shrikhande, net ⊔ net, net ⊔ Shrikhande. Reason: **in those objects a
  different-orbit pair sharing a cell is separated by ONE individualization**, so divergence fires at depth 0
  and no mixed pick ever precedes it. The question was never asked.
- ⛔ **Do not "strengthen" the comparison.** Comparing the whole target cell's key-multiset (a generous
  variant I tried) fires divergence at depth 0 and destroys the question. The design's comparison is over
  the **selected** vertices with **independent** picks, and that weakness is precisely what is under test.
- ⛔ **Rigid multipedes are NOT a 1-WL-blind habitat** — `probe_2wl_multipede`'s own output shows 1-WL
  *discretizing* them (n = 68 → 68 cells). They are built to defeat WL on the F₂ parity, not to be
  1-WL-coarse.
- ✅ **Habitats that do pose the question:** (i) an object whose 1-WL root cell is already mixed
  (Chang-2, orbits `[4,24]`); (ii) **two 1-WL-equivalent non-isomorphic objects side by side**
  (rook4×4 ⊔ Shrikhande), where every vertex of one shares a cell with every vertex of the other and
  separating them requires telling the objects apart.

---

## 7. Where this sits in the project ledger

- The proposed design's invariance obligation is **not new**: it is
  `SameOrbits deepenSupply Ref` = **R1**, the reason `deepenSupply` is parked out of `Publication`
  (for equivariance, **not** cost — it is billed `n⁶`). Poly + stall-free + parked-for-equivariance is an
  object the project already has.
- The condition the lift needs per level is `CellSingleOrbit`, whose universally-quantified form is
  `Tinhofer` — refuted from vertex-transitivity (`Cay(Z₁₂⋊₅Z₂)`) and measured to be a
  **(graph, selector)** property, not a graph property (Shrikhande: EXISTS-`Tinhofer` true,
  FORALL-`Tinhofer` false).
- `KEY_scoping.md`'s framing applies unchanged: separation is free for any discretizing map; the difficulty
  is **invariance of the read**. §2 above localises that difficulty precisely — the read is invariant, the
  *firing condition* is not.

---

## 8. Files

All in `scratchpad/`, all clean-room (own 1-WL with canonical colour ids, own automorphism check, no
`probe_orbit_oracle`):

| file | what it does |
|---|---|
| `probe_root_lift.py` | §4.1 — beam-width invariance sweep over relabellings (C3/C4, `Cay(Z₁₂⋊₅Z₂)`) |
| `probe_dir_flip.py` | shared helpers (`refine`, `indiv`, `all_auts`, `orbits_of`, `net`, `shrikhande`, `t8_chang`, `disjoint`); its own `__main__` is the **vacuous** v1 run |
| `probe_dir_flip4.py` | the scheme as described in §1 (independent picks, edgewise divergence) + instance search |
| `probe_dir_flip5.py` | §4.3/§4.4 — the 1-WL-equivalent-union habitat |
| `confirm_chang.py` | §4.2 — the decisive Chang-2 flip, 1000 trials × 3 seeds |

---

## 9. Open items, if this is ever picked up

1. **Quantify the certified suffix.** For the project's hard families, how many levels does consume
   certify before the first uncertifiable cell? This is the only remaining question with a measurable answer.
2. **Is there a second cheap one-way certificate** beyond Lagrange — something that proves a cell *is* a
   single orbit without solving the orbit problem? Nothing in the record suggests one exists.
3. **The §5 Lean pin** (pick-invariance below a `CellSingleOrbit` run). Bounded, self-contained, and true;
   it would be the only general theorem this line produces.
4. ⚠ Apply the **standing union filter** to anything proposed here: test `G ⊔ G` first. It is nearly free
   and it has already killed two routes in one call elsewhere in this project.
