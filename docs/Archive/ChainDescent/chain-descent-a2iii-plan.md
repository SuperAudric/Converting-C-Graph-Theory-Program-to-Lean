# A2-iii — unconditional block-visibility for closed subsets (short-lived plan)

> **STATUS (2026-06-05): RESOLVED NEGATIVELY — this scratch is CONSUMED.** The twin-pair question is
> settled: the **Shrikhande graph** refutes unconditional A2-iii. The graph-first / Aut-faithful search
> (`TwinPairSearchExperiment.cs`; `Verify_Shrikhande_BlockInvisible`, `|Aut|` cross-checked 192/1152) found
> a `ClosedSubset` `I={R₀,R₂}` (genuine block system, 4 blocks of 4) on Shrikhande's *own* rank-4 orbital
> scheme that 1-WL-from-`v` cannot see (3 SRG cells vs 4 orbital classes). So `SchemePartSeparatesBlock`
> does **not** hold for every `ClosedSubset`; block-visibility is **depth-graded**, not depth-1. **Two
> corrections to the plan below:** (1) the "counting-twin (identical intersection numbers)" framing is too
> narrow — the witness merges `R₂` (val 3) and `R₃` (val 6), *non-twins*; the real obstruction is
> single-vertex **WL-dimension ≥ 2**. (2) §1's "G = yes → exotic `(O*)` scheme to build" expectation was
> **wrong**: Shrikhande recovers at **depth 2** (small WL-dim), so a Gate-G failure is **not** a hard
> residual. **Durable record + redirect: [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md)
> §0.7 "A2-iii RESULT".** Do not pursue the §2 unconditional build. Everything below is closed attempt history.

## 0. What A2-iii is, in one line

Discharge **`BlockRefinementVisible adj P S v I`** (`Scheme.lean §13`) for **every** `ClosedSubset I`,
with **no orbit-recovery hypothesis** — or find the precise scheme where it fails. This is the
unconditional form of EOL Step 3a; if it lands, the bottom-up seal closes for homogeneous schemes modulo
only the Step-5 citation.

Target (contrapositive, the working form):
> different I-membership of `relOfPair v ·` (different block) ⟹ different `warmRefine` cell.

The theory pass ([§0.7](./chain-descent-exhaustive-obstruction.md)) established the target is **weaker than
recovery** (it asks only that 1-WL respect the *2-way* I/¬I boundary, not separate all relations), and
that the **only** obstruction is a **counting-symmetric** closed subset (I and ¬I sharing every
intersection-number signature from `v`). So A2-iii = "prove no proper closed subset is counting-symmetric
from `v`, then propagate that through 1-WL."

## 1. The decisive gate — do this first (cheap, settles the whole question)

> **G — Can a proper `ClosedSubset I` be counting-symmetric from `v`?**
> Precisely: do there exist `w, u` with `relOfPair v w ∈ I`, `relOfPair v u ∉ I`, yet *identical*
> intersection-number signatures against every relation class — so no amount of 1-WL counting separates
> them?

This single question gates everything:
- **G = no (closure forbids it):** A2-iii closes — block-visibility is unconditional (§2 builds it).
- **G = yes:** the witness *is* the exact exotic scheme to build (and it is the *rarer* "coarse-block-
  invisible" object, not merely a high-WL-dimension scheme — see §0.7). The A2 gate finally fires.

**How to settle G cheaply, in order:**
1. **Structural argument (preferred).** Split on the edge relation `j0`:
   - `R_{j0} ∈ I`: then `closure{R_0, R_{j0}} ⊆ I`. If the edge generates (`EdgeGenerates`), `I = univ`
     (not proper). So a proper `I ∋ j0` requires a *non-edge-generating* scheme — already the §3.3
     deadlock class. Check whether closure still forces the boundary detectable.
   - `R_{j0} ∉ I`: the edge connects *across* blocks (bipartite-type imprimitivity). Round-1 1-WL
     separates `v`'s neighbours (`∈ J`) from non-neighbours; the block sits among non-neighbours. Ask
     whether iterated counting then separates block from non-block.
   The diagonal `R_0 ∈ I` always (closure clause 1), so `I ⊋ {R_0}` has a non-zero relation, and `¬I` is
     non-empty (`I ≠ univ`) — the two sides each carry distinct relations; the question is whether their
     *valency/intersection vectors* must differ.
2. **`decide`/empirical fallback.** If the structural argument is unclear, instantiate small schurian
   schemes with proper closed subsets (the §0.7 / `Tier2DecompositionExperiment` battery already has the
   VT schemes; add a "counting-signature of I vs ¬I" check) and look for a counting-symmetric `I`. The
   probe infrastructure is built; this is a small extension, not new generators.

**Expectation:** moderate optimism G = no (closure under the complex product is a strong constraint; a
counting-symmetric proper closed subset would be a very special object). But G is genuinely open — settle
it before investing in §2.

### 1.1 Gate-G pass (2026-06-05) — reduction + a trap, but not yet resolved

**Trap caught (guardrail).** `ClosedSubset` is the **complex-product** closure (`Scheme.lean §1.2`,
lines 161–166); the 1-WL recovery machinery (`EdgeGenerates`/`isolationStep`) is a **pinning/counting**
closure — *different*. Do **not** argue "off-recovery ⟹ the edge-closure `J*` is a proper closed subset
⟹ imprimitive": `J*` is the *pinning* closure, not a `ClosedSubset`. Off-recovery does **not** imply
imprimitive (a **primitive** scheme can fail `EdgeGenerates` — the Cameron/Johnson case). Step 3's
direction (`¬D1 ⟹ primitive`) is *not* threatened by this.

**The reduction (real progress).** Via `iter_refines_schemePart_at` (warmRefine **finer than**
`schemePart_at`):
> **`schemePart_at(k)` separates I-membership ⟹ `BlockRefinementVisible`** (same cell ⟹ same `iter[n]`
> ⟹ same `schemePart_at(n)` class ⟹ same I-membership).

`schemePart_at` converges (from `v`) to the **WL-fusion `W`** = the relation partition 1-WL resolves
(the `EdgeGenerates`-reachable structure). Hence:
> **Gate G ⟺ does every `ClosedSubset I` respect `W`** (is `I` always a union of `W`-classes)? A
> counting-symmetric `I` is exactly a closed subset that *cuts across* a `W`-class — separating two
> relations 1-WL merges.

So G is relocated from "high WL-dimension" (unreachable, per the probe) to a sharp algebraic question
about two closures on one scheme.

**Status: open, leaning uncertain.** No closure argument yet that closed subsets respect `W`. **Named
counterexample mechanism:** relation-algebra **counting-twins** — relations `a, b` with identical
intersection numbers (so `schemePart_at` merges them) that a closed subset splits (`a ∈ I`, `b ∉ I`).
That is a *non-schurian-flavored* relation-algebra symmetry; whether `ClosedSubset` closure forbids
splitting a twin pair is the decider, and is unresolved.

**Concrete Lean step — LANDED (2026-06-05, axiom-clean, `Scheme.lean §13`).**
`SchemePartSeparatesBlock` (the predicate "`schemePart_at n` separates I") +
`blockRefinementVisible_of_schemePartSeparates` (discharge via `iter_refines_schemePart_at`). Strictly
**wider than the `EdgeGenerates` discharge** (covers off-recovery `I` that respect `W`), the honest A2-ii
graded form, and it turns the Gate-G crux into a **named Lean hypothesis** `SchemePartSeparatesBlock`.

**Gate G is now exactly: discharge `SchemePartSeparatesBlock` for every `ClosedSubset`** (= every closed
subset respects `W`), or refute it with a counting-twin scheme. That single Lean obligation *is* G — the
next move is to attack or refute it (the twin-pair question of §1.1), no longer armchair reasoning.

## 2. The proof, conditional on G = no (the build)

Mirror `theorem_2_HOR_of_edgeGenerates`'s assembly, but track the **I-boundary** instead of full isolation.

- **B1 — the counting bridge. LANDED** as `blockRefinementVisible_of_schemePartSeparates` +
  `SchemePartSeparatesBlock` (`Scheme.lean §13`, axiom-clean). `iter_refines_schemePart_at` gives
  `warmRefine` **finer than** `schemePart_at k`, so "`schemePart_at` separates the I-boundary" *suffices*
  for block-visibility — turning "1-WL sees the block" into the explicit counting question. **B1 = A2-ii.**
  The remaining work (B2–B3) is exactly *discharging* `SchemePartSeparatesBlock` = the §1.1 twin question.
- **B2 — block-isolation predicate.** Define `BlockGenerates v I` (or `IBoundaryIsolatedAt v I k`): the
  saturation closure detects I-membership within `k ≤ n` rounds. The closure operator is `isolationStep`
  applied to the **set `I`** (and its complement), not to singleton relations — reuse `isolationStep` /
  `occursFromV` / the `Saturation` engine verbatim, with `I` as the seed structure.
- **B3 — closure ⟹ detectable (the load-bearing step, where G = no is used).** Show the `ClosedSubset`
  closure clause forces the I-boundary to be pinned by counting: a vertex's I-membership is determined by
  its `(adjacency, counts-into-I)` signature. This is `isolatedCount_eq`/`relIsolatedAt_succ` repurposed —
  "counts into the isolated *set* `I`" rather than "counts into an isolated *relation*". G = no is exactly
  what makes the pinning non-degenerate.
- **B4 — assemble `BlockRefinementVisible`.** Saturation bounds the depth at `≤ n`; B3 turns the closure
  into I-boundary isolation at depth `≤ n`; B1 lifts it to `warmRefine`. Conclude
  `BlockRefinementVisible adj P S v I` for every proper `ClosedSubset I`, unconditionally. (Trivial `I`:
  `{R_0}` and `univ` give constant block partitions, visible for free.)

**Deliverable:** `blockRefinementVisible_of_closedSubset` (no `EdgeGenerates`/`PPolynomial`/recovery
hypothesis), which **supersedes** `blockRefinementVisible_of_edgeGenerates` and discharges the whole open
content of Step 3a's predicate. Axiom-clean `[propext, Classical.choice, Quot.sound]`.

## 3. Machinery inventory (all present, to be repurposed)

| Piece | Current use | A2-iii use |
|---|---|---|
| `schemePart_at`, `iter_refines_schemePart_at` | Step 2 counting bridge | B1 — suffices to separate the boundary in `schemePart_at` |
| `isolationStep`, `occursFromV`, `Saturation` engine | full relation isolation | B2 — closure on the *set* `I` |
| `RelIsolatedAt`, `relIsolatedAt_succ`, `isolatedCount_eq`, `stage_relIsolatedAt` | isolate each relation | B3 — isolate the I-boundary (counts into `I`) |
| `ClosedSubset` (closure clause) | block-system definition (§1.2) | B3 — the structural input forcing detectability |
| `schemeEquiv_graphOrbit` (general) | bridge's un-gated half | unchanged — only needed in the *recovery* route, not here |

**Landed (B1/A2-ii):** `SchemePartSeparatesBlock`, `blockRefinementVisible_of_schemePartSeparates`.
**Still needed (B3 = the twin question):** discharge `SchemePartSeparatesBlock` for every `ClosedSubset`
— either a structural lemma (closure forbids twin-splitting; may reuse `isolatedCount_eq` on the set `I`)
yielding `blockRefinementVisible_of_closedSubset`, or a refuting twin-splitting scheme.

## 4. Outcomes (all three are progress)

1. **G = no, B-chain closes →** Step 3a unconditional for homogeneous schemes; the bottom-up seal closes
   modulo only the Step-5 citation. Best case.
2. **G = yes →** the counting-symmetric witness is the exact scheme to build; the A2 gate fires; Step 3a is
   genuinely substrate-conditional and we have *named* the boundary (the coarse-block-invisible object).
3. **Graded discharge (A2-ii) — ALREADY LANDED.** `blockRefinementVisible_of_schemePartSeparates` strictly
   widens the discharged class past `EdgeGenerates` (covers off-recovery `I` respecting `W`), with
   `SchemePartSeparatesBlock` as the named residual hypothesis. This is the secured middle outcome; A2-iii
   (outcome 1) vs the counterexample (outcome 2) is what the twin question now decides.

## 5. Sequencing (updated 2026-06-05 — B1/A2-ii landed)

B1 (the counting bridge = A2-ii) is **done**. The single remaining obligation is **discharging
`SchemePartSeparatesBlock` for every `ClosedSubset`** (= the §1.1 twin-pair question). Start there:
1. **Structural attempt** — does `ClosedSubset` closure (complex-product) forbid splitting a counting-twin
   pair (two relations with identical intersection numbers)? Try the `R_{j0} ∈ I` vs `∉ I` split.
2. **`decide`/probe fallback** — search small schurian schemes for a `ClosedSubset` that splits a twin
   pair (extend the `Tier2DecompositionExperiment` battery with a "counting-signature of I vs ¬I" check).

If discharged → `blockRefinementVisible_of_closedSubset` (unconditional, supersedes the `EdgeGenerates`
and graded forms) → Step 3a closes for homogeneous schemes. If refuted → the twin-splitting scheme is the
`(O*)`-existence witness. Either resolves A2-iii; then fold the conclusion into §0.7 and delete this doc.
