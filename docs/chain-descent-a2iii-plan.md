# A2-iii — unconditional block-visibility for closed subsets (short-lived plan)

> **STATUS (2026-06-05): working plan, intentionally short-lived.** Delete or fold the surviving
> conclusion into [`chain-descent-exhaustive-obstruction.md`](./chain-descent-exhaustive-obstruction.md)
> §0.7 once A2-iii resolves (closes, or names the counterexample). This doc is scratch for the attempt,
> not a durable record.

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

## 2. The proof, conditional on G = no (the build)

Mirror `theorem_2_HOR_of_edgeGenerates`'s assembly, but track the **I-boundary** instead of full isolation.

- **B1 — the counting bridge (already have the hard half).** `iter_refines_schemePart_at` gives
  `warmRefine` **finer than** `schemePart_at k`. So it *suffices* to show `schemePart_at k` separates the
  I-boundary — then 1-WL (finer) separates it too. This turns "1-WL sees the block" into "the explicit
  depth-`k` counting partition sees the block," which is the tractable object.
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

New: `BlockGenerates`/`IBoundaryIsolatedAt`, its `_succ` step, `blockRefinementVisible_of_closedSubset`.

## 4. Outcomes (all three are progress)

1. **G = no, B-chain closes →** Step 3a unconditional for homogeneous schemes; the bottom-up seal closes
   modulo only the Step-5 citation. Best case.
2. **G = yes →** the counting-symmetric witness is the exact scheme to build; the A2 gate fires; Step 3a is
   genuinely substrate-conditional and we have *named* the boundary (the coarse-block-invisible object).
3. **G = no but B3 only graded (needs bounded closure depth) →** `BlockGenerates ⟹ BlockRefinementVisible`
   lands, strictly widening the discharged class past `EdgeGenerates`, with the depth bound as the residual
   — the honest middle.

## 5. Sequencing

G (§1) → then §2 only if G = no. Do **not** build §2 before settling G — B3 leans on G, and a G = yes
result makes §2 moot. Start with the structural argument for G (the `R_{j0} ∈ I` vs `∉ I` split); fall back
to the `decide`/probe check if it stalls.
