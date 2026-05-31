# Private Theorem Index — GraphCanonizationProofs

Index of private Lean theorems, lemmas, and definitions in the GraphCanonizationProofs project (active source), grouped by source file path. Archived counterparts live in `Archive/PrivateTheoremIndex.md`.

## Legend

- **Line**: Source-line range `start-end` covering the declaration's header (attached doc comment / attributes) and its full body. Collapses to a single number when the declaration occupies one line. Gaps between theorems represent whitespace or comments.
- **Description**: A short description of what the theorem proves.
- **Notes**: `@[simp]` / `@[ext]` attributes, `private`, instances, or other special properties.

## ChainDescent.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `witnessAdj` | 498-500 | Witness adjacency: the empty graph on 5 vertices (adjacency plays no role in the `cell_split_uniform_false` refutation). | `private` |
| `witnessP0` | 502-511 | Witness pre-guess matrix on 5 vertices with `0 < 2` and `1 < 3`; supports the `cell_split_uniform_false` refutation by relating cell-mates `0, 1` asymmetrically to the `{2, 3}` cell vertices. | `private` |
| `witnessChi` | 513-520 | Witness colouring on 5 vertices with cells `{0,1}`, `{2,3}`, `{4}`. | `private` |
| `witnessTC` | 522-534 | Explicit `closeStep`-fixpoint of `applyGuess witnessP0 2 4 less` — `witnessP0` plus the guess `2 < 4` plus the closure entry `0 < 4`. | `private` |
| `witnessTC_eq` | 536-548 | `transitiveClose (applyGuess witnessP0 2 4 .less) = witnessTC`, proved without unfolding the full 25-fold iterate via a one-step closure plus fixpoint stability. | `private` |
| `witnessChi_stable` | 550-559 | `witnessChi` is 1-WL-stable for `(witnessAdj, witnessP0)`: cell-mates have equal signatures, which via `refineStep_iff` is exactly stability. | `private` |

## ChainDescent/CFI.lean

| Name | Line | Description | Notes |
|------|------|-------------|-------|
| `Finset.card_powerset_filter_even` | 625-677 | Combinatorial identity: a nonempty `Finset` has exactly `2^(|s|−1)` even-cardinality subsets, via the alternating-sum-of-signs argument. | `private` |
