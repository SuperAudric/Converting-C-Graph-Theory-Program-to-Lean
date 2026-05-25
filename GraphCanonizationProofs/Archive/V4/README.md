# Archived V4 Lean stack

The retired V4 canonizer + correctness proof attempt. Not in the default
`lake build` — the `lean_lib` entries were removed from
[`../../lakefile.toml`](../../lakefile.toml). To reactivate, restore the
following entries (note the `srcDir`, since the files live under `Archive/V4/`
rather than the package root) and rebuild:

```toml
[[lean_lib]]
name = "LeanGraphCanonizerV4"
srcDir = "Archive/V4"

[[lean_lib]]
name = "UniqueGraphsBySize"
srcDir = "Archive/V4"

[[lean_lib]]
name = "LeanGraphCanonizerV4Tests"
srcDir = "Archive/V4"

[[lean_lib]]
name = "FullCorrectness"
srcDir = "Archive/V4"
globs = ["FullCorrectness.+"]
```

With `srcDir` set, lake resolves module names (`LeanGraphCanonizerV4`,
`FullCorrectness.Tiebreak`, `FullCorrectness.V4Reused`, …) against the
`Archive/V4/` tree, so existing imports continue to work unchanged.

Verified: `lake build FullCorrectness` produces 965 jobs with one expected
sorry (`Archive/V4/FullCorrectness/Main.lean:89`, the (⇒) direction's
unfinished σ ∉ Aut G branch).

## What's here

| File / dir                            | Status |
|---------------------------------------|--------|
| `LeanGraphCanonizerV4.lean`           | Lean port of `CanonGraphOrdererV4.cs`; compiles, no sorries. |
| `LeanGraphCanonizerV4Tests.lean`      | Small smoke tests against `UniqueGraphsBySize.lean`. |
| `UniqueGraphsBySize.lean`             | Mirrors `GraphCanonizationProject/UniqueGraphsBySize.cs` (small isomorphism class samples). |
| `FullCorrectness/`                    | Replacement correctness tree. Builds with one sorry; the (⇐) direction (`run_eq_implies_iso`) is genuinely proved, the (⇒) direction is documented but unfinished. |
| `FullCorrectness/V4Reused.lean`       | Distilled remnants of the retired `LeanGraphCanonizerV4Correctness.lean` — only the genuinely-proved lemmas (`swapVertexLabels_self_inverse`/`_comm`, `AdjMatrix.Isomorphic.symm`, `labelEdgesAccordingToRankings_isomorphic`, `run_isomorphic_to_input`, `run_eq_implies_iso`). Imported by `FullCorrectness/Main.lean`. |
| `FullCorrectness.md`                  | Phase-status snapshot for the FullCorrectness tree. |
| `OrbitCompleteAfterConv.md`           | Discharge plan for the remaining sorry. Empirically **falsified** on Cycle3/Cycle5/Cycle7/K4 CFI bases (the active V4Fast harness for this falsification lives in `GraphCanonizationProject.Tests/Archive/V4/`). |
| `ConvergeLoopAlgorithm.md`            | What the V4 `convergeLoop` actually computes — companion to `OrbitCompleteAfterConv.md`. |
| `ConvergeLoopReconstruction.md`       | Notes on reconstructing the converge-loop semantics. |
| `ConvergeLoopHistoryExtension.md`     | Notes on extending convergeLoop with history. |

The original `LeanGraphCanonizerV4Correctness.lean` was deleted in the
distillation pass — its genuinely-proved fragments are in
`FullCorrectness/V4Reused.lean`; everything else routed through the false
`orderVertices_swap_equivariant` lemma. See git history for the original text.
