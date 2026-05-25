# Archived V4 Lean stack

The retired V4 canonizer + correctness proof attempt. Not in the default
`lake build` — the `lean_lib` entries were removed from
[`../../lakefile.toml`](../../lakefile.toml). To reactivate, restore the
following entries and rebuild:

```toml
[[lean_lib]]
name = "LeanGraphCanonizerV4"

[[lean_lib]]
name = "UniqueGraphsBySize"

[[lean_lib]]
name = "LeanGraphCanonizerV4Tests"

[[lean_lib]]
name = "LeanGraphCanonizerV4Correctness"

[[lean_lib]]
name = "FullCorrectness"
globs = ["FullCorrectness.+"]
```

Lake's library lookup uses the file basename, so the existing imports
(`import LeanGraphCanonizerV4`, `import FullCorrectness.Tiebreak`, …)
continue to resolve once the libs are re-declared — files do not need to
move back to the root.

## What's here

| File / dir                            | Status |
|---------------------------------------|--------|
| `LeanGraphCanonizerV4.lean`           | Lean port of `CanonGraphOrdererV4.cs`; compiles, no sorries. |
| `LeanGraphCanonizerV4Tests.lean`      | Small smoke tests against `UniqueGraphsBySize.lean`. |
| `UniqueGraphsBySize.lean`             | Mirrors `GraphCanonizationProject/UniqueGraphsBySize.cs` (small isomorphism class samples). |
| `LeanGraphCanonizerV4Correctness.lean`| **FLAWED, ABANDONED.** Header self-declares the false premise; reused parts (`run_isomorphic_to_input`, `Isomorphic.symm`, etc.) are still depended on by `FullCorrectness/Main.lean`. |
| `FullCorrectness/`                    | Replacement correctness tree. Builds with sorries; the (⇐) direction (`run_eq_implies_iso`) is genuinely proved, the (⇒) direction is documented but unfinished. |
| `FullCorrectness.md`                  | Phase-status snapshot for the FullCorrectness tree. |
| `OrbitCompleteAfterConv.md`           | Discharge plan for the remaining sorry. Empirically **falsified** on Cycle3/Cycle5/Cycle7/K4 CFI bases (the active V4Fast harness for this falsification lives in `GraphCanonizationProject.Tests/Archive/V4/`). |
| `ConvergeLoopAlgorithm.md`            | What the V4 `convergeLoop` actually computes — companion to `OrbitCompleteAfterConv.md`. |
| `ConvergeLoopReconstruction.md`       | Notes on reconstructing the converge-loop semantics. |
| `ConvergeLoopHistoryExtension.md`     | Notes on extending convergeLoop with history. |

## Tech debt — distillation pass

A follow-up cleanup pass should:

1. Extract the genuinely-proved lemmas from `LeanGraphCanonizerV4Correctness.lean`
   — listed in that file's header — into appropriate `FullCorrectness/*` files
   (or a new `FullCorrectness/V4Reused.lean`).
2. Drop the `import LeanGraphCanonizerV4Correctness` from
   `FullCorrectness/Main.lean` and reroute references.
3. Delete `LeanGraphCanonizerV4Correctness.lean` entirely.

The work is deferred because the V4 stack as a whole is retired; doing the
distillation now would only matter for someone trying to revive the
FullCorrectness tree, who can do it then.
