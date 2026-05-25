# Archived canonizer orderers

Files in `Archive/V4/` and `Archive/Exploration/` are excluded from the
C# build (`<Compile Remove="Archive/**" />` in
[`GraphCanonizationProject.csproj`](../GraphCanonizationProject.csproj)).
To reactivate an orderer for comparison, move its `.cs` file back to
`GraphCanonizationProject/` — none of these depend on each other.

## V4 (Apr 20 – Apr 29) — retired

The original path-multiset condensation canonizer. The strategy: distill
all information from paths of length n+1 into length n. Tested empirically;
failed on the same CFI cases as 2-WL.

| File | Notes |
|------|-------|
| `CanonGraphOrdererV4.cs`     | reference implementation; the Lean port `LeanGraphCanonizerV4.lean` matches this byte-for-byte (see `GraphCanonizationProofs/Archive/V4/`). |
| `CanonGraphOrdererV4Fast.cs` | perf-focused reimplementation; canonical bit pattern not guaranteed to match V4. Exposes `RunConvergeLoopForTesting` used by the archived V4Fast falsification harness. |

Design doc: [`docs/Archive/V4/v4-canonizer.md`](../../docs/Archive/V4/v4-canonizer.md).
Strategy paper: [`docs/Archive/V4/path-condensation-strategy.md`](../../docs/Archive/V4/path-condensation-strategy.md).

## Exploration (Apr 30 – May 14) — retired in favour of chain descent

Searches for a canonizer base that could flip a guess `a<b` to `b<a` with all
outputs viable between both directions (no implicit pruning). Several
designs explored; eventually `PartialOrderSinglePair` was the working base
and was renamed to `ChainDescent`.

| File | Strategy / notes |
|------|------------------|
| `CanonGraphOrdererOneWL.cs`                 | 1-WL baseline. |
| `CanonGraphOrdererTwoWL.cs`                 | 2-WL baseline. |
| `CanonGraphOrdererPairOrder.cs`             | pair-order tiebreak. |
| `CanonGraphOrdererSupplant.cs`              | layered tiebreak with post-hoc supplant (`docs/Archive/Exploration/supplant-strategy.md`). |
| `CanonGraphOrdererOneWLPartialOrder.cs`     | 1-WL + partial order. |
| `CanonGraphOrdererOneWLTruePartialOrder.cs` | 1-WL + true partial order. |
| `CanonGraphOrdererPartialOrderIR.cs`        | partial-order IR. The archived test `GraphCanonTests.PartialOrderIR.cs` is the matching harness. |
| `CanonGraphOrdererPartialOrderSinglePair.cs`| direct ancestor of `ChainDescent.cs` (rename). |

Tiebreak design notes: [`docs/Archive/Exploration/tiebreak-tuples-strategy.md`](../../docs/Archive/Exploration/tiebreak-tuples-strategy.md).
