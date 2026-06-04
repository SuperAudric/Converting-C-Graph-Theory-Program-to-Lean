# Graph canonization project

A research project trying to build a polynomial-time graph canonizer.
Each strategy is tested in C# first, then translated to Lean for proof work
once it looks worth proving about. The project does not claim a polynomial
canonizer exists — it isolates the hard part behind one component (the
oracle) and proves the surrounding structural invariants.

> **New here? Start with [`docs/00-START-HERE.md`](docs/00-START-HERE.md)** — the
> idea, the current state, and a curated reading order for the design docs.

## Active design — chain descent

A budget-bounded recursive descent of the individualization–refinement (IR)
tree that returns the lex-smallest leaf adjacency matrix as the canonical
form. Centrepiece invariant: the two directions of a genuine ordering
decision induce the same cell partition (`warm_6_2`, proved).

- C#: [`GraphCanonizationProject/ChainDescent.cs`](GraphCanonizationProject/ChainDescent.cs)
  + [`CanonGraphOrdererChainDescent.cs`](GraphCanonizationProject/CanonGraphOrdererChainDescent.cs)
- Lean: the [`GraphCanonizationProofs/ChainDescent/`](GraphCanonizationProofs/ChainDescent/)
  module split (Saturation / Scheme / Cascade / CascadeOracle / LinearOracle / CFI /
  Group), plus the top-level [`ChainDescent.lean`](GraphCanonizationProofs/ChainDescent.lean)
  (direction-invariance + spine invariants) that everything imports.
- Lean proving reference: [`GraphCanonizationProofs/ChainDescent/README.md`](GraphCanonizationProofs/ChainDescent/README.md)
  (model + C#↔Lean correspondence); theorem index:
  [`GraphCanonizationProofs/PublicTheoremIndex.md`](GraphCanonizationProofs/PublicTheoremIndex.md)
  (what is proved — the ground truth).
- Strategy / design docs: `docs/chain-descent-*.md` — read in the order given by
  [`docs/00-START-HERE.md`](docs/00-START-HERE.md).

## Layout

```
GraphCanonizationProject/                 — active C# (chain descent + shared infra)
GraphCanonizationProject.Tests/           — active xunit tests
GraphCanonizationProofs/                  — active Lean: ChainDescent/ module split
                                            + top-level ChainDescent.lean; theorem
                                            index PublicTheoremIndex.md
docs/                                     — active strategy / design docs
                                            (00-START-HERE.md is the entry point)
*/Archive/V4/                             — retired V4 canonizer (Apr 20–29)
*/Archive/Exploration/                    — retired exploration era (Apr 30 – May 14)
docs/Archive/ChainDescent/                — closed chain-descent sub-threads
                                            (matroid memo, Tier-2 experiment,
                                            completed build briefs) — see its README
scripts/                                  — helper scripts (long-test runner, theorem-index regen)
```

See [`GraphCanonizationProject/Archive/README.md`](GraphCanonizationProject/Archive/README.md)
for what's in each archive folder and why each era was retired.

## Building

```
# C#
dotnet build workspace.sln

# Tests
dotnet test GraphCanonizationProject.Tests/GraphCanonizationProject.Tests.csproj
scripts/run-long-tests.sh                 # the LongRunning xunit category

# Lean (all modules; serial, avoids RAM thrash — see scripts/build.sh)
bash scripts/build.sh
# or one module:
cd GraphCanonizationProofs && lake build ChainDescent.CFI   # .Cascade, .CascadeOracle, …
```

`Archive/**` is excluded from the C# build (`Compile Remove` in each csproj)
and from the default lean build (no `lean_lib` entries for V4 files in
`lakefile.toml`).

## Historical note

The project started with the V4 path-distillation canonizer, ported to Lean
in `LeanGraphCanonizerV4.lean` and `FullCorrectness/`. C# testing later
revealed the same failure modes as 2-WL on CFI bases — V4 is now archived
under [`GraphCanonizationProofs/Archive/V4/`](GraphCanonizationProofs/Archive/V4/).
Several intermediate designs (1-WL/2-WL baselines, PairOrder, Supplant,
PartialOrder variants) sit under
[`GraphCanonizationProject/Archive/Exploration/`](GraphCanonizationProject/Archive/Exploration/);
one of them, `PartialOrderSinglePair`, was renamed to `ChainDescent` and is
the current line of investigation.
