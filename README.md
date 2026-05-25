# Graph canonization project

A research project trying to build a polynomial-time graph canonizer.
Each strategy is tested in C# first, then translated to Lean for proof work
once it looks worth proving about. The project does not claim a polynomial
canonizer exists — it isolates the hard part behind one component (the
oracle) and proves the surrounding structural invariants.

## Active design — chain descent

A budget-bounded recursive descent of the individualization–refinement (IR)
tree that returns the lex-smallest leaf adjacency matrix as the canonical
form. Centrepiece invariant: the two directions of a genuine ordering
decision induce the same cell partition (`warm_6_2`, proved).

- C#: [`GraphCanonizationProject/ChainDescent.cs`](GraphCanonizationProject/ChainDescent.cs)
  + [`CanonGraphOrdererChainDescent.cs`](GraphCanonizationProject/CanonGraphOrdererChainDescent.cs)
- Lean: [`GraphCanonizationProofs/ChainDescent.lean`](GraphCanonizationProofs/ChainDescent.lean)
- Proving guide: [`GraphCanonizationProofs/ChainDescent.md`](GraphCanonizationProofs/ChainDescent.md)
- Strategy / overview docs: `docs/chain-descent-*.md`

## Layout

```
GraphCanonizationProject/                 — active C# (chain descent + shared infra)
GraphCanonizationProject.Tests/           — active xunit tests
GraphCanonizationProofs/                  — active Lean (ChainDescent.lean + ChainDescent.md)
docs/                                     — active strategy / design docs
*/Archive/V4/                             — retired V4 canonizer (Apr 20–29)
*/Archive/Exploration/                    — retired exploration era (Apr 30 – May 14)
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

# Lean
cd GraphCanonizationProofs && lake build ChainDescent
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
