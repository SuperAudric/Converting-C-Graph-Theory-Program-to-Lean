# Graph canonization, machine-checked

> **Status:** winding down — see [What it does not do](#what-it-does-not-do) for the honest limits.
> Lean 4 (v4.30.0-rc2) and .NET 8.

This is a graph canonization research project written in Lean 4 and prototyped in C#.
It makes an algorithm that's proven to give a canonical output with a polynomial time complexity for a proven class of graphs. This is a major gap in the graph theory literature between "This algorithm exists" and "Here's a working program that provably does this", that's where this project sits... The major caveat is that the proven graphs that it handles are tiny. Assuming the wrap up processes complete, that's CFI graphs and Tinhofer.
This was mostly written to hone my Lean, C#, and graph theory skills. I'm pleased to have made something useful while I'm at it.
This also happened to be the first project I made heavy use of AI, I figured it would be a good place to learn due to having machine checked Lean to confirm things are doing what's being claimed.
This project is being retired, mostly due to the pittance of classes it was able to provably handle, I did try and make it as extensible as possible (see "Core design"), and it contains plenty of usable proofs and code (freely available). Perhaps it can serve as a stepping stone for a more complete implementation.

---

## What is a graph canonizer?

This takes a graph (a set of vertices connected with edges) and aims to always output it in the same order, no matter how you scramble the input.
This is a problem known as graph canonization, and is used to see if two similar looking objects are the same, such as comparing large molecules in chemistry.
Programs like nauty and Traces solve this for practical purposes, but there are some very difficult outlier graphs that can be hard to tell apart quickly, and comparing them in polynomial time (or in this case, handing you an easy to compare form that's always the same when those graphs are) is currently unsolved.

Two graphs that are the same if you were to rearrange their vertices (consider 3 vertices in a "v" shape vs a "^" shape) are called isomorphic, and if there's multiple ways to arrange the same graph that are identical (like swapping the two leaf vertices on the "v" graph), this is called an automorphism.

## Core design

This canonizer works by trying to slowly restrict the order that it outputs the vertices in, until it's just left with a single one. (A reordering that is identical for all isomorphic graphs)
The way it does this is with a partial order over the vertices: it starts off by saying every vertex could come either before or after every other vertex, and then as it learns more about the graph it adds constraints in the form "Vertex 1 must come before Vertex 29 in my answer" (usually applied in batches by cell for equivariance reasons mentioned later). Back when it only filled constraints for symmetries, this became the generating set for selecting between automorphisms, known as a stabilizer chain. This was the 'chain' from 'chain descent', but now it's mixed with constraints over which answer to choose for answers that differ, despite this I still think of the constraints as a stabilizer. The answer is in the form of something called an adjacency matrix, which is a table of which vertices are connected to each other. Two answers are identical if the tables are identical. <!-- Weak adj matrix explanation, maybe wrong place? -->

There's 2 main ways a decision is made, either it's a symmetry, or it's a real decision that impacts the output.
- If there are two possible answers that produce the same result, then this is an automorphism, just like how a graph like K3 (a triangle △) is the same no matter which order you say its vertices in, the adjacency matrix will always be the same. If these two vertices are identical under the current stabilizer, then the decision doesn't matter and you can choose either.
- If the vertices are not identical, then your decision _does_ matter and you have to make the same choice for all isomorphic graphs, or else you'd end up with different answers. Because of that, this means the things you can choose are structural, such as how many neighbors a vertex has (i.e. a rule like "All vertices should come before those that have fewer neighbors in my answer").

There's also another way a 'decision' can be made, which is transitive closure. If a\<b and b\<c, then it must be that a\<c.

Now, if we could perfectly determine either one of these, we'd have something called an orbit oracle which is GI complete, solving the entire problem. Instead we have to assume whatever we build might make mistakes so we have to verify its answer to make sure it's only incomplete, never wrong (which would ruin the answer). It also has to do this within polynomial time, otherwise it's just too slow. These are passed to the consume resolver and force resolver in turn.
- The consume resolver checks if two vertices are contained in a symmetry by trying to find two answers (adj matrices) that are identical but swap the position of these two vertices. If it succeeds then that's a verified automorphism, but it can fail on non-Tinhofer graphs. Basically, it tries to pick same-orbit (contains an automorphism under the current stabilizer) vertices in a greedy descent mirrored between both test vertices. If it individualizes everything while only grabbing same orbit vertices, then it succeeds and verifies, but if it ever reaches for same-orbit and misses (grabbing a pair of mixed orbit vertices between the two descents), then it fails and it can't verify. Tinhofer is a type of graph where you're able to grab the correct orbits each time, which is why this is where it can't fail. This can be refined further by having better ways to determine the orbits during the descent.
- The force resolver handles the real decisions, splitting a cell whose vertices genuinely differ. (1-WL, a.k.a. colour refinement, does a first pass and separates the easy cases into colour cells, but it isn't perfect and some cells still contain structurally different vertices.) It works through a key: a function that gives every vertex in a cell a value, and you keep the smallest. For that to be a canonizer the key needs three properties at once — it has to actually separate the vertices, it has to be equivariant (same answer regardless of how the input happened to be labelled, or two copies of the same graph produce different output), and it has to be polynomial. Any two of the three are easy: try every answer and keep the best (non-poly), hand it back in the exact order you're given (non-equivariant), or say every vertex is the same (non-separating). The open problem is getting all three at once.

  The reason it's hard has a shape worth stating. When the key can't decide between vertices, what's left over is a group: the part of the automorphism group the key can't see inside. The cheap way to be equivariant is to try all options in that group, which is exponential. So a polynomial key exists exactly when that group's canonical form can be found in polynomial time. That forms a ladder: Trivial (nothing to do) · Tinhofer (any pick is as good as any other) · an F₂ gauge, which is the CFI case (canonical row-reduction — this is the Gaussian elimination step) · Z_{2^k} (Smith normal form) · solvable (layer by layer) · bounded local groups (Luks, citable) · and then non-solvable, where nothing is known. That last rung is the wall, and it's the same wall the literature is stuck at. The tracks that look like separate research directions are really rungs of this one ladder.

Where this actually got to on that ladder: the bottom two rungs are closed. A rigid node needs no key at all, and a Tinhofer node doesn't need one either, since any pick there is canonical up to automorphism — that's the same fact the consume resolver runs on. The F₂ rung is where the real work is, and the algebra for it is done. A CFI gauge is a linear system over F₂, and you can canonicalise it by putting the row space into reduced row echelon form; RREF depends only on the subspace and not on whichever basis you happened to be handed, so it's equivariant for free, and Gaussian elimination gets it in polynomial time. That's all three properties at once, which is why CFI is the family the wrap up is aimed at. What's left on that rung is tying the gauge to a canonical order on the rigid part of the graph. Above it, Z_{2^k} is scoped but unbuilt, the solvable rung has its lower layers built with one obligation still carried, bounded local groups are polynomial by citation (Luks) rather than by anything proved here, and non-solvable is untouched.

Because these resolvers are always correct (and polynomial) but not complete, more of them could be added in parallel. "Run resolver 1, if it has an answer, use it, otherwise go to the next." That means that the stabilizer will always chip away at the possible remaining answers (known as the residue) as long as at least _one_ of the resolvers gives an answer _somewhere_ on the graph.

Because of that mechanism, this design isn't really about handled graphs, but rather a graph is handleable as long as it does not contain a residue where none of them fire. If it gets to this, a more traditional graph canonizer like nauty will begin an exponential search. This one instead gives up, providing a flag instead of an answer. An optional extension was considered but not yet implemented where it would begin the exhaustive search instead (i.e. fill a value on the stabilizer with \<, then compare with the answer of \> and take the better). That said, families like CFI apply a difficult residue over the top of an arbitrary graph, it can handle this residue but then hands you back the original graph if it can't handle it.

---

## What it does not do

Stated plainly, a lot.

- **It does not put graph isomorphism in P.** No part of it advances that boundary. This is a foundation built inside Lean that reaches exactly the core the literature already identifies as hard. That's a clean and useful outcome, even if a negative one.
- **It is not competitive with nauty or Traces in practice.** The value here are the proofs, not throughput.
- **No named graph family is yet proved handled.** This is intended to change for CFI and Tinhofer during wrap up, but that's unclear if it will be completed before I abandon this project fully.
- **The symmetry side reaches a known-easy class.** Tinhofer graphs sit inside a hierarchy (Discrete ⊂ Amenable ⊂ Compact ⊂ Godsil ⊂ Tinhofer ⊂ Refinable) that is already well understood and long since solved.
- **The cost bound is a declared operation count, not including recomputation.** The cost model (`canon_poly_or_flag`) bounds an explicit cost to compute all the information used in the resolver. This doesn't account for when it recomputes it (which can cause exponentials), and is very easy to do by accident in lean. Simply reusing a variable sometimes recalculates it from scratch. It makes me want to see if I can add a better system into the Lean 4 framework. Also measured runtimes are really slow compared to other languages (even after removing weird cases like Encodable.encode adding a flat ~10 minutes to the runtime).

---

## How it was built

The parts of the method that outlived the research goal:

**Two-language pipeline.** Every strategy was prototyped in C# and measured against
generated adversarial families (CFI graphs, multipedes, Cameron graphs, classical-group
constructions) *before* any Lean was written. Ideas were cheap to kill at the C# stage and
expensive to kill at the Lean stage, so nothing was formalized until it had survived
measurement. Most ideas died in C#.

**Correct theorems as a requirement, not to build towards.** The only `sorry` or `axiom` that exist will be in publication.lean, this is so that nothing can be built that is wrong. Even `native_decide` is not used anywhere as it could run native (i.e. incorrect) code and generate false theorems. This was in large part due to AI, I'd rather have a vacuous theorem with an impossible hypothesis than build off something wrong. Similarly, the axioms in publication.lean are all direct citations, in theory each is "A true statement in a known true form" taken from a paper. The bar everywhere else is that `#print axioms` on any theorem returns exactly Lean's three standard axioms: `propext`, `Classical.choice`, `Quot.sound`, and nothing else, so the trusted base is Lean's kernel and no more.

**Complexity claims made falsifiable.** Costs are tracked in a monad, so a component that
delegates work has to bill for what it delegates. This caught a real defect: a key had
declared a flat `n⁴` bound that was true *by definition* and therefore priced nothing,
making the complexity claim unfalsifiable. Cost accounting is only worth having if it can
come out wrong.

**Dead routes recorded with their falsifiers.** Roughly thirty approaches were closed
during the project, each written up with the specific witness that killed it - an explicit
24-vertex Cayley graph refuting one conjecture, a Shrikhande-graph argument showing another
property was selector-dependent rather than intrinsic. The archive of closed routes is
larger than the archive of successful ones, and re-deriving a dead route is the failure
mode this discipline exists to prevent.

**Statement-level auditing.** A machine-checked theorem is only as good as its statement.
Several audits went hunting for vacuous predicates and hypotheses satisfiable by nothing;
they found some. One pinned complexity statement turned out to be *false at n = 0* and had
to be reshaped - a reminder that "it compiles" and "it says what I meant" are different
properties.

---

## Layout

```
GraphCanonizationProofs/          Lean 4 - the proof development, ~76k lines
  ChainDescent/                   109 gated modules, plus scratch and parked experiments
  Publication.lean                the four headline theorems
  PublicTheoremIndex.md           generated index of everything proved, ~4,100 entries
GraphCanonizationProject/         C# - prototypes, graph generators, solvers, ~17k lines
GraphCanonizationProject.Tests/   xunit tests + measurement probes
docs/                             design docs and the research record, 51 documents
scripts/                          build gate, theorem-index generation
*/Archive/                        retired eras, with notes on why each was retired
```

## Building

Needs the Lean toolchain pinned in `GraphCanonizationProofs/lean-toolchain` (v4.30.0-rc2, fetched
automatically by `lake`) and .NET 8 for the C# side.

```bash
# Lean - the full verification gate (~4 min)
bash scripts/build.sh

# a single module
cd GraphCanonizationProofs && lake build ChainDescent.CFI

# C#
dotnet build workspace.sln
dotnet test GraphCanonizationProject.Tests/GraphCanonizationProject.Tests.csproj
```

## Using it

There's no executable - the C# side is a library and the Lean side is a proof development. The
short version is `new CanonGraphOrdererChainDescent().Run_ToString(new int[n], edges)`, which
returns a canonical form as a string or throws `CanonizationFlaggedException` if it declines to
answer. Two graphs are isomorphic exactly when their forms are equal.

- [`docs/USER-GUIDE.md`](docs/USER-GUIDE.md) - the full guide: both implementations, what a flag
  means, what the four theorems actually promise, and what's worth reusing on its own.
- [`GraphCanonizationProject.Tests/UsageExample.cs`](GraphCanonizationProject.Tests/UsageExample.cs)
  and [`GraphCanonizationProofs/Examples.lean`](GraphCanonizationProofs/Examples.lean) - the same
  examples in runnable form.

## Reading further

- [`GraphCanonizationProofs/PublicTheoremIndex.md`](GraphCanonizationProofs/PublicTheoremIndex.md)
  - the authoritative record of what is proved.
- [`docs/00-START-HERE.md`](docs/00-START-HERE.md) - the design in depth, and a reading
  order for the research docs.

### References

The problems and prior results this project sits against:

- L. Babai, *Graph isomorphism in quasipolynomial time*, STOC 2016.
  [arXiv:1512.03547](https://arxiv.org/abs/1512.03547) - the current best general bound, and
  the reason "polynomial" is still open rather than closed.
- B. Weisfeiler, A. Leman, *A reduction of a graph to a canonical form and an algebra arising
  during this reduction*, Nauchno-Technicheskaya Informatsia 2(9):12-16, 1968 - colour
  refinement, the 1-WL pass the force resolver sits on top of.
- J. Cai, M. Fürer, N. Immerman, *An optimal lower bound on the number of variables for graph
  identification*, Combinatorica 12(4):389-410, 1992 - the CFI construction, which is the
  family this project is aimed at and the source of the F₂ gauge.
- G. Tinhofer, *Graph isomorphism and theorems of Birkhoff type*, Computing 36:285-300, 1986 -
  the Tinhofer class the consume resolver is complete on.
- E. M. Luks, *Isomorphism of graphs of bounded valence can be tested in polynomial time*,
  J. Computer and System Sciences 25(1):42-65, 1982 - the bounded-local-group rung of the ladder.
- D. Neuen, P. Schweitzer, *An exponential lower bound for individualization-refinement
  algorithms for graph isomorphism*, STOC 2018. [arXiv:1705.03283](https://arxiv.org/abs/1705.03283)
- V. Arvind, J. Köbler, G. Rattan, O. Verbitsky, *Graph isomorphism, color refinement, and
  compactness*, computational complexity 2017. [arXiv:1502.01255](https://arxiv.org/abs/1502.01255)
- B. McKay, A. Piperno, *Practical graph isomorphism, II*, J. Symbolic Computation 2014 -
  nauty and Traces.

### What is assumed rather than proved

`Publication.lean` is the only file permitted an `axiom`, and there are exactly eight of them.
Each carries a published theorem, never anything this project is itself trying to prove. The
four headline theorems currently depend on **none** of these - they come out
`[propext, Classical.choice, Quot.sound]`. The axioms are consumed by the residue obligation,
which is still open.

| axiom | result assumed |
|---|---|
| `cameron_classification` | Cameron's classification of primitive coherent configurations (rests on CFSG) - Babai, ITCS 2014 / J. Algebra 2015; Kivva, JCTB 164:245-298, 2024 ([arXiv:2110.13861](https://arxiv.org/abs/2110.13861)); Sun, Wilmes, 2015 |
| `skresanov_two_closure` | Skresanov, rank-3 affine 2-closure. [arXiv:2007.14696](https://arxiv.org/abs/2007.14696), [arXiv:2202.03746](https://arxiv.org/abs/2202.03746) |
| `liebeck_rank3` | M. W. Liebeck, *The affine permutation groups of rank three*, Proc. LMS (3) 54:477-516, 1987 |
| `ponomarenko_2sep` | Ponomarenko, cyclotomic 2-separability. [arXiv:2006.13592](https://arxiv.org/abs/2006.13592) Thm 1.1 |
| `ftpg` | The fundamental theorem of projective geometry - Artin, *Geometric Algebra*, 1957 |
| `buekenhout_shult` | Buekenhout, Shult, *On the foundations of polar geometry*, Geom. Dedicata 3:155-170, 1974 (with Veldkamp-Tits): a polar space of rank ≥ 3 is classical |
| `payne_thas` | Payne, Thas, *Finite Generalized Quadrangles*, 1984 - recognition of classical GQs |
| `witt_flag_transitivity` | Witt's theorem, in the form of Artin, *Geometric Algebra*, 1957 |

Two of these are marked in-file as not yet safe to wire as written: `ftpg` was first formalized
in a form that is *false*, and `payne_thas` needs narrowing because there is no general
"classical GQ recognition" theorem to point at. Elsewhere in the library the same discipline
applies without axioms - a cited result is carried as a named hypothesis on the theorem that
needs it, so it is visible in the statement instead of hidden in the trusted base.
