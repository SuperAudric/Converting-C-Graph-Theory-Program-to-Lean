# User guide

How to actually run this thing, what its answers mean, and what is worth taking from it if you
don't want the canonizer itself.

Everything below has been run against this repo. Two files hold the same examples in executable
form, so they can't drift:

| | file | run it with |
|---|---|---|
| C# | [`GraphCanonizationProject.Tests/UsageExample.cs`](../GraphCanonizationProject.Tests/UsageExample.cs) | `dotnet test --filter "FullyQualifiedName~UsageExample"` |
| Lean | [`GraphCanonizationProofs/Examples.lean`](../GraphCanonizationProofs/Examples.lean) | `cd GraphCanonizationProofs && lake env lean Examples.lean` |

---

## 1. Which implementation do you want?

There are two, and they are not interchangeable.

**The C# one is the one you run.** It is a normal library, it is fast enough to be useful, and it
has the graph generators and the group machinery attached. It is not proved correct.

**The Lean one is the one that is proved correct.** It is the same algorithm expressed as a proof
object, and it is evaluated by the Lean interpreter, which is slow — fine for a handful of
vertices, unusable past a dozen or so. Use it to check what the theorems are actually about, not
to canonize anything.

If you came here because you need canonical forms for real graphs, you want **nauty or Traces**,
not this. This project's contribution is the proofs; see the README's "What it does not do".

---

## 2. C# quickstart

There is no executable — it is a library with no `Main`. Reference the project, or write a test.
The entire public surface is `ICanonGraphOrderer`:

```csharp
using Canonizer;

var orderer = new CanonGraphOrdererChainDescent();

// Adjacency matrix. Entries are edge "colours"; 0 means no edge, so a plain
// graph is 0/1. The array must be square and symmetric.
int[,] path = new int[4,4];
foreach (var (a,b) in new[]{(0,1),(1,2),(2,3)}) { path[a,b] = 1; path[b,a] = 1; }

// First argument pre-colours the vertices (atom types, say). All-zero means
// "no prior distinction". Its length is the vertex count.
string form = orderer.Run_ToString(new int[4], path);
```

`Run_ToString` gives you the canonical form as a string; `Run` gives you an `AdjMatrix` if you
want to keep working with it. **Two graphs are isomorphic exactly when their canonical forms are
equal** — so comparison is string equality, and you can use the form as a dictionary key or store
it in a database column.

Three things worth knowing:

- **The output is the edge matrix only.** Vertex types are an *input constraint* that changes
  which ordering wins; they are not printed. Two graphs that differ only in vertex colours can
  therefore share a form — if you are canonizing coloured graphs, hash the types alongside the
  form, or fold the colours into the edge weights.
- **`vertexTypes` genuinely does something.** It seeds the partial order, so colouring the
  endpoints of a 4-path changes the resulting matrix (`VertexTypesConstrainTheOrdering` in the
  example file demonstrates exactly this), and correspondingly-coloured relabellings still agree
  (`VertexTypesAreThemselvesCanonical`).
- **It may decline to answer.** See below.

### When it gives up

`Run`/`Run_ToString` either return a canonical form or throw `CanonizationFlaggedException`. They
never return a wrong answer — that is the guarantee the Lean side proves, and it is the whole
design: incomplete, never incorrect.

```csharp
try  { var form = orderer.Run_ToString(new int[n], edges); }
catch (CanonizationFlaggedException ex)
{
    ex.Reason;               // why it stopped
    ex.ResidualGroupOrder;   // |Aut| harvested before it did
    ex.Kind;                 // FlagKind: which of the two causes
}
```

`FlagKind` separates the two reasons the descent can stall:

- **`Tier2Like`** — a non-trivial, *non-abelian* residual symmetry survived. This is the genuine
  hard case, the one the project never closed.
- the abelian counterpart — a hidden abelian symmetry (a CFI gauge) that the harvest did not
  consume inside its budget. Not fundamental; a complete linear harvest absorbs it.

`BudgetOverride` caps the work, and is the honest way to bound runtime: set it and handle the
flag. With no override the budget is derived from the graph.

---

## 3. Lean quickstart

```bash
cd GraphCanonizationProofs
lake env lean Examples.lean
```

The canonizer is one definition:

```lean
def canonForm? (n : ℕ) (G : AdjMatrix n) : Option (Fin n → Fin n → Nat) :=
  Select.canonFormFastS? (RecordKey.recordKey (n := n)) (RecordCost.recordSupplyFast (n := n)) G
```

`AdjMatrix n` wraps `adj : Fin n → Fin n → Nat`. `none` is the flag. `canonForm?` returns a
function, which `#eval` can't print, so render it as rows — `Examples.lean` has the helper.

This is the same definition as `Publication.canonForm?`. `Examples.lean` repeats it rather than
importing `Publication.lean`, because that file carries the citation axioms and two open
obligations; the examples depend on neither.

**Speed, measured on this repo:** the whole examples file is ~8 s once mathlib is in the page
cache, a 5-cycle is ~32 s, and the project's own `n = 15` regression case takes ~410 s. A cold
first run is much slower because it pays to load mathlib. This is the cost of interpreting a proof
object.

---

## 4. What the guarantees actually say

Four theorems in [`Publication.lean`](../GraphCanonizationProofs/Publication.lean), and it is
worth being precise about which is which:

| theorem | what it gives you |
|---|---|
| `canon_sound` | if it returns a form, that form really is a canonical form of your input |
| `canon_complete` | two graphs get the same form exactly when they are isomorphic |
| `flag_iso_invariant` | if it flags on a graph it flags on every isomorphic copy — the *refusal* doesn't leak the labelling either |
| `canon_poly_or_flag` | on any input it either finishes inside a declared polynomial cost bound, or flags |

`flag_iso_invariant` is the non-obvious one. A canonizer that gave up unpredictably depending on
how the input happened to be written would leak information through its failures; this says the
give-up set is closed under isomorphism.

Two caveats you should read before relying on any of it. The cost bound is a *declared operation
count* and does not model recomputation, so it is not a wall-clock guarantee. And no named graph
family is yet proved to avoid the flag — the class where these theorems bite is defined by a
predicate that has not been instantiated. The README's "What it does not do" is the full list.

---

## 5. Worth taking even if you don't want the canonizer

Most of the value here is not the canonizer. Independently usable:

**Adversarial graph generators (C#)** — `CfiGraphGenerator`, `MultipedeGenerator`,
`CameronGraphGenerator`, `FormsGraphBuilder`, `ClassicalGroupGenerators`, `TwistConstruction`.
If you are testing any isomorphism or refinement code, these are the families that break it, and
they come with well-formedness assertions.

**`PermutationGroup.cs`** — a full Schreier–Sims implementation: stabilizer chain, `Order`,
`Contains`, `Orbit`, `BasePoints`, normal closure, regular normal *p*-subgroup extraction.
Self-contained.

**The Lean refinement machinery** — 1-WL / colour refinement with proofs that it is
isomorphism-invariant and that colour classes are unions of orbits. If you are formalizing
anything in this area, this is the part that is most reusable and least entangled.

**The coherent-configuration and Nullstellensatz work** — `ChainDescent.Nullstellensatz*`,
`ChainDescent.Scheme`, `ChainDescent.CoherentConfig`. The quadric Nullstellensatz was proved
in-project after starting life as a citation, and is axiom-clean.

**The research record** — `docs/` is ~50 documents, and the archive of *closed* routes is larger
than the archive of open ones. Each dead route is recorded with the specific witness that killed
it. If you are working in this area, the falsifiers are likely to be worth more than the successes.

---

## 6. Finding things

- [`PublicTheoremIndex.md`](../GraphCanonizationProofs/PublicTheoremIndex.md) — every public
  declaration with a one-line description. This is the authoritative "what is proved". It is large;
  grep it rather than reading it.
- [`docs/00-START-HERE.md`](./00-START-HERE.md) — reading order for the design docs.
- [`scripts/build.sh`](../scripts/build.sh) — the module list, in dependency order, each line
  tagged with what it is. The fastest way to get a map of the Lean side.
