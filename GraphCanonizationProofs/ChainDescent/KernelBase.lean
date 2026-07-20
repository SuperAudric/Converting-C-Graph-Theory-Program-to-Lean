import ChainDescent.KernelTransport

/-!
# `C3b` — `baseSupply` : base-graph recovery + lift (the cover-symmetry constructor)

## Why the kernel supply is not enough (remaining-work §1C C3 ii-c; `PerformanceTest` §15/§16)

`kernelSupply` certifies the *gauge* — the F₂ kernel of the parity checks — and nothing else. On the C3
witness `mp7` (the Fano multipede) that is measured to be exactly right and exactly not enough: the root
gadget cell narrows `28 → 7`, and the standing 7 is the **base** symmetry (the `Z₇` translation of the
Fano plane), which is invisible to every gauge-shaped constructor because it is not a gauge element.

⛔ **`deck` modulo the verified subgroup `K` is DEAD as a route here** — do not re-attempt it in that
form. `PerformanceTest` §13/§15 measured it: girth 6 in the incidence structure means a translate seed
forces 1 vertex of 42, and quotienting by `K` creates no chaining where there is none to create.
Propagation is not the vehicle on this family at any modulus.

## The supply

The observation that makes this work: `kernelSupply`'s *extraction* already computes the base object.
Rails are the segments, per-vertex wire supports (`wiresOf`) are the checks, and their incidence IS the
base incidence structure — on `mp7`, literally the Fano plane (measured: rails = the 7 foot pairs,
supports = the 7 lines `{i, i+1, i+3}`). So:

1. **Recover** the base graph (`baseAdj`/`baseCol`): a bipartite graph on `rails ++ supportClasses`,
   the two sides separated by the colouring, of size `baseSize < n`.
2. **Solve the base** by running the existing supply stack on it — a strictly smaller graph with the
   gauge quotiented out (`mp7`: 42 ↦ 14 vertices).
3. **Lift** each base generator: rail `i` ↦ rail `τ i`, endpoints lower↦lower, then every non-rail
   vertex to its unique same-colour partner matching the transported adjacency (`liftFun` — the same
   unique-partner rule as `flipFunK`, generalized from "flip within a rail" to "map rail to rail").
   `permOf` gates bijectivity and `Consume.verified` re-checks `IsColAut` as always.

## ★ Why the lift's choice-dependence is free (the ① story, and why this route beats propagation)

The endpoint orientation (`lower ↦ lower`) is a genuine within-cell choice, and it is *labelling*-
dependent — which endpoint is "lower" is an artefact of the input labelling. That would normally be
trap #7 all over again. It is free here for one reason: **two lifts of the same base automorphism
differ by an automorphism inducing the identity on the base, i.e. by a pure gauge element — an element
of `K`, which `kernelSupply` already emits.** So the reference is "all valid lifts of all base gens"
(equivariant, since the base object and the base supply are), the executable emits one arbitrary lift,
and `OrbitPrune.SameOrbits` closes exactly as in tranche 2.

The load-bearing detail: `WordReach` needs only that each `v` and `ρ' v` be *connected*, so a
**per-vertex** gauge element suffices — no single global `k` is required. That is what turns the coset
obligation from a graph-dependent assumption into a provable statement.

⚠ **This supply is therefore only sound to append AFTER `kernelSupply`** — `K` must be present in the
same supply for the licence above to be available.

## ⛔⛔ STATUS 2026-07-20 — THIS FILE IS **NOT IN `build.sh`** AND MUST NOT BE LANDED YET.

It compiles, and the recovery and lift halves are *measured correct*, but as written the supply emits
nothing but identities on the witness. Measurements: `ChainDescent/ScratchBase.lean` (SCRATCH); the
full write-up is remaining-work §1C C3 (ii-c), 2026-07-20 block. Read that before touching this file.

**✅ Confirmed by measurement (do not re-derive):**
· Base recovery is faithful, with no new extraction code: on `mp7`, rails = the 7 foot pairs,
  supports = the 7 Fano lines, base = 14 vertices / 2 cells = the Heawood graph, and the known `Z₇`
  translation is a colour-automorphism of the *recovered* base graph.
· **★ The coset theory above is confirmed quantitatively:** over all `2⁷` orientations the `Z₇`
  translation admits **exactly 8 = |L| = 2³** verified lifts. "Two lifts differ by a pure gauge
  element" is measured, not assumed — and it makes `⚠` above binding: `K` must be present, so this
  supply is only sound appended AFTER `kernelSupply`.

**⛔ What this file gets wrong: NO SUPPLY SOLVES THE BASE GRAPH.**
Of deck2's **301** raw base gens, exactly **1** is a genuine base colour-automorphism — the
**identity**; **zero** move a rail. fold (49) and deck (7) emit no non-trivial base automorphism
either. So `baseGens` is fed nothing to lift, and the naive `lower↦lower` orientation in
`railImgList` is untested rather than refuted.

**⚠ RETRACTED (same day, before it spread): an earlier version of this header claimed the blocker
was that liftability is the KERNEL of `Aut(base) → H¹`, hence unreachable by per-generator
filtering. That came from JUNK DATA and is WRONG — do not resurrect it.** The bug: `Consume.gens`
returns **UNVERIFIED** candidates (junk is filtered by `Consume.verified` downstream, not by
`gens`), and the first pass never applied `IsColAut` to the BASE gens. **⚠ STANDING TRAP: any probe
reading `Consume.gens` directly must filter by `IsColAut` first.** The lift itself was never
implicated — the `Z₇` control stands, and the C# cross-check below shows the whole collineation
group lifts.

**▶ C# cross-check: the C# canonizer DOES handle `mp7`** (`FanoMultipedeProbe.cs`). On the SAME
object Lean uses (uniform colouring, `n = 42`): canonical, 4 nodes, depth 3,
**|residual| = 1344 = 8 × 168 = |L| × |PGL(3,2)|**. ⚠ Note the fixture trap: the C# generator's
"fine colouring" gives every segment and cluster its own colour, excluding the base symmetry by
fiat, and the existing suite covers only `7 ∤ m` (the rigid case).

**▶ The architectural catch (the real open question).** C# gets those automorphisms by harvesting
**coinciding leaf matrices** (nauty-style, a posteriori) into a Schreier–Sims chain — which requires
exploring several leaves, while ② demands a single path of `≤ n+1` nodes or a flag. So the C#
success does not transfer for free. Settle first whether the base graph is solvable on a single
path at all; only then is the supply shape here worth completing.
-/

namespace ChainDescent
namespace Kernel

open ChainDescent.Consume (Supply gens verified IsColAut)
open ChainDescent.Deck2 (permOf)

variable {n : Nat}

/-! ## 1. Base recovery -/

/-- The non-rail vertices, in index order (an internal labelling, exactly as with `rails`). -/
def nonRails (rl : List (Fin n × Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun v => !onRail rl v)

/-- The distinct wire supports — the base "checks". -/
def supports (adj : AdjMatrix n) (rl : List (Fin n × Fin n)) : List (List Nat) :=
  ((nonRails rl).map (wiresOf adj rl)).dedup

/-- Colour code of a support class: (number of members, sum of their colours) — equivariant, lossy
only in the direction that costs firing. -/
def suppCode (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n)) (s : List Nat) :
    Nat :=
  let ms := (nonRails rl).filter (fun v => wiresOf adj rl v == s)
  ms.length * 1000 + (ms.map χ).sum

/-- The base index count: rails first, then support classes.  Always `< n` when there is a rail
(each rail eats two vertices and each class at least one non-rail vertex). -/
def baseSize (adj : AdjMatrix n) (χ : Colouring n) : Nat :=
  (rails adj χ).length + (supports adj (rails adj χ)).length

/-- The base adjacency: rail `i` ~ class `k` iff `i ∈ supports[k]`.  `m` is passed explicitly
(intended: `m = baseSize adj χ`) so the index type stays a literal at the use site. -/
def baseAdj (m : Nat) (adj : AdjMatrix n) (χ : Colouring n) : AdjMatrix m :=
  let rl := rails adj χ
  let sp := supports adj rl
  ⟨fun i j =>
    let r := rl.length
    if i.val < r && r ≤ j.val then
      (if ((sp.getD (j.val - r) []).contains i.val) then 1 else 0)
    else if j.val < r && r ≤ i.val then
      (if ((sp.getD (i.val - r) []).contains j.val) then 1 else 0)
    else 0⟩

/-- The base colouring — rails (even) and classes (odd) on separate sides, so every base
colour-automorphism preserves the rail block. -/
def baseCol (m : Nat) (adj : AdjMatrix n) (χ : Colouring n) : Colouring m :=
  let rl := rails adj χ
  let sp := supports adj rl
  fun i =>
    let r := rl.length
    if i.val < r then (match rl[i.val]? with | some p => 2 * χ p.1 | none => 0)
    else 2 * (suppCode adj χ rl (sp.getD (i.val - r) [])) + 1

/-! ## 2. The lift -/

/-- Lift a rail-image list to a candidate map on `Fin n`: rail endpoints go where `img` says, and a
non-rail vertex maps to its unique same-colour non-rail partner matching the transported adjacency
(full weights, both directions).  Junk is caught by `permOf` + verification. -/
def liftFun (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n))
    (img : List (Fin n × Fin n)) (v : Fin n) : Fin n :=
  match ((rl.zip img).findSome? fun pq =>
      if v = pq.1.1 then some pq.2.1 else if v = pq.1.2 then some pq.2.2 else none) with
  | some x => x
  | none =>
      match Deck.uniqueFilter (fun w' =>
        χ w' == χ v && !onRail rl w' &&
        (rl.zip img).all (fun pq =>
          adj.adj w' pq.2.1 == adj.adj v pq.1.1 && adj.adj pq.2.1 w' == adj.adj pq.1.1 v &&
          adj.adj w' pq.2.2 == adj.adj v pq.1.2 && adj.adj pq.2.2 w' == adj.adj pq.1.2 v)) with
      | some w' => w'
      | none => v

/-- The rail images named by a base permutation `τ`, in the naive (lower↦lower) orientation.
`none` if `τ` does not preserve the rail block. -/
def railImgList (m : Nat) (rl : List (Fin n × Fin n)) (τ : Equiv.Perm (Fin m)) :
    Option (List (Fin n × Fin n)) :=
  (List.range rl.length).mapM (fun i =>
    if h : i < m then rl[(τ ⟨i, h⟩).val]? else none)

/-- Lift one base generator, gate it, and verify it on the ORIGINAL graph. -/
def liftGen (adj : AdjMatrix n) (χ : Colouring n) (m : Nat) (rl : List (Fin n × Fin n))
    (τ : Equiv.Perm (Fin m)) : Option (Equiv.Perm (Fin n)) :=
  match railImgList m rl τ with
  | none => none
  | some img =>
      match permOf (liftFun adj χ rl img) with
      | none => none
      | some ρ => if decide (IsColAut adj χ ρ) then some ρ else none

/-! ## 3. The supply -/

/-- The stack run on the BASE graph.  Note this is not a recursive call into this supply: the base
object has the gauge quotiented out, so the gauge-shaped constructor is exactly what it does not
need. -/
def baseStack (m : Nat) : Supply m :=
  Deck.appendSupply (Fold.foldSupplyFast (n := m))
    (Deck.appendSupply (Deck.deckSupply (n := m)) (Deck2.deck2Supply (n := m)))

/-- The lifted base generators. -/
def baseGens (adj : AdjMatrix n) (χ : Colouring n) : List (Equiv.Perm (Fin n)) :=
  let rl := rails adj χ
  let m := baseSize adj χ
  let bA := baseAdj m adj χ
  let bC := baseCol m adj χ
  let τs := gens (baseStack m) bA (Refine.warmRefineVec bA bC).col
  τs.filterMap (liftGen adj χ m rl)

/-- **★ THE BASE SUPPLY.**  Recovery, base solving and lifting are all UNTRUSTED; `Consume.verified`
re-checks every emitted generator, so junk costs firing and never ①.  Cost billed flat at `n⁶`:
extraction `n³`, the base stack's own bill on `m < n` vertices, and `≤ n` lifts at `n²` each. -/
def baseSupply : Supply n := fun adj χ =>
  (baseGens adj χ, n * n * n * n * n * n)

end Kernel
end ChainDescent
