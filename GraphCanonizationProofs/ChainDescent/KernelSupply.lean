import ChainDescent.Deck2

/-!
# `C3a` — `kernelSupply` : the F₂ kernel supply (the linear-gauge constructor)

## Why deck2 is not enough (remaining-work §1C C3; `PerformanceTest` §13, measured 2026-07-19)

A gauge that is the kernel of parity checks of arity ≥ 3 with minimum weight ≥ 3 (the CFI cycle-space
shape — witness `mp7`, the Fano multipede) defeats every propagation-shaped constructor: one assigned
wire leaves ≥ 2 candidates at every check (girth kills chaining), no weight-≤2 word exists (the
identity-default has nothing valid to complete to), and a `deck_k` seed ladder is defeated in principle
by growing-weight families (there is always a `k+1`). The generators are reachable only by SOLVING the
system: this supply recovers the F₂ system structurally and emits a kernel basis.

## The supply

1. **Rails** (`twin`/`rails`): a rail pair is a same-colour, non-adjacent pair with *disjoint*
   neighbourhoods, each the other's UNIQUE such partner (`uniqueFilter` — no choice, standing trap #7).
   These are the gauge wires (CFI foot pairs).
2. **Local patterns** (`patOf`/`pats`): for each non-rail vertex `v`, every same-colour vertex whose
   rail-touch shape matches `v`'s realizes a *flip pattern* (which touched rails it sees crossed).
   The realizable patterns of a CFI gadget are exactly its even subsets.
3. **The system** (`localRows`/`kernelBasis`): per-vertex constraint rows = the perp of the span of its
   patterns, computed inside its wire support (`nullBasis` restricted + re-embedded); the global gauge
   space `L` = the null space of all rows; `kernelBasis` = an F₂ Gaussian basis of `L`.
4. **Emission** (`flipFunK`): a basis word's candidate flips its rails; a non-rail vertex touching a
   flipped rail maps to its unique same-colour partner matching the flipped adjacency (weights, both
   directions); untouched vertices stay put. `Deck2.permOf` gates bijectivity; `Consume.verified`
   re-checks `IsColAut` as always — the recognition is UNTRUSTED and junk costs firing, never ①.

## ★ The ALL-OR-NOTHING gate (the ①c design lock — trap #7, resolved at the group level)

A Gaussian basis is pivot-order-dependent — a genuine within-cell choice — and with a *partially*
verified basis, WHICH subgroup gets generated would depend on that choice (relabelling could change the
narrowing length ⟹ ①c false). So `kernelGens` emits **all of the basis or nothing**: every basis flip
must pass the permutation gate AND `IsColAut`. Since products of automorphisms are automorphisms,
"the whole basis verifies" ⟺ "every word of `L` verifies" — a *canonical* predicate — so the emitted
GROUP is a canonical function of `(adj, χ)`: the full flip-realization of the canonical subspace `L`,
or trivial. The ① story is therefore NOT `GensEquivariant` (false — the basis lists differ pointwise)
but the `OrbitPrune.SameOrbits` reduction against the set-level reference "flips of every `w ∈ L`,
same gate" (equivariant because `L` and the gate are canonical; reachability = flips commute, so a
kernel word is the symmetric difference = product of basis words — the P3b/`TreePrune` license shape).
That proof stack is **tranche 2** (with the elimination-correctness lemma `span(kernelBasis) = L` it
rides on); this file is tranche 1: the executable object and its measured firing. **Tranche 2 is
COMPLETE (2026-07-19)**: `KernelGauss.lean` (`span(kernelBasis) = L`), `KernelFlip.lean` (the product
lemma `flipFunK_xor` + `touched_moves`), `KernelRef.lean` (`sameOrbits_kernelRef` +
`sameOrbits_appendSupply`), `KernelTransport.lean` (`GensEquivariant kernelRefSupply` + the
capstones). This supply is now **in the record object** —
`Kernel.holKey_foldDeck2KernelFast_selNode_canonizer`, pinned by `Publication.canonForm?`.

## Scope, honestly

Fires on: F₂-linear gauges over rail-pair structure with per-vertex-exact pattern spaces — the CFI /
multipede / cycle-space class at ANY girth and weight (the whole point: `nullBasis` does not care).
Does NOT touch: the copy/translation symmetry of such covers (deck's territory — but deck stalls when
the gauge commutes with it, `PerformanceTest` §13 ⟹ the follow-on mechanism is deck-MODULO-the-verified
-kernel-group, remaining-work C3b); non-linear gauges (the named wall, W2). Measured on `mp7`
(`Regression` §15 gates the cheap cells; `PerformanceTest` §14 the rest): rails 7, basis dim 3, gate
passes, root cell 28 → 7 = the gauge fully certified with the Z₇ translations honestly left standing.
-/

namespace ChainDescent
namespace Kernel

open ChainDescent.CostModel (CostM)
open ChainDescent.Descend
open ChainDescent.Consume (Supply gens verified IsColAut)
open ChainDescent.Deck (uniqueFilter)
open ChainDescent.Deck2 (permOf)

variable {n : Nat}

/-! ## 1. Rails — the gauge wires -/

/-- Symmetric adjacency test (weights matter elsewhere; for rail detection presence suffices). -/
def isAdj (adj : AdjMatrix n) (v w : Fin n) : Bool :=
  adj.adj v w != 0 || adj.adj w v != 0

/-- `w` is a twin candidate for `v`: same colour, distinct, non-adjacent, disjoint neighbourhoods. -/
def twinP (adj : AdjMatrix n) (χ : Colouring n) (v w : Fin n) : Bool :=
  w != v && χ w == χ v && !isAdj adj v w &&
  (List.finRange n).all (fun u => !(isAdj adj v u && isAdj adj w u))

/-- The unique twin, if any (`uniqueFilter` — ambiguity means no rail, never a choice). -/
def twin (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) : Option (Fin n) :=
  uniqueFilter (twinP adj χ v)

/-- The rail pairs, one entry per unordered pair (listed at the lower index — an INTERNAL labelling;
the ① story never depends on it, see the header). Mutual uniqueness is required. -/
def rails (adj : AdjMatrix n) (χ : Colouring n) : List (Fin n × Fin n) :=
  (List.finRange n).filterMap fun v =>
    match twin adj χ v with
    | some w => if v.val < w.val && twin adj χ w == some v then some (v, w) else none
    | none => none

/-- Is `x` an endpoint of any rail? -/
def onRail (rl : List (Fin n × Fin n)) (x : Fin n) : Bool :=
  rl.any (fun p => p.1 = x || p.2 = x)

/-! ## 2. Local flip patterns -/

/-- `v` touches rail `(a, b)`. -/
def touches (adj : AdjMatrix n) (v : Fin n) (p : Fin n × Fin n) : Bool :=
  isAdj adj v p.1 || isAdj adj v p.2

/-- The flip pattern `w'` realizes for `v` (both non-rail, same colour, matching single-sided touch
shape): bit `r` = touched and crossed. `none` when shapes differ. -/
def patOf (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n)) (v w' : Fin n) :
    Option (List Bool) :=
  if χ w' == χ v && !onRail rl v && !onRail rl w' &&
     rl.all (fun p =>
       let va := isAdj adj v p.1; let vb := isAdj adj v p.2
       let wa := isAdj adj w' p.1; let wb := isAdj adj w' p.2
       !(va && vb) && !(wa && wb) && ((va || vb) == (wa || wb))) then
    some (rl.map (fun p =>
      (isAdj adj v p.1 || isAdj adj v p.2) && (isAdj adj v p.1 != isAdj adj w' p.1)))
  else none

/-- All realizable patterns at `v` (`v` itself contributes the zero pattern). -/
def pats (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n)) (v : Fin n) :
    List (List Bool) :=
  (List.finRange n).filterMap (patOf adj χ rl v)

/-! ## 3. The F₂ toolkit — untrusted, correctness = tranche 2 -/

def xorRow (r₁ r₂ : List Bool) : List Bool := r₁.zipWith (· != ·) r₂

def reduceRow (pivots : List (Nat × List Bool)) (r : List Bool) : List Bool :=
  pivots.foldl (fun r cp => if r.getD cp.1 false then xorRow r cp.2 else r) r

/-- Reduced row echelon form as a pivot list (column, row). -/
def echelon (rows : List (List Bool)) : List (Nat × List Bool) :=
  rows.foldl (fun pivots r =>
    let r' := reduceRow pivots r
    match r'.findIdx? id with
    | some c =>
        (c, r') :: pivots.map (fun cp => (cp.1, if cp.2.getD c false then xorRow cp.2 r' else cp.2))
    | none => pivots) []

/-- A basis of the null space of the row space, over `m` columns: one word per free column. -/
def nullBasis (m : Nat) (rows : List (List Bool)) : List (List Bool) :=
  let pivots := echelon rows
  let pivotCols := pivots.map (·.1)
  ((List.range m).filter (fun c => !pivotCols.contains c)).map (fun f =>
    (List.range m).map (fun j =>
      if j == f then true
      else match pivots.find? (fun cp => cp.1 == j) with
        | some cp => cp.2.getD f false
        | none => false))

def restrictCols (cols : List Nat) (r : List Bool) : List Bool :=
  cols.map (fun c => r.getD c false)

def embedCols (m : Nat) (cols : List Nat) (r : List Bool) : List Bool :=
  (List.range m).map (fun j =>
    match cols.findIdx? (· == j) with
    | some k => r.getD k false
    | none => false)

/-! ## 4. The system and its kernel -/

/-- The wire support of `v` (indices into `rl`). -/
def wiresOf (adj : AdjMatrix n) (rl : List (Fin n × Fin n)) (v : Fin n) : List Nat :=
  (List.range rl.length).filter (fun r =>
    match rl[r]? with
    | some p => touches adj v p
    | none => false)

/-- `v`'s constraint rows: the perp of the span of its patterns, inside its wire support. -/
def localRows (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n)) (v : Fin n) :
    List (List Bool) :=
  if onRail rl v then []
  else
    let ws := wiresOf adj rl v
    (nullBasis ws.length ((pats adj χ rl v).map (restrictCols ws))).map (embedCols rl.length ws)

/-- A Gaussian basis of the gauge space `L` = the null space of every vertex's constraints. -/
def kernelBasis (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n)) :
    List (List Bool) :=
  nullBasis rl.length ((List.finRange n).flatMap (localRows adj χ rl))

/-! ## 5. Emission -/

/-- The rail image of `x` under word `w` (`none` if `x` is not a rail endpoint). -/
def railImg (rl : List (Fin n × Fin n)) (w : List Bool) (x : Fin n) : Option (Fin n) :=
  ((rl.zip w).findSome? fun pb =>
    if x = pb.1.1 then some (if pb.2 then pb.1.2 else pb.1.1)
    else if x = pb.1.2 then some (if pb.2 then pb.1.1 else pb.1.2)
    else none)

/-- The candidate table for word `w`: rails flip; a non-rail vertex touching a flipped rail moves to
its unique same-colour partner matching the flipped adjacency (full weights, both directions);
everything else stays put. Junk is caught by `permOf` + verification. -/
def flipFunK (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n)) (w : List Bool)
    (v : Fin n) : Fin n :=
  match railImg rl w v with
  | some x => x
  | none =>
      if (rl.zip w).any (fun pb => pb.2 && touches adj v pb.1) then
        match uniqueFilter (fun w' =>
          χ w' == χ v && !onRail rl w' &&
          (rl.zip w).all (fun pb =>
            let ia := if pb.2 then pb.1.2 else pb.1.1
            let ib := if pb.2 then pb.1.1 else pb.1.2
            adj.adj w' ia == adj.adj v pb.1.1 && adj.adj ia w' == adj.adj pb.1.1 v &&
            adj.adj w' ib == adj.adj v pb.1.2 && adj.adj ib w' == adj.adj pb.1.2 v)) with
        | some w' => w'
        | none => v
      else v

/-! ## 6. The supply — with the all-or-nothing gate -/

/-- Emit the whole verified basis or nothing (the ①c design lock — see the header). -/
def kernelGens (adj : AdjMatrix n) (χ : Colouring n) : List (Equiv.Perm (Fin n)) :=
  let rl := rails adj χ
  let basis := kernelBasis adj χ rl
  let cands := basis.filterMap (fun w => permOf (flipFunK adj χ rl w))
  if cands.length == basis.length &&
     cands.all (fun ρ => decide (IsColAut adj χ ρ)) then cands else []

/-- **★ THE KERNEL SUPPLY.** Recognition and solving are untrusted; `Consume.verified` re-checks
every emitted generator. Cost billed flat at `n⁵` (extraction `n³` + elimination `≤ n³` + `≤ n`
emissions at `n²` each — generous, honest). -/
def kernelSupply : Supply n := fun adj χ =>
  (kernelGens adj χ, n * n * n * n * n)

end Kernel
end ChainDescent
