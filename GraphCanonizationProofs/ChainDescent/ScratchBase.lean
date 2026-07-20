import ChainDescent.Regression

/-!
SCRATCH — the C3b base-graph-recovery + lift measurement record (2026-07-20). **NOT in `build.sh`**
(these `#eval`s cost minutes; fold the surviving numbers into `PerformanceTest` §16 before deleting).
Written up in remaining-work §1C C3 (ii-c) 2026-07-20 block; verdict in `KernelBase.lean`'s header.

What it measures, in order: base recovery on `mp7` (rails = the 7 foot pairs, supports = the 7 Fano
lines, base = 14 vertices / 2 cells = Heawood); which supplies fire on the base (fold 49 / deck 7 /
deck2 301 gens, but **0 / 0 / 210 non-identity** — and deck2's base rail-orbit is all 7); the naive
`lower↦lower` lift (301 pass `permOf`, **exactly 1 verifies — the identity**); and the two controls
that settle the diagnosis — the known `Z₇` translation IS an automorphism of the RECOVERED base graph,
admits **exactly `8 = |L|`** verified lifts across all 128 orientations (the coset theory, confirmed),
yet is **not among deck2's gens**, and none of the 12 rail-moving gens lifts under ANY orientation.
-/

namespace ChainDescent
namespace ScratchBase

open ChainDescent.Kernel
open ChainDescent.Consume (gens IsColAut)
open ChainDescent.Deck2 (permOf)

variable {n : Nat}

/-- The non-rail vertices, in index order (an internal labelling, as with `rails`). -/
def nonRails (rl : List (Fin n × Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun v => !onRail rl v)

/-- The distinct wire supports = the base "checks". -/
def supports (adj : AdjMatrix n) (rl : List (Fin n × Fin n)) : List (List Nat) :=
  ((nonRails rl).map (wiresOf adj rl)).dedup

/-- Colour code of a support class: (number of members, sum of their colours). -/
def suppCode (adj : AdjMatrix n) (χ : Colouring n) (rl : List (Fin n × Fin n)) (s : List Nat) :
    Nat :=
  let ms := (nonRails rl).filter (fun v => wiresOf adj rl v == s)
  ms.length * 1000 + (ms.map χ).sum

/-- Base index count: rails first, then support classes. -/
def baseSize (adj : AdjMatrix n) (χ : Colouring n) : Nat :=
  (rails adj χ).length + (supports adj (rails adj χ)).length

/-- The base adjacency: rail `i` ~ class `k` iff `i ∈ supports[k]`.  `m` is passed explicitly
(= `baseSize`) so the index type stays a literal. -/
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

/-- The base colouring: rails and classes on separate sides. -/
def baseCol (m : Nat) (adj : AdjMatrix n) (χ : Colouring n) : Colouring m :=
  let rl := rails adj χ
  let sp := supports adj rl
  fun i =>
    let r := rl.length
    if i.val < r then (match rl[i.val]? with | some p => 2 * χ p.1 | none => 0)
    else 2 * (suppCode adj χ rl (sp.getD (i.val - r) [])) + 1

/-- Lift a rail permutation `rp : Fin n × Fin n → Fin n × Fin n` (rail ↦ target rail, endpoints
already oriented) to a candidate map on `Fin n`: rail endpoints go where told, and a non-rail vertex
maps to its unique same-colour non-rail partner matching the transported adjacency. -/
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

end ScratchBase
end ChainDescent

/-! ## Measurements on mp7 -/

namespace ChainDescent.ScratchBase

open ChainDescent.Regression

#eval (Kernel.rails mp7 mp7Root.col)
#eval (supports mp7 (Kernel.rails mp7 mp7Root.col))
#eval baseSize mp7 mp7Root.col

def bA : AdjMatrix 14 := baseAdj 14 mp7 mp7Root.col
def bC : Colouring 14 := baseCol 14 mp7 mp7Root.col
def bRoot := Refine.warmRefineVec bA bC

-- refinement cell count on the base graph
#eval ((List.finRange 14).map bRoot.col).dedup.length

-- do the existing supplies fire on the BASE graph?
#eval (Consume.gens (Fold.foldSupplyFast) bA bRoot.col).length
#eval (Consume.gens (Deck.deckSupply) bA bRoot.col).length
#eval (Consume.gens (Deck2.deck2Supply) bA bRoot.col).length

/-- Lift a base permutation to a candidate on `Fin 42`: rail `i` ↦ rail `τ i` (lower↦lower — the
orientation choice absorbed by `K`); `none` if `τ` does not preserve the rail block. -/
def mk42 (k : Nat) : Fin 42 := ⟨k % 42, Nat.mod_lt _ (by omega)⟩
def mk14 (k : Nat) : Fin 14 := ⟨k % 14, Nat.mod_lt _ (by omega)⟩
def z42 : Fin 42 := ⟨0, by omega⟩

def liftBase (τ : Equiv.Perm (Fin 14)) : Option (Equiv.Perm (Fin 42)) :=
  let rl := Kernel.rails mp7 mp7Root.col
  let r := rl.length
  if (List.range r).all (fun i => (τ (mk14 i)).val < r) then
    let img := (List.range r).map (fun i => rl.getD (τ (mk14 i)).val (z42, z42))
    Deck2.permOf (liftFun mp7 mp7Root.col rl img)
  else none

def bDeck2raw : List (Equiv.Perm (Fin 14)) := Consume.gens (Deck2.deck2Supply) bA bRoot.col

/-- ★ THE FIX: `Consume.gens` is UNVERIFIED (junk is filtered by `Consume.verified`
downstream). Keep only genuine base colour-automorphisms. -/
def bDeck2 : List (Equiv.Perm (Fin 14)) :=
  (bDeck2raw.filter (fun t => decide (Consume.IsColAut bA bRoot.col t))).dedup

#eval bDeck2raw.length
#eval bDeck2.length            -- how many were REAL
#eval (bDeck2.filter (fun t => decide ((t (mk14 0)).val != 0))).length  -- real movers

def liftBaseO (t : Equiv.Perm (Fin 14)) (o : List Bool) : Option (Equiv.Perm (Fin 42)) :=
  let rl := Kernel.rails mp7 mp7Root.col
  let r := rl.length
  if (List.range r).all (fun i => (t (mk14 i)).val < r) then
    let img := (List.range r).map (fun i =>
      let q := rl.getD (t (mk14 i)).val (z42, z42)
      if o.getD i false then (q.2, q.1) else q)
    Deck2.permOf (liftFun mp7 mp7Root.col rl img)
  else none

def allOrients : List (List Bool) :=
  (List.range 128).map (fun k => (List.range 7).map (fun i => (k / 2^i) % 2 == 1))

def goodOrients (t : Equiv.Perm (Fin 14)) : Nat :=
  (allOrients.filter (fun o => match liftBaseO t o with
    | some p => decide (Consume.IsColAut mp7 mp7Root.col p)
    | none => false)).length

def movers : List (Equiv.Perm (Fin 14)) :=
  (bDeck2.filter (fun t => decide ((t (mk14 0)).val != 0)))

-- ★ do the VERIFIED movers lift? (expect 8 = |L| each, per the C# residual 1344 = 8*168)
#eval (movers.take 6).map (fun t => (t (mk14 0)).val)
#eval (movers.take 6).map goodOrients

end ChainDescent.ScratchBase
