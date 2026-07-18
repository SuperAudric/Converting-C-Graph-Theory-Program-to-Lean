import ChainDescent.FoldFast
import ChainDescent.Regression

/-!
# The MULTIPEDE FOLD witness — F2 at scale, on a genuinely WL-blind core (OFF the build path)

`lake build ChainDescent.MultipedeWitness` (~2.5 min of eval at `n = 36/72` — deliberately not in
`scripts/build.sh`, exactly like `PerformanceTest` and `SelectWitness`).

## Why this witness had to exist (fold-tower plan §8 item 4, the staged tail)

Every fold witness in `Regression`/`PerformanceTest` is honest about a limitation: at those sizes a PIN
still discretizes something (`vfold*`: everything but the mirror class; `wcyc*`: the whole cycle), so the
matching supplies also fire there and the machine-checked separation is only against specific mechanisms.
The claim that F2's structural harvest is *needed* — not merely cheaper — requires a core where refinement
is blind EVERYWHERE: a **multipede** (the C# IR-blindspot family, `BuildNativeMultipede` ported: native-Z₂
over the 6-circulant `{0,1,3}`). Its defining property, measured exhaustively below: **individualizing any
segment vertex creates exactly two singletons (the pinned pair) and cascades NOWHERE** — 34 of 36 vertices
stay in non-singleton cells after any pin.

## The construction

- `mp36` — segments `0..11` (position `p = v/2`, state `a = v%2`; type = `p`), gadgets `12..35` (line
  `li = g/4` over positions `(li, li+1, li+3) mod 6`, one gadget per sum-zero tuple `(t₀, t₁, t₀+t₁)`;
  type = one class). Rigid (the blindspot: rigid but 1-WL-blind).
- `dmp72` — the matched double (`DoubleAndMatch` port): two copies + the perfect matching `i ↔ 36+i`.
  `Aut(dmp72) = Z₂` (the copy swap σ), over a rigid core.

## The measured content (2026-07-18)

1. **Exhaustive pin-blindness**: all 12 segment pins leave the refinement non-discrete. This carries the
   any-`d` deadness structurally: the copy swap moves EVERY vertex, `partialMatch` needs each moved vertex
   singleton on one side (`CatchesAt`), and `d` pins produce ≤ `2d + 2` singletons — so no matching supply
   can catch σ below `d ≈ n/2`. (The `d = 0` deadness is also measured directly.)
2. **`foldSupplyFast` fires refinement-free**: 16/16 candidates verify (the diagonal identities + the
   fiber-wise copy swaps from every cross-copy seed pair) and the branch 4-cell narrows to **2**.
3. **The graded endpoint is honest**: the remaining pair is the GAUGE decision `{x, x̄}` — segment states
   of a rigid core, a real (force-side) decision that is exactly the IR blind spot: 1-WL look-ahead cannot
   rank it (pins do not cascade — that is measurement 1), and the L = 3 holonomy key is structurally out on
   a 2-fold cover (no copy triangles ⟹ every `holSig` is the all-ones vector). In the C# this decision is
   the B1/B2 SOLVE; in Lean it is the F3b Smith/CRT gate — which stays gated on exactly this shape of
   witness becoming force-critical. Consume's half of the fold family is closed; the residue is attributed,
   not hidden.

## Deliberately NOT measured here

- `deckSupply` on `dmp72` (~72⁴ per propagation interpreted, tens of minutes): its content — generators of
  odd/any order — is orthogonal to this witness and measured on `wcyc27`/`vring18` (`PerformanceTest` §9).
- The joint F2+F3 measurement at multipede scale (a TWISTED triple multipede cover, `U ⊔ T` at `n = 216`):
  the spec-shaped `holKeyFast` cost (`n⁵` flat) is out of interpreted-eval range there; the theorems
  (`holKey_foldDeckFast_selNode_canonizer`) already cover the object, and the measurement is gated on a
  compiled-evaluation tranche, recorded in the plan §8.
-/

namespace ChainDescent.MultipedeWitness

open ChainDescent ChainDescent.Descend ChainDescent.Refine
open ChainDescent.Consume ChainDescent.Composite ChainDescent.Regression

/-- Segment–gadget incidence of the native-Z₂ multipede over the 6-circulant `{0,1,3}`. -/
def mpE (u v : Nat) : Bool :=
  let seg2gad (s g' : Nat) : Bool :=
    let g := g' - 12
    let li := g / 4
    let c := g % 4
    let t0 := c % 2
    let t1 := c / 2
    let t2 := (t0 + t1) % 2
    (s == (li % 6) * 2 + t0) || (s == ((li + 1) % 6) * 2 + t1) || (s == ((li + 3) % 6) * 2 + t2)
  (u < 12 && 12 ≤ v && v < 36 && seg2gad u v) || (v < 12 && 12 ≤ u && u < 36 && seg2gad v u)

def mp36 : AdjMatrix 36 := ⟨fun i j => if mpE i.val j.val then 1 else 0⟩

/-- Typed seed: segment position (the multipede's segments are individually typed); gadgets one class. -/
def mpTypes : Fin 36 → Nat := fun v => if v.val < 12 then v.val / 2 else 6

def mp36Root : Refine.ColData 36 := Refine.warmRefineVec mp36 mpTypes

/-! ### 1. The core: 1-WL-blind, exhaustively -/

/-! The least non-singleton cell is a segment state-pair — 1-WL cannot split any of them. -/
#guard (branches mp36Root.col).map Fin.val = [0, 1]

/-! **★ THE BLIND SPOT, MEASURED EXHAUSTIVELY**: individualizing ANY segment vertex leaves the
refinement non-discrete — no pin cascades. (This is what no `vfold`/`wcyc` witness could show: there,
pins discretize everything outside one tied class.) -/
#guard ((List.finRange 36).filter (fun v => v.val < 12)).all (fun v =>
  !decide (Discrete ((Consume.lookData mp36 mp36Root.col v).col)))

/-! ### 2. The matched double: matching supplies dead, the structural fold supply fires -/

/-- Two copies + the perfect matching `i ↔ 36 + i` (the C# `DoubleAndMatch` port). -/
def dmp72 : AdjMatrix 72 :=
  ⟨fun i j =>
    if i.val / 36 == j.val / 36 then (if mpE (i.val % 36) (j.val % 36) then 1 else 0)
    else if i.val % 36 == j.val % 36 then 1 else 0⟩

def dmpTypes : Fin 72 → Nat := fun v => if v.val % 36 < 12 then (v.val % 36) / 2 else 6

def dmp72Root : Refine.ColData 72 := Refine.warmRefineVec dmp72 dmpTypes

/-! The branch cell: segment 0's states × both copies. -/
#guard (branches dmp72Root.col).map Fin.val = [0, 1, 36, 37]

/-! **Refinement-based matching is DEAD** — `deepMatchSupply 0` constructs nothing; `partialMatchSupply 0`
verifies only the 4 diagonal identities. Neither narrows the 4-fan at all. (For larger `d` the deadness is
structural, not sampled: σ moves every vertex and `d` pins make ≤ `2d + 2` singletons — see the header.) -/
#guard (Consume.verified (DeepMatch.deepMatchSupply 0) dmp72 dmp72Root.col).length = 0
#guard (narrow (consume (DeepMatch.deepMatchSupply 0)) dmp72 dmp72Root.col).length = 4
#guard (narrow (consume (PartialMatch.partialMatchSupply 0)) dmp72 dmp72Root.col).length = 4

/-! **★ THE STRUCTURAL FOLD SUPPLY FIRES, REFINEMENT-FREE**: all 16 seed-pair candidates verify and the
copy direction is consumed — 4-fan → 2. The remaining pair is the rigid GAUGE decision (the IR blind spot,
force's job — see the header's honest-endpoint note). -/
#guard (Consume.verified (Fold.foldSupplyFast) dmp72 dmp72Root.col).length = 16
#guard (narrow (consume (Fold.foldSupplyFast)) dmp72 dmp72Root.col).length = 2

end ChainDescent.MultipedeWitness
