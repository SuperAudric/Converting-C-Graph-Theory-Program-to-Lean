import ChainDescent.SelectNode
import ChainDescent.Regression

/-!
# The sel-rewrite EXPOSURE WITNESS — `Z4S` (OFF the build path; run on demand)

`lake build ChainDescent.SelectWitness` (~3 min of `#guard` eval at `n = 14` — deliberately not in
`scripts/build.sh`, exactly like `PerformanceTest`).

## The graph

`Z4S` — the **Z₄ chiral subdivided wheel**: a C₈ ring `r₁…r₈` whose FORWARD arcs are subdivided (`s₁…s₄` — the
chirality, WL-visibly: reflections would map subdivided forward arcs onto unsubdivided backward arcs), plus two
apexes `a, b` on alternating odd spokes. `Aut(Z4S) = Z₄ = ⟨γ⟩` with `γ = (a b)(r₁r₃r₅r₇)(r₂r₄r₆r₈)(s₁s₂s₃s₄)`.
Root cells: `{a, b}` (the LEAST cell — a 2-orbit: `γ²` fixes both) and the ring/subdivision cells (4-orbits).

## The mechanism, and the four measured quadrants

Pinning an apex leaves `γ²` alive ⟹ the refinement does NOT discretize ⟹ the least-rooted harvest
(`matchSupply`, pins of `{a, b}` only) constructs NOTHING — and force is `γ`-tied on every cell. Pinning a ring
or subdivision vertex kills all of `γ` ⟹ discretizes ⟹ the ALL-CELLS harvest (`Select.allCellsMatchSupply`)
reconstructs and verifies `γ`. The 4-orbit cells are then single verified orbits (consume collapses them) while
the least `{a, b}` cell resolves only after a ring pin breaks the symmetry.

| object | supply | result |
|---|---|---|
| guarded blind | `matchSupply` (least-rooted) | **flags** |
| fused `selNode` | `matchSupply` (least-rooted) | **flags** |
| guarded blind | `allCellsMatchSupply` | answers |
| fused `selNode` | `allCellsMatchSupply` | **answers** |

**What this witnesses:** the fused canonizer in its intended configuration (resolver-aware selector + all-cells
harvest, handoff §6.1 items) ANSWERS where the prior object of record (guarded blind + least-rooted harvest)
FLAGS — the exposure-dependency the sel rewrite was built for. **Attribution (row 3 is deliberate):** at `d = 0`
on THIS graph the all-cells harvest alone already suffices (the blind object's least cell is a single `γ`-orbit
once `γ` is verified). A SELECTOR-strict witness — same supply on both rows, blind flags, fused answers — needs
the least cell to hold ≥ 2 verified orbits (or a key-tied non-orbit) while another cell resolves; the 2026-07-17
search (handoff §6.1 build-state) found every small candidate collapses: with `Aut = Z₂ᵏ` products a single pin
never discretizes (both objects flag); with pin-discretizing least cells `matchCol` or the leaf-branch key fires
(both answer). The candidate that separates lives where 1-WL is weak at scale (SRG-land) — carried as an open
item, NOT assumed.

## ⚠ Trap #1, measured in the wild (why `canonFormFastS?` exists)

The first fused runs HUNG (> 9 min at `n = 14`): `selNode`'s generic `refineV rf …` children compile as partial
applications whose body re-runs the refinement on EVERY colour lookup — measured **≈ 30 ms per lookup** (2000
lookups ≈ 60 s), and the fused probe does ≈ `n²` lookups per node. `selNodeFast`/`canonFormFastS?` (definitional
`rfl`-twins) hand `Refine.ColData`-materialised colourings: the same descent now runs in ≈ 10 s.
-/

namespace ChainDescent.SelectWitness

open ChainDescent ChainDescent.Descend ChainDescent.Refine ChainDescent.Select
open ChainDescent.Force ChainDescent.Consume ChainDescent.Composite ChainDescent.Stall

/-! The Z₄ chiral subdivided wheel: apexes `a = 0`, `b = 1`; ring `r₁…r₈ = 2…9`; subdivisions `s₁…s₄ = 10…13`
on the forward arcs `r₁r₂, r₃r₄, r₅r₆, r₇r₈`. -/
def Z4S : AdjMatrix 14 := ⟨fun i j =>
  let e : List (Nat × Nat) :=
    [(2,10),(10,3),(4,11),(11,5),(6,12),(12,7),(8,13),(13,9),   -- subdivided forward arcs
     (3,4),(5,6),(7,8),(9,2),                                    -- direct backward arcs
     (0,2),(0,6),(1,4),(1,8)]                                    -- apex spokes on the odd ring
  if e.contains (i.val, j.val) ∨ e.contains (j.val, i.val) then 1 else 0⟩

def rootZ : Refine.ColData 14 := Refine.warmRefineVec Z4S (fun _ => 0)

/-! ### The structural pins of the mechanism -/

/-! The least cell is the apex 2-orbit. -/
#guard branches rootZ.col = [0, 1]

/-! Pinning an apex does NOT discretize (`γ²` survives) — the least-rooted harvest is empty. -/
#guard ¬ Discrete ((Consume.lookData Z4S rootZ.col 0).col)

/-! Pinning a subdivision vertex DOES discretize (trivial stabiliser) — the all-cells harvest fires. -/
#guard Discrete ((Consume.lookData Z4S rootZ.col 10).col)

/-! ### The four quadrants -/

/-! Guarded blind object, least-rooted harvest: **flags**. -/
#guard ¬ (canonForm? encodeFreeFast (guard (forceThenConsume lookaheadKey matchSupply)) Z4S).isSome

/-! Fused object, least-rooted harvest: **flags** (the selector alone cannot conjure candidates). -/
#guard ¬ (canonFormFastS? lookaheadKey matchSupply Z4S).isSome

/-! Guarded blind object, all-cells harvest: answers (the attribution row — see the header). -/
#guard (canonForm? encodeFreeFast
  (guard (forceThenConsume lookaheadKey allCellsMatchSupply)) Z4S).isSome

/-! **★ THE WITNESS ROW — the fused object of record ANSWERS where the prior record FLAGS.** -/
#guard (canonFormFastS? lookaheadKey allCellsMatchSupply Z4S).isSome

/-! ### `①c`, behavioural, for the fused object on the witness graph -/

#guard canonFormFastS? lookaheadKey allCellsMatchSupply Z4S
  = canonFormFastS? lookaheadKey allCellsMatchSupply (relabelAdj (Equiv.swap 3 9) Z4S)

end ChainDescent.SelectWitness
