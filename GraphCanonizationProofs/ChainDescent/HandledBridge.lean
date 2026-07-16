import ChainDescent.SealDepthBridge
import ChainDescent.PrunedSupply
import ChainDescent.SupplyTransport

/-!
# THE `Handled` POPULATION BRIDGE — the seal's structural hypotheses discharge `③`'s capability predicate

## Why this file exists

`Residue.Handled` is the project's boundary object: the **positive capability predicate** whose complement is the
residue, the mixed-canonizer analogue of the seal's `reachesRigidOrCameron`. Until this file it had **zero theorem
instances**: the original definition quantified over *all* colourings, while the seal corpus speaks only about
**committed individualization paths** (`SealBridge.pathCol`) — and `CellsAreOrbits` genuinely fails at colourings
the descent never visits, so no structural hypothesis could ever discharge it. The 2026-07-16 correction re-based
`Handled` on `Descend.Reaches` (the descent's own reachable node colourings); this file supplies the two missing
connections and the first population theorems:

1. **`reaches_pathCol`** — every reachable node colouring of the concrete (encode-free) canonizer **is** a
   `pathCol`. This is the reachable-node induction that `SealBridge` had only asserted in prose; it is one
   structural induction, because `pathCol`'s two equations are *definitionally* the descent's root and branch
   steps (`Refine.refineV_encodeFreeFast`).
2. **`handled_of_seal`** — the population capstone: **depth** (`CascadesAt adj (constP n) k`, exactly what
   `theorem_1_HOR_*` / the sealed families / `viaSpielman` produce at their respective bounds) **and**
   **localisation at every committed set** (`∀ T, CellsAreOrbits adj (constP n) T`) together put the graph in
   `Residue.Handled key (deepMatchSupply k)` — for **every** key. Consume alone suffices; force can only enlarge
   the handled set further.
3. **`handled_of_seal_pruned`** — the same boundary for the **cheap** supply, transferred through
   `OrbitPrune.SameOrbits` with no new proof (`P3a` doing its job).
4. **`seal_graph_answers`** — the showcase corollary: such a graph is canonized by the guarded mixed canonizer —
   sound, iso-invariant, complete (`SupplyTransport.deep`/`prunedSupply` capstones), **single-path** (`Stall`),
   and it **answers**.

## How to read the two hypotheses (the honest boundary)

* **Depth** is a solved import at bounded `k`: `theorem_1_HOR_cfi_oddDeg` gives `CascadesAt` at `k ≤ tw`,
  `viaSpielman`'s `SeparatesAtBoundedBase` *is* `CascadesAt (schemeAdj S)` at `Õ(n^{1/3})` (claw-bounded scope).
* **Localisation at every committed set** is the seal's own open per-family obligation (the handoff's "seal
  hypotheses hold at every reachable node"), now pinned to a single named hypothesis instead of being folded
  invisibly into an undischargeable `∀ χ`. A family instance = a proof of `∀ T, CellsAreOrbits` for that family;
  each one extends the boundary with **no re-proof** of anything here — exactly the iteratively-improvable shape
  `reachesRigidOrCameron` had.

§4 instantiates the boundary concretely: the **edgeless graphs** (every `n`) are `Handled` — and at `n = 2` that
is the *same graph* `Residue.residue_nonvacuous` shows residual for the certify-nothing resolvers, so both halves
of the endgame's non-vacuity obligation are now **theorems about one graph**, differing only in resolver strength.
(The innermost ring — 1-WL-rigid graphs, `Residue.handled_of_root_discrete` — needs neither seal hypothesis; a
concrete kernel-`decide` instance is blocked by `Multiset.sort`'s well-founded recursion, which the kernel cannot
reduce, so runtime evidence for that ring stays in `Regression.lean`'s `#guard`s.)
-/

namespace ChainDescent
namespace HandledBridge

open ChainDescent.Descend
open ChainDescent.Consume (Supply)
open ChainDescent.Force (Key)
open ChainDescent.DeepMatch (deepMatchSupply)
open ChainDescent.Composite (forceThenConsume)
open ChainDescent.Stall (guard)

variable {n : Nat}

/-! ## 1. The reachable-node induction: every reached colouring is a committed path's colouring -/

/-- **★★ EVERY REACHABLE NODE IS A `pathCol` NODE.** The concrete canonizer's reachable colourings are exactly
the committed-path colourings the seal corpus speaks about: the root is `pathCol adj []` and the branch step is
`pathCol`'s cons equation, both definitionally (`Refine.refineV_encodeFreeFast`). This is the induction
`SealBridge`'s prose ("`pathCol` is exactly the colouring `descend` carries") appealed to; now it is a theorem. -/
theorem reaches_pathCol {adj : AdjMatrix n} {χ : Colouring n}
    (h : Reaches (Refine.encodeFreeFast (n := n)) adj χ) :
    ∃ p : List (Fin n), χ = SealBridge.pathCol adj p := by
  induction h with
  | root => exact ⟨[], by rw [Refine.refineV_encodeFreeFast]; rfl⟩
  | @step χ' v _ _ _ ih =>
      obtain ⟨p, rfl⟩ := ih
      exact ⟨v :: p, by rw [Refine.refineV_encodeFreeFast]; rfl⟩

/-! ## 2. ★★★ THE POPULATION CAPSTONE — the seal's two structural hypotheses discharge `Handled` -/

/-- **★★★ `handled_of_seal` — THE FIRST STRUCTURAL DISCHARGE OF `Residue.Handled`.** A graph with the seal's
**depth** content (`CascadesAt` at bound `k` — what `theorem_1_HOR_*` / the sealed families produce) and its
**localisation** content at every committed set (`∀ T, CellsAreOrbits` — the seal's open per-family obligation,
carried honestly) is handled by the bounded-depth oracle `deepMatchSupply k`, for **every** key: at each reachable
node the branch cell is a certified orbit (`SealDepthBridge.cellIsOrbit_pathCol_of_seal`), so consume alone
resolves it. A stronger key can only enlarge `Handled` further. -/
theorem handled_of_seal {adj : AdjMatrix n} {k : Nat} (key : Key n)
    (hdepth : CascadesAt adj (Refine.constP n) k)
    (hloc : ∀ T : Finset (Fin n), CellsAreOrbits adj (Refine.constP n) T) :
    Residue.Handled key (deepMatchSupply (n := n) k) adj := by
  intro χ hr _hd
  obtain ⟨p, rfl⟩ := reaches_pathCol hr
  exact Or.inl (SealDepthBridge.cellIsOrbit_pathCol_of_seal p hdepth (hloc p.toFinset))

/-- The same boundary for the **cheap** reference-matching supply — transferred through `SameOrbits`, no new
proof (`P3a`'s reduction doing its job: the pruned supply proves the same orbits, so it handles the same graphs). -/
theorem handled_of_seal_pruned {adj : AdjMatrix n} {k : Nat} (key : Key n)
    (hdepth : CascadesAt adj (Refine.constP n) k)
    (hloc : ∀ T : Finset (Fin n), CellsAreOrbits adj (Refine.constP n) T) :
    Residue.Handled key (PrunedSupply.prunedSupply (n := n) k) adj :=
  OrbitPrune.handled_congr (PrunedSupply.sameOrbits_deepMatchSupply k)
    (handled_of_seal key hdepth hloc)

/-! ## 3. The showcase corollary — such a graph is CANONIZED -/

/-- **★★ A seal-covered graph ANSWERS** under the guarded mixed canonizer with the deep oracle — which is sound,
iso-invariant and complete (`SupplyTransport.deepMatchSupply_guarded_canonizer`) and a single path of `≤ n+1`
nodes (`Stall.resolvedAll_guard`) on every input. So on this class: **canonical form, poly node count, no flag.** -/
theorem seal_graph_answers {adj : AdjMatrix n} {k : Nat} (key : Key n)
    (hdepth : CascadesAt adj (Refine.constP n) k)
    (hloc : ∀ T : Finset (Fin n), CellsAreOrbits adj (Refine.constP n) T) :
    Descend.canonForm? (Refine.encodeFreeFast (n := n))
      (guard (forceThenConsume key (deepMatchSupply (n := n) k))) adj ≠ none :=
  Residue.answers_of_handled (handled_of_seal key hdepth hloc)

/-- …and with the cheap pruned supply. -/
theorem seal_graph_answers_pruned {adj : AdjMatrix n} {k : Nat} (key : Key n)
    (hdepth : CascadesAt adj (Refine.constP n) k)
    (hloc : ∀ T : Finset (Fin n), CellsAreOrbits adj (Refine.constP n) T) :
    Descend.canonForm? (Refine.encodeFreeFast (n := n))
      (guard (forceThenConsume key (PrunedSupply.prunedSupply (n := n) k))) adj ≠ none :=
  Residue.answers_of_handled (handled_of_seal_pruned key hdepth hloc)

/-! ## 4. A concrete HANDLED family — and the residue SHRINKS, at theorem level

`Residue.residue_nonvacuous` inhabits the residue (the empty two-vertex graph defeats the **empty** supply);
this section proves the **same graph** — indeed every edgeless graph, at every `n` — is `Handled` once the
supply is the real deep oracle. That is the whole architecture's story as a pair of theorems: the residue is
inhabited, and it shrinks when the resolver strengthens, with no re-proof of `①`/`②` anywhere. It also closes
the **handled half** of the endgame's `unhandledResidue_nonvacuous` obligation (the load-bearing half). -/

/-- The edgeless graph on `n` vertices. Vertex-transitive, so 1-WL alone never finishes it (`n ≥ 2`) — the
supply genuinely fires at every reached node; this is *not* a vacuously-handled instance. -/
def emptyAdj (n : Nat) : AdjMatrix n := ⟨fun _ _ => 0⟩

/-- **Localisation holds at every committed set on the edgeless graph**: every permutation is an automorphism,
so two same-cell vertices are swapped by a transposition — which fixes the committed set pointwise, because a
same-cell pair is never committed (same `warmRefine` colour ⟹ same individualized colour, `warmRefine_refines`,
and committed vertices carry unique non-zero colours). -/
theorem cellsAreOrbits_emptyAdj (n : Nat) (T : Finset (Fin n)) :
    CellsAreOrbits (emptyAdj n) (Refine.constP n) T := by
  intro v w hcell
  by_cases hvw : v = w
  · exact hvw ▸ OrbitPartition.refl v
  · have hinit : individualizedColouring n T v = individualizedColouring n T w :=
      warmRefine_refines _ _ _ hcell
    have hvT : v ∉ T := fun hv => by
      by_cases hw : w ∈ T
      · exact hvw (Fin.ext (by simpa [individualizedColouring, hv, hw] using hinit))
      · simp [individualizedColouring, hv, hw] at hinit
    have hwT : w ∉ T := fun hw => by
      by_cases hv : v ∈ T
      · exact hvw (Fin.ext (by simpa [individualizedColouring, hv, hw] using hinit))
      · simp [individualizedColouring, hv, hw] at hinit
    refine ⟨Equiv.swap v w, fun _ _ => rfl, fun _ _ => rfl, ?_, Equiv.swap_apply_left v w⟩
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hvT (h ▸ hx)) (fun h => hwT (h ▸ hx))

/-- **★★ A CONCRETE HANDLED FAMILY, for every `n` and every key:** the edgeless graphs, handled by the deep
oracle at the trivial depth bound `k = n` (`cascadesAt_univ`). The first inhabited instance of
`Residue.Handled` — the boundary predicate is populated. -/
theorem handled_emptyAdj (n : Nat) (key : Key n) :
    Residue.Handled key (deepMatchSupply (n := n) n) (emptyAdj n) :=
  handled_of_seal key (cascadesAt_univ (emptyAdj n) (Refine.constP n)) (cellsAreOrbits_emptyAdj n)

/-- **★ THE RESIDUE SHRINKS, AT THEOREM LEVEL.** The very graph `Residue.residue_nonvacuous` shows residual
for the certify-nothing resolvers is handled by the deep oracle — the non-vacuity pair is about ONE graph, and
the difference is purely resolver strength. -/
theorem adjE2_handled (key : Key 2) :
    Residue.Handled key (DeepMatch.deepMatchSupply (n := 2) 2) Residue.adjE2 :=
  handled_emptyAdj 2 key

/-- …and it therefore **answers** under the guarded mixed canonizer (which is also sound, iso-invariant,
complete, and a single path — the standing capstones). -/
theorem adjE2_answers (key : Key 2) :
    Descend.canonForm? (Refine.encodeFreeFast (n := 2))
      (guard (forceThenConsume key (DeepMatch.deepMatchSupply (n := 2) 2))) Residue.adjE2
      ≠ none :=
  Residue.answers_of_handled (adjE2_handled key)

end HandledBridge
end ChainDescent
