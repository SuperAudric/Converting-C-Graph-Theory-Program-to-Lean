import ChainDescent.DeepMatchSupply
import ChainDescent.SealBridge

/-!
# `P2b` — THE DEPTH BRIDGE: a bounded-base discreteness hypothesis fires the deep oracle

## Why this file exists

`P0` (`SealBridge.lean`) bridged the seal's **localisation** — `CellsAreOrbits adj P D ⟹ horb`, the hypothesis
`Consume.cellIsOrbit_matchSupply` (and `DeepMatch.cellIsOrbit_deepMatchSupply`) take. It did **not** bridge the
seal's **depth**: `DeepMatch.cellIsOrbit_deepMatchSupply` *also* needs `DeepMatch.SeparatesAt adj χ d`, and until now
**no theorem produced `SeparatesAt` from anything** — it could only be `#guard`ed on concrete cycles. So the sealed
families (`theorem_1_HOR_*`, the four form families, `viaSpielman`), whose whole content is a bounded-depth
discreteness statement (`CascadesAt` / `SeparatesAtBoundedBase`), could not populate `Residue.Handled`.

This file closes the descent-side half of that gap. The seal's depth hypothesis says *some bounded set discretizes*;
the descent's `SeparatesAt` asks *for each branch vertex, some bounded sequence discretizes*. The bridge is a single
monotonicity fact:

> **Individualizing MORE only refines further, and refining a discrete colouring keeps it discrete.**

So a bounded set `S₀` that discretizes from `χ` also discretizes after *prepending any branch vertex `v`* (that only
individualizes a superset), and `S₀.toList` is a witness sequence of length `≤ |S₀|` for **every** `v`. Hence

> **`CascadesFrom adj χ k ⟹ SeparatesAt adj χ k`** (`separatesAt_of_cascadesFrom`),

and combined with localisation (`horb`, imported from the seal by `SealBridge.horb_of_cellsAreOrbits`) the deep
oracle **fires** at that node (`cellIsOrbit_of_cascadesFrom_of_horb`). That is the depth analogue of P0's
`cellIsOrbit_of_cellsAreOrbits`.

## `P2c` — connecting `CascadesFrom` to the seal's `CascadesAt` (§4)

`CascadesFrom` is stated in the **descent's** vocabulary (`deepCol`); the seal produces `CascadesAt` /
`SeparatesAtBoundedBase` in `warmRefine adj (constP n) (individualizedColouring n S₀)`. The connection turned out to
be a single **exact equality**, not a partition argument:

> **`deepCol adj (pathCol adj p) s = pathCol adj (s.reverse ++ p)`** (`deepCol_pathCol`)

— deepening the descent's node colouring `SealBridge.pathCol adj p` along `s` is *literally* the colouring at the
longer committed path, because `pathCol adj (v :: p)` is definitionally `warmRefineR adj (indivOne (pathCol adj p) v)`
= exactly `deepCol`'s step. `SealBridge.pathCol_samePartition` then reads the partition off as `warmRefine ∘
individualizedColouring`, and a seal witness `S₀` that discretizes it discretizes the superset `S₀ ∪ p.toFinset` too
(monotonicity). So the seal's depth hypothesis fires the deep oracle at **every** descent node from one global set:
`cascadesFrom_pathCol_of_cascadesAt`, and the packaged `cellIsOrbit_pathCol_of_seal` (depth **and** localisation, both
imported from the seal). Note `Refine.constP n` *is* `fun _ _ => POE.unknown` — the seal's own PMatrix — so no PMatrix
translation is needed.
-/

namespace ChainDescent
namespace SealDepthBridge

open ChainDescent.Descend
open ChainDescent.Consume (IsColAut CellIsOrbit)
open ChainDescent.DeepMatch (deepCol SeparatesAt deepMatchSupply)

variable {n : Nat}

/-! ## 1. Descent-side monotonicity of the deep colouring

`Refines χ₁ χ₂` means `χ₁` is **finer** (its partition separates at least as much). We need three facts about the
descent's own refiner `warmRefineR` and its iterate `deepCol`. -/

/-- Refinement is transitive. -/
theorem refines_trans {χ₁ χ₂ χ₃ : Colouring n} (h₁ : Refines χ₁ χ₂) (h₂ : Refines χ₂ χ₃) :
    Refines χ₁ χ₃ := fun a b hab => h₂ a b (h₁ a b hab)

/-- **A finer colouring of a discrete one is discrete.** (`Discrete χ := χ` injective; `Refines` only ever splits.) -/
theorem discrete_of_refines {χ₁ χ₂ : Colouring n} (h : Refines χ₁ χ₂) (hd : Discrete χ₂) :
    Discrete χ₁ := fun i j hij => hd i j (h i j hij)

/-- The encode-free warm round **refines its input** (`iterate_splits`: it never merges a colour class). -/
theorem warmRefineR_refines (adj : AdjMatrix n) (χ : Colouring n) :
    Refines (Refine.warmRefineR adj χ) χ :=
  fun x y h => Refine.iterate_splits adj n χ x y h

/-- The encode-free warm round is **monotone**: a finer input gives a finer output. Transferred from the stock
`warmRefine adj (constP n)` (where `warmRefine_refines_initial` supplies monotonicity) through
`SealBridge.warmRefineR_samePartition`, since both refiners induce the same partition. -/
theorem warmRefineR_mono (adj : AdjMatrix n) {χ₁ χ₂ : Colouring n} (h : Refines χ₁ χ₂) :
    Refines (Refine.warmRefineR adj χ₁) (Refine.warmRefineR adj χ₂) := by
  have s1 := SealBridge.warmRefineR_samePartition adj χ₁
  have s2 := SealBridge.warmRefineR_samePartition adj χ₂
  have hw : Refines (warmRefine adj (Refine.constP n) χ₁) (warmRefine adj (Refine.constP n) χ₂) :=
    warmRefine_refines_initial h
  intro a b hab
  exact (s2 a b).mpr (hw a b ((s1 a b).mp hab))

/-- **`deepCol` is monotone in its starting colouring** — refining the input refines every deepened colouring. -/
theorem deepCol_mono (adj : AdjMatrix n) :
    ∀ (s : List (Fin n)) {χ₁ χ₂ : Colouring n}, Refines χ₁ χ₂ →
      Refines (deepCol adj χ₁ s) (deepCol adj χ₂ s)
  | [], _, _, h => h
  | v :: s, χ₁, χ₂, h => by
      show Refines (deepCol adj (Refine.warmRefineR adj (indivOne χ₁ v)) s)
                   (deepCol adj (Refine.warmRefineR adj (indivOne χ₂ v)) s)
      exact deepCol_mono adj s (warmRefineR_mono adj (SealBridge.indivOne_mono h v))

/-- **★ PREPENDING A VERTEX ONLY REFINES.** Individualizing `v` first (the branch step) gives a starting colouring
finer than `χ`, and `deepCol` is monotone, so `deepCol adj χ (v :: s)` refines `deepCol adj χ s`. This is the whole
bridge: an `s` that discretizes from `χ` still discretizes after the branch vertex is pinned. -/
theorem deepCol_cons_refines (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) (s : List (Fin n)) :
    Refines (deepCol adj χ (v :: s)) (deepCol adj χ s) := by
  have hstart : Refines (Refine.warmRefineR adj (indivOne χ v)) χ :=
    refines_trans (warmRefineR_refines adj _) (SealBridge.indivOne_refines χ v)
  exact deepCol_mono adj s hstart

/-! ## 2. The depth hypothesis, in the descent's vocabulary, and the bridge -/

/-- **The seal's depth content, restated on the descent's `deepCol`.** Some set `S₀` of size `≤ k` discretizes when
individualized (with refinement) on top of `χ`. This is `SeparatesAtBoundedBase` / `OrbitRecovery.CascadesAt`
translated into the descent's own step; connecting the two objects at the partition level is the follow-on `P2c`. -/
def CascadesFrom (adj : AdjMatrix n) (χ : Colouring n) (k : Nat) : Prop :=
  ∃ S₀ : Finset (Fin n), S₀.card ≤ k ∧ Discrete (deepCol adj χ S₀.toList)

/-- **★★★ THE DEPTH BRIDGE.** A bounded-base discreteness hypothesis at a node produces the deep oracle's firing
hypothesis `SeparatesAt` there — with the **same bound `k`**. The witness sequence for *every* branch vertex is the
one set `S₀.toList`: prepending the branch vertex only refines (`deepCol_cons_refines`), and a finer colouring of a
discrete one is discrete. -/
theorem separatesAt_of_cascadesFrom (adj : AdjMatrix n) (χ : Colouring n) (k : Nat)
    (h : CascadesFrom adj χ k) : SeparatesAt adj χ k := by
  obtain ⟨S₀, hcard, hdisc⟩ := h
  intro v _
  refine ⟨S₀.toList, ?_, ?_⟩
  · rw [Finset.length_toList]; exact hcard
  · exact discrete_of_refines (deepCol_cons_refines adj χ v S₀.toList) hdisc

/-! ## 3. Firing — depth (this file) + localisation (P0) ⟹ the deep oracle fires -/

/-- **★★★ THE DEPTH ANALOGUE OF `SealBridge.cellIsOrbit_of_cellsAreOrbits`.** Given the seal's **depth** hypothesis
(`CascadesFrom`, ≡ `CascadesAt` / `SeparatesAtBoundedBase` in descent vocabulary) and its **localisation**
hypothesis (`horb`, which `SealBridge.horb_of_cellsAreOrbits` imports straight from `CellsAreOrbits`), the
bounded-depth oracle `deepMatchSupply k` certifies the branch cell as an orbit at this node — so `consume` collapses
it to one branch. This is exactly the firing the sealed families supply, per node. -/
theorem cellIsOrbit_of_cascadesFrom_of_horb (adj : AdjMatrix n) (χ : Colouring n) (k : Nat)
    (hcasc : CascadesFrom adj χ k)
    (horb : ∀ u ∈ branches χ, ∀ w ∈ branches χ,
      ∃ α : Equiv.Perm (Fin n), IsColAut adj χ α ∧ α u = w) :
    CellIsOrbit (deepMatchSupply (n := n) k) adj χ :=
  DeepMatch.cellIsOrbit_deepMatchSupply (separatesAt_of_cascadesFrom adj χ k hcasc) horb

/-! ## 4. `P2c` — the seal's `CascadesAt` IS `CascadesFrom` at a descent node -/

/-- **★ DEEPENING A DESCENT NODE = COMMITTING THE LONGER PATH.** `deepCol` from the descent's node colouring
`SealBridge.pathCol adj p` along `s` is *literally* the colouring at the longer committed path `s.reverse ++ p` —
an **exact** equality, because `pathCol adj (v :: p)` is definitionally `warmRefineR adj (indivOne (pathCol adj p) v)`,
which is exactly `deepCol`'s step. This one identity is the whole `P2c` vocabulary bridge. -/
theorem deepCol_pathCol (adj : AdjMatrix n) :
    ∀ (s p : List (Fin n)),
      deepCol adj (SealBridge.pathCol adj p) s = SealBridge.pathCol adj (s.reverse ++ p)
  | [], p => rfl
  | v :: s, p => by
      calc deepCol adj (SealBridge.pathCol adj p) (v :: s)
          = deepCol adj (SealBridge.pathCol adj (v :: p)) s := rfl
        _ = SealBridge.pathCol adj (s.reverse ++ (v :: p)) := deepCol_pathCol adj s (v :: p)
        _ = SealBridge.pathCol adj ((v :: s).reverse ++ p) := by
              rw [List.reverse_cons, List.append_assoc]; rfl

/-- **★★★ THE SEAL'S DEPTH HYPOTHESIS, AT A DESCENT NODE.** The seal's `CascadesAt adj (constP n) k` — a **global**
bounded-base discreteness witness — produces the descent-side `CascadesFrom` at **every** committed path `p`, from
the *same* set `S₀`: deepening reaches the longer path (`deepCol_pathCol`), whose partition is
`warmRefine ∘ individualizedColouring` (`SealBridge.pathCol_samePartition`), and a superset individualization stays
discrete. -/
theorem cascadesFrom_pathCol_of_cascadesAt {adj : AdjMatrix n} {k : Nat} (p : List (Fin n))
    (h : CascadesAt adj (Refine.constP n) k) :
    CascadesFrom adj (SealBridge.pathCol adj p) k := by
  obtain ⟨S₀, hcard, hdisc⟩ := h
  refine ⟨S₀, hcard, ?_⟩
  rw [deepCol_pathCol]
  set q := S₀.toList.reverse ++ p with hq
  have hqf : q.toFinset = S₀ ∪ p.toFinset := by
    rw [hq, List.toFinset_append, List.toFinset_reverse, Finset.toList_toFinset]
  have hsub : S₀ ⊆ q.toFinset := by rw [hqf]; exact Finset.subset_union_left
  refine Discrete.of_samePartition (SealBridge.pathCol_samePartition adj q).symm ?_
  exact discrete_of_refines
    (warmRefine_refines_initial (individualizedColouring_refines hsub)) hdisc

/-- **★★★ THE FULL SEAL → DEEP FIRING BRIDGE.** Depth (`CascadesAt`) **and** localisation (`CellsAreOrbits`) — the two
hypotheses the sealed families (`theorem_1_HOR_*`, the four form families, `viaSpielman`) discharge — together fire
the bounded-depth oracle `deepMatchSupply k` at the descent node `pathCol adj p`, so `consume` collapses the branch
cell to one branch. Both halves are now **imports** from the seal: this is the depth+localisation completion of P0's
`cellIsOrbit_of_cellsAreOrbits`, which had only the localisation half. -/
theorem cellIsOrbit_pathCol_of_seal {adj : AdjMatrix n} {k : Nat} (p : List (Fin n))
    (hdepth : CascadesAt adj (Refine.constP n) k)
    (hco : CellsAreOrbits adj (Refine.constP n) p.toFinset) :
    CellIsOrbit (deepMatchSupply (n := n) k) adj (SealBridge.pathCol adj p) := by
  refine cellIsOrbit_of_cascadesFrom_of_horb adj (SealBridge.pathCol adj p) k
    (cascadesFrom_pathCol_of_cascadesAt p hdepth) (fun u hu w hw => ?_)
  obtain ⟨c, hc, huc⟩ := Consume.exists_targetColour_of_mem hu
  have hwc : SealBridge.pathCol adj p w = c := (mem_branches_iff hc w).mp hw
  exact SealBridge.horb_of_cellsAreOrbits hco (by rw [huc, hwc])

/-! ## 5. The `viaSpielman` POC import — the seal's *sub-exponential* rung, literally imported

Proof of concept, not the workhorse. `SeparatesAtBoundedBase S bound` is **definitionally**
`CascadesAt (schemeAdj S) (constP n) bound` — the same `∃ S₀, S₀.card ≤ bound ∧ Discrete (warmRefine …
(individualizedColouring n S₀))`, since `Refine.constP n` *is* `fun _ _ => POE.unknown`, the seal's own PMatrix. So
§4 applies at `adj := schemeAdj S` with **no translation layer**, and the whole ladder — including its
sub-exponential top — feeds the descent's supply.

⚠ **Scope, twice over.** (i) Spielman's `bound = Õ(n^{1/3})` is citable for **claw-bounded** primitive SRGs only;
the Neumaier-exceptional Steiner / Latin-square families have base `Θ(√n)` and exit via Cameron (see `Cascade`'s
`viaSpielman` docstring and the citation register). (ii) This fires on the scheme's **own** adjacency
`schemeAdj S`, not yet on an arbitrary graph *realizing* `S` — that hop is `RouteCTransport`, deliberately out of
scope here. The **poly** rungs (`theorem_1_HOR_*`) are what the real construction is built from; this rung exists
to show the import is generic in the bound. -/

/-- The seal's engine interface **is** the descent's depth hypothesis, on the scheme's own adjacency. -/
theorem cascadesAt_of_separatesAtBoundedBase {m : Nat} (S : SchurianScheme m) (bound : Nat)
    (h : SeparatesAtBoundedBase S bound) :
    CascadesAt (schemeAdj S.toAssociationScheme) (Refine.constP m) bound := h

/-- **★★ THE POC.** A scheme separating at a bounded base fires the bounded-depth oracle at every committed path
of the descent on its own adjacency — given localisation there. Depth is the pure import; localisation is the
seal's standing per-family obligation, carried here as a hypothesis exactly as everywhere else. -/
theorem cellIsOrbit_pathCol_of_spielman {m : Nat} (S : SchurianScheme m) (bound : Nat)
    (p : List (Fin m)) (hsep : SeparatesAtBoundedBase S bound)
    (hco : CellsAreOrbits (schemeAdj S.toAssociationScheme) (Refine.constP m) p.toFinset) :
    CellIsOrbit (deepMatchSupply (n := m) bound)
      (schemeAdj S.toAssociationScheme)
      (SealBridge.pathCol (schemeAdj S.toAssociationScheme) p) :=
  cellIsOrbit_pathCol_of_seal p (cascadesAt_of_separatesAtBoundedBase S bound hsep) hco

end SealDepthBridge
end ChainDescent
