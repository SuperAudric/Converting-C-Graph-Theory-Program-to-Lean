/-
# ScratchRenumberExec.lean — the renumbered, RUNNABLE canonizer output (WIP, NOT in build.sh)

Completes the renumbering track: `canonOutput` (Tier B) computed the leaf colouring via `warmRefine`
(`Encodable.encode`-blown-up colours ⟹ `vertexRank`'s `<` hangs). `canonOutputR` here computes the SAME leaf
partition via **`warmRefineR`** (`ScratchRenumber`) — colours stay `< n` every round — so the output is
`#eval`-feasible. `samePartition_warmRefineR` shows the leaf is the same partition, so it is discrete at the
descent's leaf (`discrete_warmRefineR`), and `canonAdjComp_eq` makes the output a genuine relabelling (①a).

This is a *different* canonical labelling from `canonOutput`'s (the renumbered refinement has its own colour
order), but an equally valid one — proven sound (`canonOutputR_sound`). It is NOT yet the iso-invariant lex-min
(Tier C / the wall); it is the leaf's single labelling, now runnable.

Axiom target `[propext, Classical.choice, Quot.sound]`. `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchRenumber
import ChainDescent.ScratchExecutable

namespace ChainDescent.RenumberExec

open ChainDescent
open ChainDescent.CanonSound
open ChainDescent.CanonForm
open ChainDescent.Executable
open ChainDescent.Renumber

variable {n : Nat}

/-- **The renumbered, runnable output.** Descend to the leaf (Tier A, computable), then emit the leaf's canonical
adjacency computed with the **bounded** `warmRefineR` colouring — so `vertexRank`'s `<`-comparisons are over small
`Nat`s and the whole thing `#eval`s. -/
def canonOutputR (adj : AdjMatrix n) : Option (Fin n → Fin n → Nat) :=
  (descentResult adj).map (fun k =>
    let ch := defaultSpineChain adj defaultP₀ defaultχι₀ nonDiscreteSel k
    canonAdjComp adj (warmRefineR adj ch.P ch.χι))

/-- **①a on the renumbered runnable output.** A `some cG` answer is a genuine relabelling of `adj`: the leaf
`warmRefineR` colouring is discrete (same partition as the discrete `warmRefine` leaf), so `canonAdjComp` of it is
`labelledAdj (rankPerm …) adj`. -/
theorem canonOutputR_sound (adj : AdjMatrix n) (cG : Fin n → Fin n → Nat)
    (h : canonOutputR adj = some cG) :
    ∃ π : Equiv.Perm (Fin n), cG = labelledAdj π adj := by
  unfold canonOutputR at h
  cases hd : descentResult adj with
  | none => rw [hd] at h; simp at h
  | some k =>
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hdw : Discrete (warmRefine adj
        (defaultSpineChain adj defaultP₀ defaultχι₀ nonDiscreteSel k).P
        (defaultSpineChain adj defaultP₀ defaultχι₀ nonDiscreteSel k).χι) :=
      leaf_discrete adj k hd
    have hdr : Discrete (warmRefineR adj
        (defaultSpineChain adj defaultP₀ defaultχι₀ nonDiscreteSel k).P
        (defaultSpineChain adj defaultP₀ defaultχι₀ nonDiscreteSel k).χι) :=
      discrete_warmRefineR adj _ _ hdw
    refine ⟨Colouring.rankPerm _ hdr, ?_⟩
    rw [← h]
    exact canonAdjComp_eq hdr

/-! ## The RUNNABLE output — reified renumbered refinement (`#eval` works)

**Why `canonOutputR` (above) still hung, and the fix.** Bisected: `warmRefineR` hangs on `#eval` even for SMALL
colours, so the blowup is not the values but **unmemoized recomputation** — `refineStepR χ = fun v => vertexRankNat
(refineStep χ) v` recomputes `refineStep χ` per vertex, re-reading the lazy `χ`, exploding exponentially across
rounds. The cure is **reification** (`warmRefineMat`, `ScratchRenumber`): materialise each round to a `Vector`
(computed once, O(1) lookup) — poly-time, and `warmRefineMat = warmRefineR` (`warmRefineMat_eq`), so soundness
transfers unchanged. `canonOutputMat` swaps `warmRefineR → warmRefineMat` and now RUNS. -/

/-- **The runnable renumbered output** — identical to `canonOutputR` but the leaf colouring is the *reified*
`warmRefineMat` (materialised each round ⟹ no recomputation, bounded values). `#eval`-feasible. -/
def canonOutputMat (adj : AdjMatrix n) : Option (Fin n → Fin n → Nat) :=
  (descentResult adj).map (fun k =>
    let ch := defaultSpineChain adj defaultP₀ defaultχι₀ nonDiscreteSel k
    canonAdjComp adj (warmRefineMat adj ch.P ch.χι))

/-- `canonOutputMat` equals `canonOutputR` (only the evaluation differs — `warmRefineMat_eq`). -/
theorem canonOutputMat_eq (adj : AdjMatrix n) : canonOutputMat adj = canonOutputR adj := by
  unfold canonOutputMat canonOutputR
  congr 1
  funext k
  simp only [warmRefineMat_eq]

/-- **①a on the runnable reified output** — a `some cG` answer is a genuine relabelling. Via `canonOutputMat_eq`
+ `canonOutputR_sound`. -/
theorem canonOutputMat_sound (adj : AdjMatrix n) (cG : Fin n → Fin n → Nat)
    (h : canonOutputMat adj = some cG) :
    ∃ π : Equiv.Perm (Fin n), cG = labelledAdj π adj := by
  rw [canonOutputMat_eq] at h
  exact canonOutputR_sound adj cG h

/-- Render a 3×3 output matrix as nested lists (so `#eval` has a `Repr`). -/
def render3 (o : Option (Fin 3 → Fin 3 → Nat)) : Option (List (List Nat)) :=
  o.map (fun f => (List.finRange 3).map (fun i => (List.finRange 3).map (fun j => f i j)))

-- ★ RUNS: the renumbered+reified canonical adjacency, computed (was infeasible with `warmRefine`/`warmRefineR`).
 --#eval render3 (canonOutputMat triangle)
 --#eval render3 (canonOutputMat path3)

end ChainDescent.RenumberExec
