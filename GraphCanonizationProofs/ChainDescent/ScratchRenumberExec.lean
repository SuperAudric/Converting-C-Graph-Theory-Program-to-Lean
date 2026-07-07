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

/-! ## `#eval` — STILL hangs; the fix needs a fully-renumbered DESCENT, not just a renumbered output.

**★ FINDING (2026-07-07, bisected empirically).** `canonOutputR` renumbers the *output* warm-refinement, but it
still hangs, because the leaf SEED `ch.χι = defaultColouring … k` is **itself already blown up**: at `n = 3`,
`(defaultSpineChain triangle … 1).χι` is a ~2000-decimal-digit (~7000-bit) triple and the `warmRefine` leaf is
~27M-bit. `IndivStep.default` keeps `warmRefine`'s blown-up colour values (plus a small individualization offset),
so `ch.χι` embeds the compounding, and a single `refineStep` on a 7000-bit seed explodes to ~27M-bit via `O(bits²)`
bignum arithmetic — which is what hangs (not the final `<`). So renumbering only the output stage cannot help.

**The real fix = a fully renumbered descent** `defaultColouringR` / `defaultSpineChainR` using `refineStepR` at
EVERY level, so the seed `χι` stays `< n` throughout and no `refineStep` ever sees a large value. The primitive
(`refineStepR`) + bridge (`warmRefineR`/`samePartition_warmRefineR`) built here are exactly the pieces that
descent re-derivation reuses; `canonOutputR_sound` (①a) transfers to it verbatim. That re-derivation is the
scoped NEXT increment. (The theory — computable + ①a-sound renumbered output — is complete; only the runnable
`#eval` waits on the renumbered descent.) -/

/-- Render a 3×3 output matrix as nested lists (so `#eval` has a `Repr`). -/
def render3 (o : Option (Fin 3 → Fin 3 → Nat)) : Option (List (List Nat)) :=
  o.map (fun f => (List.finRange 3).map (fun i => (List.finRange 3).map (fun j => f i j)))

-- HANGS (seed already blown up — see the FINDING above; needs `defaultColouringR`):
-- #eval render3 (canonOutputR triangle)
-- #eval render3 (canonOutputR path3)

end ChainDescent.RenumberExec
