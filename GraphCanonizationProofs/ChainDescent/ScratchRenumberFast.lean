/-
# ScratchRenumberFast.lean — the fully reified+renumbered DESCENT (fast `#eval`) (WIP, NOT in build.sh)

`canonOutputMat` (`ScratchRenumberExec`) reified only the OUTPUT warm-refine; it ran, but took ~10 min for `n=3`
because the DESCENT internals (`descentResult` via `costedWarmRefine`, and `defaultColouring`) still use the lazy,
`Encodable.encode`-blown-up `warmRefine` — recomputed exponentially (unmemoised closures) and over huge `Nat`s.

This module reifies the **whole descent**:
  · `defaultColouringMat` — the descent's accumulated colouring, but each level uses `warmRefineMat` (reified +
    renumbered ⟹ bounded, no recomputation) and is **materialised** (`Vector`, computed once). `IndivStep.default`
    only doubles the colour (`2·χ v (+1)`), so a bounded `π` ⟹ bounded `χ'` — the descent stays `O(n²)`-valued.
  · `leafLevelMat` — the first level `≤ n` whose `warmRefineMat` leaf is `Discrete`, by a bounded `List.find?`.
  · `canonOutputFast` — emit `canonAdjComp` at that leaf. `#eval`s FAST (no blowup, no exponential recomputation).

**①a is self-contained here**: `leafLevelMat` returns `k` only where the leaf is *decidably* `Discrete`, so
`canonAdjComp` of it is a genuine relabelling (`canonAdjComp_eq`) — no need to bridge to the original descent.
(Completeness — that it returns `some` — would use `defaultSpineChain_reaches_leaf` + the partition bridge; later.)

Axiom target `[propext, Classical.choice, Quot.sound]`. `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchRenumberExec

namespace ChainDescent.RenumberFast

open ChainDescent
open ChainDescent.CanonSound
open ChainDescent.Executable
open ChainDescent.Renumber

variable {n : Nat}

/-- **Materialise a colouring** — compute it at all `n` vertices once (into a `Vector`), then O(1) lookup. Kills
the cross-level unmemoised recomputation. Value-unchanged (`materialize_eq`). -/
def materialize (χ : Colouring n) : Colouring n :=
  let v := Vector.ofFn χ
  fun i => v.get i

theorem materialize_eq (χ : Colouring n) : materialize χ = χ := by
  funext i; simp [materialize, Vector.get]

/-- **The reified+renumbered descent colouring.** Mirrors `defaultColouring`, but each level refines with the
reified `warmRefineMat` (bounded, no recomputation) and materialises the result. Stays `O(n²)`-valued. -/
def defaultColouringMat (adj : AdjMatrix n) (P₀ : PMatrix n) (χι₀ : Colouring n)
    (sel : Colouring n → Finset (Fin n)) : Nat → Colouring n
  | 0 => materialize χι₀
  | k + 1 =>
    let χι := defaultColouringMat adj P₀ χι₀ sel k
    let π := warmRefineMat adj P₀ χι
    materialize (IndivStep.default π (sel π)).χ'

/-- The reified leaf colouring at level `k`: `warmRefineMat` of the reified descent colouring. -/
def leafColouringMat (adj : AdjMatrix n) (k : Nat) : Colouring n :=
  warmRefineMat adj defaultP₀ (defaultColouringMat adj defaultP₀ defaultχι₀ nonDiscreteSel k)

/-- **The reified leaf level** — the first `k ≤ n` whose reified leaf colouring is `Discrete`, by a bounded search. -/
def leafLevelMat (adj : AdjMatrix n) : Option Nat :=
  (List.range (n + 1)).find? (fun k => decide (Discrete (leafColouringMat adj k)))

/-- **The fast runnable canonizer output** — descend (reified) to the leaf, emit `canonAdjComp` at it. `#eval`s
without blowup or exponential recomputation. -/
def canonOutputFast (adj : AdjMatrix n) : Option (Fin n → Fin n → Nat) :=
  (leafLevelMat adj).map (fun k => canonAdjComp adj (leafColouringMat adj k))

/-- **①a on the fast output** — a `some cG` answer is a genuine relabelling of `adj`. The search returns `k` only
where `leafColouringMat adj k` is `Discrete`, so `canonAdjComp` of it is `labelledAdj (rankPerm …) adj`. -/
theorem canonOutputFast_sound (adj : AdjMatrix n) (cG : Fin n → Fin n → Nat)
    (h : canonOutputFast adj = some cG) :
    ∃ π : Equiv.Perm (Fin n), cG = labelledAdj π adj := by
  unfold canonOutputFast at h
  cases hl : leafLevelMat adj with
  | none => rw [hl] at h; simp at h
  | some k =>
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hdec : decide (Discrete (leafColouringMat adj k)) = true := by
      have := List.find?_some (p := fun k => decide (Discrete (leafColouringMat adj k)))
        (l := List.range (n + 1)) (by rw [← hl]; rfl)
      exact this
    have hdisc : Discrete (leafColouringMat adj k) := of_decide_eq_true hdec
    exact ⟨Colouring.rankPerm _ hdisc, by rw [← h]; exact canonAdjComp_eq hdisc⟩

/-- Render a 3×3 output matrix as nested lists (so `#eval` has a `Repr`). -/
def render3 (o : Option (Fin 3 → Fin 3 → Nat)) : Option (List (List Nat)) :=
  o.map (fun f => (List.finRange 3).map (fun i => (List.finRange 3).map (fun j => f i j)))

-- ★ RUNS FAST (fully reified descent): the canonical adjacency of K₃ / the path.
 #eval render3 (canonOutputFast triangle)
 #eval render3 (canonOutputFast path3)

end ChainDescent.RenumberFast
