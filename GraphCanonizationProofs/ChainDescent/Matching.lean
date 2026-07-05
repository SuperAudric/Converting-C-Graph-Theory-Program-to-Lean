/-
# The matching-trick first moment — increment 4/5 combinatorial core (SCRATCH).

Abstract finite-counting lemma that makes the "anchor existence dissolves into averaging" claim a theorem.
Model the base as `m` matched pairs `P : Fin m → W` (here `W = V × V` will be the probe×anchor space; a matched
pair separates a target `(u,u')` iff `¬fail`). Because the `m` coordinates of `P` are independent, the number of
bases that FAIL a fixed target factors as `(#fail)^m`; a union bound over targets gives existence of a base that
covers every target as soon as `|Targets| · F^m < |W|^m` (`F` = per-target fail-set size bound). Pure cardinality —
NO probability/measure. The analytic input (the per-target `F ≤ c̄₀·|W|`, `c̄₀<1`) is increments 2/3 + the
bad-anchor density; this lemma is what consumes it.

NOT in build (scratch; `lake env lean ChainDescent/ScratchMatching.lean`).
-/
import ChainDescent.GaussCount

namespace ChainDescent

open Finset

/-- **The matching-trick first moment.** `fail g w` = "matched pair `w` fails to separate target `g`". If every
target's fail-set has at most `F` elements and `|Targets| · F^m < |W|^m`, then some base `P : Fin m → W` covers
every target (each target has a non-failing coordinate). The independence of the `m` coordinates makes the
count of bases failing a fixed target exactly `(#fail)^m`; a union bound over targets closes it. -/
theorem exists_separating_base
    {W : Type*} [Fintype W] [DecidableEq W]
    {ι : Type*} [Fintype ι]
    (fail : ι → W → Prop) [∀ g, DecidablePred (fail g)]
    (m F : ℕ)
    (hF : ∀ g, (univ.filter (fun w => fail g w)).card ≤ F)
    (hlt : Fintype.card ι * F ^ m < Fintype.card W ^ m) :
    ∃ P : Fin m → W, ∀ g, ∃ j, ¬ fail g (P j) := by
  -- the count of bases that fail a fixed target factors as a product over the independent coordinates
  have hcard : ∀ g, (univ.filter (fun P : Fin m → W => ∀ j, fail g (P j))).card
      = (univ.filter (fun w => fail g w)).card ^ m := by
    intro g
    have heq : (univ.filter (fun P : Fin m → W => ∀ j, fail g (P j)))
        = Fintype.piFinset (fun _ : Fin m => univ.filter (fun w => fail g w)) := by
      ext P
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    rw [heq, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  by_contra h
  simp only [not_exists, not_forall, not_not] at h
  -- every base fails some target ⟹ the universe is covered by the per-target fail-sets
  have hcover : (univ : Finset (Fin m → W))
      ⊆ univ.biUnion (fun g => univ.filter (fun P : Fin m → W => ∀ j, fail g (P j))) := by
    intro P _
    obtain ⟨g, hg⟩ := h P
    exact Finset.mem_biUnion.2 ⟨g, Finset.mem_univ g, Finset.mem_filter.2 ⟨Finset.mem_univ P, hg⟩⟩
  have h1 : (Fintype.card W) ^ m ≤ Fintype.card ι * F ^ m := by
    calc (Fintype.card W) ^ m
        = (univ : Finset (Fin m → W)).card := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
      _ ≤ (univ.biUnion (fun g => univ.filter (fun P : Fin m → W => ∀ j, fail g (P j)))).card :=
          Finset.card_le_card hcover
      _ ≤ ∑ g, (univ.filter (fun P : Fin m → W => ∀ j, fail g (P j))).card :=
          Finset.card_biUnion_le
      _ = ∑ _g : ι, (univ.filter (fun w => fail _g w)).card ^ m :=
          Finset.sum_congr rfl (fun g _ => hcard g)
      _ ≤ ∑ _g : ι, F ^ m :=
          Finset.sum_le_sum (fun g _ => Nat.pow_le_pow_left (hF g) m)
      _ = Fintype.card ι * F ^ m := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact absurd h1 (not_le.2 hlt)

end ChainDescent

--#print axioms ChainDescent.exists_separating_base
