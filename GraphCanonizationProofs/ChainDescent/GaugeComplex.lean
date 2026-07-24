import ChainDescent.WLGeneric

/-!
# W2 localization spine — Tier A, piece 1: the split-vs-count base lemma

Planning doc: `docs/chain-descent-w2-solvability-route.md` §2 (the gauge complex) and §5 (Tier A).

This is the base lemma the W2 solvability route rests on — the object the completeness
(dual-of-the-seal) argument localizes onto. It is the current-API realization of the
open Lean lemma stated in `docs/Archive/ChainDescent/chain-descent-matroid.md:146-151`:

> at every warm-refine round, a vertex `v` breaks from its cell `C` iff the count vector
> `(|N(v) ∩ Dᵢ|)ᵢ` over the sub-cells `Dᵢ` of some neighbour cell differs from at least one
> other vertex in `C` — a multiset-cardinality reformulation of `refineStep_iff`.

In `WLGeneric`'s vocabulary the "sub-cells of a neighbour cell" are the
`(neighbour-colour, adjacency-value, P-relation)` classes `t : Nat × Nat × POE`, and the
"count vector" is `fun t => Multiset.count t (signature adj P χ v)`. So the lemma is:
`refineStep` separates two co-cellular vertices iff some class-count differs
(`refineStep_ne_iff_exists_count_ne`), plus the gloss that each class-count *is* a literal
neighbour cardinality `|{u ≠ v : class of u = t}|` (`count_signature_eq_card`).

Nothing here assumes anything about the *group* structure of the gauge — that is Tier B
(`forceSolvable`). This piece is the non-circular skeleton: it says *what warm refinement
does at each step*, and is exactly the "1 of k, unless cancellation" mechanism of
`chain-descent-matroid.md:141-144` made precise (cancellation = two class-counts that both
change but leave the multiset fixed — impossible here, since the multiset IS the count
vector, so a real split is exactly a real count difference).
-/

namespace ChainDescent
namespace GaugeComplex

-- NB: do NOT `open WLGeneric` — the enclosing `ChainDescent` namespace also exposes the
-- top-level `signature`/`refineStep` (over `AdjMatrix`), which would shadow the generic
-- `WLGeneric.*` versions. Qualify explicitly.

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The split-vs-count base lemma (W2 Tier A, piece 1).** Two vertices `v, w` in the same
cell (`χ v = χ w`) are *separated* by one round of 1-WL refinement iff their neighbour
class-count vectors differ in *some* class `t = (colour, adj-value, P-relation)`.

This is `refineStep_iff` (equal refined colour ⟺ same old colour ∧ same signature) composed
with multiset extensionality (`Multiset.ext`: two multisets agree iff every count agrees).
It is the precise, current-API form of `chain-descent-matroid.md:146-151`, and the base case
of the gauge-complex localization: a mixed cell splits under warm refinement exactly where a
neighbour-class count separates its vertices. -/
theorem refineStep_ne_iff_exists_count_ne
    (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) {v w : V} (hcol : χ v = χ w) :
    WLGeneric.refineStep adj P χ v ≠ WLGeneric.refineStep adj P χ w ↔
      ∃ t : Nat × Nat × POE,
        Multiset.count t (WLGeneric.signature adj P χ v)
          ≠ Multiset.count t (WLGeneric.signature adj P χ w) := by
  have hstep : WLGeneric.refineStep adj P χ v = WLGeneric.refineStep adj P χ w ↔
      WLGeneric.signature adj P χ v = WLGeneric.signature adj P χ w := by
    rw [WLGeneric.refineStep_iff, and_iff_right hcol]
  rw [ne_eq, hstep, Multiset.ext, not_forall]

/-- **The gloss — a class-count is a literal neighbour cardinality.** For any class
`t = (colour, adj-value, P-relation)`, the multiset count `Multiset.count t (signature …)`
equals the number of vertices `u ≠ v` whose own class `(χ u, adj v u, P v u)` is exactly `t`.
This is what makes "count vector over neighbour sub-cells" in the base lemma literal:
`Multiset.count t (signature adj P χ v) = |{u ≠ v : (χ u, adj v u, P v u) = t}|`. -/
theorem count_signature_eq_card
    (adj : WLGeneric.GAdj V) (P : WLGeneric.GPOE V) (χ : V → Nat) (v : V) (t : Nat × Nat × POE) :
    Multiset.count t (WLGeneric.signature adj P χ v)
      = (Finset.univ.filter (fun u => u ≠ v ∧ t = (χ u, adj v u, P v u))).card := by
  unfold WLGeneric.signature
  rw [Multiset.count_map]
  simp only [Finset.card, Finset.filter_val, Multiset.filter_filter, and_comm]

--#print axioms refineStep_ne_iff_exists_count_ne
--#print axioms count_signature_eq_card

end GaugeComplex
end ChainDescent
