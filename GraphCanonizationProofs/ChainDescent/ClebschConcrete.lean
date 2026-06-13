import ChainDescent.CascadeAffine

/-!
# The concrete ℤ₄² amorphic-NLS Clebsch scheme — the first NON-AFFINE δ′ closure in Lean

This module hard-codes the rank-4 amorphic-NLS Clebsch scheme on `ℤ₄²` (16 points, the **primitive G2-B
bullseye** — see `docs/chain-descent-general-cc-separability.md` §1A + §8) as an explicit
`AssociationScheme 16` from its colour matrix (extracted by
`Theorem41ConditionsProbe.Probe_DumpClebschMatrix`), and proves its forced-triangle **dominator closure
exhausts Ω from the 2-point base `{0,1}`** — discharging the seal's `hclo` content **for a genuinely
non-affine residue**, by `decide` (NOT `native_decide`, which would break the axiom bar).

The closure construction is the probe-extracted **rainbow-triangle rigidity** one (`clebschRank` = the BFS
pinning rank, layers `[2,2,6,6]`, depth 3); `dominatorReachable_of_rank`'s `decide` discovers the pinning
pairs itself, so only the rank function is supplied. **Scope:** this is one concrete scheme (parameter-scoped
to the Clebsch `(16,5,0,2)`), an existence witness that the δ′ route reaches a real non-affine residue — not
the general family theorem. It deliberately stays at the `AssociationScheme` level (the `Discrete` /
`SeparatesAtBoundedBase` content); feeding the *seal* capstone additionally needs `SchurianScheme`
(the automorphism data), deferred.

`#print axioms clebsch_closure` ⟹ `[propext, Classical.choice, Quot.sound]`.
-/

namespace ChainDescent

open Finset

/-- The ℤ₄² Clebsch colour matrix (rank-4: colours `0..3`, `0` = diagonal), extracted from the probe. -/
def clebschColF : Fin 16 → Fin 16 → Fin 4 :=
  ![![0,2,1,2,1,1,3,2,2,3,3,3,1,2,3,1],
    ![2,0,2,1,2,1,1,3,3,2,3,3,1,1,2,3],
    ![1,2,0,2,3,2,1,1,3,3,2,3,3,1,1,2],
    ![2,1,2,0,1,3,2,1,3,3,3,2,2,3,1,1],
    ![1,2,3,1,0,2,1,2,1,1,3,2,2,3,3,3],
    ![1,1,2,3,2,0,2,1,2,1,1,3,3,2,3,3],
    ![3,1,1,2,1,2,0,2,3,2,1,1,3,3,2,3],
    ![2,3,1,1,2,1,2,0,1,3,2,1,3,3,3,2],
    ![2,3,3,3,1,2,3,1,0,2,1,2,1,1,3,2],
    ![3,2,3,3,1,1,2,3,2,0,2,1,2,1,1,3],
    ![3,3,2,3,3,1,1,2,1,2,0,2,3,2,1,1],
    ![3,3,3,2,2,3,1,1,2,1,2,0,1,3,2,1],
    ![1,1,3,2,2,3,3,3,1,2,3,1,0,2,1,2],
    ![2,1,1,3,3,2,3,3,1,1,2,3,2,0,2,1],
    ![3,2,1,1,3,3,2,3,3,1,1,2,1,2,0,2],
    ![1,3,2,1,3,3,3,2,2,3,1,1,2,1,2,0]]

/-- Relation `i` holds at `(v,w)` iff the matrix colour there is `i`. -/
def clebschRel (i : Fin 4) (v w : Fin 16) : Bool := clebschColF v w == i

/-- A representative pair for each colour (in `R_k`): used to define the intersection numbers. -/
def clebschRep : Fin 4 → Fin 16 × Fin 16 := ![(0, 0), (0, 2), (0, 1), (0, 6)]

/-- The intersection numbers, read off a representative pair per colour. -/
def clebschIN (i j k : Fin 4) : Nat :=
  (univ.filter (fun u : Fin 16 =>
    clebschRel i (clebschRep k).1 u = true ∧ clebschRel j u (clebschRep k).2 = true)).card

/-- **The concrete ℤ₄² Clebsch scheme as an `AssociationScheme 16`.** All four axioms by `decide`
(the coherence axiom is the heavy one — confirmed feasible). -/
def clebschScheme : AssociationScheme 16 where
  rank := 3
  rel := clebschRel
  rel_zero_iff_eq := by decide
  rel_symm := by decide
  rel_partition := by decide
  intersectionNumber := clebschIN
  intersectionNumber_well_defined := by decide

/-- The colour matrix *is* the relation index: `relOfPair v w = clebschColF v w`. The computable bridge
that lets `decide` evaluate the (otherwise `noncomputable`) `relOfPair` in the closure proof. -/
theorem clebsch_relOfPair (v w : Fin 16) :
    clebschScheme.relOfPair v w = clebschColF v w :=
  (clebschScheme.relOfPair_unique (show clebschRel (clebschColF v w) v w = true from
    beq_self_eq_true _)).symm

/-- The probe-extracted BFS pinning rank for base `{0,1}` (layers `[2,2,6,6]`, depth 3). -/
def clebschRank : Fin 16 → Nat := ![0, 0, 2, 2, 3, 2, 1, 2, 3, 3, 3, 3, 2, 3, 2, 1]

/-- **THE NON-AFFINE CLOSURE.** Every point of the ℤ₄² Clebsch scheme is forced-triangle
dominator-reachable from the 2-base `{0,1}` — the seal's `hclo` content, discharged for a real non-affine
residue. `dominatorReachable_of_rank` with the probe's rank; `hbase`/`hstep` by `decide` (the latter after
rewriting `relOfPair` to the matrix via the bridge — so `decide` finds the rainbow-triangle pinners itself). -/
theorem clebsch_closure :
    ∀ v, DominatorReachable clebschScheme {0, 1} v := by
  refine dominatorReachable_of_rank clebschRank (by decide) ?_
  simp only [clebsch_relOfPair]
  decide

/-- **The payoff: the ℤ₄² Clebsch scheme is discrete after individualizing `{0,1}`** — `b(X) ≤ 2`, a
non-affine `SeparatesAtBoundedBase`-grade recovery, fully in Lean and axiom-clean. -/
theorem clebsch_discrete :
    Discrete (warmRefine (schemeAdj clebschScheme) (fun _ _ => POE.unknown)
      (individualizedColouring 16 {0, 1})) :=
  discrete_of_dominatorClosure clebschScheme clebsch_closure

end ChainDescent
