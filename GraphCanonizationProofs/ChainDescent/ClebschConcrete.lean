import ChainDescent.CascadeAffine

/-!
# The concrete ℤ₄² amorphic-NLS Clebsch scheme — the first NON-AFFINE δ′ closure in Lean

This module hard-codes the rank-4 amorphic-NLS Clebsch scheme on `ℤ₄²` (16 points, the **primitive G2-B
bullseye** — see `docs/chain-descent-general-cc-separability.md` §1A + §8) as an explicit
`AssociationScheme 16` from its colour matrix (extracted by
`Theorem41ConditionsProbe.Probe_DumpClebschMatrix`), and proves its forced-triangle **dominator closure
exhausts Ω from the 2-point base `{0,1}`** — discharging the seal's `hclo` content **for a genuinely
non-affine residue**, by `decide` (NOT `native_decide`, which would break the axiom bar).

The closure construction is the probe-extracted **rainbow-triangle rigidity** one (`clebschZ4Rank` = the BFS
pinning rank, layers `[2,2,6,6]`, depth 3); `dominatorReachable_of_rank`'s `decide` discovers the pinning
pairs itself, so only the rank function is supplied. **Scope:** this is one concrete scheme (parameter-scoped
to the Clebsch `(16,5,0,2)`), an existence witness that the δ′ route reaches a real non-affine residue — not
the general family theorem. It deliberately stays at the `AssociationScheme` level (the `Discrete` /
`SeparatesAtBoundedBase` content); feeding the *seal* capstone additionally needs `SchurianScheme`
(the automorphism data), deferred.

`#print axioms clebschZ4_closure` ⟹ `[propext, Classical.choice, Quot.sound]`.
-/

namespace ChainDescent

open Finset

/-- The ℤ₄² Clebsch colour matrix (rank-4: colours `0..3`, `0` = diagonal), extracted from the probe. -/
def clebschZ4ColF : Fin 16 → Fin 16 → Fin 4 :=
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
def clebschZ4Rel (i : Fin 4) (v w : Fin 16) : Bool := clebschZ4ColF v w == i

/-- A representative pair for each colour (in `R_k`): used to define the intersection numbers. -/
def clebschZ4Rep : Fin 4 → Fin 16 × Fin 16 := ![(0, 0), (0, 2), (0, 1), (0, 6)]

/-- The intersection numbers, read off a representative pair per colour. -/
def clebschZ4IN (i j k : Fin 4) : Nat :=
  (Finset.univ.filter (fun u : Fin 16 =>
    clebschZ4Rel i (clebschZ4Rep k).1 u = true ∧ clebschZ4Rel j u (clebschZ4Rep k).2 = true)).card

/-- **The concrete ℤ₄² Clebsch scheme as an `AssociationScheme 16`.** All four axioms by `decide`
(the coherence axiom is the heavy one — confirmed feasible). -/
def clebschZ4Scheme : AssociationScheme 16 where
  rank := 3
  rel := clebschZ4Rel
  rel_zero_iff_eq := by decide
  rel_symm := by decide
  -- `∃!` has no synthesizable `Decidable` instance; give the term (the unique colour is `clebschZ4ColF v w`).
  rel_partition := fun v w =>
    ⟨clebschZ4ColF v w, beq_self_eq_true _, fun j hj => (beq_iff_eq.mp hj).symm⟩
  intersectionNumber := clebschZ4IN
  -- split per colour `k` to keep each `decide`'s kernel working-set small (¼ the peak):
  -- one `decide` over `Fin 4 × Fin 4 × Fin 16 × Fin 16` per fixed `k`.
  intersectionNumber_well_defined := by
    intro i j k
    fin_cases k <;> revert i j <;> decide

/-- The colour matrix *is* the relation index: `relOfPair v w = clebschZ4ColF v w`. The computable bridge
that lets `decide` evaluate the (otherwise `noncomputable`) `relOfPair` in the closure proof. -/
theorem clebschZ4_relOfPair (v w : Fin 16) :
    clebschZ4Scheme.relOfPair v w = clebschZ4ColF v w :=
  (clebschZ4Scheme.relOfPair_unique (show clebschZ4Rel (clebschZ4ColF v w) v w = true from
    beq_self_eq_true _)).symm

/-- The probe-extracted BFS pinning rank for base `{0,1}` (layers `[2,2,6,6]`, depth 3). -/
def clebschZ4Rank : Fin 16 → Nat := ![0, 0, 2, 2, 3, 2, 1, 2, 3, 3, 3, 3, 2, 3, 2, 1]

/-- The probe-extracted explicit pinning pair `(µ,λ)` for each point (rank-0 base points get a dummy). The
rainbow triangle that pins each point — supplied explicitly so each `hstep` `decide` is a tiny per-point
`∀u` check rather than an ∃-search over all 256 pairs (which OOMs the kernel). -/
def clebschZ4Pin : Fin 16 → Fin 16 × Fin 16 :=
  ![(0, 0), (0, 0), (6, 15), (6, 15), (2, 3), (0, 6), (0, 1), (1, 6),
    (0, 2), (0, 12), (0, 2), (0, 7), (1, 15), (2, 3), (0, 15), (0, 1)]

/-- A rank engine keyed on the **intersection-number** premise (a Nat equality) rather than the
`relOfPair`-profile uniqueness. The `interNum = 1` form is `decide`-friendly (no nested implications, which
have no synthesizable `Decidable` instance), so the whole `hstep` obligation closes in one `decide` after
the `relOfPair`→matrix bridge. Strong induction on `rank`, with the pinner pair `pin γ` and
`DominatorReachable.step`. -/
private theorem domReach_of_rank_pin {n : Nat} {S : AssociationScheme n} {T : Finset (Fin n)}
    (rank : Fin n → Nat) (pin : Fin n → Fin n × Fin n)
    (hbase : ∀ v : Fin n, rank v = 0 → v ∈ T)
    (hstep : ∀ γ : Fin n, 0 < rank γ →
        rank (pin γ).1 < rank γ ∧ rank (pin γ).2 < rank γ ∧
        S.intersectionNumber (S.relOfPair (pin γ).1 γ) (S.relOfPair γ (pin γ).2)
          (S.relOfPair (pin γ).1 (pin γ).2) = 1) :
    ∀ v : Fin n, DominatorReachable S T v := by
  have key : ∀ k : Nat, ∀ v : Fin n, rank v = k → DominatorReachable S T v := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv
      rcases Nat.eq_zero_or_pos (rank v) with h0 | hpos
      · exact DominatorReachable.base (hbase v h0)
      · obtain ⟨hlt1, hlt2, hone⟩ := hstep v hpos
        exact DominatorReachable.step (ih (rank (pin v).1) (hv ▸ hlt1) _ rfl)
          (ih (rank (pin v).2) (hv ▸ hlt2) _ rfl) hone
  intro v; exact key (rank v) v rfl

/-- **THE NON-AFFINE CLOSURE.** Every point of the ℤ₄² Clebsch scheme is forced-triangle
dominator-reachable from the 2-base `{0,1}` — the seal's `hclo` content, discharged for a real non-affine
residue. `domReach_of_rank_pin` with the probe's rank and explicit per-point rainbow pinners
(`clebschZ4Pin`); `hbase`/`hstep` by `decide` (the `hstep` `interNum = 1` premise after the
`relOfPair`→matrix bridge — so `decide` checks each rainbow triangle is rigid). -/
theorem clebschZ4_closure :
    ∀ v, DominatorReachable clebschZ4Scheme {0, 1} v :=
  domReach_of_rank_pin clebschZ4Rank clebschZ4Pin (by decide)
    (by simp only [clebschZ4_relOfPair]; decide)

/-- **The payoff: the ℤ₄² Clebsch scheme is discrete after individualizing `{0,1}`** — `b(X) ≤ 2`, a
non-affine `SeparatesAtBoundedBase`-grade recovery, fully in Lean and axiom-clean. -/
theorem clebschZ4_discrete :
    Discrete (warmRefine (schemeAdj clebschZ4Scheme) (fun _ _ => POE.unknown)
      (individualizedColouring 16 {0, 1})) :=
  discrete_of_dominatorClosure clebschZ4Scheme clebschZ4_closure

/-- **The bullseye is rainbow-rigid (non-vacuity of the family lemma).** `RainbowRigid clebschZ4Scheme` by
`decide`: every rainbow triangle (three pairwise-distinct non-diagonal colours) of the ℤ₄² Clebsch scheme has
`≤ 1` common neighbour — the amorphic `(16,5,0,2)` structure the probe extracted, now a checked fact. Witnesses
that `dominatorReachable_of_rainbowRank`'s hypothesis is satisfiable on the genuine non-affine residue, so the
δ′ family closure is not vacuous; `clebschZ4_closure` is its concrete instance. Axiom-clean (plain `decide`). -/
theorem clebschZ4_rainbowRigid : RainbowRigid clebschZ4Scheme := by
  unfold RainbowRigid; decide

/-- **The family engine fires on the real residue.** The ℤ₄² Clebsch closure, re-derived through the *family*
lemma `dominatorReachable_of_rainbowRank` (rather than the bespoke `interNum`-keyed `domReach_of_rank_pin` of
`clebschZ4_closure`): every point is dominator-reachable from `{0,1}` using only `clebschZ4_rainbowRigid` and a
**rainbow rank** — the probe rank `clebschZ4Rank` with the explicit rainbow triangles `clebschZ4Pin` (each a triple
of pairwise-distinct non-diagonal colours, checked by `decide` after the `relOfPair`→matrix bridge). This is the
**non-vacuity witness for `dominatorReachable_of_rainbowRank`** on a genuine non-affine residue — and hence for the
seal capstone `reachesRigidOrCameron_viaRainbowRank` built on it: the rainbow `hbase`/`hstep` data it requires is
satisfiable on real amorphic-NLS data (the `n = 16` instance of the uniform rainbow rank the node-2 rung needs).
The remaining gap to a *sealed* instance is the `SchurianScheme` (automorphism) structure on `clebschZ4Scheme`,
deferred. Axiom-clean (`decide`, not `native_decide`). -/
theorem clebschZ4_closure_viaRainbow :
    ∀ v, DominatorReachable clebschZ4Scheme {0, 1} v := by
  -- The rainbow data in the *matrix* colours (computable), decided directly as in `clebschZ4_closure`.
  have hstep : ∀ γ : Fin 16, 0 < clebschZ4Rank γ →
      clebschZ4Rank (clebschZ4Pin γ).1 < clebschZ4Rank γ ∧
      clebschZ4Rank (clebschZ4Pin γ).2 < clebschZ4Rank γ ∧
      clebschZ4ColF (clebschZ4Pin γ).1 γ ≠ 0 ∧ clebschZ4ColF γ (clebschZ4Pin γ).2 ≠ 0 ∧
      clebschZ4ColF (clebschZ4Pin γ).1 (clebschZ4Pin γ).2 ≠ 0 ∧
      clebschZ4ColF (clebschZ4Pin γ).1 γ ≠ clebschZ4ColF γ (clebschZ4Pin γ).2 ∧
      clebschZ4ColF γ (clebschZ4Pin γ).2 ≠ clebschZ4ColF (clebschZ4Pin γ).1 (clebschZ4Pin γ).2 ∧
      clebschZ4ColF (clebschZ4Pin γ).1 γ ≠ clebschZ4ColF (clebschZ4Pin γ).1 (clebschZ4Pin γ).2 := by
    decide
  refine dominatorReachable_of_rainbowRank clebschZ4_rainbowRigid clebschZ4Rank (by decide) ?_
  intro γ hγ
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hstep γ hγ
  exact ⟨(clebschZ4Pin γ).1, (clebschZ4Pin γ).2, h1, h2,
    by rw [clebschZ4_relOfPair]; exact h3, by rw [clebschZ4_relOfPair]; exact h4,
    by rw [clebschZ4_relOfPair]; exact h5,
    by rw [clebschZ4_relOfPair, clebschZ4_relOfPair]; exact h6,
    by rw [clebschZ4_relOfPair, clebschZ4_relOfPair]; exact h7,
    by rw [clebschZ4_relOfPair, clebschZ4_relOfPair]; exact h8⟩

end ChainDescent
