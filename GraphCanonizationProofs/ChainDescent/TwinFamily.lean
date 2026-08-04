import ChainDescent.KeyComplete
import ChainDescent.CascadeOracle

/-!
# The TWIN family — the first NAMED family populating `Select.HandledS`

## What this file is for

`KeyComplete.handledS_of_reached_tinhofer` turns *"`Deepen.Tinhofer` holds at every reached
non-discrete node"* into `Select.HandledS`, but it is **hypothesis-defined**: the wind-down's W1
records that the only populations of the capability predicate are that hypothesis and
`HandledBridge.handled_emptyAdj`. This file supplies a **named family** and the generic machinery
that lifts any such family into the socket.

## The mechanism, in one line

If every pair of vertices a colouring merges is a **modular twin pair**, then the transposition of
any same-coloured pair is a colour-preserving automorphism — so every cell is a single orbit, for
free, at every level. `Consume.IsColAut` is two conjuncts, and `Equiv.swap` discharges both.

## Why the induction is cheap — refinement only refines

The invariant `TwinCells` ("every merged pair is a twin pair") is **inherited by every descendant**
with no graph-specific reasoning: `Deepen.step` is `refineV encodeFreeFast ∘ indivOne`, both of which
only *split* cells (`Refine.refineSplits_encodeFreeFast`, `indivOne_splits`), so a pair merged
downstream was already merged upstream. Consequently the entire per-family obligation collapses to a
**single root-level condition** (`RootTwins`, §4) — everything below the root is free.

⚠ This is why the file is short. The content is not in the descent; it is in §5's arithmetic, where a
concrete family has to earn the root condition.

## Scope — what is and is NOT claimed (measured 2026-08-04, wind-down W1 step 0)

* ✅ The complete multipartite / cluster graphs pass the target at **every** reached node: 1766
  graphs, 0 failures, 0 unknowns, 0 truncations, descents to 14 levels
  (`scratchpad/probe_w1_multipartite.py`). The probe measures the **selector-independent** form
  (every cell is an orbit), which is strictly stronger than `Tinhofer` and hence implies it under any
  selector — so no colour-id-order cross-check is owed.
* ⛔ **Cographs are REFUTED** at n = 7 by `K₃ ⊔ C₄` (`probe_w1_cographs.py`): the graph is 2-regular,
  so 1-WL gives one cell while `Aut = S₃ × D₄` has two orbits. The family boundary is **narrower than
  "modules"** — complete multipartite survives only because degree `= n − |part|` forces
  *equal degree ⟹ equal part size ⟹ conjugate*. Any wider candidate must supply its own
  degree↔orbit coupling. **Do not attempt to widen this file to cographs.**
* ⚠ This family is canonizable by sorting degrees. It is an honest *first* population of the
  predicate; it is **not** the "polynomial where IR solvers are exponential" claim, which is W2 (CFI).
-/

namespace ChainDescent
namespace TwinFamily

open ChainDescent.Descend
open ChainDescent.Consume (IsColAut)

variable {n : Nat}

/-! ## 1. Modular twins, and the transposition that witnesses them -/

/-- The simple-graph setting: `adj` symmetric and loopless. Both are needed by
`isColAut_swap_of_twin` — symmetry to transport the twin condition to the *other* coordinate, and
looplessness for the diagonal case. -/
def Simple (adj : AdjMatrix n) : Prop :=
  (∀ a b, adj.adj a b = adj.adj b a) ∧ (∀ a, adj.adj a a = 0)

/-- **`u` and `w` are modular twins**: identical adjacency to every *other* vertex. Note this
constrains neither `adj u w` nor the diagonal, so it covers both *false* twins (non-adjacent,
`N(u) = N(w)`) and *true* twins (adjacent, `N[u] = N[w]`) — the transposition is an automorphism
either way. -/
def Twin (adj : AdjMatrix n) (u w : Fin n) : Prop :=
  ∀ s, s ≠ u → s ≠ w → adj.adj u s = adj.adj w s

/-- Pointwise value of a transposition, as an `if`-cascade — the form the case analyses below want. -/
private theorem swap_val (u w x : Fin n) :
    Equiv.swap u w x = if x = u then w else if x = w then u else x := by
  by_cases h1 : x = u
  · subst h1; simp
  · by_cases h2 : x = w
    · subst h2; simp [Equiv.swap_apply_right, h1]
    · simp [Equiv.swap_apply_of_ne_of_ne h1 h2, h1, h2]

/-- **★ THE WITNESS.** Transposing a same-coloured twin pair is a colour-preserving automorphism.
Both `IsColAut` conjuncts are discharged by case analysis: the adjacency half by `Twin` (plus
symmetry on the reversed coordinate and looplessness on the diagonal), the colouring half because the
transposition moves only two vertices and those two already share a colour. -/
theorem isColAut_swap_of_twin {adj : AdjMatrix n} (hs : Simple adj)
    {χ : Colouring n} {u w : Fin n} (htw : Twin adj u w) (hcol : χ u = χ w) :
    IsColAut adj χ (Equiv.swap u w) := by
  -- The adjacency half is exactly `CascadeOracle.isAut_swap_of_twin` (`IsAut` unfolds to
  -- `IsColAut`'s first conjunct), so only the colouring half is new here.
  refine ⟨isAut_swap_of_twin hs.1 hs.2 htw, ?_⟩
  intro v
  rw [swap_val]
  by_cases hvu : v = u
  · rw [if_pos hvu, hvu]; exact hcol.symm
  · by_cases hvw : v = w
    · rw [if_neg hvu, if_pos hvw, hvw]; exact hcol
    · rw [if_neg hvu, if_neg hvw]

/-! ## 2. The invariant, and why it is inherited

`TwinCells` is the whole content: it says the colouring never merges a non-twin pair. -/

/-- **The invariant**: every pair `χ` merges is a modular twin pair. -/
def TwinCells (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ u w : Fin n, χ u = χ w → Twin adj u w

/-- Individualization only SPLITS: a pair it merges was already merged. (`indivOne` sends `v` to
`2·χ v + 1` and everything else to `2·χ ·`, so a merge across the `v` boundary is a parity clash.) -/
private theorem indivOne_splits (χ : Colouring n) (v x y : Fin n)
    (h : Descend.indivOne χ v x = Descend.indivOne χ v y) : χ x = χ y := by
  simp only [Descend.indivOne] at h
  by_cases hx : x = v
  · by_cases hy : y = v
    · rw [hx, hy]
    · rw [if_pos hx, if_neg hy] at h; omega
  · by_cases hy : y = v
    · rw [if_neg hx, if_pos hy] at h; omega
    · rw [if_neg hx, if_neg hy] at h; omega

/-- **★ THE INVARIANT IS INHERITED — with no graph-specific reasoning.** `Deepen.step` is
`refineV encodeFreeFast ∘ indivOne`; both halves only split, so any pair merged by the child was
already merged by the parent, where the hypothesis applies. This is what makes the whole per-family
obligation collapse to the root. -/
theorem twinCells_step {adj : AdjMatrix n} {χ : Colouring n} (h : TwinCells adj χ)
    (v : Fin n) : TwinCells adj (Deepen.step adj χ v).col := by
  intro x y hxy
  rw [KeyComplete.step_col_eq_refineV] at hxy
  have hind := Refine.refineSplits_encodeFreeFast (n := n) adj (Descend.indivOne χ v) x y hxy
  exact h x y (indivOne_splits χ v x y hind)

/-- Under the invariant EVERY cell is a single orbit — the selector-independent statement, which is
what the step-0 probe measured and is strictly stronger than what `TinhoferPath` asks for. -/
theorem cellSingleOrbit_of_twinCells {adj : AdjMatrix n} (hs : Simple adj)
    {χ : Colouring n} (h : TwinCells adj χ) (cid : Nat) :
    Deepen.CellSingleOrbit adj χ cid := by
  intro u w hu hw
  have hcol : χ u = χ w := hu.trans hw.symm
  exact ⟨Equiv.swap u w, isColAut_swap_of_twin hs (h u w hcol) hcol, Equiv.swap_apply_left u w⟩

/-! ## 3. `TinhoferPath` and `Tinhofer` from the invariant -/

/-- **`TinhoferPath` at every fuel.** Induction on fuel: the level's `CellSingleOrbit` comes from §2,
and the recursive call is at `step adj χc w`, where the invariant still holds by `twinCells_step`. -/
theorem tinhoferPath_of_twinCells {adj : AdjMatrix n} (hs : Simple adj) (χp : Colouring n) :
    ∀ (fuel : Nat) (cur : Refine.ColData n), TwinCells adj cur.col →
      Deepen.TinhoferPath adj χp fuel cur := by
  intro fuel
  induction fuel with
  | zero => intro cur _; trivial
  | succ f ih =>
      intro cur hcur
      unfold Deepen.TinhoferPath
      dsimp only
      -- `cases hch :` substitutes in the GOAL, so the match reduces (as in `DeepenCertified`).
      cases hch : Deepen.chooseIdK (List.finRange n) cur.col with
      | none => trivial
      | some cid =>
          refine ⟨cellSingleOrbit_of_twinCells hs hcur cid, ?_⟩
          cases hf : (List.finRange n).filter (fun v => cur.col v == cid) with
          | nil => trivial
          | cons w _ => exact ih _ (twinCells_step hcur w)

/-- **`Tinhofer` from the invariant.** Each anchor's first step lands in a colouring that still
satisfies the invariant, and §3 covers the rest of the path. -/
theorem tinhofer_of_twinCells {adj : AdjMatrix n} (hs : Simple adj)
    {χ : Colouring n} (h : TwinCells adj χ) : Deepen.Tinhofer adj χ :=
  fun r _ => tinhoferPath_of_twinCells hs χ n _ (twinCells_step h r)

/-! ## 4. The root condition — the ONLY thing a family has to earn -/

/-- The descent's root colouring. -/
def rootCol (adj : AdjMatrix n) : Colouring n :=
  Descend.refineV (Refine.encodeFreeFast (n := n)) adj (fun _ => 0)

/-- **The per-family obligation, stated once**: every pair the ROOT colouring merges is a twin pair.
Everything below the root is free (§2). -/
def RootTwins (adj : AdjMatrix n) : Prop :=
  ∀ u w : Fin n, rootCol adj u = rootCol adj w → Twin adj u w

/-- Every reached colouring refines the root — the descent's steps only split. -/
theorem twinCells_of_reaches {adj : AdjMatrix n} (hR : RootTwins adj) {χ : Colouring n}
    (hr : Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ) : TwinCells adj χ := by
  induction hr with
  | root => intro u w h; exact hR u w h
  | step _ _ _ ih =>
      intro x y hxy
      have hind := Refine.refineSplits_encodeFreeFast (n := n) adj (Descend.indivOne _ _) x y hxy
      exact ih x y (indivOne_splits _ _ x y hind)

/-- **★★★ THE SOCKET.** A simple graph whose root colouring merges only twin pairs is `HandledS`:
every reached non-discrete node has a resolvable cell, so the fused resolver never stalls there.
This is the generic half — §5 supplies a family that satisfies the hypothesis. -/
theorem handledS_of_rootTwins {adj : AdjMatrix n} (hs : Simple adj) (hR : RootTwins adj) :
    Select.HandledS Deepen.orbKey Deepen.deepenSupply adj :=
  KeyComplete.handledS_of_reached_tinhofer
    (fun _ hr _ => tinhofer_of_twinCells hs (twinCells_of_reaches hR hr))

/-! ## 5. A NAMED FAMILY — complete multipartite graphs with distinct part sizes

The root condition has to be *earned*, and this is where the graph-specific content lives. The
argument is the one the step-0 probe's Claim S pinned, in its cheapest form:

* one refinement round from the constant colouring already separates by **degree** (§5.1);
* in a complete multipartite graph a vertex's degree is `n − |its part|` (§5.2);
* so if the part sizes are pairwise distinct, equal root colour forces the **same part** — and
  same-part vertices are modular twins outright (§5.3).

⚠ **Why "distinct part sizes" and not all complete multipartite graphs.** With two parts of equal
size the root cell is their *union*, which is still a single orbit — but the witness is a
part-**swap**, not a transposition, and Claim S's case (ii) is where that construction would go. This
file deliberately takes only case (i): the probe recorded `spans = 0` on exactly the distinct-size
profiles, so nothing is lost *for this family* and the expensive construction is not needed. Widening
to case (ii) is a bounded, separate piece of work — see the module doc-block.
-/

/-- The complete multipartite graph induced by a part assignment: adjacent iff in different parts. -/
def IsCompleteMultipartite (adj : AdjMatrix n) (part : Fin n → Nat) : Prop :=
  ∀ a b, adj.adj a b = if part a = part b then 0 else 1

/-- The number of vertices in `v`'s part. -/
def psize (part : Fin n → Nat) (p : Nat) : Nat :=
  (Finset.univ.filter (fun s => part s = p)).card

/-- **The family's defining hypothesis**: distinct parts have distinct sizes. Stated through
vertices, so it only ever constrains *inhabited* parts. -/
def DistinctPartSizes (part : Fin n → Nat) : Prop :=
  ∀ u w : Fin n, psize part (part u) = psize part (part w) → part u = part w

/-- A complete multipartite graph is symmetric and loopless. -/
theorem simple_of_multipartite {adj : AdjMatrix n} {part : Fin n → Nat}
    (hM : IsCompleteMultipartite adj part) : Simple adj := by
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · rw [hM a b, hM b a]
    by_cases h : part a = part b
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]
  · rw [hM a a, if_pos rfl]

/-! ### 5.1 One round already separates by degree -/

/-- **Equal root colour ⟹ equal degree.** The root is `n` rounds; peeling all but the first
(`Refine.iterate_splits`) leaves round 1, whose fibres are the `sigKey` fibres
(`Refine.refineRound_eq_iff`), and at the *constant* colouring a `sigKey` carries exactly the
multiset of incident edge-values — whose sum is the degree. -/
theorem degSum_eq_of_rootCol_eq {adj : AdjMatrix n} {u w : Fin n}
    (h : rootCol adj u = rootCol adj w) :
    ∑ s ∈ Finset.univ.filter (fun s => s ≠ u), adj.adj u s
      = ∑ s ∈ Finset.univ.filter (fun s => s ≠ w), adj.adj w s := by
  -- `rfl` here SUBSTITUTES `n := m + 1`; rewriting `n` in place is not type-correct, because
  -- `adj : AdjMatrix n` and the iterate would then disagree on the index.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := u.isLt; omega⟩
  -- peel the warm round down to a single round
  have h1 : Refine.refineRound adj (fun _ => 0) u = Refine.refineRound adj (fun _ => 0) w := by
    have hroot : rootCol adj = (Refine.refineRound adj)^[m + 1] (fun _ => 0) := by
      show Descend.refineV (Refine.encodeFreeFast (n := m + 1)) adj (fun _ => 0) = _
      rw [Refine.refineV_encodeFreeFast]
      rfl
    rw [hroot, Function.iterate_succ_apply] at h
    exact Refine.iterate_splits adj m _ u w h
  -- round 1's fibres are the signature fibres
  have h2 : Refine.keyOf adj (fun _ => 0) u = Refine.keyOf adj (fun _ => 0) w :=
    (Refine.refineRound_eq_iff adj (fun _ => 0) u w).mp h1
  have h3 := (sigKey_eq_iff adj (Refine.constP (m + 1)) (fun _ => 0) u w).mp h2
  -- project the signature onto its edge-value component and sum
  have h4 : ((signature adj (Refine.constP (m + 1)) (fun _ => 0) u).map (fun t => t.2.1)).sum
      = ((signature adj (Refine.constP (m + 1)) (fun _ => 0) w).map (fun t => t.2.1)).sum := by
    rw [h3.2]
  simpa [signature, Multiset.map_map, Function.comp_def, Finset.sum] using h4

/-! ### 5.2 The degree of a complete multipartite graph -/

/-- In a complete multipartite graph a vertex is adjacent to exactly the vertices outside its part. -/
theorem degSum_multipartite {adj : AdjMatrix n} {part : Fin n → Nat}
    (hM : IsCompleteMultipartite adj part) (u : Fin n) :
    ∑ s ∈ Finset.univ.filter (fun s => s ≠ u), adj.adj u s
      = (Finset.univ.filter (fun s => part s ≠ part u)).card := by
  rw [Finset.sum_congr rfl (fun s _ => hM u s)]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  have hfe : (Finset.univ.filter (fun s => s ≠ u)).filter (fun s => ¬ (part u = part s))
      = Finset.univ.filter (fun s => part s ≠ part u) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact fun hc => h hc.symm
    · intro h
      exact ⟨fun hc => h (by rw [hc]), fun hc => h hc.symm⟩
  simp [hfe]

/-- The two halves of the part/non-part split add to `n`. -/
private theorem card_split (part : Fin n → Nat) (u : Fin n) :
    (Finset.univ.filter (fun s => part s ≠ part u)).card + psize part (part u) = n := by
  have := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun s => part s = part u)
  simp only [Finset.card_univ, Fintype.card_fin, ne_eq] at this ⊢
  unfold psize
  omega

/-! ### 5.3 The family satisfies the root condition -/

/-- **★★ THE FAMILY INSTANCE.** A complete multipartite graph with pairwise distinct part sizes
merges, at the root, only vertices of the *same* part — and same-part vertices are modular twins. -/
theorem rootTwins_of_multipartite {adj : AdjMatrix n} {part : Fin n → Nat}
    (hM : IsCompleteMultipartite adj part) (hD : DistinctPartSizes part) : RootTwins adj := by
  intro u w h
  -- equal root colour ⟹ equal degree ⟹ equal part size ⟹ same part
  have hdeg := degSum_eq_of_rootCol_eq h
  rw [degSum_multipartite hM u, degSum_multipartite hM w] at hdeg
  have hu := card_split part u
  have hw := card_split part w
  have hsize : psize part (part u) = psize part (part w) := by omega
  have hpart : part u = part w := hD u w hsize
  -- same part ⟹ modular twins
  intro s _ _
  rw [hM u s, hM w s, hpart]

/-- **★★★ THE NAMED FAMILY IS `HandledS`.** The wind-down's W1: a family, not a hypothesis. -/
theorem handledS_of_multipartite {adj : AdjMatrix n} {part : Fin n → Nat}
    (hM : IsCompleteMultipartite adj part) (hD : DistinctPartSizes part) :
    Select.HandledS Deepen.orbKey Deepen.deepenSupply adj :=
  handledS_of_rootTwins (simple_of_multipartite hM) (rootTwins_of_multipartite hM hD)

/-! ## 6. NON-VACUITY — the family is not the root-discrete ring in disguise

⚠ This section is the point of the exercise, not decoration. `Residue.handled_of_root_discrete`
already gives `Handled` to every graph whose refined root is discrete, *for free and for any
resolvers*. A "family" living inside that ring would be a restatement, so the standing steer (check
non-vacuity against probe data **before** building on a predicate) demands a theorem here. -/

/-- The complete multipartite graph on a given part assignment — a constructor, so the family is
visibly inhabited at every `n` rather than only hypothetically. -/
def mpAdj (part : Fin n → Nat) : AdjMatrix n :=
  ⟨fun a b => if part a = part b then 0 else 1⟩

theorem isCompleteMultipartite_mpAdj (part : Fin n → Nat) :
    IsCompleteMultipartite (mpAdj part) part := fun _ _ => rfl

/-- **★★ THE NON-VACUITY LEMMA.** A distinct same-coloured twin pair survives refinement, so the
root is **not** discrete: `Equiv.swap u w` is an automorphism fixing the constant colouring, the
refiner is equivariant (`Refine.refineEquivariant_encodeFreeFast`, obligation ①b), and an equivariant
refiner cannot separate a pair some automorphism swaps. Hence these graphs are genuinely *outside*
`handled_of_root_discrete`'s ring and the descent really runs. -/
theorem rootCol_eq_of_twin {adj : AdjMatrix n} (hs : Simple adj) {u w : Fin n}
    (htw : Twin adj u w) : rootCol adj u = rootCol adj w := by
  have haut : IsColAut adj (fun _ => 0 : Colouring n) (Equiv.swap u w) :=
    isColAut_swap_of_twin hs htw rfl
  have hrel : relabelAdj (Equiv.swap u w) adj = adj := haut.relabel
  have htr : transportColouring (Equiv.swap u w) (fun _ => 0 : Colouring n) = (fun _ => 0) :=
    haut.transport
  have hEq := Refine.refineEquivariant_encodeFreeFast (n := n) (Equiv.swap u w) adj (fun _ => 0)
  rw [hrel, htr] at hEq
  -- `hEq : rootCol adj = transportColouring (swap u w) (rootCol adj)`
  have hcf := congrFun hEq u
  show Descend.refineV (Refine.encodeFreeFast (n := n)) adj (fun _ => 0) u
      = Descend.refineV (Refine.encodeFreeFast (n := n)) adj (fun _ => 0) w
  rw [hcf]
  show Descend.refineV (Refine.encodeFreeFast (n := n)) adj (fun _ => 0)
      ((Equiv.swap u w).symm u) = _
  rw [Equiv.symm_swap, Equiv.swap_apply_left]

/-- A complete multipartite graph with a part of size ≥ 2 has a non-discrete root. -/
theorem not_discrete_rootCol_mpAdj {part : Fin n → Nat} {u w : Fin n}
    (hne : u ≠ w) (hsame : part u = part w) :
    ¬ Discrete (rootCol (mpAdj part)) := by
  intro hdisc
  refine hne (hdisc u w ?_)
  refine rootCol_eq_of_twin (simple_of_multipartite (isCompleteMultipartite_mpAdj part)) ?_
  intro s _ _
  show (if part u = part s then 0 else 1) = (if part w = part s then 0 else 1)
  rw [hsame]

/-! ### 6.1 A concrete witness — `K₁,₂,₃` on 6 vertices

Part sizes `1, 2, 3` are pairwise distinct, so the family hypothesis holds; the size-3 part gives a
twin pair, so the root is not discrete. The step-0 probe measured this exact profile at
**30 reached nodes, 18 of them non-discrete, 3 descent levels, and `spans = 0`** — the last confirming
that Claim S's case (ii) genuinely never arises here, which is what §5's restriction relies on. -/

/-- Parts of sizes 1, 2 and 3. -/
def part123 : Fin 6 → Nat := ![0, 1, 1, 2, 2, 2]

theorem distinctPartSizes_part123 : DistinctPartSizes part123 := by
  unfold DistinctPartSizes psize
  decide

/-- **★ THE CONCRETE INSTANCE** — a specific 6-vertex graph that is `HandledS` … -/
theorem handledS_part123 :
    Select.HandledS Deepen.orbKey Deepen.deepenSupply (mpAdj part123) :=
  handledS_of_multipartite (isCompleteMultipartite_mpAdj part123) distinctPartSizes_part123

/-- … and whose root is **not** discrete, so it is not covered by `handled_of_root_discrete`. -/
theorem not_discrete_part123 : ¬ Discrete (rootCol (mpAdj part123)) :=
  not_discrete_rootCol_mpAdj (part := part123) (u := 1) (w := 2) (by decide) (by decide)

/-! ## 7. THE PUBLICATION-FACING STATEMENT — the family is ANSWERED, never flagged

`Select.answersS_of_handledS` needs only `HandledS`, so this is free.

⚠⚠ **What is NOT claimed here, and why — read before quoting this as "canonized".** The canonical-form
half (`①`, `Select.isCanonicalFormOptS_canonFormS?`) additionally needs `NodeTransport`, hence
`SupplyTransport.SupplyEquivariant` on the supply. `foldSupply`, `deckSupply` and `deck2Supply` carry
it; **`deepenSupply` does not** — which is exactly why `deepenSupply` is deliberately held out of
`Publication.canonForm?`'s record object. That boundary is **pre-existing and untouched by this
family**: `handledS_of_reached_tinhofer`, the socket W1 names, is stated at
`(orbKey, deepenSupply)`. So the honest claim is *"the fused descent terminates with an answer on this
family, and never flags"*, **not** *"the record canonizer canonizes it"*. Closing the gap means either
`SupplyEquivariant deepenSupply` or re-basing the family onto the record supply — neither is in W1's
box, and the second is the live route (`OrbitPrune.SameOrbits` + `Select.handledS_of_sameOrbits`). -/

/-- **★★★ THE FAMILY ANSWERS.** No flag on any complete multipartite graph with distinct part sizes. -/
theorem answersS_of_multipartite {adj : AdjMatrix n} {part : Fin n → Nat}
    (hM : IsCompleteMultipartite adj part) (hD : DistinctPartSizes part) :
    Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) Deepen.orbKey Deepen.deepenSupply) adj
      ≠ none :=
  Select.answersS_of_handledS (handledS_of_multipartite hM hD)

/-- The concrete 6-vertex witness answers. -/
theorem answersS_part123 :
    Select.canonFormS? (Refine.encodeFreeFast (n := 6))
        (Select.selNode (Refine.encodeFreeFast (n := 6)) Deepen.orbKey Deepen.deepenSupply)
        (mpAdj part123)
      ≠ none :=
  answersS_of_multipartite (isCompleteMultipartite_mpAdj part123) distinctPartSizes_part123

end TwinFamily
end ChainDescent
