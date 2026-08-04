import ChainDescent.KeyComplete
import ChainDescent.CascadeOracle

/-!
# NO RIGID OBSTRUCTION — the capability socket, and the first NAMED family through it

## What this file is for

`KeyComplete.handledS_of_reached_tinhofer` turns *"`Deepen.Tinhofer` holds at every reached
non-discrete node"* into `Select.HandledS`, but it is **hypothesis-defined**: the wind-down's W1
records that the only populations of the capability predicate are that hypothesis and
`HandledBridge.handled_emptyAdj`. This file supplies (a) the **general socket**, stated on *"the
descent meets no rigid obstruction"*, (b) a **named family** through it, and (c) a route to the full
canonical-form claim, not merely termination.

## The three layers, in the order they matter

1. **§3–§4 — the socket.** `handledS_of_noRigidObstruction`: any **step-closed** class of colourings
   carrying **no rigid obstruction** (`SchurianAt`, proved equivalent to `¬ RigidObstructionAt` in
   `schurianAt_iff_no_rigidObstruction`) that holds at the root gives `Select.HandledS`. *To enlarge
   the handled region, supply a wider class — nothing below changes.* The step-closure hypothesis is
   the formal content of "peeling a layer leaves you in the class", which is why this shape is
   tractable per-family at all.
2. **§1–§2, §5 — one way to feed it.** Modular twins discharge Schurianity by transposition, and
   complete multipartite graphs with distinct part sizes discharge the root condition. This is the
   *narrowest* mechanism, not the boundary of the socket.
3. **§8 — answers → canonized.** A computable, equivariant **twin supply** replaces
   `(orbKey, deepenSupply)`, yielding the blind `Residue.Handled` and the full `①`.

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
  ★ The **socket** (§3–§4) is what carries forward; the family is a non-vacuity witness for it.
* ⚠ **The socket cannot be widened for free.** `SchurianAt` is *not* preserved by `Deepen.step` in
  general — that is exactly CAO propagation, refuted at 1-WL (`chain-descent-cao-propagation.md`).
  This is why `StepClosed` is a hypothesis and not a lemma: a wider class must prove its own closure.
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

/-! ## 3. THE GENERAL PREDICATE — no rigid obstruction, on a step-closed class

⚠ **This is the socket; the twin story of §1–§2 is only one way to feed it.** The hypothesis a family
actually has to meet is *"the descent never meets a rigid obstruction"* — nothing about twins. Twins
are one mechanism for discharging it, and the narrowest one. -/

/-- **`SchurianAt`** — every cell of `χ` is a single orbit of the colour-stabilizer. This is
"`χ` is Schurian": 1-WL's partition at `χ` *is* the orbit partition. -/
def SchurianAt (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ cid : Nat, Deepen.CellSingleOrbit adj χ cid

/-- **★ `SchurianAt` IS the absence of rigid obstructions** — de Morgan on
`Deepen.rigidObstruction_of_not_cellSingleOrbit`, both directions. This is the reading to quote: the
class is *"contains no rigid obstruction"*, and it is the exact complement of the rigid resolver's
domain, which is what lets it later be weakened to *"no rigid obstruction the rigid resolver does not
already handle"* without touching anything below. -/
theorem schurianAt_iff_no_rigidObstruction (adj : AdjMatrix n) (χ : Colouring n) :
    SchurianAt adj χ ↔ ∀ cid : Nat, ¬ Deepen.RigidObstructionAt adj χ cid := by
  constructor
  · rintro h cid ⟨u, w, hu, hw, hno⟩
    obtain ⟨σ, hσ, hσu⟩ := h cid u w hu hw
    exact hno σ hσ hσu
  · intro h cid
    by_contra hc
    exact h cid (Deepen.rigidObstruction_of_not_cellSingleOrbit adj χ cid hc)

/-- **A class of colourings closed under the descent's own step** — *peeling a layer keeps you in the
class*. This is the structural property that makes a per-family discharge finite: without it the
obligation would have to be re-earned at every node. (It is exactly why the `Tinhofer` reading is
tractable and the CFI reading is not: peeling a Tinhofer layer leaves a Tinhofer graph, whereas
peeling the CFI layer exposes whatever the CFI construction was built over.) -/
def StepClosed (P : Colouring n → Prop) (adj : AdjMatrix n) : Prop :=
  ∀ χ, P χ → ∀ v : Fin n, P (Deepen.step adj χ v).col

/-- **`TinhoferPath` at every fuel, for ANY step-closed obstruction-free class.** Induction on fuel:
the level's `CellSingleOrbit` is the class's Schurianity, and the recursive call stays in the class by
step-closure. -/
theorem tinhoferPath_of_stepClosed {adj : AdjMatrix n} {P : Colouring n → Prop}
    (hcl : StepClosed P adj) (hS : ∀ χ, P χ → SchurianAt adj χ) (χp : Colouring n) :
    ∀ (fuel : Nat) (cur : Refine.ColData n), P cur.col →
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
          refine ⟨hS _ hcur cid, ?_⟩
          cases hf : (List.finRange n).filter (fun v => cur.col v == cid) with
          | nil => trivial
          | cons w _ => exact ih _ (hcl _ hcur w)

/-- `Deepen.Tinhofer` for any colouring in the class. -/
theorem tinhofer_of_stepClosed {adj : AdjMatrix n} {P : Colouring n → Prop}
    (hcl : StepClosed P adj) (hS : ∀ χ, P χ → SchurianAt adj χ)
    {χ : Colouring n} (h : P χ) : Deepen.Tinhofer adj χ :=
  fun r _ => tinhoferPath_of_stepClosed hcl hS χ n _ (hcl χ h r)

/-! ## 4. The root condition — the ONLY thing a family has to earn -/

/-- The descent's root colouring. -/
def rootCol (adj : AdjMatrix n) : Colouring n :=
  Descend.refineV (Refine.encodeFreeFast (n := n)) adj (fun _ => 0)

/-- A step-closed class that holds at the root holds at **every reached node** — because
`Descend.Reaches`'s step and `Deepen.step` are the same operation
(`KeyComplete.step_col_eq_refineV`). So a family only ever has to earn the root. -/
theorem mem_of_reaches {adj : AdjMatrix n} {P : Colouring n → Prop}
    (hcl : StepClosed P adj) (hroot : P (rootCol adj)) {χ : Colouring n}
    (hr : Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ) : P χ := by
  induction hr with
  | root => exact hroot
  | step _ _ _ ih =>
      rw [← KeyComplete.step_col_eq_refineV]
      exact hcl _ ih _

/-- **★★★ THE SOCKET — stated on "no rigid obstruction", not on twins.** A step-closed class that
holds at the root and carries no rigid obstruction gives `Select.HandledS`: every reached non-discrete
node has a resolvable cell, so the fused resolver never stalls there.

▶ **How to extend the handled region**: supply a *wider* `P`. Nothing below this theorem changes —
which is the point of stating it here rather than at the twin layer. -/
theorem handledS_of_noRigidObstruction {adj : AdjMatrix n} {P : Colouring n → Prop}
    (hcl : StepClosed P adj) (hroot : P (rootCol adj))
    (hS : ∀ χ, P χ → SchurianAt adj χ) :
    Select.HandledS Deepen.orbKey Deepen.deepenSupply adj :=
  KeyComplete.handledS_of_reached_tinhofer
    (fun _ hr _ => tinhofer_of_stepClosed hcl hS (mem_of_reaches hcl hroot hr))

/-! ### 4.1 The twin class is one instance of the socket -/

/-- Twin-merging is step-closed (§2). -/
theorem stepClosed_twinCells (adj : AdjMatrix n) : StepClosed (TwinCells adj) adj :=
  fun _ h v => twinCells_step h v

/-- A twin-merging colouring is Schurian (§2). -/
theorem schurianAt_of_twinCells {adj : AdjMatrix n} (hs : Simple adj) :
    ∀ χ : Colouring n, TwinCells adj χ → SchurianAt adj χ :=
  fun _ h cid => cellSingleOrbit_of_twinCells hs h cid

/-- **The per-family obligation for the twin route**: every pair the ROOT colouring merges is a twin
pair. Definitionally `TwinCells adj (rootCol adj)`. -/
def RootTwins (adj : AdjMatrix n) : Prop :=
  TwinCells adj (rootCol adj)

/-- Every reached colouring merges only twin pairs. -/
theorem twinCells_of_reaches {adj : AdjMatrix n} (hR : RootTwins adj) {χ : Colouring n}
    (hr : Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ) : TwinCells adj χ :=
  mem_of_reaches (stepClosed_twinCells adj) hR hr

/-- The twin route into the socket. -/
theorem handledS_of_rootTwins {adj : AdjMatrix n} (hs : Simple adj) (hR : RootTwins adj) :
    Select.HandledS Deepen.orbKey Deepen.deepenSupply adj :=
  handledS_of_noRigidObstruction (stepClosed_twinCells adj) hR (schurianAt_of_twinCells hs)

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

⚠ **Scope of THIS section — `①` is not available at this key/supply pair.** The canonical-form half
(`Select.isCanonicalFormOptS_canonFormS?`) needs `NodeTransport`, hence
`SupplyTransport.SupplyEquivariant`; `deepenSupply` is not known to carry it, and `orbKey` is
`noncomputable` besides. That is a pre-existing boundary of the `(orbKey, deepenSupply)` pair — it is
why `deepenSupply` is held out of `Publication.canonForm?`'s record object — **not** a limitation of
the family. ▶ **§8 crosses it** by dropping both objects: under `TwinCells` the orbits are generated
by transpositions, so a computable twin supply certifies the cell directly and carries
`SupplyEquivariant` outright. Read §8 before quoting this section's weaker claim. -/

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

/-! ## 8. CROSSING THE ANSWERS → CANONIZED WALL — a COMPUTABLE twin supply

§7's gap is that `handledS_of_reached_tinhofer` is stated at `(orbKey, deepenSupply)`: `orbKey` is
`noncomputable` (its `TinhoferPath` guard is an `n!` search) and `deepenSupply` is not known
equivariant. Neither is needed. Under `TwinCells` the orbits are generated by **transpositions**, so a
supply that simply emits the twin transpositions of the branch cell certifies the cell **in one
`WordReach` step** — and it is computable, cheap, and a structural function of `(adj, χ)`.

That buys the strictly stronger **blind** predicate `Residue.Handled` (which demands the LEAST cell
resolve, and implies `Select.HandledS` by `Select.handledS_of_handled`), at a key of the caller's
choice — so the equivariant computable `HolKey.holKeyFast` can be used instead of `orbKey`. -/

instance decidableTwin (adj : AdjMatrix n) (u w : Fin n) : Decidable (Twin adj u w) := by
  unfold Twin; infer_instance

/-- **The twin supply**: every transposition of a twin pair inside the branch cell. Cost is the honest
enumeration bill (`|B|²` pairs, each an `n²` twin test). -/
def twinSupply : Consume.Supply n := fun adj χ =>
  let B := Descend.branches χ
  (B.flatMap (fun u => B.filterMap (fun w => if Twin adj u w then some (Equiv.swap u w) else none)),
   B.length * B.length * (n * n))

theorem mem_gens_twinSupply_iff {adj : AdjMatrix n} {χ : Colouring n} {g : Equiv.Perm (Fin n)} :
    g ∈ Consume.gens (twinSupply (n := n)) adj χ ↔
      ∃ u ∈ Descend.branches χ, ∃ w ∈ Descend.branches χ, Twin adj u w ∧ g = Equiv.swap u w := by
  constructor
  · intro hg
    obtain ⟨u, hu, hmem⟩ := List.mem_flatMap.mp hg
    obtain ⟨w, hw, hfm⟩ := List.mem_filterMap.mp hmem
    by_cases htw : Twin adj u w
    · rw [if_pos htw] at hfm
      exact ⟨u, hu, w, hw, htw, (Option.some.inj hfm).symm⟩
    · rw [if_neg htw] at hfm; exact absurd hfm (by simp)
  · rintro ⟨u, hu, w, hw, htw, rfl⟩
    exact List.mem_flatMap.mpr ⟨u, hu,
      List.mem_filterMap.mpr ⟨w, hw, by rw [if_pos htw]⟩⟩

/-- **★★ THE FIRING THEOREM FOR THE TWIN SUPPLY.** Under `TwinCells` the branch cell is a single orbit
of the *verified* twin transpositions — reached in ONE step, since the connecting permutation is itself
a generator. -/
theorem cellIsOrbit_twinSupply {adj : AdjMatrix n} (hs : Simple adj) {χ : Colouring n}
    (h : TwinCells adj χ) : Consume.CellIsOrbit (twinSupply (n := n)) adj χ := by
  intro u hu w hw
  by_cases huw : u = w
  · subst huw; exact Consume.WordReach.refl u
  obtain ⟨c, hc, huc⟩ := Consume.exists_targetColour_of_mem hu
  have hwc : χ w = c := (Descend.mem_branches_iff hc w).mp hw
  have hcol : χ u = χ w := by rw [huc, hwc]
  have htw : Twin adj u w := h u w hcol
  have hg : Equiv.swap u w ∈ Consume.verified (twinSupply (n := n)) adj χ :=
    List.mem_filter.mpr ⟨mem_gens_twinSupply_iff.mpr ⟨u, hu, w, hw, htw, rfl⟩,
      decide_eq_true (isColAut_swap_of_twin hs htw hcol)⟩
  have hstep := Consume.WordReach.step (Consume.WordReach.refl u) hg
  rwa [Equiv.swap_apply_left] at hstep

/-- **★★★ THE BLIND `Handled` PREDICATE — for EVERY key.** Strictly stronger than §7's `HandledS`
(`Select.handledS_of_handled`), and with no `orbKey`/`deepenSupply` anywhere. -/
theorem handled_of_rootTwins {adj : AdjMatrix n} (hs : Simple adj) (hR : RootTwins adj)
    (key : Force.Key n) : Residue.Handled key (twinSupply (n := n)) adj :=
  fun _ hr _ => Or.inl (cellIsOrbit_twinSupply hs (twinCells_of_reaches hR hr))

/-- The named family, at the blind predicate. -/
theorem handled_of_multipartite {adj : AdjMatrix n} {part : Fin n → Nat}
    (hM : IsCompleteMultipartite adj part) (hD : DistinctPartSizes part) (key : Force.Key n) :
    Residue.Handled key (twinSupply (n := n)) adj :=
  handled_of_rootTwins (simple_of_multipartite hM) (rootTwins_of_multipartite hM hD) key

/-- **★★★ THE GUARDED CANONIZER ANSWERS ON THE FAMILY** — the `②` half at a *computable* key and
supply. `Residue.answers_of_handled` needs only `Handled`, no equivariance. -/
theorem answers_of_multipartite {adj : AdjMatrix n} {part : Fin n → Nat}
    (hM : IsCompleteMultipartite adj part) (hD : DistinctPartSizes part) (key : Force.Key n) :
    Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume key (twinSupply (n := n)))) adj ≠ none :=
  Residue.answers_of_handled (handled_of_multipartite hM hD key)

/-! ### 8.1 The twin supply is EQUIVARIANT — and that closes `①`

`Residue.guarded_mixed_canonizer` carries `KeyEquivariant` + `StallEquivariant`, and
`SupplyTransport.stallEquivariant_forceThenConsume` discharges the second from `SupplyEquivariant`.
The twin supply is a **structural function of `(adj, χ)`** — the case `SupplyTransport`'s own
doc-block calls free — so its generators σ-conjugate, and the conjugate of a transposition is the
transposition of the images. -/

/-- `Twin` transports: on the relabelled graph the twin pairs are exactly the `σ`-images. -/
theorem twin_relabel {adj : AdjMatrix n} (σ : Equiv.Perm (Fin n)) (u w : Fin n) :
    Twin (relabelAdj σ adj) (σ u) (σ w) ↔ Twin adj u w := by
  constructor
  · intro h s hsu hsw
    have hs' := h (σ s) (fun hc => hsu (σ.injective hc)) (fun hc => hsw (σ.injective hc))
    simpa using hs'
  · intro h s hsu hsw
    have hs' := h (σ.symm s)
      (fun hc => hsu (by rw [← hc]; simp)) (fun hc => hsw (by rw [← hc]; simp))
    simpa using hs'

theorem gensEquivariant_twinSupply :
    SupplyTransport.GensEquivariant (twinSupply (n := n)) := by
  intro σ adj χ g
  have hbr : ∀ x, x ∈ Descend.branches (transportColouring σ χ) ↔
      ∃ y ∈ Descend.branches χ, σ y = x := by
    intro x
    rw [(Descend.branches_transport_perm σ χ).mem_iff, List.mem_map]
  simp only [mem_gens_twinSupply_iff]
  constructor
  · rintro ⟨a, ha, b, hb, htw, rfl⟩
    obtain ⟨u, hu, rfl⟩ := (hbr a).mp ha
    obtain ⟨w, hw, rfl⟩ := (hbr b).mp hb
    exact ⟨Equiv.swap u w, ⟨u, hu, w, hw, (twin_relabel σ u w).mp htw, rfl⟩,
      Equiv.swap_apply_apply σ u w⟩
  · rintro ⟨h, ⟨u, hu, w, hw, htw, rfl⟩, rfl⟩
    exact ⟨σ u, (hbr _).mpr ⟨u, hu, rfl⟩, σ w, (hbr _).mpr ⟨w, hw, rfl⟩,
      (twin_relabel σ u w).mpr htw, (Equiv.swap_apply_apply σ u w).symm⟩

theorem supplyEquivariant_twinSupply :
    SupplyTransport.SupplyEquivariant (twinSupply (n := n)) :=
  SupplyTransport.supplyEquivariant_of_gensEquivariant gensEquivariant_twinSupply

/-- **★★★ `①` FOR THE TWIN-SUPPLY CANONIZER** — sound and iso-invariant, hence (with
`Descend.canonForm?_complete`) complete. Note this is a statement about the *function*, independent of
any family: the family enters only through `answers_of_multipartite`, which says it never flags. -/
theorem canonizer_twinSupply :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (Hol.holKeyFast (n := n))
          (twinSupply (n := n))))) :=
  Residue.guarded_mixed_canonizer Hol.keyEquivariant_holKeyFast
    (SupplyTransport.stallEquivariant_forceThenConsume Hol.keyEquivariant_holKeyFast
      supplyEquivariant_twinSupply)

/-- **★★★ THE FAMILY IS CANONIZED — the publication-shaped statement, both halves.**
`①` (sound + iso-invariant + complete) from `canonizer_twinSupply`, and *it answers* — never flags —
on every complete multipartite graph with distinct part sizes. Both at a **computable** key and
supply, with the guard in place, so the descent is also single-path. -/
theorem canonized_of_multipartite {adj : AdjMatrix n} {part : Fin n → Nat}
    (hM : IsCompleteMultipartite adj part) (hD : DistinctPartSizes part) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (Hol.holKeyFast (n := n))
          (twinSupply (n := n)))))
    ∧ Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (Hol.holKeyFast (n := n))
          (twinSupply (n := n)))) adj ≠ none :=
  ⟨canonizer_twinSupply, answers_of_multipartite hM hD _⟩

/-- The concrete `K₁,₂,₃` witness, canonized. -/
theorem canonized_part123 :
    Descend.canonForm? (Refine.encodeFreeFast (n := 6))
      (Stall.guard (Composite.forceThenConsume (Hol.holKeyFast (n := 6))
        (twinSupply (n := 6)))) (mpAdj part123) ≠ none :=
  answers_of_multipartite (isCompleteMultipartite_mpAdj part123) distinctPartSizes_part123 _

/-! ## 9. ★★★ THE LITERATURE BRIDGE — Tinhofer graphs PROGRESS

The point of §3's socket is that it is fed by a *class*, and the widest class worth naming is the
literature's own. This section supplies it, and it costs almost nothing, because the class is
**step-closed by construction** — no CAO-propagation obligation appears anywhere.

**Why this is the leverage.** One theorem here covers every family known to be Tinhofer, by citation
of membership rather than by new Lean: trees and cycles (compact — Tinhofer 1986), complete graphs
(Birkhoff), matchings `mK₂`, complete multipartite (§5, proved natively here), and everything in
`Discrete ⊂ Amenable ⊂ Compact ⊂ Godsil ⊂ Tinhofer` (Arvind–Köbler–Rattan–Verbitsky), which is closed
under complement and under `G ↦ mG`. Per-family Lean proofs do not pay for themselves against that.

**⚠ The hypothesis is deliberately NOT computable, and that is correct.** `TinhoferGraph` is a
*classifier*, not part of the algorithm: deciding it is at least as hard as GI on vertex-transitive
graphs (AKRV Thm 22). What the artifact needs — and what is proved here — is the implication
*"if it IS Tinhofer, the descent progresses"*, whose contrapositive
(`not_tinhoferGraph_of_flagS`) is the showcase statement: **if the canonizer flags, the input is
provably not Tinhofer.** That is `③`'s shape against a *named literature class* instead of opaque
structural atoms.

**⚠ Naming, stated precisely.** `IndivReach` ranges over exactly the colourings AKRV write `P_F` (the
1-WL-stable colouring after individualizing a sequence `F`), and `SchurianAt` says each of its cells
is one orbit of `IsColAut adj P_F`, the colour-stabilizer. The identification of that stabilizer with
AKRV's pointwise stabilizer `Aut_F` is standard (individualized vertices carry unique colours, and
1-WL is isomorphism-invariant) but is **prose here, not a Lean theorem** — the paper must say so.
Contrast §7's `Deepen.Tinhofer`, which is the strictly weaker *path-local* predicate. -/

/-- **The individualization closure** — every colouring reachable from the refined root by
individualizing a vertex and refining, under **any** sequence of choices. Step-closure is definitional,
which is exactly why this class costs nothing to feed to §4's socket. -/
inductive IndivReach (adj : AdjMatrix n) : Colouring n → Prop
  | root : IndivReach adj (rootCol adj)
  | step {χ : Colouring n} (h : IndivReach adj χ) (v : Fin n) :
      IndivReach adj (Deepen.step adj χ v).col

theorem stepClosed_indivReach (adj : AdjMatrix n) : StepClosed (IndivReach adj) adj :=
  fun _ h v => IndivReach.step h v

/-- **`TinhoferGraph`** — the literature's Tinhofer condition in the project's vocabulary: at every
individualization-reachable colouring, every cell is a single orbit, i.e. **no rigid obstruction
anywhere, under any selector**. -/
def TinhoferGraph (adj : AdjMatrix n) : Prop :=
  ∀ χ : Colouring n, IndivReach adj χ → SchurianAt adj χ

/-- **★★★ THE BRIDGE.** A Tinhofer graph is `HandledS`: every reached non-discrete node has a
resolvable cell, so the descent progresses at every step. -/
theorem handledS_of_tinhoferGraph {adj : AdjMatrix n} (h : TinhoferGraph adj) :
    Select.HandledS Deepen.orbKey Deepen.deepenSupply adj :=
  handledS_of_noRigidObstruction (stepClosed_indivReach adj) IndivReach.root h

/-- **★★ A Tinhofer graph ANSWERS** — the fused descent never flags on it. -/
theorem answersS_of_tinhoferGraph {adj : AdjMatrix n} (h : TinhoferGraph adj) :
    Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) Deepen.orbKey Deepen.deepenSupply) adj
      ≠ none :=
  Select.answersS_of_handledS (handledS_of_tinhoferGraph h)

/-- **★★★ THE SHOWCASE STATEMENT — the flag is evidence about the INPUT.** If the canonizer flags,
the graph is provably **not Tinhofer**. This is `③`'s shape against a named literature class rather
than an opaque structural atom, and it is the contrapositive the classifier's non-computability makes
the *useful* direction. -/
theorem not_tinhoferGraph_of_flagS {adj : AdjMatrix n}
    (hflag : Select.canonFormS? (Refine.encodeFreeFast (n := n))
      (Select.selNode (Refine.encodeFreeFast (n := n)) Deepen.orbKey Deepen.deepenSupply) adj
        = none) :
    ¬ TinhoferGraph adj :=
  fun h => answersS_of_tinhoferGraph h hflag

/-! ### 9.1 The class is inhabited — two independent witnesses

⚠ Non-vacuity is load-bearing here for the same reason as everywhere else in this file: a bridge whose
hypothesis nothing satisfies proves nothing. -/

/-- Every individualization-reachable colouring of a root-twin graph merges only twin pairs. -/
theorem twinCells_of_indivReach {adj : AdjMatrix n} (hR : RootTwins adj) {χ : Colouring n}
    (h : IndivReach adj χ) : TwinCells adj χ := by
  induction h with
  | root => exact hR
  | step _ v ih => exact twinCells_step ih v

/-- **Witness 1 — the twin/multipartite family is Tinhofer.** -/
theorem tinhoferGraph_of_rootTwins {adj : AdjMatrix n} (hs : Simple adj) (hR : RootTwins adj) :
    TinhoferGraph adj :=
  fun _ h => schurianAt_of_twinCells hs _ (twinCells_of_indivReach hR h)

theorem tinhoferGraph_of_multipartite {adj : AdjMatrix n} {part : Fin n → Nat}
    (hM : IsCompleteMultipartite adj part) (hD : DistinctPartSizes part) : TinhoferGraph adj :=
  tinhoferGraph_of_rootTwins (simple_of_multipartite hM) (rootTwins_of_multipartite hM hD)

/-- Individualization-reachable colourings of a 1-WL-discretizing graph stay discrete. -/
theorem discrete_of_indivReach {adj : AdjMatrix n} (hd : Discrete (rootCol adj)) {χ : Colouring n}
    (h : IndivReach adj χ) : Discrete χ := by
  induction h with
  | root => exact hd
  | step _ v ih =>
      intro x y hxy
      rw [KeyComplete.step_col_eq_refineV] at hxy
      have hind := Refine.refineSplits_encodeFreeFast (n := n) adj (Descend.indivOne _ v) x y hxy
      exact ih x y (indivOne_splits _ v x y hind)

/-- **★★ Witness 2 — every 1-WL-discretizing graph is Tinhofer.** A discrete colouring has only
singleton cells, so `SchurianAt` is witnessed by the identity.

★ **This is the largest coverage statement the artifact has**: by Babai–Erdős–Selkow, 1-WL discretizes
a random graph with high probability, so *almost all graphs* land in this ring — and hence, through
the bridge, progress. (The measure claim is the citation; the implication is this theorem.)

⚠⚠ **BUT DO NOT OVERSELL IT — the resolvers do no work here.** On a root-discrete graph `HandledS`
holds **vacuously**: there is no reached non-discrete node, refinement alone finishes, and neither
consume nor force is ever consulted (`Residue.handled_of_root_discrete` says exactly this). So this
witness demonstrates *breadth of the answering claim*, *not* that the resolver architecture does
anything. The witness that exercises the resolvers is the twin/multipartite one — which is why
`not_discrete_part123` is proved alongside it. A write-up that quotes the measure claim without this
caveat is claiming credit refinement earned. -/
theorem tinhoferGraph_of_root_discrete {adj : AdjMatrix n} (hd : Discrete (rootCol adj)) :
    TinhoferGraph adj := by
  intro χ h cid u w hu hw
  have hdχ : Discrete χ := discrete_of_indivReach hd h
  have : u = w := hdχ u w (hu.trans hw.symm)
  exact ⟨1, Consume.IsColAut.one adj χ, by simpa using this⟩

end TwinFamily
end ChainDescent
