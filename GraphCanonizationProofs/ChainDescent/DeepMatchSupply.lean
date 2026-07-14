import ChainDescent.SupplyTransport

/-!
# `P2` — `deepMatchSupply d` : the BOUNDED-DEPTH oracle

## The problem

`matchSupply` (the one-step colour match) fires only at a **`Discretizing`** node. That is far stronger than it
sounds: an automorphism **fixing** a branch vertex `v` preserves `indivOne χ v`, hence (refiner equivariance) its
refinement — and a **discrete** colouring preserved by it forces it to be the identity. So

> **`Discretizing` ⟹ every branch vertex has a TRIVIAL POINT STABILIZER**,

and with `CellIsOrbit` (transitivity) `matchSupply` certifies a cell only under a **regular action**. `C₅` and `C₇`
fail not because they are cycles but because their dihedral groups have a **reflection fixing each vertex**. The
residue was inflated by every graph with a non-trivial point stabilizer — i.e. most of them.

## Why the obvious fixes are dead

* **A recursive stabilizer chain** must *pick* a vertex whose stabilizer it recurses into. Any deterministic pick
  (least index) is **not equivariant**, so the harvested generators are not `σ`-conjugates and
  `SupplyTransport.GensEquivariant` — hence `①c` — **fails**. Unioning over the whole cell restores equivariance at
  `|cell|^depth` cost.
* **Porting `CascadeOracle.matchOracleSet` / `matchOracleSeq`** is refuted by the project's own
  **`lockstep_disc_imp_stab_trivial`**: an *equivariant* multi-step deepening rule whose footprint discretizes forces
  `stab(v) = 1` — exactly the regime `matchSupply` already covers.
* **The C# `DeepenAnchor`/`ReplayDeepening`** individualizes the *lowest-index* vertex of the recorded cell, which is
  not equivariant either. It is a heuristic-with-verification (sound over-split on failure), not a theorem.

## The fix: make no choice at all

Enumerate **every** individualization sequence of length `≤ d`, on both sides, and colour-match all pairs. Then

* **equivariance is free** — the enumeration is characterized purely by **length** (`mem_allSeqs`), so `σ` maps it
  onto itself and no choice is ever made. `lockstep_disc_imp_stab_trivial` does not apply: it constrains an
  equivariant `expand` *function*, and there is none here.
* **the deepening is the descent's own step** — `indivOne` then refine, iterated (`deepCol`). It is index-free, so
  it transports (`deepCol_transport`), and it gives position-distinct colours, which the uniform set-colouring
  `indivWithSet` was forced into and could not.
* **the candidate is still untrusted** — `Consume.verified` re-checks it, so soundness is free as always.

## What it reaches, stated honestly

> **`SeparatesAt adj χ d`** — every branch vertex, plus **some** sequence of `≤ d` further individualizations,
> discretizes.

That is the descent-side form of the seal's **`SeparatesAtBoundedBase`** (Spielman's hypothesis), and
`SealBridge.horb_of_cellsAreOrbits` supplies the other half (`CellsAreOrbits`, the seal's carried localisation).
`separatesAt_zero_iff` shows `matchSupply` is the `d = 0` case, so this is a strict generalization.

**Cost is `n^{O(d)}`** (`|cell| · n^d` refinements, then a pairwise match). **Polynomial for bounded `d`;
sub-exponential at Spielman's `d = Õ(n^{1/3})`.** That is exactly the seal's own boundary — *poly to consume all
symmetry unless Node-4/Cameron, then quasi-poly* — and the polynomial base case is exactly the open one
(`hSmallAutThin`). The cost is **billed in `supplyCost`**, so `②` sees it.
-/

namespace ChainDescent
namespace DeepMatch

open ChainDescent.CostModel (CostM)
open ChainDescent.Descend
open ChainDescent.Consume (Supply gens verified IsColAut WordReach CellIsOrbit matchCol)
open ChainDescent.Force (Key KeyEquivariant)
open ChainDescent.Composite (forceThenConsume)
open ChainDescent.SupplyTransport (GensEquivariant SupplyEquivariant)

variable {n : Nat}

/-! ## 1. The enumeration — characterised by LENGTH, hence equivariant for free -/

/-- All sequences of vertices of length exactly `k`. -/
def seqsLen (n : Nat) : Nat → List (List (Fin n))
  | 0 => [[]]
  | k + 1 => (List.finRange n).flatMap (fun v => (seqsLen n k).map (fun s => v :: s))

theorem mem_seqsLen (k : Nat) (s : List (Fin n)) : s ∈ seqsLen n k ↔ s.length = k := by
  induction k generalizing s with
  | zero => simp [seqsLen, List.length_eq_zero_iff]
  | succ k ih =>
      constructor
      · intro h
        obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp h
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
        simp [(ih t).mp ht]
      · intro h
        cases s with
        | nil => simp at h
        | cons v t =>
            refine List.mem_flatMap.mpr ⟨v, List.mem_finRange v, ?_⟩
            exact List.mem_map.mpr ⟨t, (ih t).mpr (by simpa using h), rfl⟩

/-- **The search space: every sequence of length `≤ d`.** No representative is ever *chosen* — which is the whole
point (a choice would break `GensEquivariant`, hence `①c`). -/
def allSeqs (n d : Nat) : List (List (Fin n)) :=
  (List.range (d + 1)).flatMap (seqsLen n)

theorem mem_allSeqs (d : Nat) (s : List (Fin n)) : s ∈ allSeqs n d ↔ s.length ≤ d := by
  unfold allSeqs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨k, hk, hs⟩
    rw [List.mem_range] at hk
    rw [(mem_seqsLen k s).mp hs]
    omega
  · intro h
    exact ⟨s.length, List.mem_range.mpr (by omega), (mem_seqsLen _ s).mpr rfl⟩

/-- **★ THE SEARCH SPACE IS `σ`-INVARIANT**, and trivially so — membership depends only on the **length**. This one
line is why the bounded-depth oracle escapes `lockstep_disc_imp_stab_trivial`. -/
theorem mem_allSeqs_map (σ : Equiv.Perm (Fin n)) (d : Nat) (s : List (Fin n)) :
    s.map σ ∈ allSeqs n d ↔ s ∈ allSeqs n d := by
  rw [mem_allSeqs, mem_allSeqs, List.length_map]

theorem exists_preimage_seq (σ : Equiv.Perm (Fin n)) (d : Nat) {s : List (Fin n)}
    (h : s ∈ allSeqs n d) : ∃ t ∈ allSeqs n d, t.map σ = s :=
  ⟨s.map σ.symm, (mem_allSeqs_map σ.symm d s).mpr h, by simp [List.map_map]⟩

/-! ## 2. The deep colouring — the descent's own step, iterated -/

/-- **The colouring reached by individualizing `s` in order, refining after each.** This is *literally* what
`descend` does along the path `s`; it is index-free, so it **transports** (`deepCol_transport`) — which the seal's
`indivWithSeq` (index-coloured) does not, and which its `indivWithSet` (uniform-coloured) bought only by giving up
discretization *within* the explored set.

⚠ **Spec only — never evaluated.** Its type ends in `Colouring n`, so it is subject to the eta-expansion trap
(`Refine.lean` §4); the executable path goes through `deepData`, tied to it by `deepData_col`. -/
def deepCol (adj : AdjMatrix n) : Colouring n → List (Fin n) → Colouring n
  | χ, [] => χ
  | χ, v :: s => deepCol adj (Refine.warmRefineR adj (indivOne χ v)) s

/-- The **materialised** version — `ColData`-valued, so each level's colouring is forced **once**. -/
def deepData (adj : AdjMatrix n) : Refine.ColData n → List (Fin n) → Refine.ColData n
  | c, [] => c
  | c, v :: s => deepData adj (Refine.warmRefineVec adj (indivOne c.col v)) s

/-- The runnable version computes exactly the reasoned-about one (`Refine.warmRefineVec_col_eq`, lifted). -/
theorem deepData_col (adj : AdjMatrix n) : ∀ (s : List (Fin n)) (c : Refine.ColData n),
    (deepData adj c s).col = deepCol adj c.col s := by
  intro s
  induction s with
  | nil => intro c; rfl
  | cons v t ih =>
      intro c
      show (deepData adj (Refine.warmRefineVec adj (indivOne c.col v)) t).col
          = deepCol adj (Refine.warmRefineR adj (indivOne c.col v)) t
      rw [ih, Refine.warmRefineVec_col_eq]

/-- **★ THE DEEP COLOURING TRANSPORTS.** (`indivOne` is index-free; the refiner is equivariant.) -/
theorem deepCol_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) :
    ∀ (s : List (Fin n)) (χ : Colouring n),
      deepCol (relabelAdj σ adj) (transportColouring σ χ) (s.map σ)
        = transportColouring σ (deepCol adj χ s) := by
  intro s
  induction s with
  | nil => intro χ; rfl
  | cons v t ih =>
      intro χ
      show deepCol (relabelAdj σ adj)
            (Refine.warmRefineR (relabelAdj σ adj) (indivOne (transportColouring σ χ) (σ v))) (t.map σ)
          = transportColouring σ (deepCol adj (Refine.warmRefineR adj (indivOne χ v)) t)
      rw [indivOne_transport σ χ v]
      have he : Refine.warmRefineR (relabelAdj σ adj) (transportColouring σ (indivOne χ v))
          = transportColouring σ (Refine.warmRefineR adj (indivOne χ v)) := by
        simpa [Refine.refineV_encodeFree] using
          Refine.refineEquivariant_encodeFree σ adj (indivOne χ v)
      rw [he, ih]

/-! ## 3. The candidate — construct, do not trust -/

/-- Individualize `v` then `sv`; individualize `w` then `sw`; if both discretize, colour-match. -/
def deepCandidate (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) (sv : List (Fin n))
    (w : Fin n) (sw : List (Fin n)) : Option (Equiv.Perm (Fin n)) :=
  matchCol (deepCol adj χ (v :: sv)) (deepCol adj χ (w :: sw))

/-- A discrete colouring and its `α`-transport colour-match to **exactly `α`**. -/
theorem matchCol_self_transport (α : Equiv.Perm (Fin n)) {ψ : Colouring n} (hd : Discrete ψ) :
    matchCol ψ (transportColouring α ψ) = some α := by
  have hd' : Discrete (transportColouring α ψ) := (discrete_transport α ψ).mpr hd
  unfold Consume.matchCol
  rw [dif_pos hd, dif_pos hd']
  congr 1
  refine Equiv.ext (fun u => ?_)
  show rankInv (transportColouring α ψ) (Colouring.vertexRank ψ u) = α u
  rw [Consume.rankInv_transport α hd]
  congr 1
  have hinj : Function.Injective (Colouring.vertexRank ψ) := fun a b hab =>
    (Colouring.rankPerm ψ hd).injective hab
  exact hinj (rankInv_spec ψ hd _)

/-- **★★ THE ORACLE RECONSTRUCTS THE AUTOMORPHISM EXACTLY, AT DEPTH.**

If `α` is a colouring-preserving automorphism and individualizing `v` **followed by `s`** discretizes, then the
pair `(v, s)` against `(α v, α·s)` constructs **`α` itself**. And `α·s` has the *same length* as `s`, so it is in
the search space — **that is the entire content of the design**: we never have to *guess* `α`'s continuation,
because we enumerate all of them. -/
theorem deepCandidate_eq_of_isColAut {adj : AdjMatrix n} {χ : Colouring n} {α : Equiv.Perm (Fin n)}
    (hα : IsColAut adj χ α) (v : Fin n) (s : List (Fin n))
    (hdisc : Discrete (deepCol adj χ (v :: s))) :
    deepCandidate adj χ v s (α v) (s.map α) = some α := by
  have ht : deepCol adj χ (α v :: s.map α) = transportColouring α (deepCol adj χ (v :: s)) := by
    have h := deepCol_transport α adj (v :: s) χ
    rw [hα.relabel, hα.transport] at h
    simpa using h
  unfold deepCandidate
  rw [ht]
  exact matchCol_self_transport α hdisc

/-- The candidate conjugates — the engine of `GensEquivariant`. -/
theorem deepCandidate_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (v : Fin n) (sv : List (Fin n)) (w : Fin n) (sw : List (Fin n)) :
    deepCandidate (relabelAdj σ adj) (transportColouring σ χ) (σ v) (sv.map σ) (σ w) (sw.map σ)
      = (deepCandidate adj χ v sv w sw).map (fun t => σ * t * σ⁻¹) := by
  have h1 : deepCol (relabelAdj σ adj) (transportColouring σ χ) (σ v :: sv.map σ)
      = transportColouring σ (deepCol adj χ (v :: sv)) := by
    simpa using deepCol_transport σ adj (v :: sv) χ
  have h2 : deepCol (relabelAdj σ adj) (transportColouring σ χ) (σ w :: sw.map σ)
      = transportColouring σ (deepCol adj χ (w :: sw)) := by
    simpa using deepCol_transport σ adj (w :: sw) χ
  unfold deepCandidate
  rw [h1, h2, Consume.matchCol_transport]

/-! ## 4. The supply -/

/-- The `(branch, sequence)` table, with each deep colouring **materialised once**.

⚠ The per-branch base refinement is bound **outside** the sequence loop. Recomputing it per sequence would be
`|cell| · n^d` refinements where `|cell|` suffice — the same `O(n)`-in-the-algorithm bug `matchSupply` shipped with
(standing Lean trap #2). -/
def deepTable (adj : AdjMatrix n) (χ : Colouring n) (d : Nat) :
    List ((Fin n × List (Fin n)) × Refine.ColData n) :=
  (branches χ).flatMap (fun v =>
    let base : Refine.ColData n := Refine.warmRefineVec adj (indivOne χ v)
    (allSeqs n d).map (fun s => ((v, s), deepData adj base s)))

theorem mem_deepTable_iff {adj : AdjMatrix n} {χ : Colouring n} {d : Nat}
    {p : (Fin n × List (Fin n)) × Refine.ColData n} :
    p ∈ deepTable adj χ d ↔ ∃ v ∈ branches χ, ∃ s ∈ allSeqs n d,
      p = ((v, s), deepData adj (Refine.warmRefineVec adj (indivOne χ v)) s) := by
  unfold deepTable
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨v, hv, hp⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
    exact ⟨v, hv, s, hs, rfl⟩
  · rintro ⟨v, hv, s, hs, rfl⟩
    exact ⟨v, hv, List.mem_map.mpr ⟨s, hs, rfl⟩⟩

/-- Every table row's colouring **is** the deep colouring it is indexed by. -/
theorem deepTable_col {adj : AdjMatrix n} {χ : Colouring n} {d : Nat}
    {p : (Fin n × List (Fin n)) × Refine.ColData n} (hp : p ∈ deepTable adj χ d) :
    p.2.col = deepCol adj χ (p.1.1 :: p.1.2) := by
  obtain ⟨v, _, s, _, rfl⟩ := mem_deepTable_iff.mp hp
  show (deepData adj (Refine.warmRefineVec adj (indivOne χ v)) s).col
      = deepCol adj (Refine.warmRefineR adj (indivOne χ v)) s
  rw [deepData_col, Refine.warmRefineVec_col_eq]

/-- **★ THE BOUNDED-DEPTH ORACLE.** Colour-match every `(branch, sequence≤d)` pair against every other. Untrusted:
`Consume.verified` re-checks each candidate, so `consume_canonizer` holds for it with no obligation. -/
def deepMatchSupply (d : Nat) : Supply n := fun adj χ =>
  let table := deepTable adj χ d
  (table.flatMap (fun p => table.filterMap (fun q => matchCol p.2.col q.2.col)),
   table.length * (d + 1) * CostModel.WarmRefine.warmRefineCost n
     + table.length * table.length * (n * n))

theorem mem_gens_deepMatchSupply_iff {d : Nat} {adj : AdjMatrix n} {χ : Colouring n}
    {g : Equiv.Perm (Fin n)} :
    g ∈ gens (deepMatchSupply (n := n) d) adj χ ↔
      ∃ v ∈ branches χ, ∃ sv ∈ allSeqs n d, ∃ w ∈ branches χ, ∃ sw ∈ allSeqs n d,
        deepCandidate adj χ v sv w sw = some g := by
  constructor
  · intro hg
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hg
    obtain ⟨q, hq2, hmc⟩ := List.mem_filterMap.mp hq
    rw [deepTable_col hp, deepTable_col hq2] at hmc
    obtain ⟨v, hv, sv, hsv, rfl⟩ := mem_deepTable_iff.mp hp
    obtain ⟨w, hw, sw, hsw, rfl⟩ := mem_deepTable_iff.mp hq2
    exact ⟨v, hv, sv, hsv, w, hw, sw, hsw, hmc⟩
  · rintro ⟨v, hv, sv, hsv, w, hw, sw, hsw, hmc⟩
    refine List.mem_flatMap.mpr ⟨_, mem_deepTable_iff.mpr ⟨v, hv, sv, hsv, rfl⟩, ?_⟩
    refine List.mem_filterMap.mpr ⟨_, mem_deepTable_iff.mpr ⟨w, hw, sw, hsw, rfl⟩, ?_⟩
    show matchCol (deepData adj (Refine.warmRefineVec adj (indivOne χ v)) sv).col
        (deepData adj (Refine.warmRefineVec adj (indivOne χ w)) sw).col = some g
    rw [deepData_col, deepData_col, Refine.warmRefineVec_col_eq, Refine.warmRefineVec_col_eq]
    exact hmc

/-! ## 5. `①c` — the supply is equivariant -/

/-- **★★ THE BOUNDED-DEPTH ORACLE IS EQUIVARIANT** — because the search space is `σ`-invariant (`mem_allSeqs_map`)
and the deep colouring transports. **No representative is ever chosen**, which is exactly what a stabilizer-chain
supply could not arrange. -/
theorem gensEquivariant_deepMatchSupply (d : Nat) :
    GensEquivariant (deepMatchSupply (n := n) d) := by
  intro σ adj χ g
  have hbr : ∀ x : Fin n, x ∈ branches (transportColouring σ χ) ↔ ∃ y ∈ branches χ, σ y = x := by
    intro x
    rw [(branches_transport_perm σ χ).mem_iff, List.mem_map]
  simp only [mem_gens_deepMatchSupply_iff]
  constructor
  · rintro ⟨v, hv, sv, hsv, w, hw, sw, hsw, hmc⟩
    obtain ⟨v₀, hv₀, rfl⟩ := (hbr v).mp hv
    obtain ⟨w₀, hw₀, rfl⟩ := (hbr w).mp hw
    obtain ⟨sv₀, hsv₀, rfl⟩ := exists_preimage_seq σ d hsv
    obtain ⟨sw₀, hsw₀, rfl⟩ := exists_preimage_seq σ d hsw
    rw [deepCandidate_conj] at hmc
    rcases hcase : deepCandidate adj χ v₀ sv₀ w₀ sw₀ with _ | t
    · rw [hcase] at hmc; simp at hmc
    · rw [hcase] at hmc
      simp only [Option.map_some, Option.some.injEq] at hmc
      exact ⟨t, ⟨v₀, hv₀, sv₀, hsv₀, w₀, hw₀, sw₀, hsw₀, hcase⟩, hmc.symm⟩
  · rintro ⟨h, ⟨v, hv, sv, hsv, w, hw, sw, hsw, hmc⟩, rfl⟩
    refine ⟨σ v, (hbr _).mpr ⟨v, hv, rfl⟩, sv.map σ, (mem_allSeqs_map σ d sv).mpr hsv,
            σ w, (hbr _).mpr ⟨w, hw, rfl⟩, sw.map σ, (mem_allSeqs_map σ d sw).mpr hsw, ?_⟩
    rw [deepCandidate_conj, hmc]
    rfl

theorem supplyEquivariant_deepMatchSupply (d : Nat) :
    SupplyEquivariant (deepMatchSupply (n := n) d) :=
  SupplyTransport.supplyEquivariant_of_gensEquivariant (gensEquivariant_deepMatchSupply d)

/-! ## 6. ★★★ FIRING — the seal's `SeparatesAtBoundedBase`, in the descent's vocabulary -/

/-- **The depth witness.** Every branch vertex, plus **some** sequence of `≤ d` further individualizations,
discretizes. This is the descent-side form of `Cascade.SeparatesAtBoundedBase` (Spielman's hypothesis), and it is
the *only* thing the oracle needs beyond localisation. -/
def SeparatesAt (adj : AdjMatrix n) (χ : Colouring n) (d : Nat) : Prop :=
  ∀ v ∈ branches χ, ∃ s : List (Fin n), s.length ≤ d ∧ Discrete (deepCol adj χ (v :: s))

/-- **`matchSupply` is the `d = 0` case** — `SeparatesAt … 0` *is* `Consume.Discretizing`. So the bounded-depth
oracle is a strict generalization, not a replacement. -/
theorem separatesAt_zero_iff (adj : AdjMatrix n) (χ : Colouring n) :
    SeparatesAt adj χ 0 ↔ Consume.Discretizing adj χ := by
  constructor
  · intro h v hv
    obtain ⟨s, hs, hd⟩ := h v hv
    have : s = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hs)
    subst this
    rw [Consume.lookData_col]
    exact hd
  · intro h v hv
    refine ⟨[], le_refl 0, ?_⟩
    have := h v hv
    rwa [Consume.lookData_col] at this

/-- **★★★ THE ORACLE FIRES.** Given the **depth** witness (`SeparatesAt`) and **localisation** (`horb` — which
`SealBridge.horb_of_cellsAreOrbits` imports straight from the seal's `CellsAreOrbits`), `deepMatchSupply d`
certifies the branch cell as an orbit and `consume` collapses it to one branch.

The proof is the design in one line: take `α` from localisation and `s` from the depth witness; then `α·s` has the
**same length** as `s`, so it is in the search space, so the pair `(v, s) / (α v, α·s)` **is enumerated** and
reconstructs `α` exactly. No guessing, no lockstep, no choice. -/
theorem cellIsOrbit_deepMatchSupply {d : Nat} {adj : AdjMatrix n} {χ : Colouring n}
    (hsep : SeparatesAt adj χ d)
    (horb : ∀ u ∈ branches χ, ∀ w ∈ branches χ,
      ∃ α : Equiv.Perm (Fin n), IsColAut adj χ α ∧ α u = w) :
    CellIsOrbit (deepMatchSupply (n := n) d) adj χ := by
  intro u hu w hw
  obtain ⟨α, hα, hαu⟩ := horb u hu w hw
  obtain ⟨s, hs, hdisc⟩ := hsep u hu
  have hmem : α ∈ verified (deepMatchSupply (n := n) d) adj χ := by
    refine List.mem_filter.mpr ⟨?_, by simpa using hα⟩
    refine mem_gens_deepMatchSupply_iff.mpr
      ⟨u, hu, s, (mem_allSeqs d s).mpr hs, α u, by rw [hαu]; exact hw,
       s.map α, (mem_allSeqs d _).mpr (by simpa using hs), ?_⟩
    exact deepCandidate_eq_of_isColAut hα u s hdisc
  have hstep := (Consume.WordReach.refl
    (G := verified (deepMatchSupply (n := n) d) adj χ) u).step hmem
  rwa [hαu] at hstep

/-! ## 7. ★★★ THE CAPSTONE -/

/-- **★★★ THE BOUNDED-DEPTH MIXED CANONIZER.** Sound, complete, iso-invariant (answer **and** flag), and
unconditionally polynomial in the descent — for **every** depth `d`, with **no carried hypothesis**. `d` buys
*firing*, never correctness: raising it can only shrink `Residue.Handled`'s complement, and it is billed in
`supplyCost` so `②` sees the price. -/
theorem deepMatchSupply_guarded_canonizer (d : Nat) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume (Force.lookaheadKey (n := n))
          (deepMatchSupply (n := n) d)))) :=
  SupplyTransport.guarded_mixed_canonizer Force.keyEquivariant_lookahead
    (supplyEquivariant_deepMatchSupply d)

end DeepMatch
end ChainDescent
