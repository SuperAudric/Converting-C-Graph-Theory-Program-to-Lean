import ChainDescent.SelectNode

/-!
# `F2a` — `foldSupply` : the STRUCTURAL fold supply (the C# B4 port, consume side)

## Why F1 is not enough (`docs/chain-descent-fold-tower-plan.md` §4)

`partialMatchSupply` (F1) catches a copy transposition at the depth that discretizes ONE copy — but that needs the
copy **refinement-visible**. A fold whose copies carry surviving within-copy symmetry (a mirror tie; in the limit,
a WL-blind multipede core) never produces the singletons F1's constructor reads: `CatchesAt` fails at every depth,
and the copy symmetry — which is *real*, verified-checkable, and worth `s!` in pruning — goes unharvested.

The C# testbed harvests it **structurally** (`Option2Solver.TryCanonicalOrderWithFold`): FIBERS = connected
components of the same-cell-neighbour graph, COPIES = components of the graph minus same-cell edges, and the
copy-swap candidate is the fiber-wise transposition of two copies, verified edge-by-edge. No refinement is
involved, so within-copy blindness is irrelevant.

## The supply

`foldSupply` is that harvest as an untrusted `Supply`: for every **pair of branch-cell vertices** `(u₁, u₂)` —
the enumeration is over the cell, so no representative is ever chosen (standing trap #7) — build the fiber-wise
swap of `u₁`'s and `u₂`'s cross-cell components (`swapFun`: a copy-`u₁` vertex maps to the **unique** same-cell-
component partner in copy `u₂`, mirrored, identity elsewhere), keep it iff it is an involution (decidable), and
let `Consume.verified` re-check `IsColAut` as always. Soundness needs nothing; a dirty layout just yields
candidates that fail one of the two gates.

* **Reconstruction** (`swapCand_eq_of_foldSwap`): on a clean fold pair the candidate is **exactly** the copy-swap
  automorphism — the hypotheses are precisely the cover geometry (τ maps each copy-`u₁` vertex to its unique
  fiber partner in copy `u₂`, is the identity off the two copies, and is an involution).
* **Equivariance** (`gensEquivariant_foldSupply`): components, unique lookups and the pair enumeration all
  transport (`mem_relComp_transport`), so the emitted generator set conjugates — same shape as
  `partialMatchSupply`, and it feeds both `SupplyTransport.guarded_mixed_canonizer` and the fused
  `SelectNode.selNode_canonizer`.
* **Cost**: billed flat at `|cell|² · n⁵` — the naive per-candidate closure recomputation, honestly priced (a
  materialised fast twin is a later constant-factor item; the point here is reach, not the constant).

## What this closes, and what it does not

With F1: refinement-visible folds (any `k`). With F2a: folds over refinement-**blind** cores too — measured on
2- and 3-fold covers of `C₄`+pendant whose copies keep their mirror tie (F1 dead at `d = 0`, `foldSupply`
collapses the copy cell). Still open, by design: the **parallel-class involutions** of
distinguishable `Z₂ᵏ` towers (F2b — same file when built: enumerate every seed edge, propagate the induced-
4-cycle matching, emit the whole-graph involution) and the ordering of genuinely-different copies (F3, the ring
key). Guards: `Regression` §10 (n = 10); measurements: `PerformanceTest` §8 (n = 15). A cell that is an orbit only under a *non*-copy-swap symmetry (e.g. the global mirror) is correctly left
unresolved by this supply — that is `matchSupply`/F1's or F3's job at the node where it surfaces.
-/

namespace ChainDescent
namespace Fold

open ChainDescent.CostModel (CostM)
open ChainDescent.Descend
open ChainDescent.Consume (Supply gens verified IsColAut WordReach CellIsOrbit)
open ChainDescent.SupplyTransport (GensEquivariant SupplyEquivariant)
open ChainDescent.Composite (forceThenConsume)

variable {n : Nat}

/-! ## 1. The two edge relations — vertical (same cell) vs horizontal (cross cell) -/

/-- Same-cell adjacency: the "vertical" edges of a fold cover (copies of one core vertex are 1-WL twins). -/
def sameCellRel (adj : AdjMatrix n) (χ : Colouring n) (v w : Fin n) : Bool :=
  decide (adj.adj v w ≠ 0) && decide (χ v = χ w)

/-- Cross-cell adjacency: the "horizontal" (within-copy) edges — removing the vertical edges leaves the copies. -/
def crossCellRel (adj : AdjMatrix n) (χ : Colouring n) (v w : Fin n) : Bool :=
  decide (adj.adj v w ≠ 0) && !(decide (χ v = χ w))

theorem sameCellRel_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (a b : Fin n) :
    sameCellRel (relabelAdj σ adj) (transportColouring σ χ) (σ a) (σ b) = sameCellRel adj χ a b := by
  simp [sameCellRel, transportColouring]

theorem crossCellRel_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (a b : Fin n) :
    crossCellRel (relabelAdj σ adj) (transportColouring σ χ) (σ a) (σ b) = crossCellRel adj χ a b := by
  simp [crossCellRel, transportColouring]

/-! ## 2. The reachability closure — components, computably, with membership-level transport -/

/-- One closure round: everything already reached, plus every `rel`-successor of it. -/
def relStep (rel : Fin n → Fin n → Bool) (S : List (Fin n)) : List (Fin n) :=
  (S ++ (List.finRange n).filter (fun w => S.any (fun v => rel v w))).dedup

/-- The `rel`-component of `b` (as computed: `n` closure rounds from `{b}` — enough for any component, and no
convergence proof is ever needed: every downstream statement is relative to what `relComp` computes). -/
def relComp (rel : Fin n → Fin n → Bool) (b : Fin n) : List (Fin n) :=
  (relStep rel)^[n] [b]

theorem mem_relStep_iff {rel : Fin n → Fin n → Bool} {S : List (Fin n)} {x : Fin n} :
    x ∈ relStep rel S ↔ x ∈ S ∨ ∃ v ∈ S, rel v x = true := by
  simp [relStep, List.mem_filter, List.any_eq_true]

/-- **★ Components transport, membership-level** — the engine of everything equivariant in this file. -/
theorem mem_relComp_transport {rel rel' : Fin n → Fin n → Bool} (σ : Equiv.Perm (Fin n))
    (hrel : ∀ a b, rel' (σ a) (σ b) = rel a b) (b x : Fin n) :
    σ x ∈ relComp rel' (σ b) ↔ x ∈ relComp rel b := by
  suffices h : ∀ (k : Nat) (y : Fin n),
      σ y ∈ (relStep rel')^[k] [σ b] ↔ y ∈ (relStep rel)^[k] [b] from h n x
  intro k
  induction k with
  | zero =>
      intro y
      constructor
      · intro h
        have : σ y = σ b := by simpa using h
        simp [σ.injective this]
      · intro h
        have : y = b := by simpa using h
        simp [this]
  | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        mem_relStep_iff, mem_relStep_iff]
      constructor
      · rintro (h | ⟨v, hv, hrv⟩)
        · exact Or.inl ((ih y).mp h)
        · refine Or.inr ⟨σ.symm v, (ih (σ.symm v)).mp (by simpa using hv), ?_⟩
          have h2 := hrel (σ.symm v) y
          rw [Equiv.apply_symm_apply] at h2
          rw [← h2]
          exact hrv
      · rintro (h | ⟨v, hv, hrv⟩)
        · exact Or.inl ((ih y).mpr h)
        · exact Or.inr ⟨σ v, (ih v).mpr hv, by rw [hrel v y]; exact hrv⟩

/-! ## 3. The unique-partner lookup — canonical, so no choice is ever made -/

private theorem existsUnique_univ {p : Fin n → Prop} (h : ∃! x, p x) :
    ∃! x, x ∈ (Finset.univ : Finset (Fin n)) ∧ p x := by
  obtain ⟨x, hx, hu⟩ := h
  exact ⟨x, ⟨Finset.mem_univ x, hx⟩, fun y hy => hu y hy.2⟩

instance (P : Fin n → Bool) : Decidable (∃! w : Fin n, P w = true) :=
  inferInstanceAs (Decidable (∃ w : Fin n, P w = true ∧ ∀ x : Fin n, P x = true → x = w))

/-- The unique vertex satisfying `P`, if there is exactly one — the fiber-partner lookup. -/
def uniqueMem (P : Fin n → Bool) : Option (Fin n) :=
  if h : ∃! w : Fin n, P w = true then
    some (Finset.choose (fun w => P w = true) Finset.univ (existsUnique_univ h))
  else none

theorem uniqueMem_eq_some {P : Fin n → Bool} {w : Fin n}
    (hw : P w = true) (huniq : ∀ x, P x = true → x = w) : uniqueMem P = some w := by
  have hex : ∃! x : Fin n, P x = true := ⟨w, hw, huniq⟩
  rw [uniqueMem, dif_pos hex]
  exact congrArg some
    (huniq _ (Finset.choose_spec (fun x => P x = true) Finset.univ (existsUnique_univ hex)).2)

private theorem existsUnique_bool_transport (σ : Equiv.Perm (Fin n)) {P P' : Fin n → Bool}
    (hP : ∀ w, P' (σ w) = P w) :
    (∃! w : Fin n, P' w = true) ↔ (∃! w : Fin n, P w = true) := by
  constructor
  · rintro ⟨w, hw, hu⟩
    have hw' : P (σ.symm w) = true := by
      have h2 := hP (σ.symm w)
      rw [Equiv.apply_symm_apply] at h2
      rw [← h2]; exact hw
    refine ⟨σ.symm w, hw', fun x hx => ?_⟩
    have hx' : P' (σ x) = true := by rw [hP x]; exact hx
    have h3 := hu (σ x) hx'
    simp [← h3]
  · rintro ⟨w, hw, hu⟩
    have hw' : P' (σ w) = true := by rw [hP w]; exact hw
    refine ⟨σ w, hw', fun x hx => ?_⟩
    have hx' : P (σ.symm x) = true := by
      have h2 := hP (σ.symm x)
      rw [Equiv.apply_symm_apply] at h2
      rw [← h2]; exact hx
    have h3 := hu (σ.symm x) hx'
    simpa using congrArg σ h3

theorem uniqueMem_transport (σ : Equiv.Perm (Fin n)) {P P' : Fin n → Bool}
    (hP : ∀ w, P' (σ w) = P w) :
    uniqueMem P' = (uniqueMem P).map σ := by
  by_cases h : ∃! w : Fin n, P w = true
  · have h' : ∃! w : Fin n, P' w = true := (existsUnique_bool_transport σ hP).mpr h
    rw [uniqueMem, uniqueMem, dif_pos h, dif_pos h', Option.map_some]
    refine congrArg some (h'.unique ?_ ?_)
    · exact (Finset.choose_spec (fun w => P' w = true) Finset.univ (existsUnique_univ h')).2
    · rw [hP]
      exact (Finset.choose_spec (fun w => P w = true) Finset.univ (existsUnique_univ h)).2
  · have h' : ¬ ∃! w : Fin n, P' w = true := fun hc => h ((existsUnique_bool_transport σ hP).mp hc)
    rw [uniqueMem, uniqueMem, dif_neg h, dif_neg h']
    rfl

/-! ## 4. The copy-swap candidate -/

/-- The fiber-wise swap of `u₁`'s and `u₂`'s copies: a copy-`u₁` vertex maps to its unique same-cell-component
partner in copy `u₂` (and mirrored); identity elsewhere. Total; the involution check lives in `swapCand`. -/
def swapFun (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) (v : Fin n) : Fin n :=
  if v ∈ relComp (crossCellRel adj χ) u₁ then
    (uniqueMem (fun w => decide (w ∈ relComp (sameCellRel adj χ) v)
      && decide (w ∈ relComp (crossCellRel adj χ) u₂))).getD v
  else if v ∈ relComp (crossCellRel adj χ) u₂ then
    (uniqueMem (fun w => decide (w ∈ relComp (sameCellRel adj χ) v)
      && decide (w ∈ relComp (crossCellRel adj χ) u₁))).getD v
  else v

/-- **The structural candidate constructor**: keep the swap iff it is an involution (decidable). Untrusted —
`Consume.verified` still re-checks `IsColAut`; a dirty layout only wastes the candidate. -/
def swapCand (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) :
    Option (Equiv.Perm (Fin n)) :=
  if h : ∀ v, swapFun adj χ u₁ u₂ (swapFun adj χ u₁ u₂ v) = v then
    some (Function.Involutive.toPerm _ h)
  else none

/-! ### 4b. The rfl-twins — same definition, `let`-materialised components

`swapFun`'s spec form recomputes `relComp` inside the `uniqueMem` scan (`n` predicate evaluations × 2 closures
each). The twins bind each closure **once per call** — a ~500× runtime cut, measured — and are **definitionally
equal** (`rfl`: ζ-reduction), so every theorem about `swapFun`/`swapCand` applies to them unchanged. House
pattern: `Refine.warmRefineVec`, `Select.selNodeFast`. -/

def swapFunFast (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) (v : Fin n) : Fin n :=
  let A := relComp (crossCellRel adj χ) u₁
  let B := relComp (crossCellRel adj χ) u₂
  if v ∈ A then
    let fib := relComp (sameCellRel adj χ) v
    (uniqueMem (fun w => decide (w ∈ fib) && decide (w ∈ B))).getD v
  else if v ∈ B then
    let fib := relComp (sameCellRel adj χ) v
    (uniqueMem (fun w => decide (w ∈ fib) && decide (w ∈ A))).getD v
  else v

theorem swapFunFast_eq : @swapFunFast n = @swapFun n := rfl

def swapCandFast (adj : AdjMatrix n) (χ : Colouring n) (u₁ u₂ : Fin n) :
    Option (Equiv.Perm (Fin n)) :=
  if h : ∀ v, swapFunFast adj χ u₁ u₂ (swapFunFast adj χ u₁ u₂ v) = v then
    some (Function.Involutive.toPerm _ h)
  else none

theorem swapCandFast_eq : @swapCandFast n = @swapCand n := rfl

/-! ## 5. Reconstruction — on a clean fold pair the candidate IS the copy swap -/

/-- **★ The reconstruction, pointwise.** If `τ` maps each copy-`u₁` vertex to its **unique** fiber partner in
copy `u₂` (and mirrored) and is the identity off the two copies, then `swapFun` computes exactly `τ` — the
hypotheses are precisely the cover geometry, with uniqueness carrying the "clean layout" content. -/
theorem swapFun_eq_of_foldSwap {adj : AdjMatrix n} {χ : Colouring n} {u₁ u₂ : Fin n}
    {τ : Equiv.Perm (Fin n)}
    (h₁ : ∀ v ∈ relComp (crossCellRel adj χ) u₁,
      τ v ∈ relComp (sameCellRel adj χ) v ∧ τ v ∈ relComp (crossCellRel adj χ) u₂ ∧
        ∀ w, w ∈ relComp (sameCellRel adj χ) v → w ∈ relComp (crossCellRel adj χ) u₂ → w = τ v)
    (h₂ : ∀ v ∈ relComp (crossCellRel adj χ) u₂,
      τ v ∈ relComp (sameCellRel adj χ) v ∧ τ v ∈ relComp (crossCellRel adj χ) u₁ ∧
        ∀ w, w ∈ relComp (sameCellRel adj χ) v → w ∈ relComp (crossCellRel adj χ) u₁ → w = τ v)
    (hid : ∀ v, v ∉ relComp (crossCellRel adj χ) u₁ → v ∉ relComp (crossCellRel adj χ) u₂ →
      τ v = v) :
    ∀ v, swapFun adj χ u₁ u₂ v = τ v := by
  intro v
  unfold swapFun
  by_cases hv₁ : v ∈ relComp (crossCellRel adj χ) u₁
  · rw [if_pos hv₁]
    obtain ⟨hf, hc, huniq⟩ := h₁ v hv₁
    rw [uniqueMem_eq_some (w := τ v) (by simp [hf, hc]) (fun x hx => ?_)]
    · rfl
    · have hx' := hx
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hx'
      exact huniq x hx'.1 hx'.2
  · rw [if_neg hv₁]
    by_cases hv₂ : v ∈ relComp (crossCellRel adj χ) u₂
    · rw [if_pos hv₂]
      obtain ⟨hf, hc, huniq⟩ := h₂ v hv₂
      rw [uniqueMem_eq_some (w := τ v) (by simp [hf, hc]) (fun x hx => ?_)]
      · rfl
      · have hx' := hx
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hx'
        exact huniq x hx'.1 hx'.2
    · rw [if_neg hv₂]
      exact (hid v hv₁ hv₂).symm

/-- **★★ THE RECONSTRUCTION.** A clean fold pair's copy-swap automorphism is returned exactly. -/
theorem swapCand_eq_of_foldSwap {adj : AdjMatrix n} {χ : Colouring n} {u₁ u₂ : Fin n}
    {τ : Equiv.Perm (Fin n)} (hinv : ∀ v, τ (τ v) = v)
    (h₁ : ∀ v ∈ relComp (crossCellRel adj χ) u₁,
      τ v ∈ relComp (sameCellRel adj χ) v ∧ τ v ∈ relComp (crossCellRel adj χ) u₂ ∧
        ∀ w, w ∈ relComp (sameCellRel adj χ) v → w ∈ relComp (crossCellRel adj χ) u₂ → w = τ v)
    (h₂ : ∀ v ∈ relComp (crossCellRel adj χ) u₂,
      τ v ∈ relComp (sameCellRel adj χ) v ∧ τ v ∈ relComp (crossCellRel adj χ) u₁ ∧
        ∀ w, w ∈ relComp (sameCellRel adj χ) v → w ∈ relComp (crossCellRel adj χ) u₁ → w = τ v)
    (hid : ∀ v, v ∉ relComp (crossCellRel adj χ) u₁ → v ∉ relComp (crossCellRel adj χ) u₂ →
      τ v = v) :
    swapCand adj χ u₁ u₂ = some τ := by
  have heq := swapFun_eq_of_foldSwap h₁ h₂ hid
  have hcheck : ∀ v, swapFun adj χ u₁ u₂ (swapFun adj χ u₁ u₂ v) = v := fun v => by
    rw [heq, heq]; exact hinv v
  rw [swapCand, dif_pos hcheck]
  exact congrArg some (Equiv.ext heq)

/-! ## 6. Equivariance of the constructor -/

theorem swapFun_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (u₁ u₂ : Fin n) (x : Fin n) :
    swapFun (relabelAdj σ adj) (transportColouring σ χ) (σ u₁) (σ u₂) x
      = σ (swapFun adj χ u₁ u₂ (σ.symm x)) := by
  have hx : x = σ (σ.symm x) := (σ.apply_symm_apply x).symm
  have hmem : ∀ (u y : Fin n),
      y ∈ relComp (crossCellRel (relabelAdj σ adj) (transportColouring σ χ)) (σ u)
        ↔ σ.symm y ∈ relComp (crossCellRel adj χ) u := by
    intro u y
    conv_lhs => rw [(σ.apply_symm_apply y).symm]
    exact mem_relComp_transport σ (crossCellRel_transport σ adj χ) u (σ.symm y)
  have hPmem : ∀ (u : Fin n) (w : Fin n),
      (decide (σ w ∈ relComp (sameCellRel (relabelAdj σ adj) (transportColouring σ χ)) x)
        && decide (σ w ∈ relComp (crossCellRel (relabelAdj σ adj) (transportColouring σ χ)) (σ u)))
      = (decide (w ∈ relComp (sameCellRel adj χ) (σ.symm x))
        && decide (w ∈ relComp (crossCellRel adj χ) u)) := by
    intro u w
    have hsame : σ w ∈ relComp (sameCellRel (relabelAdj σ adj) (transportColouring σ χ)) x
        ↔ w ∈ relComp (sameCellRel adj χ) (σ.symm x) := by
      conv_lhs => rw [hx]
      exact mem_relComp_transport σ (sameCellRel_transport σ adj χ) (σ.symm x) w
    have hcross' : σ w ∈ relComp (crossCellRel (relabelAdj σ adj) (transportColouring σ χ)) (σ u)
        ↔ w ∈ relComp (crossCellRel adj χ) u :=
      mem_relComp_transport σ (crossCellRel_transport σ adj χ) u w
    rw [decide_eq_decide.mpr hsame, decide_eq_decide.mpr hcross']
  unfold swapFun
  by_cases h₁ : σ.symm x ∈ relComp (crossCellRel adj χ) u₁
  · rw [if_pos ((hmem u₁ x).mpr h₁), if_pos h₁, uniqueMem_transport σ (hPmem u₂)]
    cases uniqueMem (fun w => decide (w ∈ relComp (sameCellRel adj χ) (σ.symm x))
      && decide (w ∈ relComp (crossCellRel adj χ) u₂)) with
    | none => simp
    | some w => simp
  · rw [if_neg (fun hc => h₁ ((hmem u₁ x).mp hc)), if_neg h₁]
    by_cases h₂ : σ.symm x ∈ relComp (crossCellRel adj χ) u₂
    · rw [if_pos ((hmem u₂ x).mpr h₂), if_pos h₂, uniqueMem_transport σ (hPmem u₁)]
      cases uniqueMem (fun w => decide (w ∈ relComp (sameCellRel adj χ) (σ.symm x))
        && decide (w ∈ relComp (crossCellRel adj χ) u₁)) with
      | none => simp
      | some w => simp
    · rw [if_neg (fun hc => h₂ ((hmem u₂ x).mp hc)), if_neg h₂]
      simp

private theorem swap_check_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (u₁ u₂ : Fin n) :
    (∀ v, swapFun (relabelAdj σ adj) (transportColouring σ χ) (σ u₁) (σ u₂)
        (swapFun (relabelAdj σ adj) (transportColouring σ χ) (σ u₁) (σ u₂) v) = v)
      ↔ (∀ v, swapFun adj χ u₁ u₂ (swapFun adj χ u₁ u₂ v) = v) := by
  constructor
  · intro h v
    have := h (σ v)
    rw [swapFun_conj, swapFun_conj] at this
    simp only [Equiv.symm_apply_apply] at this
    exact σ.injective this
  · intro h v
    rw [swapFun_conj, swapFun_conj]
    simp only [Equiv.symm_apply_apply]
    rw [h (σ.symm v)]
    exact σ.apply_symm_apply v

/-- The candidate transports up to conjugation, **including its failure mode** — the `matchCol_transport` /
`partialMatch_conj` analogue, so the supply equivariance proof is the standard one. -/
theorem swapCand_conj (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (u₁ u₂ : Fin n) :
    swapCand (relabelAdj σ adj) (transportColouring σ χ) (σ u₁) (σ u₂)
      = (swapCand adj χ u₁ u₂).map (fun t => σ * t * σ⁻¹) := by
  unfold swapCand
  by_cases h : ∀ v, swapFun adj χ u₁ u₂ (swapFun adj χ u₁ u₂ v) = v
  · rw [dif_pos h, dif_pos ((swap_check_conj σ adj χ u₁ u₂).mpr h), Option.map_some]
    refine congrArg some (Equiv.ext fun x => ?_)
    show swapFun (relabelAdj σ adj) (transportColouring σ χ) (σ u₁) (σ u₂) x
        = σ (swapFun adj χ u₁ u₂ (σ⁻¹ x))
    rw [swapFun_conj]
    rfl
  · rw [dif_neg h, dif_neg (fun hc => h ((swap_check_conj σ adj χ u₁ u₂).mp hc))]
    rfl

/-! ## 7. The supply -/

/-- **★ THE STRUCTURAL FOLD SUPPLY.** Every branch-cell pair seeds a copy-swap candidate; the involution gate and
`Consume.verified` filter the junk. Cost is billed flat at `|cell|² · n⁵` (the naive per-candidate closure
recomputation — honest for this first implementation; a materialised twin is a constant-factor item). -/
def foldSupply : Supply n := fun adj χ =>
  let B := branches χ
  (B.flatMap (fun u₁ => B.filterMap (fun u₂ => swapCandFast adj χ u₁ u₂)),
   B.length * B.length * (n * n * n * n * n))

theorem mem_gens_foldSupply_iff {adj : AdjMatrix n} {χ : Colouring n} {g : Equiv.Perm (Fin n)} :
    g ∈ gens (foldSupply (n := n)) adj χ ↔
      ∃ u₁ ∈ branches χ, ∃ u₂ ∈ branches χ, swapCand adj χ u₁ u₂ = some g := by
  constructor
  · intro hg
    obtain ⟨u₁, h₁, hq⟩ := List.mem_flatMap.mp hg
    obtain ⟨u₂, h₂, hc⟩ := List.mem_filterMap.mp hq
    exact ⟨u₁, h₁, u₂, h₂, hc⟩
  · rintro ⟨u₁, h₁, u₂, h₂, hc⟩
    exact List.mem_flatMap.mpr ⟨u₁, h₁, List.mem_filterMap.mpr ⟨u₂, h₂, hc⟩⟩

/-! ## 8. `①c` — the supply is equivariant -/

/-- **★★ THE STRUCTURAL FOLD SUPPLY IS EQUIVARIANT** — the pair enumeration is the branch cell (which
transports), and the candidate conjugates (`swapCand_conj`). The construction consults only component
*membership* and canonical unique lookups, so no representative is ever chosen (standing trap #7). -/
theorem gensEquivariant_foldSupply : GensEquivariant (foldSupply (n := n)) := by
  intro σ adj χ g
  have hbr : ∀ x : Fin n, x ∈ branches (transportColouring σ χ) ↔ ∃ y ∈ branches χ, σ y = x := by
    intro x
    rw [(branches_transport_perm σ χ).mem_iff, List.mem_map]
  simp only [mem_gens_foldSupply_iff]
  constructor
  · rintro ⟨u₁, h₁, u₂, h₂, hc⟩
    obtain ⟨v₁, hv₁, rfl⟩ := (hbr u₁).mp h₁
    obtain ⟨v₂, hv₂, rfl⟩ := (hbr u₂).mp h₂
    rw [swapCand_conj] at hc
    rcases hcase : swapCand adj χ v₁ v₂ with _ | t
    · rw [hcase] at hc; simp at hc
    · rw [hcase] at hc
      simp only [Option.map_some, Option.some.injEq] at hc
      exact ⟨t, ⟨v₁, hv₁, v₂, hv₂, hcase⟩, hc.symm⟩
  · rintro ⟨h, ⟨u₁, h₁, u₂, h₂, hc⟩, rfl⟩
    refine ⟨σ u₁, (hbr _).mpr ⟨u₁, h₁, rfl⟩, σ u₂, (hbr _).mpr ⟨u₂, h₂, rfl⟩, ?_⟩
    rw [swapCand_conj, hc]
    rfl

theorem supplyEquivariant_foldSupply : SupplyEquivariant (foldSupply (n := n)) :=
  SupplyTransport.supplyEquivariant_of_gensEquivariant gensEquivariant_foldSupply

/-! ## 9. Firing -/

/-- **Graded firing, per pair:** a verified swap candidate carrying `u₁` to `u₂` puts the pair into the verified
`WordReach` — and products of caught swaps reach the rest (`WordReach` is a word, so `τ₁₂·τ₁₃·τ₁₂ = τ₂₃`-style
compositions come free). -/
theorem wordReach_foldSupply {adj : AdjMatrix n} {χ : Colouring n} {u₁ u₂ : Fin n}
    {τ : Equiv.Perm (Fin n)}
    (h₁ : u₁ ∈ branches χ) (h₂ : u₂ ∈ branches χ) (hτ : IsColAut adj χ τ)
    (hcand : swapCand adj χ u₁ u₂ = some τ) (hval : τ u₁ = u₂) :
    WordReach (verified (foldSupply (n := n)) adj χ) u₁ u₂ := by
  have hmem : τ ∈ verified (foldSupply (n := n)) adj χ := by
    refine List.mem_filter.mpr ⟨?_, by simpa using hτ⟩
    exact mem_gens_foldSupply_iff.mpr ⟨u₁, h₁, u₂, h₂, hcand⟩
  have hstep := (Consume.WordReach.refl
    (G := verified (foldSupply (n := n)) adj χ) u₁).step hmem
  rwa [hval] at hstep

/-- **★★★ THE ORACLE FIRES.** If every branch-cell pair is connected by a verified swap candidate, the cell is
certified as one orbit and `consume` collapses it to a single branch — with **no refinement involved**, so a
refinement-blind copy costs nothing. -/
theorem cellIsOrbit_foldSupply {adj : AdjMatrix n} {χ : Colouring n}
    (h : ∀ u ∈ branches χ, ∀ w ∈ branches χ, ∃ τ : Equiv.Perm (Fin n),
      IsColAut adj χ τ ∧ swapCand adj χ u w = some τ ∧ τ u = w) :
    CellIsOrbit (foldSupply (n := n)) adj χ := by
  intro u hu w hw
  obtain ⟨τ, hτ, hcand, hval⟩ := h u hu w hw
  exact wordReach_foldSupply hu hw hτ hcand hval

/-! ## 10. ★★★ THE CAPSTONES — both objects, no carried hypotheses -/

/-- **★★★ The guarded (blind) mixed canonizer over the structural fold supply.** -/
theorem foldSupply_guarded_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (forceThenConsume (Force.lookaheadKey (n := n)) (foldSupply (n := n))))) :=
  SupplyTransport.guarded_mixed_canonizer Force.keyEquivariant_lookahead
    supplyEquivariant_foldSupply

/-- **★★★ The FUSED (resolver-aware) canonizer over the structural fold supply** — the selector probes every
cell with this supply's verified list, so a fold cell resolves wherever it sits in the colour order. -/
theorem foldSupply_selNode_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Select.canonFormS? (Refine.encodeFreeFast (n := n))
        (Select.selNode (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (foldSupply (n := n)))) :=
  Select.selNode_canonizer Force.keyEquivariant_lookahead supplyEquivariant_foldSupply

end Fold
end ChainDescent
