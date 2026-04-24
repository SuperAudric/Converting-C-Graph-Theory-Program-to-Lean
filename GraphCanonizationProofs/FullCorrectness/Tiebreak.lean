import FullCorrectness.Equivariance

/-!
# §5–§6  `breakTie` analysis

Defines `TypedAut G vts` (the subgroup of `Aut G` that also preserves a vertex-type
array pointwise) and states the two `breakTie` theorems (§5) plus the tiebreak
choice-independence theorem (§6).

## Subgroup chain

For Aut-invariant `vts`, `TypedAut G vts ≤ Aut G`. Each `breakTie` strictly shrinks
the `TypedAut` group until it is trivial (all vertex types distinct). The chain
terminates in at most `n` steps because `Aut G` is finite.

## Status
- `TypedAut`: defined.
- §5 `breakTie_Aut_stabilizer`:   stated; proof pending.
- §5 `breakTie_strict_shrink`:     stated; proof pending.
- §6 `tiebreak_choice_independent`: stated; proof pending (the conceptual crux).
-/

namespace Graph

open AdjMatrix

variable {n : Nat}

/-! ## Typed automorphism group `TypedAut G vts`

A permutation `σ ∈ Aut(G, vts)` iff
  1. `σ ∈ Aut G` (preserves the graph), and
  2. `σ` preserves vertex types pointwise: `vts[σ v] = vts[v]` for all `v`.

Condition (2) is written using `Array.getD` with default `0` to keep it total
(the algorithm uses `getD` throughout).
-/

/-- Pointwise σ-invariance of a vertex-type array. -/
def VtsInvariant (σ : Equiv.Perm (Fin n)) (vts : Array VertexType) : Prop :=
  ∀ v : Fin n, vts.getD (σ v).val 0 = vts.getD v.val 0

theorem VtsInvariant.one (vts : Array VertexType) : VtsInvariant (n := n) 1 vts := by
  intro v; simp

theorem VtsInvariant.mul {σ τ : Equiv.Perm (Fin n)} {vts : Array VertexType}
    (hσ : VtsInvariant σ vts) (hτ : VtsInvariant τ vts) :
    VtsInvariant (σ * τ) vts := by
  intro v
  rw [Equiv.Perm.mul_apply]
  exact (hσ (τ v)).trans (hτ v)

theorem VtsInvariant.inv {σ : Equiv.Perm (Fin n)} {vts : Array VertexType}
    (hσ : VtsInvariant σ vts) :
    VtsInvariant σ⁻¹ vts := by
  intro v
  have := hσ (σ⁻¹ v)
  have hback : (σ (σ⁻¹ v)) = v := by simp
  rw [hback] at this
  exact this.symm

/-- The typed automorphism group: automorphisms of `G` that also preserve `vts`. -/
def AdjMatrix.TypedAut (G : AdjMatrix n) (vts : Array VertexType) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := { σ | G.permute σ = G ∧ VtsInvariant σ vts }
  mul_mem' := by
    rintro σ τ ⟨hGσ, hvσ⟩ ⟨hGτ, hvτ⟩
    refine ⟨?_, hvσ.mul hvτ⟩
    rw [AdjMatrix.permute_mul, hGτ, hGσ]
  one_mem' := by
    refine ⟨AdjMatrix.permute_one G, VtsInvariant.one vts⟩
  inv_mem' := by
    rintro σ ⟨hGσ, hvσ⟩
    refine ⟨?_, hvσ.inv⟩
    calc G.permute σ⁻¹
        = (G.permute σ).permute σ⁻¹ := by rw [hGσ]
      _ = G := AdjMatrix.permute_permute_symm σ G

theorem mem_TypedAut_iff {G : AdjMatrix n} {vts : Array VertexType}
    {σ : Equiv.Perm (Fin n)} :
    σ ∈ G.TypedAut vts ↔ G.permute σ = G ∧ VtsInvariant σ vts := Iff.rfl

/-- `TypedAut G vts ≤ Aut G`: the typed automorphism group is a subgroup of `Aut G`. -/
theorem AdjMatrix.TypedAut_le_Aut (G : AdjMatrix n) (vts : Array VertexType) :
    G.TypedAut vts ≤ G.Aut := by
  intro σ hσ
  exact hσ.1

/-! ## Decidability and finiteness of `TypedAut`

For §6's strong induction on `|TypedAut G vts|`, we need a `Fintype` instance. As with
`Aut G`, this follows from `Equiv.Perm (Fin n)` being finite (`n!`) plus decidable
membership in `TypedAut G vts`. -/

instance (vts : Array VertexType) (σ : Equiv.Perm (Fin n)) :
    Decidable (VtsInvariant σ vts) :=
  inferInstanceAs (Decidable (∀ v : Fin n,
    vts.getD (σ v).val 0 = vts.getD v.val 0))

instance (G : AdjMatrix n) (vts : Array VertexType) (σ : Equiv.Perm (Fin n)) :
    Decidable (σ ∈ G.TypedAut vts) :=
  inferInstanceAs (Decidable (G.permute σ = G ∧ VtsInvariant σ vts))

instance (G : AdjMatrix n) (vts : Array VertexType) : Fintype (G.TypedAut vts) :=
  Subtype.fintype _

/-- The all-zeros array is σ-invariant for every σ. (Boundary case for the main
theorem: `run` is invoked with `Array.replicate n 0` as the starting vertex types.) -/
theorem VtsInvariant.replicate_zero (σ : Equiv.Perm (Fin n)) :
    VtsInvariant σ (Array.replicate n (0 : VertexType)) := by
  intro v
  simp [v.isLt, (σ v).isLt]

/-- For any `G`, every automorphism is in `TypedAut G (Array.replicate n 0)` — i.e. the
typed-automorphism group with all-zeros types coincides with the full automorphism group. -/
theorem TypedAut_replicate_zero (G : AdjMatrix n) :
    G.TypedAut (Array.replicate n (0 : VertexType)) = G.Aut := by
  ext σ
  refine ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, VtsInvariant.replicate_zero σ⟩⟩

/-! ## §5  `breakTie` shrinks the typed-automorphism group

Let `t₀` be the smallest repeated value in `vts`, `V_{t₀} := { v | vts[v] = t₀ }` its
type-class, and `v* := min V_{t₀}` (by `Fin` order). Write `vts' := (breakTie vts t₀).1`.
Then:

  **(§5.1)** `σ ∈ TypedAut G vts'`  ↔  `σ ∈ TypedAut G vts ∧ σ v* = v*`.

  **(§5.2)** If `|V_{t₀}| ≥ 2` and `vts` is Aut(G)-invariant (so all of `V_{t₀}` is in
           a single `Aut(G, vts)`-orbit by §4's corollary), then `TypedAut G vts' ⊊
           TypedAut G vts`.

The stabilizer characterization (§5.1) is immediate from the definition of `breakTie`:
`breakTie` keeps `v*` at value `t₀` and promotes every other vertex in `V_{t₀}` to
`t₀ + 1`. So `σ` preserves `vts'` iff it preserves `vts` AND fixes `v*`.

The strict-shrinking claim (§5.2) uses §4's corollary: same-type vertices in an
Aut(G)-invariant typing lie in one Aut(G, vts)-orbit, hence if there are ≥ 2 of them,
not all are fixed by `TypedAut G vts`, so the stabilizer is a proper subgroup.
-/

/-- The type class of `t₀` in `vts`: vertices with `vts[v] = t₀`. -/
def typeClass (vts : Array VertexType) (t₀ : VertexType) : Set (Fin n) :=
  { v | vts.getD v.val 0 = t₀ }

/-! ### Characterizing `breakTie`'s output

Before the §5 theorems, we characterize the output of `breakTie` position-by-position.
After the fold runs over `[0, 1, …, size-1]`:

  - size is preserved;
  - positions outside `typeClass vts t₀` keep their value;
  - the **first** position (smallest-index) with value `t₀` keeps its value;
  - every other position with value `t₀` is promoted to `t₀ + 1`.
-/

/-- The body of the `breakTie` fold. Written using explicit projections (rather than a
`let (arr, first, chg) := triple` destructure) so that `split` on the branches keeps the
goal in terms of `triple.1` / `triple.2.1` / `triple.2.2`. The definitional equality with
the `let`-destructured form used by `breakTie` is established in `breakTie_eq_fold`. -/
private def btStep (t₀ : VertexType)
    (triple : Array VertexType × Bool × Bool) (i : Nat) :
    Array VertexType × Bool × Bool :=
  if triple.1.getD i 0 == t₀ then
    if triple.2.1 then (triple.1, false, triple.2.2)
    else (triple.1.set! i (t₀ + 1), false, true)
  else triple

private theorem btStep_size (t₀ : VertexType)
    (triple : Array VertexType × Bool × Bool) (i : Nat) :
    (btStep t₀ triple i).1.size = triple.1.size := by
  simp only [btStep]
  split_ifs <;> simp

/-- `breakTie` unfolded into the `btStep` fold. Proved via pointwise function extensionality
on the lambda body (both bodies reduce to the same `match` expression on a 3-tuple). -/
private theorem breakTie_eq_fold (vts : Array VertexType) (t₀ : VertexType) :
    breakTie vts t₀ =
      let triple := (List.range vts.size).foldl (btStep t₀) (vts, true, false)
      (triple.1, triple.2.2) := by
  -- The `let (a,b,c) := triple` destructure inside `breakTie`'s lambda is semantically the
  -- same as projecting `.1`, `.2.1`, `.2.2`; we normalize by `funext` + `split_ifs`.
  unfold breakTie btStep
  congr 1

/-- Size is preserved by the breakTie fold. -/
private theorem btFold_size (t₀ : VertexType) :
    ∀ (l : List Nat) (triple : Array VertexType × Bool × Bool),
      (l.foldl (btStep t₀) triple).1.size = triple.1.size
  | [], _ => rfl
  | x :: xs, triple => by
      rw [List.foldl_cons, btFold_size t₀ xs (btStep t₀ triple x), btStep_size]

/-- Positions whose value is not `t₀` are preserved by one `btStep`. -/
private theorem btStep_getD_ne (t₀ : VertexType)
    (triple : Array VertexType × Bool × Bool) (i j : Nat)
    (hj : triple.1.getD j 0 ≠ t₀) :
    (btStep t₀ triple i).1.getD j 0 = triple.1.getD j 0 := by
  unfold btStep
  split
  · -- current value at position `i` equals `t₀`
    split
    · rfl
    · rename_i hcmp _
      -- If `i = j`, the hypothesis `hj` contradicts `hcmp` (which says `triple.1.getD i 0 = t₀`).
      have hij : i ≠ j := by
        intro hij
        apply hj
        rw [← hij]
        exact beq_iff_eq.mp hcmp
      -- `set!` at position `i ≠ j` leaves position `j` untouched.
      simp only [Array.getD_eq_getD_getElem?]
      rcases lt_or_ge j triple.1.size with hjs | hjs
      · rw [Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_ne hij]
      · rw [Array.set!_eq_setIfInBounds]
        simp [hjs]
  · rfl

/-- Positions whose value is not `t₀` are preserved across the whole fold. -/
private theorem btFold_getD_ne (t₀ : VertexType) :
    ∀ (l : List Nat) (triple : Array VertexType × Bool × Bool) (j : Nat),
      triple.1.getD j 0 ≠ t₀ →
      (l.foldl (btStep t₀) triple).1.getD j 0 = triple.1.getD j 0
  | [], _, _, _ => rfl
  | x :: xs, triple, j, hj => by
      rw [List.foldl_cons]
      have hstep : (btStep t₀ triple x).1.getD j 0 = triple.1.getD j 0 :=
        btStep_getD_ne t₀ triple x j hj
      have hj' : (btStep t₀ triple x).1.getD j 0 ≠ t₀ := by rw [hstep]; exact hj
      rw [btFold_getD_ne t₀ xs _ j hj', hstep]

/-- `breakTie` preserves array size. -/
theorem breakTie_size (vts : Array VertexType) (t₀ : VertexType) :
    (breakTie vts t₀).1.size = vts.size := by
  rw [breakTie_eq_fold]
  exact btFold_size t₀ _ (vts, true, false)

/-- `breakTie` leaves untouched any position whose value is not the target. -/
theorem breakTie_getD_of_ne (vts : Array VertexType) (t₀ : VertexType)
    {j : Nat} (hj : vts.getD j 0 ≠ t₀) :
    (breakTie vts t₀).1.getD j 0 = vts.getD j 0 := by
  rw [breakTie_eq_fold]
  exact btFold_getD_ne t₀ _ (vts, true, false) j hj

/-! The remaining characterizations — "first-target keeps value, later targets get promoted"
— require tracking the `firstAppearance` flag across the fold. Two lemmas do the heavy
lifting:

  - `btFold_no_target`:  if every index in the list has `vts.getD _ 0 ≠ t₀`, the fold is
    a no-op on `(vts, first, chg)`.
  - `btFold_from_notfirst`: starting from `(arr, false, chg)` (so `first = false`), any
    subsequent index `j` in the list with `arr.getD j 0 = t₀` gets promoted to `t₀ + 1`. -/

/-- If no index in the list has target value, the fold is a no-op. -/
private theorem btFold_no_target (t₀ : VertexType) :
    ∀ (l : List Nat) (arr : Array VertexType) (first chg : Bool),
      (∀ i ∈ l, arr.getD i 0 ≠ t₀) →
      l.foldl (btStep t₀) (arr, first, chg) = (arr, first, chg)
  | [], _, _, _, _ => rfl
  | x :: xs, arr, first, chg, hne => by
      rw [List.foldl_cons]
      have hxne : arr.getD x 0 ≠ t₀ := hne x (List.mem_cons_self)
      -- One step is a no-op: btStep t₀ (arr, first, chg) x = (arr, first, chg).
      have hstep : btStep t₀ (arr, first, chg) x = (arr, first, chg) := by
        simp only [btStep]
        have : ¬ (arr.getD x 0 == t₀) = true := by
          intro h; exact hxne (beq_iff_eq.mp h)
        rw [if_neg this]
      rw [hstep]
      apply btFold_no_target t₀ xs arr first chg
      intro i hi
      exact hne i (List.mem_cons_of_mem x hi)

/-- Explicit form of `btStep` when the accumulator already has `first = false`:
    no `first`-flip case; either promote at `i` or leave untouched. -/
private theorem btStep_notfirst (t₀ : VertexType) (arr : Array VertexType)
    (chg : Bool) (i : Nat) :
    btStep t₀ (arr, false, chg) i =
      if arr.getD i 0 == t₀ then (arr.set! i (t₀ + 1), false, true)
      else (arr, false, chg) := by
  unfold btStep
  rfl

/-- `t₀ + 1 ≠ t₀` for any integer `t₀`. -/
private theorem VertexType_add_one_ne (t₀ : VertexType) : t₀ + 1 ≠ t₀ :=
  fun h => absurd (Int.add_left_cancel (show t₀ + 1 = t₀ + 0 from by
    rw [h, Int.add_zero])) (by decide)

/-- Starting with `first = false`, any index `j` in a `Nodup` list with target value gets
promoted to `t₀ + 1`. The `Nodup` hypothesis rules out visiting `j` twice. `List.range n`
is `Nodup`, which is the only case we need. -/
private theorem btFold_from_notfirst_getD (t₀ : VertexType) :
    ∀ (l : List Nat) (_hnd : l.Nodup) (arr : Array VertexType) (chg : Bool) (j : Nat),
      j ∈ l →
      arr.getD j 0 = t₀ →
      j < arr.size →
      (l.foldl (btStep t₀) (arr, false, chg)).1.getD j 0 = t₀ + 1
  | [], _, _, _, _, hj, _, _ => absurd hj List.not_mem_nil
  | x :: xs, hnd, arr, chg, j, hj, hjt, hjs => by
      rw [List.foldl_cons, btStep_notfirst]
      have hxnotin : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      rcases List.mem_cons.mp hj with hjeq | hjtail
      · -- j = x: this step promotes position j; later steps preserve it (j ∉ xs).
        subst hjeq
        have hcmp : (arr.getD j 0 == t₀) = true := by
          rw [hjt]; exact beq_self_eq_true _
        rw [if_pos hcmp]
        have hjt' : (arr.set! j (t₀ + 1)).getD j 0 = t₀ + 1 := by
          simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
                     Array.getElem?_setIfInBounds_self_of_lt hjs]
          rfl
        have hne' : (arr.set! j (t₀ + 1)).getD j 0 ≠ t₀ := by
          rw [hjt']; exact VertexType_add_one_ne t₀
        rw [btFold_getD_ne t₀ xs (arr.set! j (t₀ + 1), false, true) j hne']
        exact hjt'
      · -- j ∈ xs: step at x leaves j alone since x ≠ j (nodup).
        have hneq : x ≠ j := fun hxj => hxnotin (hxj ▸ hjtail)
        by_cases hcmp : (arr.getD x 0 == t₀) = true
        · rw [if_pos hcmp]
          have hjt' : (arr.set! x (t₀ + 1)).getD j 0 = t₀ := by
            simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
                       Array.getElem?_setIfInBounds_ne hneq]
            rw [← Array.getD_eq_getD_getElem?]; exact hjt
          have hjs' : j < (arr.set! x (t₀ + 1)).size := by
            rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hjs
          exact btFold_from_notfirst_getD t₀ xs hnd' _ _ j hjtail hjt' hjs'
        · rw [if_neg hcmp]
          exact btFold_from_notfirst_getD t₀ xs hnd' _ _ j hjtail hjt hjs

/-- A position `j` not in the fold's list has its value preserved across the fold.
(No step ever writes at positions outside the list.) -/
private theorem btFold_getD_not_mem (t₀ : VertexType) :
    ∀ (l : List Nat) (triple : Array VertexType × Bool × Bool) (j : Nat),
      j ∉ l →
      (l.foldl (btStep t₀) triple).1.getD j 0 = triple.1.getD j 0
  | [], _, _, _ => rfl
  | x :: xs, triple, j, hnotin => by
      rw [List.foldl_cons]
      have hneq : x ≠ j := fun h => hnotin (h ▸ List.mem_cons_self)
      have hnotin' : j ∉ xs := fun h => hnotin (List.mem_cons_of_mem x h)
      have hstep : (btStep t₀ triple x).1.getD j 0 = triple.1.getD j 0 := by
        unfold btStep
        split_ifs
        · rfl
        · -- promoting branch: set! at x, x ≠ j preserves
          simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
                     Array.getElem?_setIfInBounds_ne hneq]
        · rfl
      rw [btFold_getD_not_mem t₀ xs _ j hnotin', hstep]

/-- `breakTie` leaves the minimum-index target-valued position at value `t₀`. Requires
`v_star` is the unique minimum: no earlier index has value `t₀` in `vts`. -/
theorem breakTie_getD_at_min (vts : Array VertexType) (t₀ : VertexType)
    {v_star_idx : Nat} (hv_size : v_star_idx < vts.size)
    (hv_val : vts.getD v_star_idx 0 = t₀)
    (hv_min : ∀ i, i < v_star_idx → vts.getD i 0 ≠ t₀) :
    (breakTie vts t₀).1.getD v_star_idx 0 = t₀ := by
  rw [breakTie_eq_fold]
  -- Split List.range vts.size = List.range v_star_idx ++ [v_star_idx] ++
  --                             List.range' (v_star_idx + 1) (vts.size - v_star_idx - 1)
  -- But it's cleaner to do induction step-by-step.
  --
  -- Strategy: use btFold_no_target on List.range v_star_idx (no targets), then one step at
  -- v_star_idx (flips first, array unchanged), then btFold_getD_not_mem on the rest (since
  -- v_star_idx is not in the remaining list after it's been visited).
  --
  -- We prove this by showing `List.range vts.size = List.range (v_star_idx + 1) ++ tail` and
  -- that the fold over the prefix leaves position `v_star_idx` at value `t₀`.
  --
  -- Direct approach: induction on List.range vts.size with generalized invariant.
  have h_split : List.range vts.size =
      (List.range (v_star_idx + 1)) ++ List.range' (v_star_idx + 1) (vts.size - (v_star_idx + 1)) := by
    have h_sum : vts.size = (v_star_idx + 1) + (vts.size - (v_star_idx + 1)) := by omega
    conv_lhs => rw [List.range_eq_range', h_sum, ← List.range'_append_1]
    simp [List.range_eq_range']
  rw [h_split, List.foldl_append]
  -- After processing List.range (v_star_idx + 1): position v_star_idx has value t₀,
  -- first = false (because at index v_star_idx, arr[v_star_idx] = t₀ triggered the flip).
  -- Key claim: fold over List.range (v_star_idx + 1) starting from (vts, true, false) gives
  --            (vts, false, false).
  have h_prefix : (List.range (v_star_idx + 1)).foldl (btStep t₀) (vts, true, false) =
                    (vts, false, false) := by
    -- List.range (v_star_idx + 1) = List.range v_star_idx ++ [v_star_idx]
    rw [List.range_succ, List.foldl_append]
    -- First: fold over List.range v_star_idx (no targets) is a no-op.
    have h_pre : (List.range v_star_idx).foldl (btStep t₀) (vts, true, false) = (vts, true, false) := by
      apply btFold_no_target
      intro i hi
      exact hv_min i (List.mem_range.mp hi)
    rw [h_pre]
    -- Now step at v_star_idx with (vts, true, false)
    simp only [List.foldl_cons, List.foldl_nil]
    -- btStep t₀ (vts, true, false) v_star_idx = ?
    have hcmp : (vts.getD v_star_idx 0 == t₀) = true := by
      rw [hv_val]; exact beq_self_eq_true _
    show btStep t₀ (vts, true, false) v_star_idx = (vts, false, false)
    unfold btStep
    rw [if_pos hcmp]
    rfl
  rw [h_prefix]
  -- Now the goal is: fold over List.range' (v_star_idx + 1) ... starting from (vts, false, false)
  -- evaluates at position v_star_idx to t₀. Since v_star_idx is not in the suffix list, the
  -- position's value is preserved.
  have h_notin : v_star_idx ∉ List.range' (v_star_idx + 1) (vts.size - (v_star_idx + 1)) := by
    intro h
    rcases List.mem_range'.mp h with ⟨hge, _⟩
    omega
  rw [btFold_getD_not_mem t₀ _ (vts, false, false) v_star_idx h_notin]
  exact hv_val

/-- `breakTie` promotes every other target-valued position to `t₀ + 1`. -/
theorem breakTie_getD_at_other (vts : Array VertexType) (t₀ : VertexType)
    {v_star_idx : Nat} (hv_size : v_star_idx < vts.size)
    (hv_val : vts.getD v_star_idx 0 = t₀)
    (hv_min : ∀ i, i < v_star_idx → vts.getD i 0 ≠ t₀)
    {w_idx : Nat} (hw_size : w_idx < vts.size)
    (hw_val : vts.getD w_idx 0 = t₀)
    (hw_ne : w_idx ≠ v_star_idx) :
    (breakTie vts t₀).1.getD w_idx 0 = t₀ + 1 := by
  rw [breakTie_eq_fold]
  -- w_idx > v_star_idx (since v_star is min and w ≠ v_star).
  have hw_gt : v_star_idx < w_idx := by
    rcases lt_or_ge w_idx v_star_idx with hlt | hge
    · exact absurd hw_val (hv_min w_idx hlt)
    · exact lt_of_le_of_ne hge (Ne.symm hw_ne)
  -- Same split as before.
  have h_split : List.range vts.size =
      (List.range (v_star_idx + 1)) ++ List.range' (v_star_idx + 1) (vts.size - (v_star_idx + 1)) := by
    have h_sum : vts.size = (v_star_idx + 1) + (vts.size - (v_star_idx + 1)) := by omega
    conv_lhs => rw [List.range_eq_range', h_sum, ← List.range'_append_1]
    simp [List.range_eq_range']
  rw [h_split, List.foldl_append]
  have h_prefix : (List.range (v_star_idx + 1)).foldl (btStep t₀) (vts, true, false) =
                    (vts, false, false) := by
    rw [List.range_succ, List.foldl_append]
    have h_pre : (List.range v_star_idx).foldl (btStep t₀) (vts, true, false) = (vts, true, false) := by
      apply btFold_no_target
      intro i hi
      exact hv_min i (List.mem_range.mp hi)
    rw [h_pre]
    simp only [List.foldl_cons, List.foldl_nil]
    have hcmp : (vts.getD v_star_idx 0 == t₀) = true := by
      rw [hv_val]; exact beq_self_eq_true _
    show btStep t₀ (vts, true, false) v_star_idx = (vts, false, false)
    unfold btStep
    rw [if_pos hcmp]
    rfl
  rw [h_prefix]
  -- Suffix fold starting from (vts, false, false); w_idx ∈ suffix, value = t₀ at w_idx.
  have h_mem : w_idx ∈ List.range' (v_star_idx + 1) (vts.size - (v_star_idx + 1)) :=
    List.mem_range'_1.mpr ⟨by omega, by omega⟩
  have h_nd : (List.range' (v_star_idx + 1) (vts.size - (v_star_idx + 1))).Nodup :=
    List.nodup_range' (step := 1) (by decide)
  show (List.foldl (btStep t₀) (vts, false, false)
           (List.range' (v_star_idx + 1) (vts.size - (v_star_idx + 1)))).1.getD w_idx 0 = t₀ + 1
  exact btFold_from_notfirst_getD t₀ _ h_nd vts false w_idx h_mem hw_val hw_size

/-- **§5.1**  `TypedAut` after `breakTie` is the `v*`-stabilizer of the original.

Let `t₀` be the smallest tied value, `v* := min (typeClass vts t₀)` (by `Fin` order), and
`vts' := (breakTie vts t₀).1`. Then a permutation σ belongs to `TypedAut G vts'` iff it
belongs to `TypedAut G vts` and additionally fixes `v*`.

**Required hypotheses beyond the plan sketch.**

  - `hsize : vts.size = n` — in the algorithm, `vts` always has size exactly `n`. This is
    needed to connect `Fin n` indexing to `Array.getD`.
  - `hAutInv : ∀ σ ∈ G.Aut, VtsInvariant σ vts` — `vts` is `Aut(G)`-invariant. This extra
    assumption (compared to the original plan) is genuinely necessary. Without it, the
    (⟹) direction fails: if `vts` contains a value `t₀ + 1` at some position outside
    `typeClass vts t₀`, a label-swap between that position and a non-`v*` member of
    `typeClass t₀` preserves `vts'` (both acquire value `t₀ + 1`) but not `vts` (they had
    different values in `vts`). `Aut(G)`-invariance rules this out: if such a swap is an
    automorphism of `G`, then Aut-invariance forces the two positions to already have the
    same value in `vts`, contradicting the setup. In the algorithm's usage (see §7's
    prefix invariant), `vts` is always Aut-invariant at each `breakTie` call, so the
    hypothesis is satisfied.

**Proof.** By the characterizations `breakTie_getD_at_min`, `breakTie_getD_at_other`, and
`breakTie_getD_of_ne`, the output of `breakTie vts t₀` has value `t₀` exactly at `v*`,
value `t₀ + 1` at every `w ∈ typeClass vts t₀ \ {v*}`, and preserves `vts` elsewhere.

  - (⟹) `σ ∈ TypedAut G vts'` means `σ ∈ Aut G` and `σ` preserves `vts'`. By Aut-invariance
        of `vts`, `σ ∈ Aut G` already implies `σ` preserves `vts`; so `σ ∈ TypedAut G vts`.
        For `σ v* = v*`: the unique `vts'`-value-`t₀` vertex is `v*`, and σ must send it
        to itself (since σ preserves vts').

  - (⟸) Case analysis on `vts[v]`: same/same, in-class/in-class-not-star (σ permutes
        `typeClass t₀ \ {v*}` because it preserves vts and fixes v_star), or outside/outside.
-/
theorem breakTie_Aut_stabilizer
    (G : AdjMatrix n) (vts : Array VertexType) (t₀ : VertexType) (v_star : Fin n)
    (hsize : vts.size = n)
    (hAutInv : ∀ σ ∈ G.Aut, VtsInvariant σ vts)
    (hmin : ∀ w ∈ @typeClass n vts t₀, v_star.val ≤ w.val)
    (hmem : v_star ∈ @typeClass n vts t₀) :
    ∀ σ : Equiv.Perm (Fin n),
      σ ∈ G.TypedAut (breakTie vts t₀).1 ↔
      (σ ∈ G.TypedAut vts ∧ σ v_star = v_star) := by
  intro σ
  have hv_size : v_star.val < vts.size := hsize ▸ v_star.isLt
  have hv_val : vts.getD v_star.val 0 = t₀ := hmem
  -- Convert hmin to the form required by the characterization lemmas.
  have hv_min : ∀ i, i < v_star.val → vts.getD i 0 ≠ t₀ := by
    intro i hi heq
    have hi_lt_n : i < n := lt_of_lt_of_le hi (by
      have := v_star.isLt; omega)
    have hle : v_star.val ≤ i := hmin ⟨i, hi_lt_n⟩ heq
    omega
  -- Position-by-position characterization of (breakTie vts t₀).1.
  have h_vstar : (breakTie vts t₀).1.getD v_star.val 0 = t₀ :=
    breakTie_getD_at_min vts t₀ hv_size hv_val hv_min
  have h_other : ∀ w : Fin n, vts.getD w.val 0 = t₀ → w ≠ v_star →
      (breakTie vts t₀).1.getD w.val 0 = t₀ + 1 := by
    intro w hw hne
    have hw_size : w.val < vts.size := hsize ▸ w.isLt
    have hne_val : w.val ≠ v_star.val := fun h => hne (Fin.ext h)
    exact breakTie_getD_at_other vts t₀ hv_size hv_val hv_min hw_size hw hne_val
  have h_out : ∀ w : Fin n, vts.getD w.val 0 ≠ t₀ →
      (breakTie vts t₀).1.getD w.val 0 = vts.getD w.val 0 :=
    fun w hw => breakTie_getD_of_ne vts t₀ hw
  constructor
  · -- (⟹)
    rintro ⟨hGσ, hvσ'⟩
    have hσAut : σ ∈ G.Aut := hGσ
    have hvσ : VtsInvariant σ vts := hAutInv σ hσAut
    -- Show σ v_star = v_star: only v_star has vts' value t₀.
    have hfix : σ v_star = v_star := by
      by_contra hne
      have hσv_val : (breakTie vts t₀).1.getD (σ v_star).val 0 = t₀ := by
        rw [hvσ' v_star, h_vstar]
      by_cases hin : vts.getD (σ v_star).val 0 = t₀
      · -- σ v_star ∈ typeClass, σ v_star ≠ v_star ⟹ value t₀ + 1, not t₀
        have := h_other (σ v_star) hin hne
        rw [this] at hσv_val
        exact VertexType_add_one_ne t₀ hσv_val
      · -- σ v_star ∉ typeClass ⟹ value = vts[σ v_star] ≠ t₀
        have := h_out (σ v_star) hin
        rw [this] at hσv_val
        exact hin hσv_val
    exact ⟨⟨hGσ, hvσ⟩, hfix⟩
  · -- (⟸)
    rintro ⟨⟨hGσ, hvσ⟩, hfix⟩
    refine ⟨hGσ, ?_⟩
    intro v
    by_cases hv : vts.getD v.val 0 = t₀
    · -- v ∈ typeClass
      have hσv : vts.getD (σ v).val 0 = t₀ := by rw [hvσ v, hv]
      by_cases hv_eq : v = v_star
      · subst hv_eq; rw [hfix]
      · -- v ≠ v_star
        have hσv_ne : σ v ≠ v_star := by
          intro h
          apply hv_eq
          apply σ.injective
          rw [h, hfix]
        rw [h_other v hv hv_eq, h_other (σ v) hσv hσv_ne]
    · -- v ∉ typeClass
      have hσv : vts.getD (σ v).val 0 ≠ t₀ := by rw [hvσ v]; exact hv
      rw [h_out v hv, h_out (σ v) hσv, hvσ v]

/-- **§5.1 (corollary)**  Non-strict inclusion `TypedAut(breakTie vts t₀) ≤ TypedAut vts`.

The ≤ direction of §5.2. Given the §5.1 biconditional, `TypedAut vts' = {σ ∈ TypedAut vts |
σ v_star = v_star}`, which is trivially ≤ `TypedAut vts`. Unlike the strict version, this
does not require any orbit-connectivity hypothesis. -/
theorem breakTie_TypedAut_le
    (G : AdjMatrix n) (vts : Array VertexType) (t₀ : VertexType)
    (hsize : vts.size = n)
    (hAutInv : ∀ σ ∈ G.Aut, VtsInvariant σ vts)
    (v_star : Fin n)
    (hmin : ∀ w ∈ @typeClass n vts t₀, v_star.val ≤ w.val)
    (hmem : v_star ∈ @typeClass n vts t₀) :
    G.TypedAut (breakTie vts t₀).1 ≤ G.TypedAut vts := by
  intro σ hσ
  exact (breakTie_Aut_stabilizer G vts t₀ v_star hsize hAutInv hmin hmem σ |>.mp hσ).1

/-- **§5.2**  Strict shrinking of `TypedAut` under `breakTie`.

**Requires `hmove`.** The original plan stated this with only `hAutInv` and `htwo`
(existence of two distinct vertices with value `t₀`). That is insufficient — strictness
requires that *some automorphism actually moves `v*`*. This is the `hmove` hypothesis.

In the algorithm's context, `hmove` follows from the fact that same-type vertices
(under an Aut-invariant typing) are in the same Aut-orbit, i.e., the "completeness"
of `convergeLoop`. That completeness is essentially the algorithm's correctness and is
not derivable from `Aut`-invariance alone. The plan implicitly assumed it; we make it
explicit here via `hmove`.

**Proof.**
  - (≤) by `breakTie_TypedAut_le` (uses §5.1).
  - (≠) by §5.1: `hmove` supplies some σ ∈ TypedAut G vts with σ v* ≠ v*, and §5.1 says
        such σ ∉ TypedAut G (breakTie vts t₀).1.
-/
theorem breakTie_strict_shrink
    (G : AdjMatrix n) (vts : Array VertexType) (t₀ : VertexType)
    (hsize : vts.size = n)
    (hAutInv : ∀ σ ∈ G.Aut, VtsInvariant σ vts)
    (v_star : Fin n)
    (hmin : ∀ w ∈ @typeClass n vts t₀, v_star.val ≤ w.val)
    (hmem : v_star ∈ @typeClass n vts t₀)
    (hmove : ∃ σ ∈ G.TypedAut vts, σ v_star ≠ v_star) :
    G.TypedAut (breakTie vts t₀).1 < G.TypedAut vts := by
  rw [lt_iff_le_and_ne]
  refine ⟨breakTie_TypedAut_le G vts t₀ hsize hAutInv v_star hmin hmem, ?_⟩
  intro heq
  obtain ⟨σ, hσ, hσmv⟩ := hmove
  -- σ is in TypedAut vts. If the subgroups were equal, σ would be in TypedAut vts'.
  -- By §5.1, that forces σ v_star = v_star, contradicting hσmv.
  have : σ ∈ G.TypedAut (breakTie vts t₀).1 := heq ▸ hσ
  have := (breakTie_Aut_stabilizer G vts t₀ v_star hsize hAutInv hmin hmem σ |>.mp this).2
  exact hσmv this

/-! ## §6  Tiebreak choice-independence (conceptual crux)

After `convergeLoop` produces an Aut(G)-invariant typing `vts`, the next `breakTie`
promotes all-but-one vertex of some type class. The plan's "choice-independence" claim is:

```
∀ v₁, v₂ ∈ typeClass vts t₀,
  (run the remainder of the pipeline starting from (G, bt(vts, v₁))) =
  (run the remainder of the pipeline starting from (G, bt(vts, v₂)))
```

where `bt(vts, v)` is the alternative-`breakTie` that keeps `v` at `t₀` and promotes the
rest. By §5.1 + §4, `bt(vts, v₁)` and `bt(vts, v₂)` are related by some τ ∈ TypedAut G vts
sending v₁ to v₂. The remainder of the pipeline is τ-equivariant (Stages B–D with σ := τ)
and the final `labelEdgesAccordingToRankings` step produces the same matrix for both
choices because the final typing has all-distinct values.

The algorithm always picks the lowest-index representative, but the theorem says *any*
choice would have produced the same canonical output — that's what makes the canonical
output a graph invariant.

**Proof sketch.** Strong induction on `|TypedAut G vts|`:

  * **Base** `|TypedAut G vts| = 1`. Then the trivial group is the only typed automorphism,
    so typed-invariance + σ = 1 forces `vts` to have all values distinct. No further
    `breakTie` fires non-trivially, and `labelEdgesAccordingToRankings` with a
    distinct-valued typing is deterministic. The two pipeline runs reduce to the same.

  * **Step** `|TypedAut G vts| > 1`. Then some class `typeClass vts t₀` has size ≥ 2 and
    `TypedAut G bt(vts, _)` is strictly smaller (§5.2). The two choices
    `bt(vts, v₁)`, `bt(vts, v₂)` are related by τ ∈ TypedAut G vts with τ v₁ = v₂; by
    Stage B equivariance the ranks after the next `convergeLoop` are τ-related; by the IH,
    the rest of the pipeline on the two inputs produces the same final canonical matrix.

**Finiteness measure.** `Fintype.card (TypedAut G vts)` is well-defined because
`Equiv.Perm (Fin n)` is finite (of cardinality `n!`) and `TypedAut G vts` is a subgroup.
Strong induction on this finite cardinality is well-founded.

**Dependencies.** Uses §3 (Stage B + Stage C equivariance) and §5 (the two `breakTie`
theorems). This is the single step the flat old proof could not formulate — the flat
proof tried to assert a single-orbit `breakTie` equivariance, which is false; the correct
phrasing is choice-independence *modulo the full pipeline*, which is what this theorem
captures.
-/

/-- Running the pipeline from an intermediate typing. This is the "remainder of the
pipeline" referenced in §6 — feed a typing in, run the remaining `orderVertices` outer
iterations and the final `labelEdgesAccordingToRankings`, and produce the canonical
matrix. -/
def runFrom {n : Nat} (start : Nat) (vts : Array VertexType) (G : AdjMatrix n) :
    AdjMatrix n :=
  let state := initializePaths G
  let orderedRanks := (List.range (state.vertexCount - start)).foldl
    (fun currentTypes targetPosition =>
      let convergedTypes := convergeLoop state currentTypes state.vertexCount
      (breakTie convergedTypes (Int.ofNat (start + targetPosition))).1)
    vts
  labelEdgesAccordingToRankings orderedRanks G

/-- `breakTieAt vts t₀ keep`: the "what if we had kept vertex `keep` instead of
`min (typeClass vts t₀)`" alternative to `breakTie`. Promotes every vertex with value
`t₀` except `keep` to `t₀ + 1`. The algorithm's actual `breakTie` corresponds to
`breakTieAt vts t₀ (min (typeClass vts t₀))`. -/
def breakTieAt {n : Nat} (vts : Array VertexType) (t₀ : VertexType) (keep : Fin n) :
    Array VertexType :=
  (List.finRange n).foldl
    (fun acc v =>
      if acc.getD v.val 0 = t₀ ∧ v ≠ keep then acc.set! v.val (t₀ + 1) else acc)
    vts

/-- **§6** Tiebreak choice-independence.

For any Aut(G)-invariant typing `vts`, any smallest-tied value `t₀`, and any two vertices
`v₁`, `v₂ ∈ typeClass vts t₀`, running the rest of the pipeline from
`breakTieAt vts t₀ v₁` vs. `breakTieAt vts t₀ v₂` produces the same canonical matrix.

In the algorithm, the fixed choice `v* := min (typeClass vts t₀)` is used; this theorem
says the canonical output would be *identical* if any other representative were chosen
(which is why the algorithm's canonical output is a graph invariant).

**Proof plan.** Strong induction on `|TypedAut G vts|`, closed by §3 (Stages B–D
equivariance), §4 (convergeLoop Aut-invariance), and §5 (breakTie theorems).
See the section header above for the full sketch.
-/
theorem tiebreak_choice_independent
    (G : AdjMatrix n) (start : Nat) (vts : Array VertexType) (t₀ : VertexType)
    (v₁ v₂ : Fin n)
    (_hAutInv : ∀ σ ∈ G.Aut, VtsInvariant σ vts)
    (_hv₁ : v₁ ∈ @typeClass n vts t₀) (_hv₂ : v₂ ∈ @typeClass n vts t₀) :
    runFrom (start + 1) (breakTieAt vts t₀ v₁) G =
    runFrom (start + 1) (breakTieAt vts t₀ v₂) G := by
  sorry

end Graph
