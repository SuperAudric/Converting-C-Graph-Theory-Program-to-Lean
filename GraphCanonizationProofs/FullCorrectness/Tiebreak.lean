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
[sparse→dense] `breakTie` is now `breakTiePromote ∘ shiftAbove` (gated on the
target-class size). The two-stage decomposition is reflected in the lemma layout below:
first we describe the inner `breakTiePromote` fold (size, getD characterizations), then
we lift via `shiftAbove` lemmas to the outer `breakTie`.

After the full pipeline:

  - size is preserved;
  - positions with value strictly **less** than `t₀` keep their value;
  - positions with value strictly **greater** than `t₀` are bumped to `value + 1`;
  - the **first** position (smallest-index) with value `t₀` keeps `t₀`;
  - every other position with value `t₀` is promoted to `t₀ + 1`.

If the target class has size `< 2`, `breakTie` is the identity (no shift, no promote);
the per-position characterizations specialize to "output = input" in this case.
-/

/-! #### `shiftAbove` lemmas [sparse→dense] -/

theorem shiftAbove_size (t₀ : VertexType) (vts : Array VertexType) :
    (shiftAbove t₀ vts).size = vts.size := by
  unfold shiftAbove; simp

/-- Unified pointwise characterization of `shiftAbove`: at every position, the output is
the input value, possibly bumped by 1 if it exceeded `t₀`. The `0` default works because
`f 0 = 0` (zero is never `> t₀` for a `Nat` `t₀`). -/
theorem shiftAbove_getD (t₀ : VertexType) (vts : Array VertexType) (j : Nat) :
    (shiftAbove t₀ vts).getD j 0 =
      (if vts.getD j 0 > t₀ then vts.getD j 0 + 1 else vts.getD j 0) := by
  unfold shiftAbove
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  rcases h : vts[j]? with _ | x
  · simp
  · simp [Option.map, Option.getD]

theorem shiftAbove_getD_below (t₀ : VertexType) (vts : Array VertexType)
    {j : Nat} (hj : vts.getD j 0 ≤ t₀) :
    (shiftAbove t₀ vts).getD j 0 = vts.getD j 0 := by
  rw [shiftAbove_getD]
  have : ¬ (vts.getD j 0 > t₀) := Nat.not_lt.mpr hj
  rw [if_neg this]

theorem shiftAbove_getD_above (t₀ : VertexType) (vts : Array VertexType)
    {j : Nat} (hj : vts.getD j 0 > t₀) :
    (shiftAbove t₀ vts).getD j 0 = vts.getD j 0 + 1 := by
  rw [shiftAbove_getD]
  rw [if_pos hj]

theorem shiftAbove_getD_target (t₀ : VertexType) (vts : Array VertexType) (j : Nat)
    (hj : vts.getD j 0 = t₀) :
    (shiftAbove t₀ vts).getD j 0 = t₀ := by
  rw [shiftAbove_getD_below t₀ vts (le_of_eq hj), hj]

/-! #### `breakTie` composition lemmas [sparse→dense] -/

/-- Number of target-valued positions in `vts`. Definitionally equal to the count
expression appearing inside `breakTie`. -/
def breakTieCount (vts : Array VertexType) (t₀ : VertexType) : Nat :=
  vts.foldl (fun c v => if v == t₀ then c + 1 else c) 0

/-- `breakTie` is the identity when the target class has fewer than 2 elements. -/
theorem breakTie_noop (vts : Array VertexType) (t₀ : VertexType)
    (hcount : breakTieCount vts t₀ < 2) :
    breakTie vts t₀ = (vts, false) := by
  unfold breakTie
  show (if breakTieCount vts t₀ < 2 then (vts, false)
        else breakTiePromote (shiftAbove t₀ vts) t₀) = (vts, false)
  simp [hcount]

/-- When the target class has at least 2 elements, `breakTie` is `breakTiePromote ∘ shiftAbove`. -/
theorem breakTie_eq_promote_shift (vts : Array VertexType) (t₀ : VertexType)
    (hcount : 2 ≤ breakTieCount vts t₀) :
    breakTie vts t₀ = breakTiePromote (shiftAbove t₀ vts) t₀ := by
  unfold breakTie
  show (if breakTieCount vts t₀ < 2 then (vts, false)
        else breakTiePromote (shiftAbove t₀ vts) t₀)
        = breakTiePromote (shiftAbove t₀ vts) t₀
  simp [by omega]


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

/-- `breakTiePromote` unfolded into the `btStep` fold. Proved via pointwise function
extensionality on the lambda body (both bodies reduce to the same `match` expression on a
3-tuple). [sparse→dense] Renamed from `breakTie_eq_fold`: the body of `breakTiePromote`
is the body of the original `breakTie`, so this lemma's statement and proof are unchanged
modulo the rename. -/
private theorem breakTiePromote_eq_fold (vts : Array VertexType) (t₀ : VertexType) :
    breakTiePromote vts t₀ =
      let triple := (List.range vts.size).foldl (btStep t₀) (vts, true, false)
      (triple.1, triple.2.2) := by
  unfold breakTiePromote btStep
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

/-- `breakTiePromote` preserves array size. -/
theorem breakTiePromote_size (vts : Array VertexType) (t₀ : VertexType) :
    (breakTiePromote vts t₀).1.size = vts.size := by
  rw [breakTiePromote_eq_fold]
  exact btFold_size t₀ _ (vts, true, false)

/-- `breakTiePromote` leaves untouched any position whose value is not the target. -/
theorem breakTiePromote_getD_of_ne (vts : Array VertexType) (t₀ : VertexType)
    {j : Nat} (hj : vts.getD j 0 ≠ t₀) :
    (breakTiePromote vts t₀).1.getD j 0 = vts.getD j 0 := by
  rw [breakTiePromote_eq_fold]
  exact btFold_getD_ne t₀ _ (vts, true, false) j hj

/-- `breakTie` preserves array size. -/
theorem breakTie_size (vts : Array VertexType) (t₀ : VertexType) :
    (breakTie vts t₀).1.size = vts.size := by
  by_cases hcount : breakTieCount vts t₀ < 2
  · rw [breakTie_noop vts t₀ hcount]
  · rw [breakTie_eq_promote_shift vts t₀ (by omega),
        breakTiePromote_size, shiftAbove_size]

/-- [sparse→dense] `breakTie` leaves positions with value `< t₀` unchanged. -/
theorem breakTie_getD_below (vts : Array VertexType) (t₀ : VertexType)
    {j : Nat} (hj : vts.getD j 0 < t₀) :
    (breakTie vts t₀).1.getD j 0 = vts.getD j 0 := by
  by_cases hcount : breakTieCount vts t₀ < 2
  · rw [breakTie_noop vts t₀ hcount]
  · have hcount' : 2 ≤ breakTieCount vts t₀ := Nat.le_of_not_lt hcount
    rw [breakTie_eq_promote_shift vts t₀ hcount']
    have hshift : (shiftAbove t₀ vts).getD j 0 = vts.getD j 0 :=
      shiftAbove_getD_below t₀ vts (le_of_lt hj)
    have hne : (shiftAbove t₀ vts).getD j 0 ≠ t₀ := by
      rw [hshift]; exact ne_of_lt hj
    rw [breakTiePromote_getD_of_ne (shiftAbove t₀ vts) t₀ hne, hshift]

/-- [sparse→dense] `breakTie` bumps positions with value `> t₀` up by one — but only when
the breakTie actually fires (target class has ≥ 2 members). When the class has < 2 members,
`breakTie` is the identity and values above `t₀` are also unchanged; see
`breakTie_getD_above_or` below for the disjunctive version that handles both cases. -/
theorem breakTie_getD_above (vts : Array VertexType) (t₀ : VertexType)
    (hcount : 2 ≤ breakTieCount vts t₀)
    {j : Nat} (hj : vts.getD j 0 > t₀) :
    (breakTie vts t₀).1.getD j 0 = vts.getD j 0 + 1 := by
  rw [breakTie_eq_promote_shift vts t₀ hcount]
  have hshift : (shiftAbove t₀ vts).getD j 0 = vts.getD j 0 + 1 :=
    shiftAbove_getD_above t₀ vts hj
  have hne : (shiftAbove t₀ vts).getD j 0 ≠ t₀ := by
    rw [hshift]
    exact Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt hj))
  rw [breakTiePromote_getD_of_ne (shiftAbove t₀ vts) t₀ hne, hshift]

/-- [sparse→dense] Disjunctive form covering both gating branches: a position with value
`> t₀` is either preserved (no-op when target class has < 2 members) or bumped (when the
breakTie fires). Convenient when callers don't want to case-split on `breakTieCount`. -/
theorem breakTie_getD_above_or (vts : Array VertexType) (t₀ : VertexType)
    {j : Nat} (hj : vts.getD j 0 > t₀) :
    (breakTie vts t₀).1.getD j 0 = vts.getD j 0 ∨
    (breakTie vts t₀).1.getD j 0 = vts.getD j 0 + 1 := by
  by_cases hcount : breakTieCount vts t₀ < 2
  · rw [breakTie_noop vts t₀ hcount]; exact Or.inl rfl
  · exact Or.inr (breakTie_getD_above vts t₀ (by omega) hj)

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

/-- `t₀ + 1 ≠ t₀` for any natural number `t₀`. -/
private theorem VertexType_add_one_ne (t₀ : VertexType) : t₀ + 1 ≠ t₀ :=
  Nat.succ_ne_self t₀

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

/-- `breakTiePromote` leaves the minimum-index target-valued position at value `t₀`.
Requires `v_star` is the unique minimum: no earlier index has value `t₀` in `vts`.
[sparse→dense] Renamed from `breakTie_getD_at_min`; now describes the inner `breakTiePromote`
stage. The corresponding `breakTie`-level lemma is below, derived via `shiftAbove`. -/
theorem breakTiePromote_getD_at_min (vts : Array VertexType) (t₀ : VertexType)
    {v_star_idx : Nat} (hv_size : v_star_idx < vts.size)
    (hv_val : vts.getD v_star_idx 0 = t₀)
    (hv_min : ∀ i, i < v_star_idx → vts.getD i 0 ≠ t₀) :
    (breakTiePromote vts t₀).1.getD v_star_idx 0 = t₀ := by
  rw [breakTiePromote_eq_fold]
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

/-- `breakTiePromote` promotes every other target-valued position to `t₀ + 1`.
[sparse→dense] Renamed from `breakTie_getD_at_other`; the corresponding `breakTie`-level
lemma is below. -/
theorem breakTiePromote_getD_at_other (vts : Array VertexType) (t₀ : VertexType)
    {v_star_idx : Nat} (hv_size : v_star_idx < vts.size)
    (hv_val : vts.getD v_star_idx 0 = t₀)
    (hv_min : ∀ i, i < v_star_idx → vts.getD i 0 ≠ t₀)
    {w_idx : Nat} (hw_size : w_idx < vts.size)
    (hw_val : vts.getD w_idx 0 = t₀)
    (hw_ne : w_idx ≠ v_star_idx) :
    (breakTiePromote vts t₀).1.getD w_idx 0 = t₀ + 1 := by
  rw [breakTiePromote_eq_fold]
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

/-! #### Composing `breakTie = breakTiePromote ∘ shiftAbove` [sparse→dense]

The next two lemmas lift `breakTiePromote_getD_at_min` / `..._at_other` to the top-level
`breakTie` by chasing through the `shiftAbove` pre-pass. The key observations:

  - `shiftAbove` does not touch positions with value `≤ t₀` (in particular, target-valued
    positions stay at `t₀`), so the inner `breakTiePromote` sees the same target class.
  - Positions with value `≠ t₀` in `vts` remain `≠ t₀` after shift (values `< t₀` are
    untouched; values `> t₀` get bumped to `> t₀ + 1`, still `≠ t₀`). So the `hv_min`
    hypothesis lifts cleanly to `shiftAbove t₀ vts`. -/

private theorem shiftAbove_getD_ne_target (t₀ : VertexType) (vts : Array VertexType)
    {j : Nat} (hj : vts.getD j 0 ≠ t₀) :
    (shiftAbove t₀ vts).getD j 0 ≠ t₀ := by
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · rw [shiftAbove_getD_below t₀ vts (le_of_lt hlt)]; exact hj
  · rw [shiftAbove_getD_above t₀ vts hgt]
    exact Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt hgt))

theorem breakTie_getD_at_min (vts : Array VertexType) (t₀ : VertexType)
    {v_star_idx : Nat} (hv_size : v_star_idx < vts.size)
    (hv_val : vts.getD v_star_idx 0 = t₀)
    (hv_min : ∀ i, i < v_star_idx → vts.getD i 0 ≠ t₀) :
    (breakTie vts t₀).1.getD v_star_idx 0 = t₀ := by
  by_cases hcount : breakTieCount vts t₀ < 2
  · rw [breakTie_noop vts t₀ hcount]; exact hv_val
  · rw [breakTie_eq_promote_shift vts t₀ (by omega)]
    have hsz : v_star_idx < (shiftAbove t₀ vts).size := by
      rw [shiftAbove_size]; exact hv_size
    have hval : (shiftAbove t₀ vts).getD v_star_idx 0 = t₀ :=
      shiftAbove_getD_target t₀ vts v_star_idx hv_val
    have hmin : ∀ i, i < v_star_idx → (shiftAbove t₀ vts).getD i 0 ≠ t₀ :=
      fun i hi => shiftAbove_getD_ne_target t₀ vts (hv_min i hi)
    exact breakTiePromote_getD_at_min (shiftAbove t₀ vts) t₀ hsz hval hmin

/-- Counting helper: two distinct in-bounds positions with value `t₀` give `count ≥ 2`.
[sparse→dense] Single-purpose lemma, isolated as a `sorry` for now — the formal proof is
a routine induction on `vts.toList` that extracts both contributions to the foldl. The
content is straightforwardly true; pinning it as a focused obligation keeps the
breakTie-level proofs structurally clean. -/
private theorem breakTieCount_ge_two_of_distinct (vts : Array VertexType) (t₀ : VertexType)
    (i j : Nat) (hi_size : i < vts.size) (hj_size : j < vts.size) (hij : i ≠ j)
    (hi_val : vts.getD i 0 = t₀) (hj_val : vts.getD j 0 = t₀) :
    2 ≤ breakTieCount vts t₀ := by
  sorry

theorem breakTie_getD_at_other (vts : Array VertexType) (t₀ : VertexType)
    {v_star_idx : Nat} (hv_size : v_star_idx < vts.size)
    (hv_val : vts.getD v_star_idx 0 = t₀)
    (hv_min : ∀ i, i < v_star_idx → vts.getD i 0 ≠ t₀)
    {w_idx : Nat} (hw_size : w_idx < vts.size)
    (hw_val : vts.getD w_idx 0 = t₀)
    (hw_ne : w_idx ≠ v_star_idx) :
    (breakTie vts t₀).1.getD w_idx 0 = t₀ + 1 := by
  have hcount : 2 ≤ breakTieCount vts t₀ :=
    breakTieCount_ge_two_of_distinct vts t₀ v_star_idx w_idx hv_size hw_size
      (Ne.symm hw_ne) hv_val hw_val
  rw [breakTie_eq_promote_shift vts t₀ hcount]
  have hsz : v_star_idx < (shiftAbove t₀ vts).size := by
    rw [shiftAbove_size]; exact hv_size
  have hval : (shiftAbove t₀ vts).getD v_star_idx 0 = t₀ :=
    shiftAbove_getD_target t₀ vts v_star_idx hv_val
  have hmin : ∀ i, i < v_star_idx → (shiftAbove t₀ vts).getD i 0 ≠ t₀ :=
    fun i hi => shiftAbove_getD_ne_target t₀ vts (hv_min i hi)
  have hwsz : w_idx < (shiftAbove t₀ vts).size := by
    rw [shiftAbove_size]; exact hw_size
  have hwval : (shiftAbove t₀ vts).getD w_idx 0 = t₀ :=
    shiftAbove_getD_target t₀ vts w_idx hw_val
  exact breakTiePromote_getD_at_other (shiftAbove t₀ vts) t₀ hsz hval hmin hwsz hwval hw_ne

/-- **Disjunctive characterization.** For any in-bounds position `w` whose value in `vts`
is the target `t₀`, the breakTie output at `w` is *either* `t₀` (if `w` is the kept
representative) *or* `t₀ + 1` (if `w` was promoted). Useful when callers don't need to
know which alternative obtains. Derived from `breakTie_getD_at_min` /
`breakTie_getD_at_other` by picking `v_star` as the smallest target-valued index. -/
theorem breakTie_getD_target (vts : Array VertexType) (t₀ : VertexType)
    {w : Nat} (hw_size : w < vts.size) (hw : vts.getD w 0 = t₀) :
    (breakTie vts t₀).1.getD w 0 = t₀ ∨ (breakTie vts t₀).1.getD w 0 = t₀ + 1 := by
  classical
  -- The set of target-valued, in-bounds indices is non-empty (contains `w`).
  have h_ex : ∃ i, i < vts.size ∧ vts.getD i 0 = t₀ := ⟨w, hw_size, hw⟩
  set v_star := Nat.find h_ex with h_vstar_def
  have hv_spec : v_star < vts.size ∧ vts.getD v_star 0 = t₀ := Nat.find_spec h_ex
  have hv_min_raw : ∀ i, i < v_star → ¬ (i < vts.size ∧ vts.getD i 0 = t₀) :=
    fun i hi => Nat.find_min h_ex hi
  have hv_min : ∀ i, i < v_star → vts.getD i 0 ≠ t₀ := by
    intro i hi heq
    exact hv_min_raw i hi ⟨lt_trans hi hv_spec.1, heq⟩
  by_cases hwv : w = v_star
  · -- `w` is the smallest target-valued index — kept at `t₀`.
    subst hwv
    exact Or.inl (breakTie_getD_at_min vts t₀ hv_spec.1 hv_spec.2 hv_min)
  · -- `w` is some other target-valued index — promoted to `t₀ + 1`.
    exact Or.inr (breakTie_getD_at_other vts t₀ hv_spec.1 hv_spec.2 hv_min hw_size hw hwv)

/-- **Lower-bound corollary.** For target-valued positions, the breakTie output is at
least `t₀`. Convenient when only the lower bound matters (e.g., in the §7 prefix
invariant: tied values after `breakTie p` cannot drop below `p`). -/
theorem breakTie_getD_target_ge (vts : Array VertexType) (t₀ : VertexType)
    {w : Nat} (hw_size : w < vts.size) (hw : vts.getD w 0 = t₀) :
    t₀ ≤ (breakTie vts t₀).1.getD w 0 := by
  rcases breakTie_getD_target vts t₀ hw_size hw with h | h
  · exact le_of_eq h.symm
  · exact le_of_lt (h.symm ▸ Nat.lt_succ_self t₀)

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
  -- [sparse→dense] The "non-target preserved" facet now splits into below (always
  -- preserved) and above (preserved when no-op, bumped when fired). We expose unified
  -- "preserves σ-invariance" facets that work in both gating cases.
  have h_vstar : (breakTie vts t₀).1.getD v_star.val 0 = t₀ :=
    breakTie_getD_at_min vts t₀ hv_size hv_val hv_min
  have h_other : ∀ w : Fin n, vts.getD w.val 0 = t₀ → w ≠ v_star →
      (breakTie vts t₀).1.getD w.val 0 = t₀ + 1 := by
    intro w hw hne
    have hw_size : w.val < vts.size := hsize ▸ w.isLt
    have hne_val : w.val ≠ v_star.val := fun h => hne (Fin.ext h)
    exact breakTie_getD_at_other vts t₀ hv_size hv_val hv_min hw_size hw hne_val
  -- σ-invariance lifts to the post-breakTie array for any v with vts[v] ≠ t₀.
  -- This is the σ-relational replacement for the old `h_out` / `breakTie_getD_of_ne`.
  -- [sparse→dense] Case on whether the breakTie actually fires (count ≥ 2). In both
  -- cases σ-invariance carries through.
  have h_out_invariant : ∀ (σ : Equiv.Perm (Fin n)),
      VtsInvariant σ vts →
      ∀ v : Fin n, vts.getD v.val 0 ≠ t₀ →
        (breakTie vts t₀).1.getD (σ v).val 0 = (breakTie vts t₀).1.getD v.val 0 := by
    intro σ hvσ v hv
    by_cases hcount : breakTieCount vts t₀ < 2
    · -- noop: output = vts pointwise; σ-invariance is direct.
      rw [breakTie_noop vts t₀ hcount, hvσ v]
    · -- fired: split on below/above; both branches preserve σ-invariance.
      have hcount' : 2 ≤ breakTieCount vts t₀ := Nat.le_of_not_lt hcount
      rcases lt_or_gt_of_ne hv with hlt | hgt
      · have hσv_lt : vts.getD (σ v).val 0 < t₀ := by rw [hvσ v]; exact hlt
        rw [breakTie_getD_below vts t₀ hσv_lt, breakTie_getD_below vts t₀ hlt, hvσ v]
      · have hσv_gt : vts.getD (σ v).val 0 > t₀ := by rw [hvσ v]; exact hgt
        rw [breakTie_getD_above vts t₀ hcount' hσv_gt,
            breakTie_getD_above vts t₀ hcount' hgt, hvσ v]
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
      · -- σ v_star ∉ typeClass: by the σ-invariance lemma, output[σ v_star] = output[v_star] = t₀.
        -- But hin says vts[σ v_star] ≠ t₀, and below/above outputs are ≠ t₀.
        -- Direct: vts[σ v_star] < t₀ → output[σ v_star] = vts[σ v_star] ≠ t₀ ≠ t₀.
        --        vts[σ v_star] > t₀ → output[σ v_star] = vts[σ v_star] (noop) or +1 (fired);
        --                              both ≠ t₀.
        rcases lt_or_gt_of_ne hin with hlt | hgt
        · rw [breakTie_getD_below vts t₀ hlt] at hσv_val
          exact (Nat.ne_of_lt hlt) hσv_val
        · rcases breakTie_getD_above_or vts t₀ hgt with hk | hb
          · rw [hk] at hσv_val
            exact (Ne.symm (Nat.ne_of_lt hgt)) hσv_val
          · rw [hb] at hσv_val
            exact (Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt hgt))) hσv_val
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
      · have hσv_ne : σ v ≠ v_star := by
          intro h
          apply hv_eq
          apply σ.injective
          rw [h, hfix]
        rw [h_other v hv hv_eq, h_other (σ v) hσv hσv_ne]
    · -- v ∉ typeClass: σ-invariance carries through.
      exact h_out_invariant σ hvσ v hv

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
  let orderedRanks := (List.range (n - start)).foldl
    (fun currentTypes targetPosition =>
      let convergedTypes := convergeLoop state currentTypes n
      (breakTie convergedTypes (start + targetPosition)).1)
    vts
  labelEdgesAccordingToRankings orderedRanks G

/-! ### Pipeline τ-equivariance for `runFrom`

The single load-bearing reduction needed by §6. It says: for any `τ ∈ Aut G` and any two
`τ`-related input typings `arr₁, arr₂` (i.e., `arr₂[w] = arr₁[τ⁻¹ w]` for every vertex
`w`), the canonical matrix produced by `runFrom` is the same on both inputs.

**Why this is exactly §3 chained.** Inside `runFrom` the work is:
  1. `initializePaths G` — independent of the input typing.
  2. A `foldl` over `[0, …, n - start)` that alternates `convergeLoop` and `breakTie`.
     Each `convergeLoop` step preserves τ-relatedness of the typing array (Stage B + the
     `convergeLoop_Aut_invariant`-style argument generalized to the relational form: if
     `arr₂[w] = arr₁[τ⁻¹ w]` going in, the same relation holds coming out).
     Each `breakTie` step preserves τ-relatedness too: the smallest index in
     `typeClass arr_i t₀` differs by τ between the two arrays in exactly the way the
     τ-relation predicts (because the typeClass on `arr₂` is the τ-image of the typeClass
     on `arr₁`), so the promoted/kept positions correspond under τ.
  3. `labelEdgesAccordingToRankings` (Stage D): given τ-related rank arrays and `τ ∈ Aut G`,
     produces equal canonical matrices because the dense-rank/swap procedure factors out τ.

So this lemma is precisely the chained Stages B–D specialized to the bounded `runFrom`
loop. The `hτ : τ ∈ G.Aut` hypothesis is exactly what the Stage B–D theorems require. The
size hypotheses make the size of intermediate arrays computable (every `breakTie` and
`convergeLoop` step preserves array size).

**Status: stated, proof pending.** Once the four Stage A–D theorems in `Equivariance.lean`
are discharged, this reduction is mechanical (induct on the fold; apply Stage B/D at each
step). Listed as the single load-bearing sorry that §6 reduces to. -/
theorem runFrom_VtsInvariant_eq
    (G : AdjMatrix n) (s : Nat) (τ : Equiv.Perm (Fin n))
    (_hτ : τ ∈ G.Aut)
    (arr₁ arr₂ : Array VertexType)
    (_h_size₁ : arr₁.size = n) (_h_size₂ : arr₂.size = n)
    (_h_rel : ∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (τ⁻¹ w).val 0) :
    runFrom s arr₁ G = runFrom s arr₂ G := by
  sorry

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

/-! ### Characterizing `breakTieAt`

Each `Fin n` position in `List.finRange n` is visited exactly once (the list is `Nodup`),
and the only write at step `v` is at position `v.val`. So the value at position `w.val`
in the output is determined by the step at `w` alone:
  - `vts[w] ≠ t₀`: no promotion, value = `vts[w]`.
  - `vts[w] = t₀` and `w = keep`: no promotion (keep-exception), value = `t₀`.
  - `vts[w] = t₀` and `w ≠ keep`: promoted, value = `t₀ + 1`.

The structure of the proof mirrors the `breakTie` characterization but is simpler: no
`firstAppearance` flag to track. We factor out the step function and prove the invariants
as fold properties. -/

/-- The step function of `breakTieAt`, extracted. -/
private def bTAStep {n : Nat} (t₀ : VertexType) (keep : Fin n)
    (acc : Array VertexType) (v : Fin n) : Array VertexType :=
  if acc.getD v.val 0 = t₀ ∧ v ≠ keep then acc.set! v.val (t₀ + 1) else acc

private theorem breakTieAt_eq_fold (vts : Array VertexType) (t₀ : VertexType) (keep : Fin n) :
    breakTieAt vts t₀ keep = (List.finRange n).foldl (bTAStep t₀ keep) vts := rfl

private theorem bTAStep_size (t₀ : VertexType) (keep : Fin n)
    (acc : Array VertexType) (v : Fin n) :
    (bTAStep t₀ keep acc v).size = acc.size := by
  unfold bTAStep
  split_ifs <;> simp

private theorem bTAFold_size (t₀ : VertexType) (keep : Fin n) :
    ∀ (l : List (Fin n)) (acc : Array VertexType),
      (l.foldl (bTAStep t₀ keep) acc).size = acc.size
  | [], _ => rfl
  | x :: xs, acc => by
      rw [List.foldl_cons, bTAFold_size t₀ keep xs _, bTAStep_size]

/-- `breakTieAt` preserves array size. -/
theorem breakTieAt_size (vts : Array VertexType) (t₀ : VertexType) (keep : Fin n) :
    (breakTieAt vts t₀ keep).size = vts.size := by
  rw [breakTieAt_eq_fold]
  exact bTAFold_size t₀ keep _ vts

/-- After `bTAStep` at `v`, value at position `j ≠ v.val` is unchanged. -/
private theorem bTAStep_getD_ne (t₀ : VertexType) (keep : Fin n)
    (acc : Array VertexType) (v : Fin n) {j : Nat} (hj : v.val ≠ j) :
    (bTAStep t₀ keep acc v).getD j 0 = acc.getD j 0 := by
  unfold bTAStep
  split_ifs
  · simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
               Array.getElem?_setIfInBounds_ne hj]
  · rfl

/-- Across the fold over a list of distinct `Fin n`, positions not in the list are unchanged.
The `Nodup`ness of `List.finRange n` plus the observation that each step at `v` only writes
at position `v.val` gives us value preservation at any `j` we've visited exactly once. -/
private theorem bTAFold_getD_of_notin (t₀ : VertexType) (keep : Fin n) :
    ∀ (l : List (Fin n)) (acc : Array VertexType) (j : Nat),
      (∀ v ∈ l, v.val ≠ j) →
      (l.foldl (bTAStep t₀ keep) acc).getD j 0 = acc.getD j 0
  | [], _, _, _ => rfl
  | x :: xs, acc, j, hne => by
      rw [List.foldl_cons]
      have hx : x.val ≠ j := hne x List.mem_cons_self
      have hxs : ∀ v ∈ xs, v.val ≠ j := fun v hv => hne v (List.mem_cons_of_mem x hv)
      rw [bTAFold_getD_of_notin t₀ keep xs _ j hxs, bTAStep_getD_ne t₀ keep acc x hx]

/-- If after the step at `v` the value at `v.val` is no longer `t₀`, subsequent steps
don't re-promote (they check `== t₀` in the accumulator). Simpler but specialized form:
for positions outside `t₀`, the fold preserves the value. Follows from a "position-wise"
invariant: once position `v` carries a value not equal to `t₀`, it stays that way. -/
private theorem bTAFold_getD_of_ne (t₀ : VertexType) (keep : Fin n) :
    ∀ (l : List (Fin n)) (acc : Array VertexType) (j : Nat),
      acc.getD j 0 ≠ t₀ →
      (l.foldl (bTAStep t₀ keep) acc).getD j 0 = acc.getD j 0
  | [], _, _, _ => rfl
  | x :: xs, acc, j, hj => by
      rw [List.foldl_cons]
      have hstep : (bTAStep t₀ keep acc x).getD j 0 = acc.getD j 0 := by
        unfold bTAStep
        split_ifs with hif
        · by_cases hxj : x.val = j
          · -- x.val = j: but then acc.getD x.val 0 = acc.getD j 0 ≠ t₀,
            -- contradicting hif.1 which says acc.getD x.val 0 = t₀
            rw [hxj] at hif
            exact absurd hif.1 hj
          · simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
                       Array.getElem?_setIfInBounds_ne hxj]
        · rfl
      have hj' : (bTAStep t₀ keep acc x).getD j 0 ≠ t₀ := by rw [hstep]; exact hj
      rw [bTAFold_getD_of_ne t₀ keep xs _ j hj', hstep]

/-- `breakTieAt` preserves values at non-target positions. -/
theorem breakTieAt_getD_of_ne (vts : Array VertexType) (t₀ : VertexType) (keep : Fin n)
    {j : Nat} (hj : vts.getD j 0 ≠ t₀) :
    (breakTieAt vts t₀ keep).getD j 0 = vts.getD j 0 := by
  rw [breakTieAt_eq_fold]
  exact bTAFold_getD_of_ne t₀ keep _ vts j hj

/-- One step of `bTAStep` preserves the value at position `keep.val`. The step at
`keep` itself is a no-op because the `v ≠ keep` check fails; any other step writes at
`v.val ≠ keep.val`. -/
private theorem bTAStep_preserves_keep (t₀ : VertexType) (keep : Fin n)
    (acc : Array VertexType) (v : Fin n) :
    (bTAStep t₀ keep acc v).getD keep.val 0 = acc.getD keep.val 0 := by
  unfold bTAStep
  split_ifs with hif
  · have hne : v.val ≠ keep.val := fun h => hif.2 (Fin.ext h)
    simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
               Array.getElem?_setIfInBounds_ne hne]
  · rfl

private theorem bTAFold_preserves_keep (t₀ : VertexType) (keep : Fin n) :
    ∀ (l : List (Fin n)) (acc : Array VertexType),
      (l.foldl (bTAStep t₀ keep) acc).getD keep.val 0 = acc.getD keep.val 0
  | [], _ => rfl
  | x :: xs, acc => by
      rw [List.foldl_cons, bTAFold_preserves_keep t₀ keep xs _, bTAStep_preserves_keep]

/-- `breakTieAt` preserves the value at the kept vertex. -/
theorem breakTieAt_getD_keep (vts : Array VertexType) (t₀ : VertexType) (keep : Fin n) :
    (breakTieAt vts t₀ keep).getD keep.val 0 = vts.getD keep.val 0 := by
  rw [breakTieAt_eq_fold]
  exact bTAFold_preserves_keep t₀ keep _ vts

/-- The key promotion lemma: for `w ≠ keep` in a `Nodup` list with `acc[w.val] = t₀`,
the fold's output has `t₀ + 1` at position `w.val`. -/
private theorem bTAFold_getD_promoted (t₀ : VertexType) (keep : Fin n) :
    ∀ (l : List (Fin n)) (_hnd : l.Nodup) (acc : Array VertexType) (w : Fin n),
      w ∈ l → acc.getD w.val 0 = t₀ → w ≠ keep → w.val < acc.size →
      (l.foldl (bTAStep t₀ keep) acc).getD w.val 0 = t₀ + 1
  | [], _, _, _, hw, _, _, _ => absurd hw List.not_mem_nil
  | x :: xs, hnd, acc, w, hw, hwt, hw_ne, hw_size => by
      rw [List.foldl_cons]
      have hxnotin : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      rcases List.mem_cons.mp hw with hwx | hwxs
      · -- w = x: step at x promotes; rest is preserved at w.val.
        subst hwx
        have hstep_eq : bTAStep t₀ keep acc w = acc.set! w.val (t₀ + 1) := by
          unfold bTAStep
          rw [if_pos ⟨hwt, hw_ne⟩]
        rw [hstep_eq]
        have hjt' : (acc.set! w.val (t₀ + 1)).getD w.val 0 = t₀ + 1 := by
          simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
                     Array.getElem?_setIfInBounds_self_of_lt hw_size]
          rfl
        have hne' : (acc.set! w.val (t₀ + 1)).getD w.val 0 ≠ t₀ := by
          rw [hjt']; exact VertexType_add_one_ne t₀
        rw [bTAFold_getD_of_ne t₀ keep xs _ w.val hne']
        exact hjt'
      · -- w ∈ xs: step at x doesn't affect position w.val (x ≠ w by nodup).
        have hxneq : x ≠ w := fun h => hxnotin (h ▸ hwxs)
        have hxval : x.val ≠ w.val := fun h => hxneq (Fin.ext h)
        have hstep_at_w : (bTAStep t₀ keep acc x).getD w.val 0 = acc.getD w.val 0 :=
          bTAStep_getD_ne t₀ keep acc x hxval
        have hwt' : (bTAStep t₀ keep acc x).getD w.val 0 = t₀ := by rw [hstep_at_w]; exact hwt
        have hw_size' : w.val < (bTAStep t₀ keep acc x).size := by
          rw [bTAStep_size]; exact hw_size
        exact bTAFold_getD_promoted t₀ keep xs hnd' _ w hwxs hwt' hw_ne hw_size'

/-- `breakTieAt` promotes every non-keep target vertex to `t₀ + 1`. -/
theorem breakTieAt_getD_promoted (vts : Array VertexType) (t₀ : VertexType) (keep : Fin n)
    (hsize : vts.size = n) {w : Fin n}
    (hw_val : vts.getD w.val 0 = t₀) (hw_ne : w ≠ keep) :
    (breakTieAt vts t₀ keep).getD w.val 0 = t₀ + 1 := by
  rw [breakTieAt_eq_fold]
  have hw_size : w.val < vts.size := hsize ▸ w.isLt
  exact bTAFold_getD_promoted t₀ keep _ (List.nodup_finRange n) vts w
    (List.mem_finRange w) hw_val hw_ne hw_size

/-- **Equivariance of `breakTieAt` under a typed automorphism.**

If `τ : Equiv.Perm (Fin n)` preserves `vts` pointwise (i.e., `τ ∈ TypedAut G vts` for
graph-preserving τ — only `VtsInvariant` is used here), then the output of
`breakTieAt vts t₀ (τ keep)` is the `τ`-re-indexing of the output of `breakTieAt vts t₀
keep`: for any `w`, the value at position `w.val` in the `(τ keep)`-breakTie equals the
value at position `(τ⁻¹ w).val` in the `keep`-breakTie.

This is the first piece §6 needs: it says choosing `τ keep` instead of `keep` to preserve
amounts to a relabeling by `τ`. The second piece — that the *remainder of the pipeline*
commutes with this relabeling — is §3 equivariance and remains a `sorry`. -/
theorem breakTieAt_VtsInvariant_eq (vts : Array VertexType) (t₀ : VertexType)
    (τ : Equiv.Perm (Fin n)) (keep : Fin n)
    (hsize : vts.size = n) (hτvts : VtsInvariant τ vts) (w : Fin n) :
    (breakTieAt vts t₀ (τ keep)).getD w.val 0 =
      (breakTieAt vts t₀ keep).getD (τ⁻¹ w).val 0 := by
  -- `VtsInvariant τ⁻¹` gives `vts[(τ⁻¹ w)] = vts[w]`.
  have hτ_inv_vts : VtsInvariant τ⁻¹ vts := hτvts.inv
  have hvts_eq : vts.getD (τ⁻¹ w).val 0 = vts.getD w.val 0 := hτ_inv_vts w
  by_cases hw : vts.getD w.val 0 = t₀
  · -- w ∈ typeClass t₀
    have hτw : vts.getD (τ⁻¹ w).val 0 = t₀ := hvts_eq.trans hw
    by_cases h_eq : w = τ keep
    · -- w = τ keep → τ⁻¹ w = keep
      subst h_eq
      have h_inv_keep : τ⁻¹ (τ keep) = keep := by simp
      rw [breakTieAt_getD_keep, h_inv_keep, breakTieAt_getD_keep]
      exact hτvts keep
    · -- w ≠ τ keep, so τ⁻¹ w ≠ keep
      have h_neq : τ⁻¹ w ≠ keep := by
        intro h
        apply h_eq
        have : τ (τ⁻¹ w) = τ keep := by rw [h]
        simpa using this
      rw [breakTieAt_getD_promoted vts t₀ (τ keep) hsize hw h_eq,
          breakTieAt_getD_promoted vts t₀ keep hsize hτw h_neq]
  · -- w ∉ typeClass t₀
    have hτw : vts.getD (τ⁻¹ w).val 0 ≠ t₀ := hvts_eq.symm ▸ hw
    rw [breakTieAt_getD_of_ne vts t₀ (τ keep) hw,
        breakTieAt_getD_of_ne vts t₀ keep hτw]
    exact hvts_eq.symm

/-- **§6** Tiebreak choice-independence.

For any Aut(G)-invariant typing `vts`, any smallest-tied value `t₀`, and any two vertices
`v₁`, `v₂ ∈ typeClass vts t₀`, running the rest of the pipeline from
`breakTieAt vts t₀ v₁` vs. `breakTieAt vts t₀ v₂` produces the same canonical matrix.

**Required hypotheses beyond the plan sketch.**

  - `hsize : vts.size = n` — always satisfied by the algorithm.
  - `hconn : ∃ τ ∈ G.TypedAut vts, τ v₁ = v₂` — *orbit connectivity*. The plan's sketch
    took "same-type vertices lie in a single Aut-orbit" from §4, but §4 only proves the
    forward direction (same-orbit → same-type), not the reverse. The reverse is essentially
    the canonizer's completeness and must be provided as a separate input. In the
    algorithm, orbit connectivity is maintained throughout `orderVertices` — but proving
    that is the core correctness argument and is outside this lemma's scope. We surface
    the requirement as an explicit hypothesis.

**Proof (modulo §3).**

  1. By `hconn`, pick `τ ∈ TypedAut G vts` with `τ v₁ = v₂`.
  2. By `breakTieAt_VtsInvariant_eq`, `breakTieAt vts t₀ v₂` (= `breakTieAt vts t₀ (τ v₁)`)
     is the `τ`-relabeling of `breakTieAt vts t₀ v₁`.
  3. Apply pipeline-equivariance under `τ` (§3 Stages B–D + §4) to conclude the two
     `runFrom` values are equal. Step 3 is `sorry` pending §3.

**Remaining gap (sorry).** The reduction to §3 equivariance of `runFrom` under τ-related
inputs. In Lean terms, we need a lemma `runFrom_VtsInvariant_eq` stating:
`∀ τ ∈ G.Aut, ∀ arr₁ arr₂, (∀ w, arr₂[w] = arr₁[τ⁻¹ w]) → runFrom s arr₁ G = runFrom s arr₂ G`.
Given this, closing §6 is immediate from step 2. The lemma itself is §3 Stages B–D
chained together for the fuel-bounded loop.
-/
theorem tiebreak_choice_independent
    (G : AdjMatrix n) (start : Nat) (vts : Array VertexType) (t₀ : VertexType)
    (v₁ v₂ : Fin n)
    (hsize : vts.size = n)
    (_hAutInv : ∀ σ ∈ G.Aut, VtsInvariant σ vts)
    (_hv₁ : v₁ ∈ @typeClass n vts t₀) (_hv₂ : v₂ ∈ @typeClass n vts t₀)
    (hconn : ∃ τ ∈ G.TypedAut vts, τ v₁ = v₂) :
    runFrom (start + 1) (breakTieAt vts t₀ v₁) G =
    runFrom (start + 1) (breakTieAt vts t₀ v₂) G := by
  obtain ⟨τ, hτ, hτv⟩ := hconn
  -- τ is in TypedAut, so preserves G AND vts.
  have hτG : G.permute τ = G := hτ.1
  have hτAut : τ ∈ G.Aut := hτG
  have hτvts : VtsInvariant τ vts := hτ.2
  -- Rewrite v₂ as τ v₁ and apply breakTieAt τ-equivariance.
  have h_relabel : ∀ w : Fin n,
      (breakTieAt vts t₀ v₂).getD w.val 0 =
        (breakTieAt vts t₀ v₁).getD (τ⁻¹ w).val 0 := by
    intro w
    rw [show v₂ = τ v₁ from hτv.symm]
    exact breakTieAt_VtsInvariant_eq vts t₀ τ v₁ hsize hτvts w
  -- The two arrays are τ-related; both have size `n` (breakTieAt preserves size, and
  -- vts.size = n). The pipeline equivariance lemma `runFrom_VtsInvariant_eq` (§3 Stages
  -- B–D chained) collapses the τ-relation, giving equal final canonical matrices.
  have h_size₁ : (breakTieAt vts t₀ v₁).size = n := by
    rw [breakTieAt_size]; exact hsize
  have h_size₂ : (breakTieAt vts t₀ v₂).size = n := by
    rw [breakTieAt_size]; exact hsize
  exact runFrom_VtsInvariant_eq G (start + 1) τ hτAut
            (breakTieAt vts t₀ v₁) (breakTieAt vts t₀ v₂)
            h_size₁ h_size₂ h_relabel

end Graph
