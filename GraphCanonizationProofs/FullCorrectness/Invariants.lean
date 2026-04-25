import FullCorrectness.Equivariance.ConvergeLoop
import FullCorrectness.Tiebreak
import Mathlib.Tactic.IntervalCases

/-!
# §7  "Converged types are a prefix of ℕ" invariant

`orderVertices`' outer fold calls `breakTie convergedTypes targetPosition` at iteration
`targetPosition ∈ 0, …, n-1`. For §5/§6 to apply, the smallest repeated value at each
iteration must be exactly `targetPosition` — not some other tied value.

This module states the invariant that makes that work: after the first `p` iterations,
the typing takes values in a prefix of ℕ, specifically `{0, 1, …, p-1}` on the "already
canonicalized" part plus one more tied value for the next iteration to break.

## Status
- `IsPrefixTyping`:                   defined.
- §7 `convergeLoop_preserves_prefix`: stated; proof pending.
- §7 `breakTie_targetPos_is_min_tied`: ✅ proved.
- §7 `orderVertices_prefix_invariant`: stated; proof pending.
- §7 `orderVertices_n_distinct_ranks`: ✅ proved (pigeonhole corollary of the prefix invariant
  at `p = n`).

## Risk

If `assignRanks` / `computeDenseRanks` ever produces a sparse ranking (skips values),
the prefix invariant fails. The watch-out in the plan highlights this; the proof of
`convergeLoop_preserves_prefix` must verify each of those helpers preserves the prefix
property. Since the algorithm uses `orderInsensitiveListCmp`-sorted order + dense rank,
this should hold, but it must be checked line-by-line.

## Specialization to `initializePaths G`

`convergeLoop_preserves_prefix` and `orderVertices_prefix_invariant` are stated for
`state := initializePaths G` rather than an arbitrary `PathState n`. **The general form
is literally false**: a malformed state with multiple paths from the same start vertex
can cause `assignRanks` writes to overwrite each other, leaving non-prefix outputs.
Concrete counter-example with `n = 1`: state with two cmp-distinct paths from start 0
forces `convergeOnce`'s output to be `[1]` (no witness for value 0).

`initializePaths G` always has each `pathsOfLength[d]` with exactly `n` entries, one per
start vertex — every position in the rank-table is written exactly once with a dense
rank from `assignRanks`. The actual algorithm only invokes `convergeLoop` with this
state (via `runFrom`, `orderVertices`, `run`), so specializing matches reality.

### Backup plan if specialization proves intractable

**Option B (algorithm modification):** Insert `computeDenseRanks` after each
`convergeOnce` inside `convergeLoop`. The lemma becomes trivial (output is by
definition a prefix). Risks: re-verify `LeanGraphCanonizerV4Tests.lean` `#guard`s
(especially `countUniqueCanonicals 4 == 11`); inspect equivariance proofs for
sensitivity to `convergeOnce`'s exact value behavior; minor performance cost. Likely
all repairable since canonization is invariant under any rank-preserving relabeling.
-/

namespace Graph

open AdjMatrix

variable {n : Nat}

/-! ## Prefix-of-ℕ typings

A typing `vts : Array VertexType` is a "prefix typing" if its values are exactly a prefix
`{0, 1, …, m-1}` of ℕ for some `m ≤ n`. Now that `VertexType = Nat`, the non-negativity
condition is automatic and the definition simplifies to: every entry is `< m` and every
value in `[0, m)` is realized.
-/

/-- A typing `vts` is a prefix of ℕ: its value set equals `{0, 1, …, m-1}` for some m. -/
def IsPrefixTyping (vts : Array VertexType) : Prop :=
  ∃ m : Nat,
    (∀ v : Fin n, vts.getD v.val 0 < m) ∧
    (∀ k : Nat, k < m → ∃ v : Fin n, vts.getD v.val 0 = k)

/-- The all-zeros array is a prefix typing. (Boundary case for `run`'s entry point.)

Witness `m`:
- For `n = 0`: take `m = 0`. All conditions are vacuous (no vertices to constrain, no
  values `k < 0` to require representatives for).
- For `n ≥ 1`: take `m = 1`. Every entry is `0 < 1`; for `k = 0` the witness is `⟨0, hn⟩`.
-/
theorem IsPrefixTyping.replicate_zero :
    @IsPrefixTyping n (Array.replicate n (0 : VertexType)) := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨0, ?_, ?_⟩
    · intro v; exact v.elim0
    · intro k hk; exact absurd hk (Nat.not_lt_zero _)
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    refine ⟨1, ?_, ?_⟩
    · intro v; simp [v.isLt]
    · intro k hk
      interval_cases k
      exact ⟨⟨0, hpos⟩, by simp [hpos]⟩

/-! ## §7.1  `convergeLoop` preserves prefix typings -/

/-- `convergeLoop` preserves array size (each iteration calls `convergeOnce` which is
size-preserving via `set!` in-bounds, then either recurses on the size-preserved array
or returns it directly). -/
theorem convergeLoop_size_preserving
    {vc : Nat} (state : PathState vc) (vts : Array VertexType) (fuel : Nat) :
    (convergeLoop state vts fuel).size = vts.size := by
  induction fuel generalizing vts with
  | zero => rfl
  | succ k ih =>
    have h_step : (convergeOnce state vts).1.size = vts.size :=
      convergeOnce_size_preserving state vts
    change (if (convergeOnce state vts).2
            then convergeLoop state (convergeOnce state vts).1 k
            else (convergeOnce state vts).1).size = vts.size
    split
    · rw [ih (convergeOnce state vts).1]; exact h_step
    · exact h_step

/-! ### Inner-fold characterization

The inner fold inside `calculatePathRankings` updates `fromAcc[depth]` slot-by-slot via
nested `set!`s. The following helpers extract the slice's evolution:
- `inner_fold_slice_at_depth` — the slice after the inner fold equals a chain of
  `set!`s applied directly to the initial slice. Strips out the outer `fromAcc.set! depth`
  layer.
- (TODO) `array_set_chain_at_target` — for a chain of `set!`s with distinct indices,
  the value at any target index is the corresponding write.
-/

/-- Strip the outer `fromAcc.set! depth` wrapper from the inner fold: the slice at
position `depth` after the fold equals folding `slice.set! ... ...` directly on the
initial slice. -/
private theorem inner_fold_slice_at_depth {n : Nat}
    (l : List (PathsFrom n × Nat)) (fromAcc₀ : Array (Array Nat)) (depth : Nat)
    (h_depth_in : depth < fromAcc₀.size) :
    (l.foldl (fun (fromAcc : Array (Array Nat)) item =>
      let (pathFrom, rank) := item
      let depthSlice := fromAcc.getD depth #[]
      fromAcc.set! depth (depthSlice.set! pathFrom.startVertexIndex.val rank)) fromAcc₀).getD depth #[]
    = l.foldl (fun slice item =>
        slice.set! item.1.startVertexIndex.val item.2) (fromAcc₀.getD depth #[]) := by
  induction l generalizing fromAcc₀ with
  | nil => rfl
  | cons item l' ih =>
    rw [List.foldl_cons, List.foldl_cons]
    -- After one outer step: fromAcc' = fromAcc₀.set! depth (slice.set! ...).
    -- Inner step: slice' = slice.set! item.1.startVertexIndex.val item.2.
    -- Need: (l'.foldl ... fromAcc').getD depth #[] = l'.foldl ... slice'.
    -- IH applies once we know depth < fromAcc'.size (preserved by set!).
    set fromAcc' := fromAcc₀.set! depth ((fromAcc₀.getD depth #[]).set! item.1.startVertexIndex.val item.2) with hfromAcc'
    have h_depth_in' : depth < fromAcc'.size := by
      rw [hfromAcc']
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
      exact h_depth_in
    -- The slice at depth in fromAcc' equals slice.set! ...
    have h_slice_eq : fromAcc'.getD depth #[]
                    = (fromAcc₀.getD depth #[]).set! item.1.startVertexIndex.val item.2 := by
      rw [hfromAcc']
      rw [show fromAcc₀.set! depth ((fromAcc₀.getD depth #[]).set! item.1.startVertexIndex.val item.2)
            = fromAcc₀.setIfInBounds depth ((fromAcc₀.getD depth #[]).set! item.1.startVertexIndex.val item.2) from rfl]
      simp only [Array.getD_eq_getD_getElem?,
                 Array.getElem?_setIfInBounds_self_of_lt h_depth_in,
                 Option.getD_some]
    -- Apply IH on fromAcc'.
    rw [ih fromAcc' h_depth_in', h_slice_eq]

/-- Foldl `set!`-chain leaves untouched positions unchanged: if no entry in `l` has
its first component equal to `i`, the position-`i` value of the result equals the input. -/
private theorem array_set_chain_outside_unchanged
    {α : Type} (arr₀ : Array α) (l : List (Nat × α)) (i : Nat) (defaultV : α)
    (h : ∀ item ∈ l, item.1 ≠ i) :
    (l.foldl (fun a item => a.set! item.1 item.2) arr₀).getD i defaultV
      = arr₀.getD i defaultV := by
  induction l generalizing arr₀ with
  | nil => rfl
  | cons head l' ih =>
    rw [List.foldl_cons]
    have h_head_ne : head.1 ≠ i := h head List.mem_cons_self
    have h_tail : ∀ item ∈ l', item.1 ≠ i := fun item h_in => h item (List.mem_cons_of_mem _ h_in)
    rw [ih (arr₀.set! head.1 head.2) h_tail]
    -- arr₀.set! head.1 head.2 leaves position i unchanged (head.1 ≠ i).
    simp only [Array.getD_eq_getD_getElem?,
               Array.set!_eq_setIfInBounds,
               Array.getElem?_setIfInBounds_ne h_head_ne]

/-- Foldl `set!`-chain at the target index gives the target value, when the chain
indices are `Nodup` (the target's index appears only at the target's position). -/
private theorem array_set_chain_at_target_nodup
    {α : Type} (arr₀ : Array α) (l : List (Nat × α)) (target : Nat × α) (defaultV : α)
    (h_target_in : target ∈ l)
    (h_nodup : (l.map (·.1)).Nodup)
    (h_target_bound : target.1 < arr₀.size) :
    (l.foldl (fun a item => a.set! item.1 item.2) arr₀).getD target.1 defaultV
      = target.2 := by
  induction l generalizing arr₀ with
  | nil => exact absurd h_target_in (by simp)
  | cons head l' ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h_target_in with h_eq | h_in_tail
    · -- target = head. First step writes target.2 at target.1; later writes don't touch.
      have h_others_ne : ∀ item ∈ l', item.1 ≠ target.1 := by
        intro item h_in_item
        have h_nd' := h_nodup
        simp only [List.map_cons] at h_nd'
        have h_head_not_in : head.1 ∉ l'.map (·.1) := (List.nodup_cons.mp h_nd').1
        rw [← h_eq] at h_head_not_in
        intro h_eq_idx
        exact h_head_not_in (h_eq_idx ▸ List.mem_map.mpr ⟨item, h_in_item, rfl⟩)
      have h_step_eq : arr₀.set! head.1 head.2 = arr₀.set! target.1 target.2 := by
        rw [h_eq]
      rw [h_step_eq]
      rw [array_set_chain_outside_unchanged (arr₀.set! target.1 target.2) l' target.1 defaultV h_others_ne]
      simp only [Array.getD_eq_getD_getElem?,
                 Array.set!_eq_setIfInBounds,
                 Array.getElem?_setIfInBounds_self_of_lt h_target_bound,
                 Option.getD_some]
    · -- target ∈ l'. By Nodup, head.1 ≠ target.1, so first step doesn't touch target.1.
      have h_head_ne : head.1 ≠ target.1 := by
        have h_nd' := h_nodup
        simp only [List.map_cons] at h_nd'
        have h_head_not_in : head.1 ∉ l'.map (·.1) := (List.nodup_cons.mp h_nd').1
        intro h_eq_idx
        exact h_head_not_in (h_eq_idx ▸ List.mem_map.mpr ⟨target, h_in_tail, rfl⟩)
      have h_nodup' : (l'.map (·.1)).Nodup := by
        simp only [List.map_cons] at h_nodup
        exact (List.nodup_cons.mp h_nodup).2
      have h_bound' : target.1 < (arr₀.set! head.1 head.2).size := by
        simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact h_target_bound
      exact ih (arr₀.set! head.1 head.2) h_in_tail h_nodup' h_bound'
theorem getFrom_image_isPrefix_for_initializePaths
    (G : AdjMatrix n) (vts : Array VertexType) :
    ∃ m : Nat,
      (∀ i : Fin n, (calculatePathRankings (initializePaths G) vts).getFrom (n - 1) i.val < m) ∧
      (∀ k : Nat, k < m →
        ∃ i : Fin n, (calculatePathRankings (initializePaths G) vts).getFrom (n - 1) i.val = k) := by
  by_cases hn : n = 0
  · -- n = 0: take m = 0; both conditions vacuous over Fin 0 / Nat.lt 0.
    subst hn
    refine ⟨0, ?_, ?_⟩
    · intro v; exact v.elim0
    · intro k hk; exact absurd hk (Nat.not_lt_zero _)
  · -- n ≥ 1: deep argument via inner-fold characterization (TODO).
    sorry

/-- `convergeLoop` (on `initializePaths G`) maps prefix typings to prefix typings.

Specialized to `state := initializePaths G`; see file header for why the general form
over arbitrary `PathState n` is false. The `h_size` hypothesis (`vts.size = n`) is
required because `convergeOnce` writes via `set!`, and out-of-bounds positions retain
their default-`0` value — for small `vts`, this can introduce skipped values into the
image (e.g., `vts.size=1, n=3, getFrom = 2` gives image `{0, 2}`, not a prefix). -/
theorem convergeLoop_preserves_prefix
    (G : AdjMatrix n) (vts : Array VertexType) (fuel : Nat)
    (h_size : vts.size = n)
    (_hv : @IsPrefixTyping n vts) :
    @IsPrefixTyping n (convergeLoop (initializePaths G) vts fuel) := by
  induction fuel generalizing vts with
  | zero => exact _hv
  | succ k ih =>
    -- The convergeOnce output is always a prefix typing (when vts.size = n) regardless
    -- of input vts: every position holds `getFrom (n-1) i`, whose image is dense.
    have h_step_size : (convergeOnce (initializePaths G) vts).1.size = n := by
      rw [convergeOnce_size_preserving]; exact h_size
    have h_step_isPrefix : @IsPrefixTyping n (convergeOnce (initializePaths G) vts).1 := by
      obtain ⟨m, h_bound, h_witness⟩ := getFrom_image_isPrefix_for_initializePaths G vts
      refine ⟨m, ?_, ?_⟩
      · intro v
        rw [convergeOnce_writeback (initializePaths G) vts v.val (h_size.symm ▸ v.isLt) v.isLt]
        exact h_bound v
      · intro k hk
        obtain ⟨i, hi⟩ := h_witness k hk
        refine ⟨i, ?_⟩
        rw [convergeOnce_writeback (initializePaths G) vts i.val (h_size.symm ▸ i.isLt) i.isLt]
        exact hi
    show @IsPrefixTyping n (convergeLoop (initializePaths G) vts (k + 1))
    change @IsPrefixTyping n (
      if (convergeOnce (initializePaths G) vts).2
      then convergeLoop (initializePaths G) (convergeOnce (initializePaths G) vts).1 k
      else (convergeOnce (initializePaths G) vts).1)
    split
    · exact ih _ h_step_size h_step_isPrefix
    · exact h_step_isPrefix

/-! ## §7.2  `breakTie`'s target `p` equals the smallest tied value -/

/-- On a prefix typing, `breakTie vts p` non-trivially fires iff `p` is the smallest value
held by at least two vertices — which is exactly what the outer loop passes.

Formally: if `0..p-1` are each held by exactly one vertex going in, then after `breakTie p`,
any two vertices that share an output value must have an output value `> p`.
-/
theorem breakTie_targetPos_is_min_tied
    (vts : Array VertexType) (p : Nat)
    (hsize : vts.size = n)
    (_hv : @IsPrefixTyping n vts)
    (hfixed : ∀ k : Fin p, ∃! v : Fin n, vts.getD v.val 0 = k.val) :
    ∀ w₁ w₂ : Fin n, w₁ ≠ w₂ →
      (breakTie vts p).1.getD w₁.val 0 = (breakTie vts p).1.getD w₂.val 0 →
      (breakTie vts p).1.getD w₁.val 0 > p := by
  intro w₁ w₂ hne heq
  by_contra hgt
  have hgt : (breakTie vts p).1.getD w₁.val 0 ≤ p := not_lt.mp hgt
  have hw₁_size : w₁.val < vts.size := hsize ▸ w₁.isLt
  have hw₂_size : w₂.val < vts.size := hsize ▸ w₂.isLt
  -- [sparse→dense] If the output at `w` is ≤ p, then breakTie did not modify it.
  -- Cases on vts[w]:
  --   vts[w] < p: output[w] = vts[w] < p (always preserved by `breakTie_getD_below`).
  --   vts[w] = p: output[w] ∈ {p, p+1}; the ≤ p constraint forces output = p = vts[w].
  --   vts[w] > p: output[w] > p in both noop and fired cases — `output ≤ p` is vacuous.
  have not_promoted : ∀ (w : Fin n) (hws : w.val < vts.size),
      (breakTie vts p).1.getD w.val 0 ≤ p →
      (breakTie vts p).1.getD w.val 0 = vts.getD w.val 0 := by
    intro w hws hwout
    rcases lt_trichotomy (vts.getD w.val 0) p with hlt | heq | hgt
    · -- vts[w] < p: always preserved.
      exact breakTie_getD_below vts p hlt
    · -- vts[w] = p: output ∈ {p, p+1}; ≤ p forces output = p = vts[w].
      rcases breakTie_getD_target vts p hws heq with h | h
      · exact h.trans heq.symm
      · exfalso
        have : p + 1 ≤ p := h ▸ hwout
        omega
    · -- vts[w] > p: output[w] > p in both noop and fired branches; contradiction with hwout.
      exfalso
      rcases breakTie_getD_above_or vts p hgt with h | h
      · -- noop: output = vts[w] > p.
        have hle : vts.getD w.val 0 ≤ p := h ▸ hwout
        exact Nat.lt_irrefl _ (lt_of_lt_of_le hgt hle)
      · -- fired: output = vts[w] + 1 > p + 1 > p.
        have hle : vts.getD w.val 0 + 1 ≤ p := h ▸ hwout
        have : vts.getD w.val 0 < p := Nat.lt_of_succ_le hle
        exact Nat.lt_irrefl _ (lt_trans hgt this)
  have h₂_le : (breakTie vts p).1.getD w₂.val 0 ≤ p := heq ▸ hgt
  have h₁_pres : (breakTie vts p).1.getD w₁.val 0 = vts.getD w₁.val 0 :=
    not_promoted w₁ hw₁_size hgt
  have h₂_pres : (breakTie vts p).1.getD w₂.val 0 = vts.getD w₂.val 0 :=
    not_promoted w₂ hw₂_size h₂_le
  have hvts_eq : vts.getD w₁.val 0 = vts.getD w₂.val 0 := by
    rw [← h₁_pres, heq, h₂_pres]
  have hval_le : vts.getD w₁.val 0 ≤ p := h₁_pres ▸ hgt
  rcases lt_or_eq_of_le hval_le with hvalt | hvalt
  · -- val < p: hfixed pins both vertices to the unique witness for `val`.
    obtain ⟨_v_uniq, _hv_uniq, hu⟩ := hfixed ⟨vts.getD w₁.val 0, hvalt⟩
    have h₁_eq : vts.getD w₁.val 0 = vts.getD w₁.val 0 := rfl
    have h₂_eq : vts.getD w₂.val 0 = vts.getD w₁.val 0 := hvts_eq.symm
    exact hne ((hu w₁ h₁_eq).trans (hu w₂ h₂_eq).symm)
  · -- val = p: both vts[w_i] = p and outputs = p, but only the smallest target-valued
    -- index can have output p. So w₁ = w₂, contradiction.
    have hvts₁ : vts.getD w₁.val 0 = p := hvalt
    have hvts₂ : vts.getD w₂.val 0 = p := hvts_eq ▸ hvalt
    classical
    have h_ex : ∃ i, i < vts.size ∧ vts.getD i 0 = p :=
      ⟨w₁.val, hw₁_size, hvts₁⟩
    have hv_spec : Nat.find h_ex < vts.size ∧ vts.getD (Nat.find h_ex) 0 = p :=
      Nat.find_spec h_ex
    have hv_min : ∀ i, i < Nat.find h_ex → vts.getD i 0 ≠ p := fun i hi heq2 =>
      Nat.find_min h_ex hi ⟨lt_trans hi hv_spec.1, heq2⟩
    have eq_vstar : ∀ (w : Fin n) (hws : w.val < vts.size),
        vts.getD w.val 0 = p →
        (breakTie vts p).1.getD w.val 0 = p →
        w.val = Nat.find h_ex := by
      intro w hws hw_v hw_out
      by_contra h_ne
      have h_at := breakTie_getD_at_other vts p hv_spec.1 hv_spec.2 hv_min
        hws hw_v h_ne
      rw [h_at] at hw_out
      have : p + 1 = p := hw_out
      omega
    have h₁_out : (breakTie vts p).1.getD w₁.val 0 = p := by
      rw [h₁_pres]; exact hvts₁
    have h₂_out : (breakTie vts p).1.getD w₂.val 0 = p := by
      rw [h₂_pres]; exact hvts₂
    have hw₁_eq : w₁.val = Nat.find h_ex := eq_vstar w₁ hw₁_size hvts₁ h₁_out
    have hw₂_eq : w₂.val = Nat.find h_ex := eq_vstar w₂ hw₂_size hvts₂ h₂_out
    exact hne (Fin.ext (hw₁_eq.trans hw₂_eq.symm))

/-! ## §7.3  Prefix invariant across `orderVertices` -/

/-- After `p` iterations of `orderVertices`'s outer loop on `initializePaths G`, values
`0..p-1` are each held by a single vertex and the remaining typing is a prefix typing
over values `≥ p`. -/
theorem orderVertices_prefix_invariant
    (G : AdjMatrix n) (vts : Array VertexType) (p : Nat) (_hp : p ≤ n)
    (_hv : @IsPrefixTyping n vts) :
    ∀ k : Fin p,
      ∃! v : Fin n,
        ((List.range p).foldl
          (fun currentTypes targetPosition =>
            let convergedTypes := convergeLoop (initializePaths G) currentTypes n
            (breakTie convergedTypes targetPosition).1)
          vts).getD v.val 0 = k.val := by
  sorry

/-- After all `n` iterations of `orderVertices`'s outer loop, every vertex has a
distinct rank. This is the form of §7 used in §8 and Stage D.

**Proof.** By `orderVertices_prefix_invariant` at `p = n`, for each `k : Fin n` there is
a unique witness `v` with `rank v = k.val`. The witness map `φ : Fin n → Fin n` is
injective (distinct `k` ⟹ distinct witnesses by uniqueness), hence bijective on the
finite set `Fin n` (`Finite.injective_iff_bijective`). Surjectivity gives every vertex
a `k`, hence `rank v < n`. Then `rank i = rank j` forces `k_i = k_j` (Fin extensionality
on the same Nat), and the unique witness condition forces `i = j`. -/
theorem orderVertices_n_distinct_ranks
    (G : AdjMatrix n) (vts : Array VertexType)
    (hv : @IsPrefixTyping n vts) :
    ∀ i j : Fin n,
      i ≠ j →
      (orderVertices (initializePaths G) vts).getD i.val 0
        ≠ (orderVertices (initializePaths G) vts).getD j.val 0 := by
  intro i j hij h_eq
  -- Unfold orderVertices to the foldl form used by orderVertices_prefix_invariant.
  have h_unfold : orderVertices (initializePaths G) vts
      = (List.range n).foldl
          (fun currentTypes targetPosition =>
            let convergedTypes := convergeLoop (initializePaths G) currentTypes n
            (breakTie convergedTypes targetPosition).1)
          vts := rfl
  rw [h_unfold] at h_eq
  have h_inv := orderVertices_prefix_invariant G vts n (le_refl n) hv
  classical
  -- Witness map: each rank k in Fin n has a unique vertex.
  let φ : Fin n → Fin n := fun k => (h_inv k).exists.choose
  have h_φ : ∀ k : Fin n,
      ((List.range n).foldl
          (fun currentTypes targetPosition =>
            let convergedTypes := convergeLoop (initializePaths G) currentTypes n
            (breakTie convergedTypes targetPosition).1)
          vts).getD (φ k).val 0 = k.val := fun k =>
    (h_inv k).exists.choose_spec
  -- φ is injective.
  have h_inj : Function.Injective φ := by
    intro k₁ k₂ h_eq_φ
    have h_v1 := h_φ k₁
    have h_v2 := h_φ k₂
    rw [h_eq_φ] at h_v1
    exact Fin.ext (h_v1.symm.trans h_v2)
  -- Hence bijective on Fin n (a Finite type).
  have h_bij : Function.Bijective φ := Finite.injective_iff_bijective.mp h_inj
  -- Pull back i and j to ranks via surjectivity.
  obtain ⟨k_i, h_k_i⟩ := h_bij.surjective i
  obtain ⟨k_j, h_k_j⟩ := h_bij.surjective j
  -- rank i = k_i.val, rank j = k_j.val.
  have hri : ((List.range n).foldl
      (fun currentTypes targetPosition =>
        let convergedTypes := convergeLoop (initializePaths G) currentTypes n
        (breakTie convergedTypes targetPosition).1)
      vts).getD i.val 0 = k_i.val := h_k_i ▸ h_φ k_i
  have hrj : ((List.range n).foldl
      (fun currentTypes targetPosition =>
        let convergedTypes := convergeLoop (initializePaths G) currentTypes n
        (breakTie convergedTypes targetPosition).1)
      vts).getD j.val 0 = k_j.val := h_k_j ▸ h_φ k_j
  -- From h_eq: k_i.val = k_j.val.
  have hk_eq_val : k_i.val = k_j.val := by rw [← hri, h_eq, hrj]
  have hk_eq : k_i = k_j := Fin.ext hk_eq_val
  -- φ k_i = i, φ k_j = j. With k_i = k_j: i = j.
  exact hij (h_k_i.symm.trans (hk_eq ▸ h_k_j))

end Graph
