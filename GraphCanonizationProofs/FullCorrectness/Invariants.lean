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

/-- `convergeLoop` (on `initializePaths G`) maps prefix typings to prefix typings.

Specialized to `state := initializePaths G`; see file header for why the general form
over arbitrary `PathState n` is false. -/
theorem convergeLoop_preserves_prefix
    (G : AdjMatrix n) (vts : Array VertexType) (fuel : Nat)
    (_hv : @IsPrefixTyping n vts) :
    @IsPrefixTyping n (convergeLoop (initializePaths G) vts fuel) := by
  sorry

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
