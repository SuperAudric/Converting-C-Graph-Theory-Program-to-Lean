import FullCorrectness.Equivariance
import FullCorrectness.Tiebreak
import Mathlib.Tactic.IntervalCases

/-!
# §7  "Converged types are a prefix of ℕ" invariant

`orderVertices`' outer fold calls `breakTie convergedTypes (Int.ofNat targetPosition)` at
iteration `targetPosition ∈ 0, …, n-1`. For §5/§6 to apply, the smallest repeated value
at each iteration must be exactly `targetPosition` — not some other tied value.

This module states the invariant that makes that work: after the first `p` iterations,
the typing takes values in a prefix of ℕ, specifically `{0, 1, …, p-1}` on the "already
canonicalized" part plus one more tied value for the next iteration to break.

## Status
- `IsPrefixTyping`:              defined (sketched).
- §7 `convergeLoop_preserves_prefix`: stated; proof pending.
- §7 `breakTie_targetPos_is_min_tied`: stated; proof pending.
- §7 `orderVertices_prefix_invariant`: stated; proof pending.
- §7 `orderVertices_n_distinct_ranks`: stated; proof pending (corollary at p = n).

## Risk

If `assignRanks` / `computeDenseRanks` ever produces a sparse ranking (skips values),
the prefix invariant fails. The watch-out in the plan highlights this; the proof of
`convergeLoop_preserves_prefix` must verify each of those helpers preserves the prefix
property. Since the algorithm uses `orderInsensitiveListCmp`-sorted order + dense rank,
this should hold, but it must be checked line-by-line.
-/

namespace Graph

open AdjMatrix

variable {n : Nat}

/-! ## Prefix-of-ℕ typings

A typing `vts : Array VertexType` is a "prefix typing" if its values are exactly a prefix
`{0, 1, …, m-1}` of ℕ for some `m ≤ n`. Equivalently: every value `0 ≤ k < (max vts + 1)`
is held by at least one vertex.

For this proof, we use the weaker form: `vts` is a prefix typing iff `∀ v, 0 ≤ vts[v]` and
`∀ k : ℕ, k ≤ max vts → ∃ v, vts[v] = k`.
-/

/-- A typing `vts` is a prefix of ℕ: its value set equals `{0, 1, …, m-1}` for some m. -/
def IsPrefixTyping (vts : Array VertexType) : Prop :=
  ∃ m : Nat,
    (∀ v : Fin n, vts.getD v.val 0 < Int.ofNat m) ∧
    (∀ v : Fin n, 0 ≤ vts.getD v.val 0) ∧
    (∀ k : Nat, k < m → ∃ v : Fin n, vts.getD v.val 0 = Int.ofNat k)

/-- The all-zeros array is a prefix typing. (Boundary case for `run`'s entry point.)

Witness `m`:
- For `n = 0`: take `m = 0`. All conditions are vacuous (no vertices to constrain, no
  values `k < 0` to require representatives for).
- For `n ≥ 1`: take `m = 1`. Every entry is `0 < 1`; `0 ≤ 0`; for `k = 0` the witness is
  `⟨0, hn⟩`. -/
theorem IsPrefixTyping.replicate_zero :
    @IsPrefixTyping n (Array.replicate n (0 : VertexType)) := by
  by_cases hn : n = 0
  · -- n = 0: no vertices; take m = 0.
    subst hn
    refine ⟨0, ?_, ?_, ?_⟩
    · intro v; exact v.elim0
    · intro v; exact v.elim0
    · intro k hk; exact absurd hk (Nat.not_lt_zero _)
  · -- n ≥ 1: take m = 1; the unique value 0 is held by vertex 0.
    have hpos : 0 < n := Nat.pos_of_ne_zero hn
    refine ⟨1, ?_, ?_, ?_⟩
    · intro v; simp [v.isLt]
    · intro v; simp [v.isLt]
    · intro k hk
      interval_cases k
      exact ⟨⟨0, hpos⟩, by simp [hpos]⟩

/-! ## §7.1  `convergeLoop` preserves prefix typings -/

/-- `convergeLoop` maps prefix typings to prefix typings.

**Why.** `convergeOnce` writes `rankState.getFrom (n-1) v` into each slot. The values
produced by `assignRanks` + `setBetween`/`fromRanks` assignment are exactly the
indices-of-first-element-in-each-equivalence-class in the sorted order, which always
form a prefix `{0, 1, …, m-1}`. Hence the output typing of `convergeOnce`, and
inductively of `convergeLoop`, is a prefix typing.

**Caveat.** The rank can be any index that is the *first* of its equivalence class in
the sorted order; if there are k classes, the ranks that appear are the starting indices
`i₀ = 0, i₁, …, i_{k-1}`. These are not necessarily a prefix `{0, …, k-1}` — they are
actually `{0, 1, 1+|class 0|, …}` minus duplicates, which *is* a prefix iff every class
has size 1 (all distinct). The generic ranking produces {0, |C₀|, |C₀|+|C₁|, …}. So
strictly speaking the ranks after `assignRanks` are NOT a prefix of ℕ in general.

However, after `computeDenseRanks` (used at the end in `labelEdgesAccordingToRankings`),
the ranks *are* a prefix. For the §7 invariant to hold at `orderVertices` time, we need
either: (a) `convergeOnce`'s rank assignment is dense, or (b) the §7 argument is stated
against the dense-rank composition rather than raw `getFrom`.

**Conclusion for this stub.** The exact statement of §7.1 depends on which form of rank
the algorithm uses in the outer loop. The current algorithm uses raw `getFrom`, which is
non-dense. A possible fix is to redefine `convergeOnce` to dense-rank before writing, but
that changes the algorithm. The proof will need one of: dense-rank everywhere, or a
stronger invariant that accommodates gap-ranks. This is tracked as **R2** in the plan.
-/
theorem convergeLoop_preserves_prefix
    (state : PathState) (vts : Array VertexType) (fuel : Nat)
    (_hv : @IsPrefixTyping n vts) :
    @IsPrefixTyping n (convergeLoop state vts fuel) := by
  sorry

/-! ## §7.2  `breakTie`'s target `p` equals the smallest tied value -/

/-- On a prefix typing, `breakTie vts p` non-trivially fires iff `p` is the smallest value
held by at least two vertices — which is exactly what the outer loop passes.

Formally: after `p` iterations of the outer loop, the values `{0, …, p-1}` are each held
by exactly one vertex, and the remaining vertices hold values `≥ p` packed as a prefix.
The smallest tied value among the remainder is therefore `p` (if any tie exists), so
the algorithm's call `breakTie convergedTypes (Int.ofNat p)` targets the right class.
-/
theorem breakTie_targetPos_is_min_tied
    (vts : Array VertexType) (p : Nat)
    (hsize : vts.size = n)
    (hv : @IsPrefixTyping n vts)
    (hfixed : ∀ k : Fin p, ∃! v : Fin n, vts.getD v.val 0 = Int.ofNat k.val) :
    -- After this iteration, values `0..p` are each held by at most one vertex.
    ∀ w₁ w₂ : Fin n, w₁ ≠ w₂ →
      (breakTie vts (Int.ofNat p)).1.getD w₁.val 0 = (breakTie vts (Int.ofNat p)).1.getD w₂.val 0 →
      (breakTie vts (Int.ofNat p)).1.getD w₁.val 0 > Int.ofNat p := by
  intro w₁ w₂ hne heq
  by_contra hgt
  have hgt : (breakTie vts (Int.ofNat p)).1.getD w₁.val 0 ≤ Int.ofNat p :=
    not_lt.mp hgt
  have hw₁_size : w₁.val < vts.size := hsize ▸ w₁.isLt
  have hw₂_size : w₂.val < vts.size := hsize ▸ w₂.isLt
  obtain ⟨_m, _hmax, hpos, _hsurj⟩ := hv
  -- Output classification: every in-bounds output is either `vts[w]` (preserved) or
  -- `Int.ofNat p + 1` (promoted; only happens when `vts[w] = Int.ofNat p`).
  have output_alts : ∀ (w : Fin n), w.val < vts.size →
      (breakTie vts (Int.ofNat p)).1.getD w.val 0 = vts.getD w.val 0 ∨
      (breakTie vts (Int.ofNat p)).1.getD w.val 0 = Int.ofNat p + 1 := by
    intro w hws
    by_cases hwv : vts.getD w.val 0 = Int.ofNat p
    · rcases breakTie_getD_target vts (Int.ofNat p) hws hwv with h | h
      · exact Or.inl (h.trans hwv.symm)
      · exact Or.inr h
    · exact Or.inl (breakTie_getD_of_ne vts (Int.ofNat p) hwv)
  -- Promoted outputs (= p+1) exceed `Int.ofNat p`; ruled out under `hgt`.
  have not_promoted : ∀ (w : Fin n) (hws : w.val < vts.size),
      (breakTie vts (Int.ofNat p)).1.getD w.val 0 ≤ Int.ofNat p →
      (breakTie vts (Int.ofNat p)).1.getD w.val 0 = vts.getD w.val 0 := by
    intro w hws hwout
    rcases output_alts w hws with h | h
    · exact h
    · exfalso; have : Int.ofNat p + 1 ≤ Int.ofNat p := h ▸ hwout; omega
  have h₂_le : (breakTie vts (Int.ofNat p)).1.getD w₂.val 0 ≤ Int.ofNat p := heq ▸ hgt
  have h₁_pres : (breakTie vts (Int.ofNat p)).1.getD w₁.val 0 = vts.getD w₁.val 0 :=
    not_promoted w₁ hw₁_size hgt
  have h₂_pres : (breakTie vts (Int.ofNat p)).1.getD w₂.val 0 = vts.getD w₂.val 0 :=
    not_promoted w₂ hw₂_size h₂_le
  -- vts[w₁] = vts[w₂]: chain h₁_pres⁻¹ · heq · h₂_pres.
  have hvts_eq : vts.getD w₁.val 0 = vts.getD w₂.val 0 := by
    rw [← h₁_pres, heq, h₂_pres]
  -- Bounds on `vts[w₁]`.
  have hval_nn : 0 ≤ vts.getD w₁.val 0 := hpos w₁
  have hval_le : vts.getD w₁.val 0 ≤ Int.ofNat p := h₁_pres ▸ hgt
  rcases lt_or_eq_of_le hval_le with hvalt | hvalt
  · -- val < p: hfixed pins both vertices to the unique witness for `val.toNat`.
    have hval_lt_p : (vts.getD w₁.val 0).toNat < p := by
      have h_self : Int.ofNat (vts.getD w₁.val 0).toNat = vts.getD w₁.val 0 :=
        Int.toNat_of_nonneg hval_nn
      have hint : Int.ofNat (vts.getD w₁.val 0).toNat < Int.ofNat p := by
        rw [h_self]; exact hvalt
      exact Int.ofNat_lt.mp hint
    have h_self : Int.ofNat (vts.getD w₁.val 0).toNat = vts.getD w₁.val 0 :=
      Int.toNat_of_nonneg hval_nn
    obtain ⟨_v_uniq, _hv_uniq, hu⟩ := hfixed ⟨(vts.getD w₁.val 0).toNat, hval_lt_p⟩
    have h₁_eq : vts.getD w₁.val 0 = Int.ofNat (vts.getD w₁.val 0).toNat := h_self.symm
    have h₂_eq : vts.getD w₂.val 0 = Int.ofNat (vts.getD w₁.val 0).toNat := by
      rw [← hvts_eq]; exact h_self.symm
    exact hne ((hu w₁ h₁_eq).trans (hu w₂ h₂_eq).symm)
  · -- val = p: both `vts[w_i] = p` and outputs = p, but only one vertex (the smallest
    -- target-valued index) can have output p. So `w₁ = w₂`, contradiction.
    have hvts₁ : vts.getD w₁.val 0 = Int.ofNat p := hvalt
    have hvts₂ : vts.getD w₂.val 0 = Int.ofNat p := hvts_eq ▸ hvalt
    classical
    have h_ex : ∃ i, i < vts.size ∧ vts.getD i 0 = Int.ofNat p :=
      ⟨w₁.val, hw₁_size, hvts₁⟩
    have hv_spec : Nat.find h_ex < vts.size ∧ vts.getD (Nat.find h_ex) 0 = Int.ofNat p :=
      Nat.find_spec h_ex
    have hv_min : ∀ i, i < Nat.find h_ex → vts.getD i 0 ≠ Int.ofNat p := fun i hi heq2 =>
      Nat.find_min h_ex hi ⟨lt_trans hi hv_spec.1, heq2⟩
    -- Any target-valued w ≠ v_star gets output p+1, contradicting "output = p".
    have eq_vstar : ∀ (w : Fin n) (hws : w.val < vts.size),
        vts.getD w.val 0 = Int.ofNat p →
        (breakTie vts (Int.ofNat p)).1.getD w.val 0 = Int.ofNat p →
        w.val = Nat.find h_ex := by
      intro w hws hw_v hw_out
      by_contra h_ne
      have h_at := breakTie_getD_at_other vts (Int.ofNat p) hv_spec.1 hv_spec.2 hv_min
        hws hw_v h_ne
      rw [h_at] at hw_out
      have : Int.ofNat p + 1 = Int.ofNat p := hw_out
      omega
    have h₁_out : (breakTie vts (Int.ofNat p)).1.getD w₁.val 0 = Int.ofNat p := by
      rw [h₁_pres]; exact hvts₁
    have h₂_out : (breakTie vts (Int.ofNat p)).1.getD w₂.val 0 = Int.ofNat p := by
      rw [h₂_pres]; exact hvts₂
    have hw₁_eq : w₁.val = Nat.find h_ex := eq_vstar w₁ hw₁_size hvts₁ h₁_out
    have hw₂_eq : w₂.val = Nat.find h_ex := eq_vstar w₂ hw₂_size hvts₂ h₂_out
    exact hne (Fin.ext (hw₁_eq.trans hw₂_eq.symm))

/-! ## §7.3  Prefix invariant across `orderVertices` -/

/-- After `p` iterations of `orderVertices`'s outer loop, values `0..p-1` are each held by
a single vertex and the remaining typing is a prefix typing over values `≥ p`.

This is stated via a helper `orderVerticesStep` unfolded to match the fold. See the
file header for why this matters.
-/
theorem orderVertices_prefix_invariant
    (state : PathState) (vts : Array VertexType) (p : Nat) (_hp : p ≤ state.vertexCount)
    (_hv : @IsPrefixTyping n vts) :
    -- After p iterations, 0..p-1 each held by a unique vertex.
    ∀ k : Fin p,
      ∃! v : Fin n,
        ((List.range p).foldl
          (fun currentTypes targetPosition =>
            let convergedTypes := convergeLoop state currentTypes state.vertexCount
            (breakTie convergedTypes (Int.ofNat targetPosition)).1)
          vts).getD v.val 0 = Int.ofNat k.val := by
  sorry

/-- After all `n` iterations of `orderVertices`'s outer loop, every vertex has a
distinct rank. This is the form of §7 used in §8 and Stage D. -/
theorem orderVertices_n_distinct_ranks
    (state : PathState) (vts : Array VertexType)
    (_hv : @IsPrefixTyping n vts) :
    ∀ i j : Fin n,
      i ≠ j →
      (orderVertices state vts).getD i.val 0 ≠ (orderVertices state vts).getD j.val 0 := by
  sorry

end Graph
