import FullCorrectness.Equivariance

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
    (_hv : @IsPrefixTyping n vts)
    (_hfixed : ∀ k : Fin p, ∃! v : Fin n, vts.getD v.val 0 = Int.ofNat k.val) :
    -- After this iteration, values `0..p` are each held by at most one vertex.
    ∀ w₁ w₂ : Fin n, w₁ ≠ w₂ →
      (breakTie vts (Int.ofNat p)).1.getD w₁.val 0 = (breakTie vts (Int.ofNat p)).1.getD w₂.val 0 →
      (breakTie vts (Int.ofNat p)).1.getD w₁.val 0 > Int.ofNat p := by
  sorry

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
