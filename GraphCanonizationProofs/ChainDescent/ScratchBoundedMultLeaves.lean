/-
# Bounded-multiplicity leaf bound — per-level branching (recovery route T0, ITEM B upgrade)

**What this module builds.** The δ′ *singleton* target (`interNum = 1`, forced triangle pins to a point) is walled on
`VO^ε` (a 2-point cut leaves `≈ q^{d−2}` POINTS, not one). The recovery route's weaker target only needs the *orbit*
multiplicity `bᵢ = #{Stab(S)-orbits in the WL cell}` to be `poly(q)`. The **non-vacuity check**
(`forced_triangle_mult.py`, 2026-07-01) measured `bᵢ` across `VO^ε` base levels and found:

  `bᵢ ≤ q(q−1)/2 = Θ(q²)`  (POLY(q)), occurring at **exactly one level** (the span-dim `0→1` transition, `|S|=2`);
  `bᵢ = 1` at every other level (`CellsAreOrbits` holds off span-dim-1); `d`-uniform (`q=3`: `B=3` at `d=4` and `d=6`).

So the branching is **concentrated**: one level with a `poly(q)` factor, the rest trivial. Phase 1's `leaves_le_pow`
uses a *uniform* bound `B^L` — adequate (with `L = branchDepth`), but it throws away the per-level structure. This module
**lifts** it to a **per-level** bound `leaves ≤ ∏ⱼ b(j)`, so a level with `b(j)=1` contributes a factor `1` and the
product collapses to the few genuinely-branching levels. With the probe's profile (`b = q(q−1)/2` at one level, `1`
elsewhere) this gives `leaves ≤ q(q−1)/2 = poly(n)` directly.

**Honest scope.** This is the *combinatorial* upgrade (the tree side, `D3`), fully proved. The **open content**
(unchanged, now probe-sharpened) is the per-level orbit-multiplicity bound itself — `b(j) ≤ q(q−1)/2` and its
concentration at span-dim-1 — the WL-orbit defect / cell-discretisation, carried as the family hypothesis exactly as the
δ′ engine carries `hclo`. This module only converts a per-level bound into a leaf bound; supplying the bounds is ITEM B.

Reuses Phase 1's `BTree`/`leaves`/`leaves_cons`/`sum_map_const`/`le_foldr_max` (`ScratchBoundedBranching`). Axiom-clean
`[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchBoundedBranching

namespace ChainDescent.BoundedBranching

open BTree

/-- Total depth (levels), counting every node — the range of the per-level product below. -/
def depth : BTree → Nat
  | .node [] => 0
  | .node cs => 1 + (cs.map depth).foldr Nat.max 0

@[simp] theorem depth_nil : depth (.node []) = 0 := by simp only [depth]
theorem depth_cons (c : BTree) (cs : List BTree) :
    depth (.node (c :: cs)) = 1 + ((c :: cs).map depth).foldr Nat.max 0 := by simp only [depth]

/-- **Per-level branching bound.** A node at depth `k` has `≤ b k` children (recursively). Generalises
`BoundedDeg B` (the constant `b ≡ B` case) to a level-dependent bound — the shape the recovery route needs, where the
branching factor `bᵢ` varies sharply by level (`q(q−1)/2` at one level, `1` elsewhere). -/
def BoundedDegAt (b : Nat → Nat) : Nat → BTree → Prop
  | k, .node cs => cs.length ≤ b k ∧ ∀ c ∈ cs, BoundedDegAt b (k + 1) c

/-- **★ Per-level leaf bound (lift of `leaves_le_pow`).** With a per-level branching bound `b` (a node at depth `k` has
`≤ b k` children) and every `b j ≥ 1`, the leaf count is `≤ ∏_{j<depth} b(k+j)`. Strictly generalises `leaves_le_pow`
(`b ≡ B` gives `≤ B^depth`); the payoff is that a level with `b j = 1` contributes a factor `1`, so branching
*concentrated* at a few levels yields a tight product. Structural induction: a leaf is `1 = ` empty product; a node sums
`≤ length ≤ b k` child-bounds, each `≤ ∏_{j<M} b(k+1+j)` (`M` = max child depth), giving
`≤ b k · ∏_{j<M} b(k+1+j) = ∏_{j<1+M} b(k+j)`. -/
theorem leaves_le_prod (b : Nat → Nat) (hb : ∀ j, 1 ≤ b j) :
    ∀ (k : Nat) (t : BTree), BoundedDegAt b k t →
      leaves t ≤ ∏ j ∈ Finset.range (depth t), b (k + j)
  | k, .node cs => by
    intro hdeg
    simp only [BoundedDegAt] at hdeg
    obtain ⟨hlen, hchild⟩ := hdeg
    cases cs with
    | nil => simp
    | cons c rest =>
      set M := ((c :: rest).map depth).foldr Nat.max 0 with hM
      have hchildbound : ∀ x ∈ c :: rest, leaves x ≤ ∏ j ∈ Finset.range M, b (k + 1 + j) := by
        intro x hx
        have hdx : depth x ≤ M := le_foldr_max (List.mem_map_of_mem hx)
        have hIH : leaves x ≤ ∏ j ∈ Finset.range (depth x), b (k + 1 + j) :=
          leaves_le_prod b hb (k + 1) x (hchild x hx)
        have hsub : Finset.range (depth x) ⊆ Finset.range M := fun i hi =>
          Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hdx)
        exact le_trans hIH (Finset.prod_le_prod_of_subset_of_one_le' hsub (fun i _ _ => hb _))
      have hsum : leaves (.node (c :: rest))
          ≤ (c :: rest).length * ∏ j ∈ Finset.range M, b (k + 1 + j) := by
        rw [leaves_cons]
        calc ((c :: rest).map leaves).sum
            ≤ ((c :: rest).map (fun _ => ∏ j ∈ Finset.range M, b (k + 1 + j))).sum :=
              List.sum_le_sum (fun x hx => hchildbound x hx)
          _ = (c :: rest).length * ∏ j ∈ Finset.range M, b (k + 1 + j) := sum_map_const _ _
      rw [depth_cons, ← hM]
      have hpeel : ∏ j ∈ Finset.range (1 + M), b (k + j)
          = b k * ∏ j ∈ Finset.range M, b (k + 1 + j) := by
        rw [Nat.add_comm 1 M, Finset.prod_range_succ']
        simp only [Nat.add_zero]
        rw [Nat.mul_comm]
        congr 1
        apply Finset.prod_congr rfl
        intro j _; rw [Nat.add_assoc, Nat.add_comm 1 j]
      rw [hpeel]
      calc leaves (.node (c :: rest))
          ≤ (c :: rest).length * ∏ j ∈ Finset.range M, b (k + 1 + j) := hsum
        _ ≤ b k * ∏ j ∈ Finset.range M, b (k + 1 + j) := Nat.mul_le_mul_right _ hlen

/-- **★ Concentration corollary — branching confined to a level set `J`.** If the per-level branching bound is `1` off a
finite set `J` of levels (`b j = 1` for `j ∉ J`), then `leaves ≤ ∏_{j ∈ J} b j` — the product over *only* the branching
levels. This is exactly the recovery route's probe profile: `J = {span-dim-1 level}`, `b = q(q−1)/2` there and `1`
elsewhere, giving `leaves ≤ q(q−1)/2 = poly(n)`. The tree-side statement that "concentrated branching ⟹ poly leaves". -/
theorem leaves_le_prod_concentrated (b : Nat → Nat) (hb : ∀ j, 1 ≤ b j) (J : Finset Nat)
    (hJ : ∀ j, j ∉ J → b j = 1) (t : BTree) (h : BoundedDegAt b 0 t) :
    leaves t ≤ ∏ j ∈ J, b j := by
  have hmain := leaves_le_prod b hb 0 t h
  simp only [Nat.zero_add] at hmain
  refine le_trans hmain ?_
  have h1 : ∏ j ∈ Finset.range (depth t), b j ≤ ∏ j ∈ Finset.range (depth t) ∪ J, b j :=
    Finset.prod_le_prod_of_subset_of_one_le' Finset.subset_union_left (fun i _ _ => hb _)
  have h2 : ∏ j ∈ J, b j = ∏ j ∈ Finset.range (depth t) ∪ J, b j :=
    Finset.prod_subset Finset.subset_union_right (fun x _ hxJ => hJ x hxJ)
  rw [h2]; exact h1

/-- **`leaves_le_pow` recovered (sanity).** The constant per-level bound `b ≡ B` gives back Phase 1's uniform bound
`leaves ≤ B^depth` — confirming `leaves_le_prod` is a genuine generalisation. -/
theorem leaves_le_pow_of_prod {B : Nat} (hB : 1 ≤ B) (t : BTree)
    (h : BoundedDegAt (fun _ => B) 0 t) : leaves t ≤ B ^ depth t := by
  have := leaves_le_prod (fun _ => B) (fun _ => hB) 0 t h
  simpa using this

end ChainDescent.BoundedBranching
