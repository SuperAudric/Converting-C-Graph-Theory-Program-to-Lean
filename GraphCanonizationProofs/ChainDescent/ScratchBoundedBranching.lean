/-
# Bounded-branching node-count bridge (Phase 1, recovery route T0) — `leaves ≤ Bᴸ`

**What this module builds.** The recovery route's poly-leaf-count target `T0`
(`docs/chain-descent-recovery-route.md` §2c, §6 Phase 1): the *generalisation* of the
single-path node-count bridge (`ScratchNodeCountBridge`, the `B = 1` corner) to **bounded
branching**. The C# default (canonical-form-preserving) mode does **not** single-path — it
*branches and resolves* (`VO⁻₄(5)`: `branchingNodes = 4`, `leaves = 6`, `STARVED = 0`,
measured by `Phase0_BranchProfile`). The descent forks over the `Stab(S)`-orbits of the
selected cell (within-orbit siblings pruned by the harvest), so the leaf count is

  `leaves = ∏ᵢ bᵢ ≤ Bᴸ`,  `B = maxᵢ bᵢ` (branching factor), `L =` #branching levels.

With `n = q^d`, `B ≤ poly(q)` and `L = O(d)` give `Bᴸ = q^{O(d)} = poly(n)` — strictly
**weaker** than `CellsAreOrbits` (`bᵢ = 1`, the single path), which is the demoted route.

**The two layers.**
* **§1 — the pure tree-combinatorics core (the load-bearing math, `D3`).** A finitely
  branching rooted tree with every node of degree `≤ B` and `≤ L` branching nodes on any
  root→leaf path has `≤ Bᴸ` leaves: `BTree.leaves_le_pow`. Self-contained, forms-graph-free.
* **§2–§3 — the bridge.** `SelectedCellOrbitsLE` / `BoundedBranchingDisposition` (the
  selected cell is covered by `≤ B` `Stab(S)`-orbits at every base) — the structural form of
  the empirical `B = MaxBranchFactor` — generalising `SelectedCellIsOrbit` /
  `SinglePathDisposition`. `CertifiedBoundedTree` bundles the disposition (the per-node
  certification, carrying ≤ B orbits) with the abstract descent tree and its degree/depth
  bounds, and **exports `leaves ≤ Bᴸ`** via §1. `certifiedSinglePath`'s `B = 1` corner is
  recovered as `leaves ≤ 1` (single leaf).

**The seam (Increment-1 residual, documented, parallel to `ScratchNodeCountBridge`'s
`canonAdj` seam).** That the *concrete* descent realises the orbit-branching tree — i.e.
`BoundedDeg B t` follows from the disposition because the tree's node degrees ARE the
per-base selected-cell orbit counts — is carried as the structure's `degBound`/`depthBound`
fields here, to be discharged when the concrete branching descent is modelled (Phase 4).
The `B = 1` instance of this is exactly the single-path module's already-landed content.

Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchNodeCountBridge

namespace ChainDescent.BoundedBranching

open ChainDescent

/-! ## §1 — the pure tree-combinatorics core: `leaves ≤ Bᴸ`

A `BTree` is a finitely branching rooted tree (a node carries the list of its children; a
childless node is a leaf). This section is independent of the canonizer — it is the formal
content of the recovery route's `D3` (`∏ bᵢ ≤ Bᴸ`). -/

/-- A finitely-branching rooted tree (rose tree). A node with no children is a leaf. -/
inductive BTree where
  | node : List BTree → BTree

namespace BTree

/-- Number of leaves: a childless node is one leaf; otherwise the sum over the children. -/
def leaves : BTree → Nat
  | .node [] => 1
  | .node cs => (cs.map leaves).sum

/-- **Branching depth** — the maximum, over root→leaf paths, of the number of nodes with
`≥ 2` children. A node adds `1` iff it itself branches (`≥ 2` children); otherwise it passes
the max child depth through. This is the `L` in `leaves ≤ Bᴸ`: the number of *genuine* forks
on a path, NOT the total depth. -/
def branchDepth : BTree → Nat
  | .node cs => (if 2 ≤ cs.length then 1 else 0) + (cs.map branchDepth).foldr Nat.max 0

/-- Every node of the tree has at most `B` children (the per-node branching bound). -/
def BoundedDeg (B : Nat) : BTree → Prop
  | .node cs => cs.length ≤ B ∧ ∀ c ∈ cs, BoundedDeg B c

@[simp] theorem leaves_nil : leaves (.node []) = 1 := by simp only [leaves]
@[simp] theorem leaves_cons (c : BTree) (cs : List BTree) :
    leaves (.node (c :: cs)) = ((c :: cs).map leaves).sum := by simp only [leaves]

/-- An element of a list is `≤` the list's `foldr max 0` (the running maximum). -/
theorem le_foldr_max {a : Nat} : ∀ {l : List Nat}, a ∈ l → a ≤ l.foldr Nat.max 0
  | _ :: _, h => by
    rcases List.mem_cons.mp h with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (le_foldr_max h) (le_max_right _ _)

/-- Sum of a constant map = length × constant. -/
theorem sum_map_const {α} (l : List α) (k : Nat) : (l.map (fun _ => k)).sum = l.length * k := by
  induction l with
  | nil => simp
  | cons _ t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- **★ The leaf bound (the recovery route's `D3`).** A tree whose every node has `≤ B`
children has at most `B ^ (branchDepth)` leaves. Proof by structural induction: a leaf has
`1 ≤ B⁰` leaves; a node with `< 2` children passes the bound through; a node with `≥ 2`
children sums `≤ length ≤ B` child-bounds, each `≤ B ^ M` (the max child depth), giving
`≤ B · B ^ M = B ^ (1 + M)`. -/
theorem leaves_le_pow (B : Nat) : ∀ t : BTree, BoundedDeg B t → leaves t ≤ B ^ branchDepth t
  | .node cs => by
    intro hdeg
    simp only [BoundedDeg] at hdeg
    obtain ⟨hlen, hchild⟩ := hdeg
    cases cs with
    | nil => rw [leaves_nil]; simp [branchDepth]
    | cons c rest =>
      set M := ((c :: rest).map branchDepth).foldr Nat.max 0 with hM
      have hchildbound : ∀ x ∈ c :: rest, leaves x ≤ B ^ M := by
        intro x hx
        have hbd : branchDepth x ≤ M := le_foldr_max (List.mem_map_of_mem hx)
        have hlencons : 1 ≤ (c :: rest).length := by
          rw [List.length_cons]; exact Nat.succ_le_succ (Nat.zero_le _)
        have hB1 : 1 ≤ B := le_trans hlencons hlen
        exact le_trans (leaves_le_pow B x (hchild x hx)) (Nat.pow_le_pow_right hB1 hbd)
      have hsum : leaves (.node (c :: rest)) ≤ (c :: rest).length * B ^ M := by
        rw [leaves_cons]
        calc ((c :: rest).map leaves).sum
            ≤ ((c :: rest).map (fun _ => B ^ M)).sum :=
              List.sum_le_sum (fun x hx => hchildbound x hx)
          _ = (c :: rest).length * B ^ M := sum_map_const _ _
      simp only [branchDepth]
      rw [← hM]
      by_cases hb : 2 ≤ (c :: rest).length
      · rw [if_pos hb, pow_add, pow_one]
        calc leaves (.node (c :: rest)) ≤ (c :: rest).length * B ^ M := hsum
          _ ≤ B * B ^ M := Nat.mul_le_mul hlen (le_refl _)
      · rw [if_neg hb, zero_add]
        have hle1 : (c :: rest).length ≤ 1 := Nat.lt_succ_iff.mp (not_le.mp hb)
        calc leaves (.node (c :: rest)) ≤ (c :: rest).length * B ^ M := hsum
          _ ≤ 1 * B ^ M := Nat.mul_le_mul hle1 (le_refl _)
          _ = B ^ M := one_mul _

/-- **`B = 1` ⟹ a single leaf.** `BoundedDeg 1` (no node branches) forces `leaves ≤ 1` — the
single path. The tree-level form of the `ScratchNodeCountBridge` single-path corner. -/
theorem leaves_le_one_of_boundedDeg_one (t : BTree) (h : BoundedDeg 1 t) : leaves t ≤ 1 := by
  have := leaves_le_pow 1 t h
  simpa using this

end BTree

variable {n : Nat}

/-! ## §2 — the bounded-branching disposition (generalising `SinglePathDisposition`)

The selected cell at base `S` is `sel (warmRefine adj P (individualizedColouring n S))`. The
descent forks over its `Stab(S)`-orbits; the branching factor `bᵢ` is the number of orbits
covering it. `SelectedCellOrbitsLE … B` says that number is `≤ B`, generalising
`SelectedCellIsOrbit` (the cell is ONE orbit). This is the structural form of the empirical
`B = MaxBranchFactor` (`Phase0_BranchProfile`). -/

/-- **The selected cell is covered by `≤ B` residual orbits.** There is a set of `≤ B`
representatives such that every cell vertex is `Stab(S)`-orbit-equivalent to one of them. The
`B`-bounded generalisation of `SelectedCellIsOrbit`; `bᵢ ≤ B` in the recovery route. -/
def SelectedCellOrbitsLE (adj : AdjMatrix n) (P : PMatrix n)
    (sel : Colouring n → Finset (Fin n)) (B : Nat) (S : Finset (Fin n)) : Prop :=
  ∃ reps : Finset (Fin n), reps.card ≤ B ∧
    ∀ v ∈ sel (warmRefine adj P (individualizedColouring n S)),
      ∃ r ∈ reps, OrbitPartition adj P S r v

/-- **The bounded-branching disposition.** Every base's selected cell is covered by `≤ B`
orbits — the bridge-keyed hypothesis, the structural form of the empirical "`B = poly(q)`,
uniform in `d`". `B = 1` is `SinglePathDisposition` (modulo the colour condition below). -/
def BoundedBranchingDisposition (adj : AdjMatrix n) (P : PMatrix n)
    (sel : Colouring n → Finset (Fin n)) (B : Nat) : Prop :=
  ∀ S : Finset (Fin n), SelectedCellOrbitsLE adj P sel B S

/-- **Monotone in `B`.** A cover by `≤ B` orbits is a cover by `≤ B'` orbits for `B ≤ B'`. -/
theorem SelectedCellOrbitsLE.mono {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {B B' : Nat} {S : Finset (Fin n)}
    (hBB' : B ≤ B') (h : SelectedCellOrbitsLE adj P sel B S) :
    SelectedCellOrbitsLE adj P sel B' S := by
  obtain ⟨reps, hcard, hcov⟩ := h
  exact ⟨reps, le_trans hcard hBB', hcov⟩

theorem BoundedBranchingDisposition.mono {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {B B' : Nat}
    (hBB' : B ≤ B') (h : BoundedBranchingDisposition adj P sel B) :
    BoundedBranchingDisposition adj P sel B' :=
  fun S => (h S).mono hBB'

/-- **The `B = 1` corner — a single-orbit cell is a `≤ 1`-orbit cover.** When the selected
cell is monochromatic (`hmono` — true for a refinement cell, the descent's target), the
single-orbit property `SelectedCellIsOrbit` yields a cover by one representative. This is the
disposition-level statement that the single path is the `B = 1` instance. -/
theorem selectedCellOrbitsLE_one_of_isOrbit {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {S : Finset (Fin n)}
    (hmono : ∀ v ∈ sel (warmRefine adj P (individualizedColouring n S)),
      ∀ w ∈ sel (warmRefine adj P (individualizedColouring n S)),
        warmRefine adj P (individualizedColouring n S) v
          = warmRefine adj P (individualizedColouring n S) w)
    (h : NodeCountBridge.SelectedCellIsOrbit adj P sel S) :
    SelectedCellOrbitsLE adj P sel 1 S := by
  by_cases hne : (sel (warmRefine adj P (individualizedColouring n S))).Nonempty
  · obtain ⟨r, hr⟩ := hne
    refine ⟨{r}, by simp, fun v hv => ⟨r, Finset.mem_singleton_self r, ?_⟩⟩
    exact h r v hr hv (hmono r hr v hv)
  · refine ⟨∅, by simp, fun v hv => ?_⟩
    exact absurd ⟨v, hv⟩ hne

/-! ## §3 — the certified bounded tree + the capstone

`CertifiedBoundedTree` bundles, for an abstract descent tree `t`: the per-node certification
(the disposition — `≤ B` orbits per cell), and the tree's degree/depth bounds, and **exports
`leaves t ≤ Bᴸ`** via §1. This is the bounded-branching analogue of `CertifiedSinglePath`
(`boundedNodes` + `cellsCertified`): here `cellsBounded` + the abstract leaf bound. -/

/-- **The certified bounded tree** — the recovery route's `T0` poly object. Bundles:
`cellsBounded` (the disposition: `≤ B` orbits per selected cell, the per-node certification),
`degBound` (the descent tree `t` branches `≤ B` ways at every node — the realisation seam),
`depthBound` (`≤ L` branching levels on any path — the `L = O(d)` obligation), and `oneLeB`.
Exports `leafBound : leaves t ≤ Bᴸ`. The meta poly-argument reads "poly leaf count" off this:
`leaves ≤ Bᴸ = q^{O(d)} = poly(n)`, `× depth × per-node-poly`. -/
structure CertifiedBoundedTree (adj : AdjMatrix n) (P : PMatrix n)
    (sel : Colouring n → Finset (Fin n)) (B L : Nat) (t : BTree) : Prop where
  oneLeB : 1 ≤ B
  cellsBounded : BoundedBranchingDisposition adj P sel B
  degBound : BTree.BoundedDeg B t
  depthBound : BTree.branchDepth t ≤ L

/-- **★ The exported leaf bound `leaves ≤ Bᴸ`.** The poly-leaf-count conclusion, from the §1
combinatorial core (`leaves ≤ B ^ branchDepth`) composed with `branchDepth ≤ L`. -/
theorem CertifiedBoundedTree.leafBound {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {B L : Nat} {t : BTree}
    (h : CertifiedBoundedTree adj P sel B L t) : BTree.leaves t ≤ B ^ L :=
  le_trans (BTree.leaves_le_pow B t h.degBound)
    (Nat.pow_le_pow_right h.oneLeB h.depthBound)

/-- **★ The bridge capstone (Phase 1).** The bounded-branching disposition, together with an
abstract descent tree realising the `≤ B` orbit-branching (`hdeg`) within `≤ L` branching
levels (`hdepth`), delivers the certified bounded tree — hence the poly leaf bound
`leaves ≤ Bᴸ`. Generalises `certifiedSinglePath_of_disposition` (the `B = 1` corner). The
realisation hypotheses `hdeg`/`hdepth` are the Increment-1 seam (the concrete branching
descent, modelled in Phase 4); the disposition `hdisp` is the per-node certification carried
unconditionally, exactly as `cellsCertified` is in the single-path bridge. -/
theorem certifiedBoundedTree_of_disposition {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {B L : Nat} {t : BTree}
    (hB : 1 ≤ B) (hdisp : BoundedBranchingDisposition adj P sel B)
    (hdeg : BTree.BoundedDeg B t) (hdepth : BTree.branchDepth t ≤ L) :
    CertifiedBoundedTree adj P sel B L t :=
  ⟨hB, hdisp, hdeg, hdepth⟩

/-- **The `B = 1` corner — single path.** A certified bounded tree with `B = 1` has a single
leaf (`leaves ≤ 1`): the bounded-branching machinery degenerates to the single descent path
of `ScratchNodeCountBridge`. This is the structural statement that "no branching ⟹ one leaf",
the recovery route's `T2` rung sitting inside `T0`. -/
theorem leaves_le_one_of_certifiedBoundedTree_one {adj : AdjMatrix n} {P : PMatrix n}
    {sel : Colouring n → Finset (Fin n)} {L : Nat} {t : BTree}
    (h : CertifiedBoundedTree adj P sel 1 L t) : BTree.leaves t ≤ 1 :=
  BTree.leaves_le_one_of_boundedDeg_one t h.degBound

end ChainDescent.BoundedBranching
