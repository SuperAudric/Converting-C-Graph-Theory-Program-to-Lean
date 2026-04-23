import LeanGraphCanonizerV4
import LeanGraphCanonizerV4Correctness
import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Correctness of the Full Graph Canonizer (with tiebreak + refinement)

The companion file `LeanGraphCanonizerV4Correctness.lean` proves the canonizer correct only
under the simplifying assumption that `breakTie` is never invoked — i.e. that `convergeLoop`
alone separates every orbit. That assumption fails on graphs with non-trivial automorphism
groups. This file is the start of a correct proof that handles the full algorithm.

## Proof-development plan (from the design document)

  1. Automorphism group `Aut G` and vertex orbits.                     ← **this file (§1)**
  2. Bridge lemma: `Isomorphic G H ↔ ∃ σ, H = G.permute σ`.             ← **planned (§2)**
  3. Aut-restricted version of the pipeline equivariance lemmas.
  4. `convergeLoop` output is Aut(G)-invariant.
  5. `breakTie` shrinks the typed-automorphism group to a point-stabilizer.
  6. Tiebreak choice-independence (the conceptual bottleneck).
  7. Discharge the "converged types form a prefix of ℕ" invariant.
  8. Assemble `run_canonical`.

Each step is intended as a separate Lean-compilable deliverable. This file implements step 1
and ends with a detailed comment plan for step 2.
-/

namespace Graph
open AdjMatrix

variable {n : Nat}

/-! ## §1  Automorphism group and vertex orbits -/

/-! ### §1.1  Permutation action on `AdjMatrix` -/

/--
Relabel the vertices of `G` by the permutation `σ`. We use `σ.symm` so that composition works
as a **left** action: `G.permute (σ * τ) = (G.permute τ).permute σ`. Intuition: treat `σ` as
"move the label" (vertex originally at position `i` now sits at `σ i`); then the edge at the
new position `(i, j)` is the edge that was at `(σ⁻¹ i, σ⁻¹ j)`.
-/
def AdjMatrix.permute (σ : Equiv.Perm (Fin n)) (G : AdjMatrix n) : AdjMatrix n :=
  { adj := fun i j => G.adj (σ.symm i) (σ.symm j) }

@[simp]
theorem AdjMatrix.permute_adj (σ : Equiv.Perm (Fin n)) (G : AdjMatrix n) (i j : Fin n) :
    (G.permute σ).adj i j = G.adj (σ.symm i) (σ.symm j) := rfl

/-- Permuting by the identity does nothing. -/
@[simp]
theorem AdjMatrix.permute_one (G : AdjMatrix n) : G.permute 1 = G := by
  apply AdjMatrix.ext
  intro i j
  simp [AdjMatrix.permute]

/-- Permutation action composes as a left action: `(σ * τ) · G = σ · (τ · G)`. -/
theorem AdjMatrix.permute_mul (σ τ : Equiv.Perm (Fin n)) (G : AdjMatrix n) :
    G.permute (σ * τ) = (G.permute τ).permute σ := by
  apply AdjMatrix.ext
  intro i j
  -- Both sides reduce to `G.adj (τ.symm (σ.symm i)) (τ.symm (σ.symm j))`.
  -- Use `Equiv.Perm.inv_def` + `mul_inv_rev` to rewrite `(σ*τ).symm = τ.symm * σ.symm`.
  simp [AdjMatrix.permute, ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.Perm.mul_apply]

/-- Permuting by an inverse undoes the original permutation. -/
@[simp]
theorem AdjMatrix.permute_permute_symm (σ : Equiv.Perm (Fin n)) (G : AdjMatrix n) :
    (G.permute σ).permute σ⁻¹ = G := by
  rw [← AdjMatrix.permute_mul, inv_mul_cancel, AdjMatrix.permute_one]

@[simp]
theorem AdjMatrix.permute_symm_permute (σ : Equiv.Perm (Fin n)) (G : AdjMatrix n) :
    (G.permute σ⁻¹).permute σ = G := by
  rw [← AdjMatrix.permute_mul, mul_inv_cancel, AdjMatrix.permute_one]

/-! ### §1.2  `swapVertexLabels` as a permutation action -/

/--
The existing `swapVertexLabels v1 v2 G` is precisely `G.permute (Equiv.swap v1 v2)`. This
lemma is the bridge between the concrete swap-based `Isomorphic` generator and the abstract
permutation action; everything downstream uses `permute`, not `swapVertexLabels`.
-/
theorem swapVertexLabels_eq_permute (G : AdjMatrix n) (v1 v2 : Fin n) :
    swapVertexLabels v1 v2 G = G.permute (Equiv.swap v1 v2) := by
  apply AdjMatrix.ext
  intro i j
  -- `Equiv.swap v1 v2` is self-inverse (`toFun = invFun` definitionally), so
  -- `.symm x = Equiv.swap v1 v2 x` by `rfl`; then `Equiv.swap_apply_def` unfolds
  -- `swap v1 v2 x` into the same `if … then … else …` chain that `swapVertexLabels` uses.
  have hsymm : ∀ x : Fin n, (Equiv.swap v1 v2).symm x = Equiv.swap v1 v2 x := fun _ => rfl
  simp only [AdjMatrix.permute_adj, swapVertexLabels, hsymm, Equiv.swap_apply_def]

/-! ### §1.3  The automorphism group `Aut G` -/

/--
The automorphism group of `G`: permutations that leave `G` invariant under relabeling.
Equivalently (see `mem_Aut_iff_adj`): permutations `σ` with `G.adj (σ⁻¹ i) (σ⁻¹ j) = G.adj i j`
for all `i, j`. These are the symmetries the canonizer cannot and should not distinguish.
-/
def AdjMatrix.Aut (G : AdjMatrix n) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := { σ | G.permute σ = G }
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Set.mem_setOf_eq] at *
    rw [AdjMatrix.permute_mul, hτ, hσ]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    exact AdjMatrix.permute_one G
  inv_mem' := by
    intro σ hσ
    simp only [Set.mem_setOf_eq] at *
    -- From `G.permute σ = G`, apply `.permute σ⁻¹` to both sides.
    calc G.permute σ⁻¹
        = (G.permute σ).permute σ⁻¹ := by rw [hσ]
      _ = G := AdjMatrix.permute_permute_symm σ G

theorem mem_Aut_iff {σ : Equiv.Perm (Fin n)} {G : AdjMatrix n} :
    σ ∈ G.Aut ↔ G.permute σ = G := Iff.rfl

/-- Characterization of `Aut` via the adjacency function. -/
theorem mem_Aut_iff_adj {σ : Equiv.Perm (Fin n)} {G : AdjMatrix n} :
    σ ∈ G.Aut ↔ ∀ i j, G.adj (σ.symm i) (σ.symm j) = G.adj i j := by
  constructor
  · intro h i j
    have := congrArg (fun (H : AdjMatrix n) => H.adj i j) h
    simpa [AdjMatrix.permute] using this
  · intro h
    apply AdjMatrix.ext
    intro i j
    simp [AdjMatrix.permute, h]

/-! ### §1.4  Vertex orbits -/

/-- The `Aut(G)`-orbit of a vertex `v`: all vertices reachable from `v` by an automorphism. -/
def AdjMatrix.orbit (G : AdjMatrix n) (v : Fin n) : Set (Fin n) :=
  { w | ∃ σ ∈ G.Aut, σ v = w }

theorem mem_orbit_iff {G : AdjMatrix n} {v w : Fin n} :
    w ∈ G.orbit v ↔ ∃ σ ∈ G.Aut, σ v = w := Iff.rfl

/-! ### §1.5  Same-orbit is an equivalence relation (orbits partition `Fin n`) -/

theorem AdjMatrix.mem_orbit_self (G : AdjMatrix n) (v : Fin n) : v ∈ G.orbit v :=
  ⟨1, G.Aut.one_mem, by simp⟩

theorem AdjMatrix.mem_orbit_symm {G : AdjMatrix n} {v w : Fin n} (h : w ∈ G.orbit v) :
    v ∈ G.orbit w := by
  obtain ⟨σ, hσ, hσv⟩ := h
  refine ⟨σ⁻¹, G.Aut.inv_mem hσ, ?_⟩
  -- σ v = w  ⟹  σ⁻¹ w = v.
  have : σ⁻¹ (σ v) = v := by simp
  rw [← hσv]; exact this

theorem AdjMatrix.mem_orbit_trans {G : AdjMatrix n} {u v w : Fin n}
    (huv : v ∈ G.orbit u) (hvw : w ∈ G.orbit v) : w ∈ G.orbit u := by
  obtain ⟨σ, hσ, hσu⟩ := huv
  obtain ⟨τ, hτ, hτv⟩ := hvw
  refine ⟨τ * σ, G.Aut.mul_mem hτ hσ, ?_⟩
  -- (τ * σ) u = τ (σ u) = τ v = w
  rw [Equiv.Perm.mul_apply, hσu, hτv]

/-- Same-orbit is an equivalence relation on vertices; its equivalence classes are the
`Aut(G)`-orbits, which therefore partition `Fin n`. -/
def AdjMatrix.orbitSetoid (G : AdjMatrix n) : Setoid (Fin n) where
  r v w := w ∈ G.orbit v
  iseqv :=
    { refl  := G.mem_orbit_self
      symm  := AdjMatrix.mem_orbit_symm
      trans := AdjMatrix.mem_orbit_trans }

/-! ### §1.6  Characterization used downstream: orbits are preserved by `Aut(G)` -/

/-- If `σ ∈ Aut G`, then `σ` maps each orbit to itself. This is the statement we use in later
steps: "any automorphism sends a vertex to a vertex in the same orbit." -/
theorem AdjMatrix.orbit_stable_under_Aut {G : AdjMatrix n} {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ G.Aut) (v : Fin n) : σ v ∈ G.orbit v :=
  ⟨σ, hσ, rfl⟩

/-- Conversely: if `w ∈ G.orbit v` there is an automorphism witnessing the fact (definitional,
but convenient as a named lemma). -/
theorem AdjMatrix.exists_Aut_of_mem_orbit {G : AdjMatrix n} {v w : Fin n}
    (h : w ∈ G.orbit v) : ∃ σ ∈ G.Aut, σ v = w := h

end Graph

/-!
--------------------------------------------------------------------------------
## §2  (Planned)  Bridge lemma: `Isomorphic ↔ ∃ σ, H = G.permute σ`

### Target statement

```
theorem Isomorphic_iff_exists_permute {n : Nat} {G H : AdjMatrix n} :
    G ≃ H ↔ ∃ σ : Equiv.Perm (Fin n), H = G.permute σ
```

### Why step 2 exists

The inductive `Isomorphic` relation is generated by `refl`, `swap`, and `trans`. Direct
structural induction on it is awkward for the proofs we need (Aut-equivariance, orbit
transport, choice-independence of tiebreak) because the group structure is hidden inside
a nested `.trans` tree. The bridge lemma converts `≃` into an extensional statement
about a single permutation, so from step 3 onward every proof works with `Equiv.Perm`
and its group operations rather than walking a constructor tree.

### Proof plan — (⟹) direction

By induction on `h : G ≃ H`:

- **Case `refl G`**: take `σ := 1`. Goal reduces to `G = G.permute 1`; closed by
  `AdjMatrix.permute_one` (already proved, §1.1).

- **Case `swap G v1 v2`**: take `σ := Equiv.swap v1 v2`. Goal is
  `swapVertexLabels v1 v2 G = G.permute (Equiv.swap v1 v2)`; closed by
  `swapVertexLabels_eq_permute` (already proved, §1.2).

- **Case `trans (h₁ : G₁ ≃ G₂) (h₂ : G₂ ≃ G₃)`**: from the IHs get σ₁ with
  `G₂ = G₁.permute σ₁` and σ₂ with `G₃ = G₂.permute σ₂`. Take `σ := σ₁ * σ₂`. Then
  ```
  G₁.permute (σ₁ * σ₂) = (G₁.permute σ₂).permute σ₁   -- permute_mul
                       = ...
  ```
  Wait — that doesn't immediately match. We have the shape
  `G₃ = G₂.permute σ₂ = (G₁.permute σ₁).permute σ₂`, and we want this equal to
  `G₁.permute (something)`. By `permute_mul`, `G₁.permute (σ₂ * σ₁) =
  (G₁.permute σ₁).permute σ₂`, so the right choice is **`σ := σ₂ * σ₁`**, not
  `σ₁ * σ₂`. This is the standard right-to-left composition quirk of our left action.
  The `simp` closer will catch it via `permute_mul`.

### Proof plan — (⟸) direction

Given `σ : Equiv.Perm (Fin n)` and `H = G.permute σ`, show `G ≃ H`.

Strategy: induct on a decomposition of `σ` into transpositions, using Mathlib's
`Equiv.Perm.swap_induction_on`:
```
theorem Equiv.Perm.swap_induction_on {P : Equiv.Perm α → Prop} (σ : Equiv.Perm α)
    (h1 : P 1)
    (hmul : ∀ (f : Equiv.Perm α) (x y : α), x ≠ y → P f → P (Equiv.swap x y * f)) :
    P σ
```
Define `P σ := G ≃ G.permute σ`.

- **`P 1`**: `G ≃ G.permute 1 = G` by `Isomorphic.refl` + `permute_one` (rewrite).
- **`P (Equiv.swap x y * f)` from `P f`**: from IH `G ≃ G.permute f`, we want
  `G ≃ G.permute (Equiv.swap x y * f)`. By `permute_mul`,
  `G.permute (Equiv.swap x y * f) = (G.permute f).permute (Equiv.swap x y)`.
  By `swapVertexLabels_eq_permute`, this equals
  `swapVertexLabels x y (G.permute f)`. Use `Isomorphic.swap` to connect
  `G.permute f ≃ swapVertexLabels x y (G.permute f)`, then chain with IH via
  `Isomorphic.trans`.

After proving `P σ` for all σ, specialize to the given σ and rewrite the goal
`G ≃ H` using `H = G.permute σ`.

### Risks / side-obligations

- **R1.** Mathlib's `swap_induction_on` might not exist under that exact name in the
  pinned toolchain; fallbacks are `Equiv.Perm.induction_on_mem_closure_swaps` or writing
  a bespoke induction via `List.Perm` / `List.prod` over a list of transpositions
  obtained from `σ.support`. Check with `#check @Equiv.Perm.swap_induction_on` before
  committing to the first plan.

- **R2.** The composition direction (`σ₁ * σ₂` vs. `σ₂ * σ₁`) must be nailed down in one
  place and reused everywhere. `permute_mul` fixes this: `permute (σ * τ) G =
  (permute τ G).permute σ`. Every proof that composes permutations must respect this
  order, or it won't close.

- **R3.** The (⟸) direction ends with a rewrite `H = G.permute σ`. Make sure the
  final form is literally `G ≃ H`, not `G ≃ G.permute σ`; a stray `subst` or explicit
  `rw [h]` at the right moment is needed.

### Deliverables of step 2

One theorem — `Isomorphic_iff_exists_permute` — plus (for convenience) two unidirectional
versions extracted from it:

```
theorem Isomorphic_of_permute   : H = G.permute σ → G ≃ H
theorem permute_of_Isomorphic  : G ≃ H → ∃ σ, H = G.permute σ
```

After step 2 lands, step 3 (Aut-restricted pipeline equivariance) can be stated entirely
in terms of `G.permute σ` with `σ ∈ G.Aut`, and the proofs no longer need to walk the
`Isomorphic` constructor tree.
-/
