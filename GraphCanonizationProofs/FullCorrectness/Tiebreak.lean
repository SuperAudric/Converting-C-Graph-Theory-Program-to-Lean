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

/-- **§5.1**  `TypedAut` after `breakTie` is the `v*`-stabilizer of the original.

Let `t₀` be the smallest tied value, `v* := min (typeClass vts t₀)` (by `Fin` order), and
`vts' := (breakTie vts t₀).1`. Then a permutation σ belongs to `TypedAut G vts'` iff it
belongs to `TypedAut G vts` and additionally fixes `v*`.

**Proof sketch.** By definition of `breakTie`, the unique vertex with `vts'[w] = t₀` is
`v*`, and `vts'[w] = vts[w]` for every `w ∉ typeClass vts t₀` and `vts'[w] = t₀ + 1` for
`w ∈ typeClass vts t₀ \ {v*}`.

  - (⟹) Let σ ∈ TypedAut G vts'. Then σ preserves vts' pointwise; in particular it
        fixes the unique value-`t₀` vertex of vts', which is `v*`. It also preserves
        `vts` because the partition into value-classes is the same (modulo the split of
        `typeClass t₀` into `{v*}` vs. the rest).

  - (⟸) Let σ ∈ TypedAut G vts with σ v* = v*. Case-analyse `vts' w`:
          * `w = v*`:              `σ v* = v*` forces `vts'[σ v*] = vts'[v*]`.
          * `w ∈ V_{t₀} \ {v*}`:   vts[σ w] = vts[w] = t₀, and σ w ≠ v* because σ is a
                                    bijection fixing v*. Hence `vts'[σ w] = t₀+1 = vts'[w]`.
          * otherwise:             `vts'[w] = vts[w]`, similarly for `σ w` (outside
                                    `typeClass t₀`), and σ preserves vts.

**Deliverable.**
-/
theorem breakTie_Aut_stabilizer
    (G : AdjMatrix n) (vts : Array VertexType) (t₀ : VertexType) (v_star : Fin n)
    (_hmin : ∀ w ∈ @typeClass n vts t₀, v_star.val ≤ w.val)
    (_hmem : v_star ∈ @typeClass n vts t₀) :
    ∀ σ : Equiv.Perm (Fin n),
      σ ∈ G.TypedAut (breakTie vts t₀).1 ↔
      (σ ∈ G.TypedAut vts ∧ σ v_star = v_star) := by
  sorry

/-- **§5.2**  Strict shrinking of `TypedAut` under `breakTie`.

If `vts` is Aut(G)-invariant (every σ ∈ Aut G preserves `vts`) and the type-class of the
smallest repeated value has size ≥ 2, then `TypedAut G (breakTie vts t₀).1` is a *proper*
subgroup of `TypedAut G vts`.

**Proof sketch.** By §4's corollary (convergeLoop_Aut_invariant), all vertices in a
given type class lie in a single Aut(G)-orbit. If the class has ≥ 2 elements, picking any
`w ≠ v*` in the class gives some σ ∈ TypedAut G vts with σ v* = w ≠ v*, so σ is not
in the `v*`-stabilizer. By §5.1 this σ is in `TypedAut G vts` but not in
`TypedAut G (breakTie vts t₀).1`. Combined with §5.1's ⊆ direction, the inclusion is
strict.
-/
theorem breakTie_strict_shrink
    (G : AdjMatrix n) (vts : Array VertexType) (t₀ : VertexType)
    (_hAutInv : ∀ σ ∈ G.Aut, VtsInvariant σ vts)
    (_htwo : ∃ v₁ v₂ : Fin n, v₁ ≠ v₂ ∧
                (vts.getD v₁.val 0 = t₀) ∧ (vts.getD v₂.val 0 = t₀)) :
    G.TypedAut (breakTie vts t₀).1 < G.TypedAut vts := by
  sorry

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
