import FullCorrectness.Automorphism

/-!
# §2  Bridge lemma: `Isomorphic ↔ ∃ σ, H = G.permute σ`  [planned]

This module is a placeholder for step 2 of the proof-development plan. It will hold one
theorem — the bridge between the inductive `Isomorphic` relation and the extensional
"∃ permutation" statement — plus its two unidirectional corollaries.

## Target statement

```
theorem Isomorphic_iff_exists_permute {n : Nat} {G H : AdjMatrix n} :
    G ≃ H ↔ ∃ σ : Equiv.Perm (Fin n), H = G.permute σ
```

## Proof plan — (⟹) direction

Induction on `h : G ≃ H`:

- **Case `refl G`**: take `σ := 1`; close by `AdjMatrix.permute_one` (§1.1).
- **Case `swap G v1 v2`**: take `σ := Equiv.swap v1 v2`; close by `swapVertexLabels_eq_permute`
  (§1.2).
- **Case `trans h₁ h₂`**: from IHs get σ₁ with `G₂ = G₁.permute σ₁` and σ₂ with
  `G₃ = G₂.permute σ₂`. Take `σ := σ₂ * σ₁`. By `permute_mul`,
  `G₁.permute (σ₂ * σ₁) = (G₁.permute σ₁).permute σ₂ = G₂.permute σ₂ = G₃`.
  The **composition order** (σ₂ * σ₁, not σ₁ * σ₂) is forced by the left-action convention.

## Proof plan — (⟸) direction

Given `H = G.permute σ`, show `G ≃ H` by induction on a decomposition of `σ` into
transpositions via Mathlib's `Equiv.Perm.swap_induction_on`. Define `P σ := G ≃ G.permute σ`:

- **`P 1`**: `G ≃ G.permute 1 = G` by `Isomorphic.refl` + `permute_one`.
- **`P (Equiv.swap x y * f)` from `P f`**: by `permute_mul`,
  `G.permute (swap x y * f) = (G.permute f).permute (swap x y)
   = swapVertexLabels x y (G.permute f)` (by `swapVertexLabels_eq_permute`).
  Use `Isomorphic.swap` then `Isomorphic.trans` with the IH.

After proving `P σ` for all σ, rewrite the goal `G ≃ H` using `H = G.permute σ`.

## Risks

- **R1.** `Equiv.Perm.swap_induction_on` may be named differently in the pinned toolchain.
  Alternative: write a bespoke induction using `σ.support` and `Equiv.Perm.cycleType`.
- **R2.** The composition direction (`σ₁ * σ₂` vs `σ₂ * σ₁`) must match `permute_mul` —
  see (⟹) case `trans`.

## Deliverables

```
theorem Isomorphic_of_permute  {σ} (h : H = G.permute σ) : G ≃ H
theorem permute_of_Isomorphic  (h : G ≃ H) : ∃ σ, H = G.permute σ
theorem Isomorphic_iff_exists_permute : G ≃ H ↔ ∃ σ, H = G.permute σ
```

With these in hand, step 3 onward can state and prove Aut-equivariance entirely in the
`permute` / `Aut` world, never re-walking the inductive `Isomorphic` constructors.
-/

namespace Graph
namespace AdjMatrix

-- (Definitions and theorems for step 2 will be added here.)

end AdjMatrix
end Graph
