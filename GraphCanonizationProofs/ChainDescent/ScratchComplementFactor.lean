/-
# Route A, increment 2 — the orthogonal split lemmas (the complement-factoring foundation)

**What this module builds.** The geometric foundation of route A's *complement-factoring* (recovery doc §8 ITEM B
"INCREMENT 2"): the step that turns the `2`-round isotropy-count separation at a span-dim-2 base `S ⊇ {0,a,b}` into a
**`d`-independent** local count over `W = ⟨a,b⟩`. The mechanism decomposes `V = W ⊕ Wᗮ` (orthogonal w.r.t. the polar
form) and factors every difference norm `Q(v − u)` across the two summands. The `(d−2)`-dimensional complement `Wᗮ`
then contributes a factor depending on `v` **only through `Q(v⊥)`** — a `Q`-level datum that cancels in the separation
comparison (Witt on the complement) — leaving a fixed local count over the `2`-dim `W`. This is exactly what the
`recovery_depth_probe.py` `r*`-flat / orbit-count-`d`-uniform evidence predicts.

**This increment lands the algebraic foundation — the orthogonal split of the difference norm.** For a submodule `W`
and its polar-orthogonal complement `Wᗮ = BilinForm.orthogonal Q.polarBilin W`:

* `map_add_of_polar_zero` — orthogonal vectors add in `Q` (`polar Q x y = 0 ⟹ Q(x+y) = Q x + Q y`), the pure-algebra
  core (from `QuadraticMap.map_add`).
* `polar_zero_of_mem_orthogonal` — membership in `Wᗮ` kills the polar pairing with `W`.
* `map_add_split` / `map_sub_split` — **the split**: `Q(v − u) = Q(v∥ − u∥) + Q(v⊥ − u⊥)` for the `W`/`Wᗮ`
  decompositions of `v, u`. This is the identity the count-factoring rests on.
* `exists_decomp_of_isCompl` — obtains the `W`/`Wᗮ` components of any vertex from `IsCompl W Wᗮ` (supplied by Mathlib's
  `BilinForm.isCompl_orthogonal_of_restrict_nondegenerate` when `Q|_W` is nondegenerate — the span-dim-2 anisotropic
  case). Together with the split, this decomposes every vertex's Gram data into a local `W`-part and a `Q(·⊥)` datum.

**What remains (the count-factoring proper, next sub-increment).** Applying the split inside the `2`-round isotropy
count: the count over `w` factors as a sum over `w = w∥ + w⊥`, and for fixed `w∥` the inner `w⊥`-count depends on the
vertex only through `Q(v⊥)` (a Gauss sum over the `(d−2)`-dim complement, evaluated by `PairForm`/`GaussCount`). That is
the `v`-independent-up-to-`Q(v⊥)` factor whose cancellation gives the `d`-independent local separation. This module is
the geometry it stands on.

Pure geometry — no `Fintype`, no Witt (the split is an identity; Witt enters only later, in `WittExtendsToOrbit`, to
turn the count-determiner into the orbit bound). Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`,
NOT in `build.sh`.
-/
import ChainDescent.PairForm
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

namespace ChainDescent.ComplementFactor

open QuadraticMap LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- **Orthogonal vectors add in `Q`.** If `polar Q x y = 0` then `Q (x + y) = Q x + Q y`. The pure-algebra core of the
split (`QuadraticMap.map_add`: `Q(x+y) = Q x + Q y + polar Q x y`). -/
theorem map_add_of_polar_zero {x y : V} (h : QuadraticMap.polar Q x y = 0) :
    Q (x + y) = Q x + Q y := by
  have hm := QuadraticMap.map_add (⇑Q) x y
  rw [h, add_zero] at hm
  exact hm

/-- **The complement kills the polar pairing.** For `x ∈ W` and `y ∈ Wᗮ = BilinForm.orthogonal Q.polarBilin W`,
`polar Q x y = 0`. Unpacks `mem_orthogonal_iff` (`∀ n ∈ W, IsOrtho polarBilin n y`) at `n = x`. -/
theorem polar_zero_of_mem_orthogonal {W : Submodule K V} {x y : V}
    (hx : x ∈ W) (hy : y ∈ BilinForm.orthogonal Q.polarBilin W) : QuadraticMap.polar Q x y = 0 := by
  have h := (BilinForm.mem_orthogonal_iff).mp hy x hx
  rw [BilinForm.isOrtho_def, polarBilin_apply_apply] at h
  exact h

/-- **The orthogonal split (sum form).** For `x ∈ W` and `y ∈ Wᗮ`, `Q (x + y) = Q x + Q y`. -/
theorem map_add_split {W : Submodule K V} {x y : V}
    (hx : x ∈ W) (hy : y ∈ BilinForm.orthogonal Q.polarBilin W) :
    Q (x + y) = Q x + Q y :=
  map_add_of_polar_zero (polar_zero_of_mem_orthogonal hx hy)

/-- **★ The orthogonal split (difference form) — the count-factoring foundation.** Writing `v = v₁ + v₂` and
`u = u₁ + u₂` with `v₁, u₁ ∈ W` and `v₂, u₂ ∈ Wᗮ`, the difference norm splits across the summands:
`Q ((v₁ + v₂) − (u₁ + u₂)) = Q (v₁ − u₁) + Q (v₂ − u₂)`. The `W`-part carries the local Gram data
(`polar · a`, `polar · b`); the `Wᗮ`-part carries the complement datum `Q(·⊥)`. This is the identity on which the
count-factoring rests. -/
theorem map_sub_split {W : Submodule K V} {v₁ u₁ v₂ u₂ : V}
    (hv₁ : v₁ ∈ W) (hu₁ : u₁ ∈ W)
    (hv₂ : v₂ ∈ BilinForm.orthogonal Q.polarBilin W) (hu₂ : u₂ ∈ BilinForm.orthogonal Q.polarBilin W) :
    Q ((v₁ + v₂) - (u₁ + u₂)) = Q (v₁ - u₁) + Q (v₂ - u₂) := by
  have hW : v₁ - u₁ ∈ W := W.sub_mem hv₁ hu₁
  have hWc : v₂ - u₂ ∈ BilinForm.orthogonal Q.polarBilin W :=
    (BilinForm.orthogonal Q.polarBilin W).sub_mem hv₂ hu₂
  have hsplit : (v₁ + v₂) - (u₁ + u₂) = (v₁ - u₁) + (v₂ - u₂) := by abel
  rw [hsplit, map_add_split hW hWc]

/-- **Decomposition into `W ⊕ Wᗮ`.** From `IsCompl W Wᗮ` (supplied by
`BilinForm.isCompl_orthogonal_of_restrict_nondegenerate` when `Q|_W` is nondegenerate — the span-dim-2 anisotropic
base), every vertex `v` splits as `v = v₁ + v₂` with `v₁ ∈ W`, `v₂ ∈ Wᗮ`. Feeds `map_sub_split` to give each vertex a
local `W`-part and a complement `Q(·⊥)` datum. -/
theorem exists_decomp_of_isCompl {W : Submodule K V}
    (h : IsCompl W (BilinForm.orthogonal Q.polarBilin W)) (v : V) :
    ∃ v₁ ∈ W, ∃ v₂ ∈ BilinForm.orthogonal Q.polarBilin W, v₁ + v₂ = v := by
  have hv : v ∈ W ⊔ BilinForm.orthogonal Q.polarBilin W := by rw [h.sup_eq_top]; trivial
  exact Submodule.mem_sup.mp hv

end ChainDescent.ComplementFactor
