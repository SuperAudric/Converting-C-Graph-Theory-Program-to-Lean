import ChainDescent.DeepenTinhofer

/-!
# The fibring lemma — Step 1 of the CAO-propagation proof plan

`docs/chain-descent-cao-propagation.md` §12.1. The question this file serves is

> start from the exact orbit partition (`CellsAreOrbits`), individualize `v`, refine —
> are the cells still orbits?

which is the domain hypothesis behind `Tinhofer` (`DeepenTinhofer.lean`). §1 of that doc reduces it
to a statement about **orbitals** (2-orbits), and this file proves the reduction.

## What is proved

Write `K = IsColAut adj χ` (a group, §1 below), `D` for the `χ`-cell of `v` and `C` for any cell.

* **`exists_row_transport`** — if `D` is a single `K`-orbit then **every orbital meets `v`'s row**:
  any pair `(a, b)` with `a ∈ D` is orbital-equivalent to some `(v, u)` with `u` in `b`'s cell.
  This is the only place transitivity on `D` is used, and it is what makes the correspondence
  surjective.
* **`sameStabOrbit_iff_sameOrbital_row`** — on `v`'s row the two notions coincide: `u, w` lie in one
  orbit of the point stabilizer `K_v` iff `(v,u)` and `(v,w)` lie in one orbital.
* **`sameStabOrbit_of_transports`** — the row transport is well defined up to `K_v`: two transports
  of the same pair land in one `K_v`-orbit.
* **`sameOrbital_iff_sameStabOrbit_of_transport`** — the row transport is a **complete invariant** of
  the orbital class. Together with `exists_row_transport` this is the bijection
  `{K-orbitals inside D × C}  ≃  {K_v-orbits on C}`, `O ↦ {u ∈ C : (v,u) ∈ O}`.

* **§4 — the bridge to refinement (the doc's Step 2).** For an `IsColAut`-invariant pair colouring
  `f` (which is what any 2-WL closure gives):
  - `pairInvariant_eq_of_sameOrbital` — `f` is constant on orbitals, i.e. its classes are *unions*
    of orbitals. This is the soundness half, and it is why refinement can never split an orbit.
  - **`levelSet_iff_stabOrbit_of_separates`** — if `f` merely *separates the orbitals in `v`'s row*,
    then the induced vertex colouring `u ↦ f v u` has level sets **exactly** the `K_v`-orbits.

  So "refinement preserves `CellsAreOrbits`" reduces to "the extension separates the orbitals
  between fibres", with nothing left over. In particular the target holds *automatically* wherever
  the closure is already orbital-separating — the doc's §12.2 reduction, which is what confines all
  remaining content to the fused classes.

**Not** proved here: that a 2-WL closure does separate them. That is the open crux (doc §12.3), and
`exists_row_transport` is deliberately stated so that the crux is the only thing left.
-/

namespace ChainDescent
namespace CaoFibring

open ChainDescent.Consume (IsColAut)
open ChainDescent.Deepen (CellSingleOrbit)

variable {n : Nat}

/-! ## 1. `IsColAut` is a group

Nothing here is surprising; it is needed because the fibring argument composes and inverts
automorphisms, and `Equiv.Perm` multiplication is `(σ * τ) x = σ (τ x)`. -/

theorem isColAut_one (adj : AdjMatrix n) (χ : Colouring n) : IsColAut adj χ 1 :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

/-- `Equiv.Perm`'s inverse is `Equiv.symm`, so the two cancellation facts are taken from the group
structure rather than from `Equiv` rewriting (the `σ⁻¹` / `σ.symm` forms do not match syntactically). -/
private theorem perm_apply_inv (σ : Equiv.Perm (Fin n)) (x : Fin n) : σ (σ⁻¹ x) = x := by
  have h : (σ * σ⁻¹) x = (1 : Equiv.Perm (Fin n)) x := by rw [mul_inv_cancel]
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h
  exact h

private theorem perm_inv_apply (σ : Equiv.Perm (Fin n)) (x : Fin n) : σ⁻¹ (σ x) = x := by
  have h : (σ⁻¹ * σ) x = (1 : Equiv.Perm (Fin n)) x := by rw [inv_mul_cancel]
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h
  exact h

theorem isColAut_mul {adj : AdjMatrix n} {χ : Colouring n} {σ τ : Equiv.Perm (Fin n)}
    (hσ : IsColAut adj χ σ) (hτ : IsColAut adj χ τ) : IsColAut adj χ (σ * τ) := by
  refine ⟨fun i j => ?_, fun v => ?_⟩
  · simp only [Equiv.Perm.mul_apply]
    rw [hσ.1, hτ.1]
  · simp only [Equiv.Perm.mul_apply]
    rw [hσ.2, hτ.2]

theorem isColAut_inv {adj : AdjMatrix n} {χ : Colouring n} {σ : Equiv.Perm (Fin n)}
    (hσ : IsColAut adj χ σ) : IsColAut adj χ σ⁻¹ := by
  refine ⟨fun i j => ?_, fun v => ?_⟩
  · have h := hσ.1 (σ⁻¹ i) (σ⁻¹ j)
    rw [perm_apply_inv, perm_apply_inv] at h
    exact h.symm
  · have h := hσ.2 (σ⁻¹ v)
    rw [perm_apply_inv] at h
    exact h.symm

/-! ## 2. Orbitals and stabilizer orbits -/

/-- Two ordered pairs lie in the same **orbital** (2-orbit) of the colour-automorphism group. -/
def SameOrbital (adj : AdjMatrix n) (χ : Colouring n) (a b a' b' : Fin n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ a = a' ∧ σ b = b'

/-- `u` and `w` lie in one orbit of the **point stabilizer** of `v`. This is the partition that
individualizing `v` imposes on every other cell. -/
def SameStabOrbit (adj : AdjMatrix n) (χ : Colouring n) (v u w : Fin n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ v = v ∧ σ u = w

variable {adj : AdjMatrix n} {χ : Colouring n}

theorem sameOrbital_refl (a b : Fin n) : SameOrbital adj χ a b a b :=
  ⟨1, isColAut_one adj χ, Equiv.Perm.one_apply a, Equiv.Perm.one_apply b⟩

theorem sameOrbital_symm {a b a' b' : Fin n} (h : SameOrbital adj χ a b a' b') :
    SameOrbital adj χ a' b' a b := by
  obtain ⟨σ, hσ, ha, hb⟩ := h
  refine ⟨σ⁻¹, isColAut_inv hσ, ?_, ?_⟩
  · rw [← ha]; exact perm_inv_apply σ a
  · rw [← hb]; exact perm_inv_apply σ b

theorem sameOrbital_trans {a b a' b' a'' b'' : Fin n} (h₁ : SameOrbital adj χ a b a' b')
    (h₂ : SameOrbital adj χ a' b' a'' b'') : SameOrbital adj χ a b a'' b'' := by
  obtain ⟨σ, hσ, ha, hb⟩ := h₁
  obtain ⟨τ, hτ, ha', hb'⟩ := h₂
  refine ⟨τ * σ, isColAut_mul hτ hσ, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, ha, ha']
  · rw [Equiv.Perm.mul_apply, hb, hb']

theorem sameStabOrbit_refl (v u : Fin n) : SameStabOrbit adj χ v u u :=
  ⟨1, isColAut_one adj χ, Equiv.Perm.one_apply v, Equiv.Perm.one_apply u⟩

theorem sameStabOrbit_symm {v u w : Fin n} (h : SameStabOrbit adj χ v u w) :
    SameStabOrbit adj χ v w u := by
  obtain ⟨σ, hσ, hv, hu⟩ := h
  refine ⟨σ⁻¹, isColAut_inv hσ, ?_, ?_⟩
  · conv_lhs => rw [← hv]
    exact perm_inv_apply σ v
  · rw [← hu]; exact perm_inv_apply σ u

theorem sameStabOrbit_trans {v u w x : Fin n} (h₁ : SameStabOrbit adj χ v u w)
    (h₂ : SameStabOrbit adj χ v w x) : SameStabOrbit adj χ v u x := by
  obtain ⟨σ, hσ, hv, hu⟩ := h₁
  obtain ⟨τ, hτ, hv', hw⟩ := h₂
  refine ⟨τ * σ, isColAut_mul hτ hσ, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hv, hv']
  · rw [Equiv.Perm.mul_apply, hu, hw]

/-- **On `v`'s row the two notions coincide.** The `K_v`-orbits on any cell are exactly the fibres
of the orbital classification over `v`. (Definitional, but it is the statement Step 2 consumes.) -/
theorem sameStabOrbit_iff_sameOrbital_row (v u w : Fin n) :
    SameStabOrbit adj χ v u w ↔ SameOrbital adj χ v u v w := Iff.rfl

/-! ## 3. The fibring lemma -/

/-- **Every orbital meets `v`'s row** — the surjectivity half, and the only place transitivity on
`v`'s cell is used. Any pair `(a, b)` whose first coordinate shares `v`'s colour is
orbital-equivalent to a pair `(v, u)`, with `u` in the same cell as `b`. -/
theorem exists_row_transport {v a : Fin n} (hD : CellSingleOrbit adj χ (χ v))
    (ha : χ a = χ v) (b : Fin n) :
    ∃ u, SameOrbital adj χ a b v u ∧ χ u = χ b := by
  obtain ⟨σ, hσ, hav⟩ := hD a v ha rfl
  exact ⟨σ b, ⟨σ, hσ, hav, rfl⟩, hσ.2 b⟩

/-- **The row transport is well defined up to the stabilizer.** Two transports of one pair into
`v`'s row differ by an element of `K_v`. -/
theorem sameStabOrbit_of_transports {a b v u u' : Fin n} (h₁ : SameOrbital adj χ a b v u)
    (h₂ : SameOrbital adj χ a b v u') : SameStabOrbit adj χ v u u' :=
  sameOrbital_trans (sameOrbital_symm h₁) h₂

/-- **★ THE FIBRING LEMMA.** The row transport is a **complete invariant** of the orbital class:
pairs `(a,b)` and `(a',b')` are orbital-equivalent iff their transports into `v`'s row lie in one
orbit of the point stabilizer. With `exists_row_transport` (which supplies the transports) this is
the bijection

  `{K-orbitals inside D × C}  ≃  {K_v-orbits on C}`,  `O ↦ {u ∈ C : (v,u) ∈ O}`.

Note it needs no hypothesis at all: `CellSingleOrbit` is required only for *existence* of the
transports, never for the correspondence itself. -/
theorem sameOrbital_iff_sameStabOrbit_of_transport {a b a' b' v u u' : Fin n}
    (h : SameOrbital adj χ a b v u) (h' : SameOrbital adj χ a' b' v u') :
    SameOrbital adj χ a b a' b' ↔ SameStabOrbit adj χ v u u' := by
  constructor
  · intro haa
    exact sameStabOrbit_of_transports h (sameOrbital_trans haa h')
  · intro hst
    exact sameOrbital_trans h (sameOrbital_trans hst (sameOrbital_symm h'))

/-! ## 4. The bridge to refinement — the doc's Step 2

`f` stands for any isomorphism-invariant colouring of *pairs*; a 2-WL closure is exactly such a
thing. The two results below are the two halves of the reduction. -/

/-- An `IsColAut`-invariant colouring of ordered pairs. -/
def PairInvariant {β : Type*} (adj : AdjMatrix n) (χ : Colouring n) (f : Fin n → Fin n → β) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → ∀ a b, f (σ a) (σ b) = f a b

/-- **Soundness.** An invariant pair colouring is constant on orbitals — its classes are *unions* of
orbitals. This is why refinement can never split an orbit, and it is the half that is free. -/
theorem pairInvariant_eq_of_sameOrbital {β : Type*} {f : Fin n → Fin n → β}
    (hf : PairInvariant adj χ f) {a b a' b' : Fin n} (h : SameOrbital adj χ a b a' b') :
    f a b = f a' b' := by
  obtain ⟨σ, hσ, ha, hb⟩ := h
  rw [← ha, ← hb, hf σ hσ a b]

/-- **★ STEP 2.** If an invariant pair colouring *separates the orbitals in `v`'s row*, then the
vertex colouring it induces there, `u ↦ f v u`, has level sets **exactly** the `K_v`-orbits — i.e.
`CellsAreOrbits` is preserved at `v`.

So preservation reduces with no remainder to orbital separation, and it holds automatically wherever
the closure already separates. The open crux (doc §12.3) is precisely the hypothesis `hsep`. -/
theorem levelSet_iff_stabOrbit_of_separates {β : Type*} {f : Fin n → Fin n → β}
    (hf : PairInvariant adj χ f) {v : Fin n}
    (hsep : ∀ u w : Fin n, f v u = f v w → SameOrbital adj χ v u v w) (u w : Fin n) :
    f v u = f v w ↔ SameStabOrbit adj χ v u w := by
  constructor
  · intro h
    exact (sameStabOrbit_iff_sameOrbital_row v u w).mpr (hsep u w h)
  · intro h
    exact pairInvariant_eq_of_sameOrbital hf ((sameStabOrbit_iff_sameOrbital_row v u w).mp h)

end CaoFibring
end ChainDescent
