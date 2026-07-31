import ChainDescent.CaoFibring

/-!
# The refinement round — Step 3's substrate (`docs/chain-descent-cao-propagation.md` §12.3, §12.6 M3)

`CaoFibring.lean` reduced CAO-propagation to a single hypothesis `hsep` about an **abstract**
invariant pair colouring `f`, with a parenthetical that "a 2-WL closure is one". This file makes that
real, and formalizes the negative theorem the M3 instrumentation is built around.

## 1. The gap this closes

`CaoFibring.levelSet_iff_stabOrbit_of_separates` asks for `PairInvariant adj χ f` — invariance under
**all** of `IsColAut adj χ`. The colouring the algorithm actually builds is the closure of the
configuration with `v` **individualized**, and that is invariant only under the **stabilizer** of `v`.
So the landed Step 2 did not literally apply to the real object. Fixed here:

* **`PairInvariantAt`** — invariance under `{σ ∈ IsColAut adj χ : σ v = v}`, which is exactly the
  group `CaoFibring.SameStabOrbit` is about.
* **`levelSet_iff_stabOrbit_of_separatesAt`** — Step 2 at that weaker hypothesis. Nothing is lost:
  the `←` direction only ever used a `σ` fixing `v`, since it comes from `SameStabOrbit`.
* **`pairInvariantAt_ext0`** + **`pairInvariantAt_iterRoundBy`** — individualizing `v` gives a
  `PairInvariantAt` colouring and *any number of refinement rounds preserves that*, so the whole
  closure is invariant. Capstone **`step2_closure`**: Step 2 applies to the real object.

## 2. The round-1 barrier (doc §12.3), machine-checked

The doc states — and every proof attempt is constrained by — that at a **coherent** `X` the round-1
refinement of `(v,u)` is an intersection number, identical across the class, so *the base point learns
nothing directly*. That was prose. Here it is **`round1_barrier`**, with coherence in the form that
actually says it: a coherent colouring is a **fixpoint** of the round (`Coherent`).

Its positive companion is **`witness_ne_base`**: if a round *does* separate `(v,u)` from `(v,w)` while
they share a colour, the difference provably lives in the intermediate points `x ≠ v`. So the marking
must leave `v` and come back — the non-locality is a theorem, not an observation, and it is the shape
the M3 cause chains exhibit (uniform depth 3, final witness `(v-ROW born r0, FAR born r2)`).

**Not** proved here: that the closure separates the orbitals. That is the open crux (doc §12.3).
-/

namespace ChainDescent
namespace CaoRound

open ChainDescent.Consume (IsColAut)
open ChainDescent.CaoFibring

variable {n : Nat}

/-! ## 1. Pointed invariance, and Step 2 at the weaker hypothesis -/

/-- A pair colouring invariant under the **stabilizer of `v`** — the group that acts once `v` has been
individualized, and the one `CaoFibring.SameStabOrbit` quantifies over. Strictly weaker than
`PairInvariant`, and it is what the real closure satisfies. -/
def PairInvariantAt {β : Type*} (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n)
    (f : Fin n → Fin n → β) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ v = v → ∀ a b, f (σ a) (σ b) = f a b

variable {adj : AdjMatrix n} {χ : Colouring n}

theorem pairInvariantAt_of_pairInvariant {β : Type*} {f : Fin n → Fin n → β} (v : Fin n)
    (hf : PairInvariant adj χ f) : PairInvariantAt adj χ v f :=
  fun σ hσ _ a b => hf σ hσ a b

/-- **Soundness at the pointed group.** An invariant pair colouring is constant on the orbits of the
`v`-stabilizer along `v`'s row — which is all Step 2 needs. -/
theorem pairInvariantAt_eq_of_sameStabOrbit {β : Type*} {f : Fin n → Fin n → β} {v : Fin n}
    (hf : PairInvariantAt adj χ v f) {u w : Fin n} (h : SameStabOrbit adj χ v u w) :
    f v u = f v w := by
  obtain ⟨σ, hσ, hv, hu⟩ := h
  have hx := hf σ hσ hv v u
  rw [hv, hu] at hx
  exact hx.symm

/-- **★ STEP 2, at the hypothesis the real object satisfies** (doc §12.2). If a colouring invariant
under the `v`-stabilizer separates the orbitals in `v`'s row, the vertex colouring it induces there has
level sets **exactly** the `K_v`-orbits.

This supersedes `CaoFibring.levelSet_iff_stabOrbit_of_separates` for applications: that version wants
invariance under all of `IsColAut adj χ`, which the individualized closure does not have. -/
theorem levelSet_iff_stabOrbit_of_separatesAt {β : Type*} {f : Fin n → Fin n → β} {v : Fin n}
    (hf : PairInvariantAt adj χ v f)
    (hsep : ∀ u w : Fin n, f v u = f v w → SameStabOrbit adj χ v u w) (u w : Fin n) :
    f v u = f v w ↔ SameStabOrbit adj χ v u w :=
  ⟨hsep u w, pairInvariantAt_eq_of_sameStabOrbit hf⟩

/-! ## 2. The refinement round

`sig f a b` is the multiset of **triangle types** `(f a x, f x b)` over intermediate points `x` — the
round's entire content, and the object `probe_cao_cause.py` extracts witnesses from. -/

/-- The multiset of triangle types at `(a, b)`. -/
def sig {β : Type*} (f : Fin n → Fin n → β) (a b : Fin n) : Multiset (β × β) :=
  (Finset.univ : Finset (Fin n)).val.map (fun x => (f a x, f x b))

/-- One 2-dimensional refinement round, then re-encoded by `enc` so the colour type is stable under
iteration (the rank-renumbering every implementation does). -/
def roundBy {β : Type*} (enc : β × Multiset (β × β) → β) (f : Fin n → Fin n → β) :
    Fin n → Fin n → β := fun a b => enc (f a b, sig f a b)

/-- `k` refinement rounds. -/
def iterRoundBy {β : Type*} (enc : β × Multiset (β × β) → β) :
    Nat → (Fin n → Fin n → β) → (Fin n → Fin n → β)
  | 0, f => f
  | k + 1, f => iterRoundBy enc k (roundBy enc f)

/-- Reindexing the intermediate point by a permutation leaves the universe multiset alone. -/
private theorem map_univ_perm (σ : Equiv.Perm (Fin n)) :
    Multiset.map σ (Finset.univ : Finset (Fin n)).val = (Finset.univ : Finset (Fin n)).val := by
  have h : (Finset.univ : Finset (Fin n)).map σ.toEmbedding = Finset.univ :=
    Finset.map_univ_equiv σ
  calc Multiset.map σ (Finset.univ : Finset (Fin n)).val
      = ((Finset.univ : Finset (Fin n)).map σ.toEmbedding).val := rfl
    _ = (Finset.univ : Finset (Fin n)).val := by rw [h]

/-- **The heart of invariance-preservation**: a `σ` under which `f` is invariant may be absorbed into
the intermediate point, because it permutes the universe. -/
theorem sig_congr {β : Type*} {f : Fin n → Fin n → β} {σ : Equiv.Perm (Fin n)}
    (h : ∀ a b, f (σ a) (σ b) = f a b) (a b : Fin n) : sig f (σ a) (σ b) = sig f a b := by
  unfold sig
  calc (Finset.univ : Finset (Fin n)).val.map (fun x => (f (σ a) x, f x (σ b)))
      = (Multiset.map σ (Finset.univ : Finset (Fin n)).val).map
          (fun x => (f (σ a) x, f x (σ b))) := by rw [map_univ_perm σ]
    _ = (Finset.univ : Finset (Fin n)).val.map (fun y => (f (σ a) (σ y), f (σ y) (σ b))) := by
          rw [Multiset.map_map]; rfl
    _ = (Finset.univ : Finset (Fin n)).val.map (fun y => (f a y, f y b)) := by
          refine Multiset.map_congr rfl (fun y _ => ?_)
          rw [h a y, h y b]

/-- **A round preserves pointed invariance.** -/
theorem pairInvariantAt_roundBy {β : Type*} {enc : β × Multiset (β × β) → β}
    {f : Fin n → Fin n → β} {v : Fin n} (hf : PairInvariantAt adj χ v f) :
    PairInvariantAt adj χ v (roundBy enc f) := by
  intro σ hσ hv a b
  show enc (f (σ a) (σ b), sig f (σ a) (σ b)) = enc (f a b, sig f a b)
  rw [hf σ hσ hv a b, sig_congr (hf σ hσ hv) a b]

/-- **Any number of rounds preserves it** — so the whole closure is invariant. -/
theorem pairInvariantAt_iterRoundBy {β : Type*} {enc : β × Multiset (β × β) → β}
    {v : Fin n} : ∀ (k : Nat) {f : Fin n → Fin n → β}, PairInvariantAt adj χ v f →
      PairInvariantAt adj χ v (iterRoundBy enc k f)
  | 0, _, hf => hf
  | k + 1, _, hf => pairInvariantAt_iterRoundBy k (pairInvariantAt_roundBy hf)

/-- The unpointed version, for the closure taken *before* individualization. -/
theorem pairInvariant_roundBy {β : Type*} {enc : β × Multiset (β × β) → β}
    {f : Fin n → Fin n → β} (hf : PairInvariant adj χ f) :
    PairInvariant adj χ (roundBy enc f) := by
  intro σ hσ a b
  show enc (f (σ a) (σ b), sig f (σ a) (σ b)) = enc (f a b, sig f a b)
  rw [hf σ hσ a b, sig_congr (hf σ hσ) a b]

/-! ### 2b. The individualized start -/

/-- The individualized initial colouring: the old colour plus the flags marking `v`. This is where —
and the **only** where — the extension's new information enters. -/
def ext0 {β : Type*} (f : Fin n → Fin n → β) (v : Fin n) : Fin n → Fin n → β × Bool × Bool :=
  fun a b => (f a b, decide (a = v), decide (b = v))

/-- Individualizing `v` keeps the colouring invariant under the **stabilizer** of `v` — the flags are
exactly what a `σ` fixing `v` preserves. -/
theorem pairInvariantAt_ext0 {β : Type*} {f : Fin n → Fin n → β} {v : Fin n}
    (hf : PairInvariantAt adj χ v f) : PairInvariantAt adj χ v (ext0 f v) := by
  intro σ hσ hv a b
  have key : ∀ c : Fin n, decide (σ c = v) = decide (c = v) := by
    intro c
    refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
    · rw [← hv] at h; exact σ.injective h
    · rw [h, hv]
  show (f (σ a) (σ b), decide (σ a = v), decide (σ b = v)) = (f a b, decide (a = v), decide (b = v))
  rw [hf σ hσ hv a b, key a, key b]

/-- **★ THE CAPSTONE — Step 2 applies to the real object.** Start from any `IsColAut`-invariant pair
colouring (the root closure), individualize `v`, take **any** number of refinement rounds: if the
result separates the orbitals in `v`'s row, its level sets there are exactly the `K_v`-orbits, i.e.
`CellsAreOrbits` is preserved at `v`. Only `hsep` (doc §12.3) is left. -/
theorem step2_closure {β : Type*} {enc : (β × Bool × Bool) × Multiset ((β × Bool × Bool) ×
    (β × Bool × Bool)) → β × Bool × Bool} {f : Fin n → Fin n → β} {v : Fin n}
    (hf : PairInvariant adj χ f) (k : Nat)
    (hsep : ∀ u w : Fin n, iterRoundBy enc k (ext0 f v) v u = iterRoundBy enc k (ext0 f v) v w →
      SameStabOrbit adj χ v u w) (u w : Fin n) :
    iterRoundBy enc k (ext0 f v) v u = iterRoundBy enc k (ext0 f v) v w ↔
      SameStabOrbit adj χ v u w :=
  levelSet_iff_stabOrbit_of_separatesAt
    (pairInvariantAt_iterRoundBy k (pairInvariantAt_ext0 (pairInvariantAt_of_pairInvariant v hf)))
    hsep u w

/-! ## 3. The round-1 barrier (doc §12.3) -/

/-- **Coherence, in the form that states the barrier**: the colouring is a *fixpoint* of the round —
pairs of equal colour have equal triangle-type multisets. For a coherent configuration this is the
intersection-number axiom, which is exactly why "the base point learns nothing directly". -/
def Coherent {β : Type*} (f : Fin n → Fin n → β) : Prop :=
  ∀ a b a' b', f a b = f a' b' → sig f a b = sig f a' b'

/-- The universe multiset splits off the base point. -/
private theorem univ_cons (v : Fin n) :
    (Finset.univ : Finset (Fin n)).val =
      v ::ₘ (((Finset.univ : Finset (Fin n)).erase v).val) :=
  (Multiset.cons_erase (by simp)).symm

/-- The `ext0` signature along `v`'s row, split into the base point and the far points. Off `v` both
flags are determined, so the far part is a relabelling of the plain triangle types. -/
private theorem sig_ext0_row {β : Type*} (f : Fin n → Fin n → β) (v u : Fin n) (hu : u ≠ v) :
    sig (ext0 f v) v u =
      ((f v v, true, true), (f v u, true, false)) ::ₘ
        ((((Finset.univ : Finset (Fin n)).erase v).val).map
          (fun x => ((f v x, true, false), (f x u, false, false)))) := by
  unfold sig ext0
  conv_lhs => rw [univ_cons v]
  rw [Multiset.map_cons]
  congr 1
  · simp [hu]
  · refine Multiset.map_congr rfl (fun x hx => ?_)
    have hxv : x ≠ v := (Finset.mem_erase.mp (Finset.mem_val.mp hx)).1
    simp [hxv, hu]

/-- The plain signature along `v`'s row, split the same way. -/
private theorem sig_row {β : Type*} (f : Fin n → Fin n → β) (v u : Fin n) :
    sig f v u = (f v v, f v u) ::ₘ
      ((((Finset.univ : Finset (Fin n)).erase v).val).map (fun x => (f v x, f x u))) := by
  unfold sig
  conv_lhs => rw [univ_cons v]
  rw [Multiset.map_cons]

/-- **★ THE ROUND-1 BARRIER** (doc §12.3, previously prose only). At a **coherent** `X`, individualizing
`v` and taking **one** refinement round does *not* separate two pairs of `v`'s row that `X` already
identified. The base point learns nothing directly: the flags contribute the same single term to both
signatures, and the rest is an intersection number, equal by coherence.

⟹ any proof of the crux must use ≥ 2 rounds, and no purely local argument at `v` can work. -/
theorem round1_barrier {β : Type*} {f : Fin n → Fin n → β} (hf : Coherent f) {v u w : Fin n}
    (hu : u ≠ v) (hw : w ≠ v) (h : f v u = f v w) :
    sig (ext0 f v) v u = sig (ext0 f v) v w := by
  have htail : (((Finset.univ : Finset (Fin n)).erase v).val).map (fun x => (f v x, f x u)) =
      (((Finset.univ : Finset (Fin n)).erase v).val).map (fun x => (f v x, f x w)) := by
    have hs := hf v u v w h
    rw [sig_row f v u, sig_row f v w, h] at hs
    exact (Multiset.cons_inj_right (f v v, f v w)).mp hs
  rw [sig_ext0_row f v u hu, sig_ext0_row f v w hw, h]
  congr 1
  have := congrArg (Multiset.map (fun p : β × β => ((p.1, true, false), (p.2, false, false))))
    htail
  simpa [Multiset.map_map, Function.comp] using this

/-- **The marking is provably non-local.** If one round *does* separate `(v,u)` from `(v,w)` while they
share a colour, the difference lives in the intermediate points `x ≠ v` — the base point's own term is
identical on both sides. This is the theorem behind M3's measured chains, whose final witness is always
a **far** class, never one on `v`'s row. -/
theorem witness_ne_base {β : Type*} {f : Fin n → Fin n → β} {v u w : Fin n}
    (hu : u ≠ v) (hw : w ≠ v) (h : f v u = f v w)
    (hne : sig (ext0 f v) v u ≠ sig (ext0 f v) v w) :
    (((Finset.univ : Finset (Fin n)).erase v).val).map (fun x => (f v x, f x u)) ≠
      (((Finset.univ : Finset (Fin n)).erase v).val).map (fun x => (f v x, f x w)) := by
  intro htail
  refine hne ?_
  rw [sig_ext0_row f v u hu, sig_ext0_row f v w hw, h]
  congr 1
  have := congrArg (Multiset.map (fun p : β × β => ((p.1, true, false), (p.2, false, false))))
    htail
  simpa [Multiset.map_map, Function.comp] using this

end CaoRound
end ChainDescent
