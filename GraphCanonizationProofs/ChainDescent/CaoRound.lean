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

/-! ## 4. The round-2 barrier — separation cannot occur before round 3

M3 measured the separation round to be **3, uniformly** (11 fused classes, 5 objects, diameters 2–4).
This section shows that is *forced*, not a coincidence: round 1 and round 2 are **both** blind on `v`'s
row, so round 3 is the earliest that can see anything.

The mechanism, made explicit. One round of the individualized configuration gives each pair exactly its
**triangle type through the base point** — `zAug f v a b = (f a b, f a v, f v b)` — measured to be
*exactly* the round-1 partition on every object tested (`probe_cao_round2.py`, 5/5). And on `v`'s row
`zAug` degenerates: the intermediate point's relation to `v` is the *same coordinate* the row already
carries, so by the transpose axiom the whole round-2 signature is the image of the round-**0**
signature under a fixed map — and coherence makes that equal across an `X`-class. -/

/-- The **transpose axiom** of a coherent configuration: the colour of `(b,a)` is a function of the
colour of `(a,b)`. Measured to hold for every root closure in the evidence base. -/
def Transposable {β : Type*} (f : Fin n → Fin n → β) : Prop :=
  ∃ T : β → β, ∀ a b, f b a = T (f a b)

/-- The **`v`-augmented colouring**: each pair tagged with its triangle type through the base point.
This is the round-1 information of the extension, made explicit. -/
def zAug {β : Type*} (f : Fin n → Fin n → β) (v : Fin n) : Fin n → Fin n → β × β × β :=
  fun a b => (f a b, f a v, f v b)

/-- **★★ THE ROUND-2 BARRIER (core).** At a coherent, transpose-closed `X`, the `v`-augmented
colouring's signature still does not separate two pairs of `v`'s row that `X` identified.

The proof is the reason: on `v`'s row the augmentation adds *nothing independent* — the intermediate
point `x` contributes `(X v x, X v v, X v x)` and `(X x u, X x v, X v u)`, and `X x v = T (X v x)`, so
the whole signature is the image of `sig X v u` under a fixed map `Φ`. Coherence then closes it. -/
theorem sig_zAug_row_eq {β : Type*} {f : Fin n → Fin n → β} (hc : Coherent f)
    (ht : Transposable f) {v u w : Fin n} (h : f v u = f v w) :
    sig (zAug f v) v u = sig (zAug f v) v w := by
  obtain ⟨T, hT⟩ := ht
  set Φ : β × β → (β × β × β) × (β × β × β) :=
    fun p => ((p.1, f v v, p.1), (p.2, T p.1, f v u)) with hΦ
  have hu : (fun x => (zAug f v v x, zAug f v x u)) = Φ ∘ (fun x => (f v x, f x u)) := by
    funext x
    show ((f v x, f v v, f v x), (f x u, f x v, f v u)) = Φ (f v x, f x u)
    rw [hΦ]
    rw [hT v x]
  have hw : (fun x => (zAug f v v x, zAug f v x w)) = Φ ∘ (fun x => (f v x, f x w)) := by
    funext x
    show ((f v x, f v v, f v x), (f x w, f x v, f v w)) = Φ (f v x, f x w)
    rw [hΦ]
    rw [hT v x, h]
  have e1 : sig (zAug f v) v u = Multiset.map Φ (sig f v u) := by
    unfold sig; rw [Multiset.map_map, hu]
  have e2 : sig (zAug f v) v w = Multiset.map Φ (sig f v w) := by
    unfold sig; rw [Multiset.map_map, hw]
  rw [e1, e2, hc v u v w h]

/-- A colouring that factors through `zAug` has its signature the `Ψ`-image of `zAug`'s. -/
theorem sig_factor {β γ : Type*} {f : Fin n → Fin n → β} {g : Fin n → Fin n → γ} {v : Fin n}
    {Ψ : β × β × β → γ} (hg : ∀ a b, g a b = Ψ (zAug f v a b)) (a b : Fin n) :
    sig g a b = Multiset.map (fun p => (Ψ p.1, Ψ p.2)) (sig (zAug f v) a b) := by
  unfold sig
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun x _ => ?_)
  simp only [Function.comp_apply]
  rw [hg a x, hg x b]

/-- **★★ THE ROUND-2 BARRIER.** Any colouring that factors through the triangle-type-through-`v` data
— which is what one round of the individualized configuration produces — **still** fails to separate
`v`'s row. With `round1_barrier` this gives: **separation cannot occur before round 3**, exactly the
uniform depth M3 measured (11/11).

⟹ the crux (doc §12.3) is not merely non-local; it needs the *third* round, i.e. the feedback from far
pairs that have themselves been refined by a count `X` does not determine. -/
theorem round2_barrier {β γ : Type*} {f : Fin n → Fin n → β} {g : Fin n → Fin n → γ}
    {v u w : Fin n} {Ψ : β × β × β → γ} (hc : Coherent f) (ht : Transposable f)
    (hg : ∀ a b, g a b = Ψ (zAug f v a b)) (h : f v u = f v w) :
    sig g v u = sig g v w := by
  rw [sig_factor hg, sig_factor hg, sig_zAug_row_eq hc ht h]

/-! ## 5. Discharging `hg` — the round-1 colour really does factor through `zAug`

`round2_barrier` carried one hypothesis: that the colouring factors through the
triangle-type-through-`v` data. That was *measured* (5/5 objects) but not proved. It is proved here,
from the coherent-configuration axioms and nothing else.

The content is `sig_ext0_congr`: **the round-1 signature is determined by `(X a b, X a v, X v b)`**.
Splitting at the base point, the `x = v` term is `(X a v, X v b)` outright, and the far part is
`sig X a b` minus that term — coherence-determined. The two remaining CC axioms enter only to recover
the base-point *flags* from `zAug`: `a = v` iff `X a v = X v v`, which is the diagonal axiom. -/

/-- The **diagonal axiom** at `v`, in the two forms used: a point related to `v` exactly as `v` is
must *be* `v`. In a coherent configuration this is "a class meeting the diagonal lies in it". -/
def DiagSep {β : Type*} (f : Fin n → Fin n → β) (v : Fin n) : Prop :=
  (∀ a, f a v = f v v → a = v) ∧ (∀ b, f v b = f v v → b = v)

/-- The signature splits at the base point (general form of `sig_row`). -/
private theorem sig_split {β : Type*} (f : Fin n → Fin n → β) (v a b : Fin n) :
    sig f a b = (f a v, f v b) ::ₘ
      ((((Finset.univ : Finset (Fin n)).erase v).val).map (fun x => (f a x, f x b))) := by
  unfold sig
  conv_lhs => rw [univ_cons v]
  rw [Multiset.map_cons]

/-- The `ext0` signature splits the same way; off the base point both flags are determined. -/
private theorem sig_ext0_split {β : Type*} (f : Fin n → Fin n → β) (v a b : Fin n) :
    sig (ext0 f v) a b =
      ((f a v, decide (a = v), true), (f v b, true, decide (b = v))) ::ₘ
        ((((Finset.univ : Finset (Fin n)).erase v).val).map
          (fun x => ((f a x, decide (a = v), false), (f x b, false, decide (b = v))))) := by
  unfold sig ext0
  conv_lhs => rw [univ_cons v]
  rw [Multiset.map_cons]
  congr 1
  · simp
  · refine Multiset.map_congr rfl (fun x hx => ?_)
    have hxv : x ≠ v := (Finset.mem_erase.mp (Finset.mem_val.mp hx)).1
    simp [hxv]

/-- The base-point flag is recoverable from `zAug`'s second coordinate (diagonal axiom). -/
private theorem flag_left {β : Type*} {f : Fin n → Fin n → β} {v a a' : Fin n}
    (hd : DiagSep f v) (hav : f a v = f a' v) : decide (a = v) = decide (a' = v) :=
  decide_eq_decide.mpr ⟨fun h => hd.1 a' (by rw [← hav, h]), fun h => hd.1 a (by rw [hav, h])⟩

/-- The base-point flag is recoverable from `zAug`'s third coordinate (diagonal axiom). -/
private theorem flag_right {β : Type*} {f : Fin n → Fin n → β} {v b b' : Fin n}
    (hd : DiagSep f v) (hvb : f v b = f v b') : decide (b = v) = decide (b' = v) :=
  decide_eq_decide.mpr ⟨fun h => hd.2 b' (by rw [← hvb, h]), fun h => hd.2 b (by rw [hvb, h])⟩

/-- **★★ THE ROUND-1 SIGNATURE IS DETERMINED BY `zAug`.** Pairs with the same colour *and* the same
triangle type through `v` have the same round-1 signature. This is the mathematical content of `hg`. -/
theorem sig_ext0_congr {β : Type*} {f : Fin n → Fin n → β} (hc : Coherent f) {v : Fin n}
    (hd : DiagSep f v) {a b a' b' : Fin n}
    (hab : f a b = f a' b') (hav : f a v = f a' v) (hvb : f v b = f v b') :
    sig (ext0 f v) a b = sig (ext0 f v) a' b' := by
  have ha := flag_left hd hav
  have hb := flag_right hd hvb
  have htail : (((Finset.univ : Finset (Fin n)).erase v).val).map (fun x => (f a x, f x b)) =
      (((Finset.univ : Finset (Fin n)).erase v).val).map (fun x => (f a' x, f x b')) := by
    have hs := hc a b a' b' hab
    rw [sig_split f v a b, sig_split f v a' b', hav, hvb] at hs
    exact (Multiset.cons_inj_right _).mp hs
  rw [sig_ext0_split f v a b, sig_ext0_split f v a' b', hav, hvb, ha, hb]
  congr 1
  have := congrArg (Multiset.map (fun p : β × β =>
    ((p.1, decide (a' = v), false), (p.2, false, decide (b' = v))))) htail
  simpa [Multiset.map_map, Function.comp] using this

/-- The whole round-1 colour (not just its signature) is determined by `zAug`. -/
theorem roundBy_ext0_congr {β : Type*}
    {enc : (β × Bool × Bool) × Multiset ((β × Bool × Bool) × (β × Bool × Bool)) → β × Bool × Bool}
    {f : Fin n → Fin n → β} (hc : Coherent f) {v : Fin n} (hd : DiagSep f v) {a b a' b' : Fin n}
    (hz : zAug f v a b = zAug f v a' b') :
    roundBy enc (ext0 f v) a b = roundBy enc (ext0 f v) a' b' := by
  obtain ⟨hab, hav, hvb⟩ : f a b = f a' b' ∧ f a v = f a' v ∧ f v b = f v b' := by
    simpa [zAug, Prod.mk.injEq, and_assoc] using hz
  show enc (ext0 f v a b, sig (ext0 f v) a b) = enc (ext0 f v a' b', sig (ext0 f v) a' b')
  rw [sig_ext0_congr hc hd hab hav hvb]
  unfold ext0
  rw [hab, flag_left hd hav, flag_right hd hvb]

/-- **★★★ `hg` DISCHARGED.** The round-1 colour of the individualized configuration is genuinely a
function of the `v`-augmented colouring. Together with §4 this makes **`round2_barrier` unconditional
on the real object**: separation cannot occur before round 3, from the CC axioms alone. -/
theorem exists_factor_roundBy_ext0 {β : Type*} [Nonempty β]
    {enc : (β × Bool × Bool) × Multiset ((β × Bool × Bool) × (β × Bool × Bool)) → β × Bool × Bool}
    {f : Fin n → Fin n → β} (hc : Coherent f) {v : Fin n} (hd : DiagSep f v) :
    ∃ Ψ : β × β × β → β × Bool × Bool,
      ∀ a b, roundBy enc (ext0 f v) a b = Ψ (zAug f v a b) := by
  classical
  refine ⟨fun z => if h : ∃ p : Fin n × Fin n, zAug f v p.1 p.2 = z then
      roundBy enc (ext0 f v) h.choose.1 h.choose.2
    else Classical.arbitrary (β × Bool × Bool), fun a b => ?_⟩
  have hex : ∃ p : Fin n × Fin n, zAug f v p.1 p.2 = zAug f v a b := ⟨(a, b), rfl⟩
  simp only [dif_pos hex]
  exact (roundBy_ext0_congr hc hd hex.choose_spec).symm

/-- **THE ROUND-2 BARRIER, UNCONDITIONAL.** No factorization hypothesis: from the coherent-configuration
axioms alone, two rounds of the individualized configuration do not separate `v`'s row. -/
theorem round2_barrier_real {β : Type*} [Nonempty β]
    {enc : (β × Bool × Bool) × Multiset ((β × Bool × Bool) × (β × Bool × Bool)) → β × Bool × Bool}
    {f : Fin n → Fin n → β} (hc : Coherent f) (ht : Transposable f) {v u w : Fin n}
    (hd : DiagSep f v) (h : f v u = f v w) :
    sig (roundBy enc (ext0 f v)) v u = sig (roundBy enc (ext0 f v)) v w := by
  obtain ⟨Ψ, hΨ⟩ := exists_factor_roundBy_ext0 (enc := enc) hc hd
  exact round2_barrier hc ht hΨ h

/-! ## 6. The conditional converse — round 3 separates **exactly when** the counts differ

§§3–5 give a sharp *lower* bound: separation cannot occur before round 3. They cannot give the matching
upper bound, and the reason is structural — every step there shows two objects are **equal**, which is
what coherence hands you for free, whereas separation needs an **inequality**, which no
"these counts are determined" statement can produce (the dual of §4.2's *"`k`-WL computes only
structure constants"*).

What *is* provable is the converse *conditionally*, and it is the useful shape: the round-3 row colours
differ **iff** the round-2 signatures differ. Since the barriers make everything on `v`'s row agree
through round 2, the remaining content **at round 3** is one inequality between **triangle counts** —
a finite, explicit, `K_v`-invariant object.

⟹ this is the honest form of *"must separation occur at round 3?"*: **not** unconditionally, but
*exactly when* `triCount` differs. That is the statement the per-family certificate (§12.4 R2/R3)
should be pinned to.

## ⚠⚠ READ THE DIRECTION — this is a SUFFICIENT pin, not a reduction of the crux

Refinement is **monotone**, so `triCount` differing at round 3 gives: round 3 separates ⟹ the closure
separates ⟹ the crux holds on that pair. **The converse fails.** If `triCount` agrees at round 3, the
row can still separate at round 4 or later, because the round-3 colours of *far* pairs go on refining
and nothing here bounds them. So

    (∀ such u w, ∃ q, triCount ... ≠ ...)   is STRICTLY STRONGER than the crux.

Do **not** read `round3_separates_iff_triCount_ne` as "the closure is discharged" (an earlier version
of doc §0 and of this file's summary did — corrected 2026-07-31). What is discharged is everything
**up to** round 3. A family where `triCount` agrees is not a counterexample to CAO propagation; it is
a family needing a different pin.

⚠ `Function.Injective enc` is satisfiable in the abstract (a pairing encode; it computes the same
partition) but is **not** met by the rank renumbering the real refiner uses — bounded range on an
unbounded domain. Instantiating at the real object needs `Set.InjOn` over the pairs that occur, or an
enc-independence lemma (doc §12.5a R1g). -/

/-- The **triangle count**: how many intermediate points realize the triangle type `q` at `(a,b)`.
This is the object doc §12.5a's sharpened R1 is about. -/
def triCount {β : Type*} [DecidableEq β] (f : Fin n → Fin n → β) (a b : Fin n) (q : β × β) : Nat :=
  Multiset.count q (sig f a b)

theorem triCount_eq_card {β : Type*} [DecidableEq β] (f : Fin n → Fin n → β) (a b : Fin n)
    (q : β × β) :
    triCount f a b q = (Finset.univ.filter (fun x => q = (f a x, f x b))).card := by
  unfold triCount sig
  rw [Multiset.count_map]
  rfl

/-- A round cannot separate what the signature does not. (No hypothesis on `enc`.) -/
theorem roundBy_eq_of_sig_eq {β : Type*} {enc : β × Multiset (β × β) → β} {f : Fin n → Fin n → β}
    {a b a' b' : Fin n} (hcol : f a b = f a' b') (hsig : sig f a b = sig f a' b') :
    roundBy enc f a b = roundBy enc f a' b' := by
  show enc (f a b, sig f a b) = enc (f a' b', sig f a' b')
  rw [hcol, hsig]

/-- **★ THE CONDITIONAL CONVERSE.** For a faithful re-encoding, a round separates two pairs of equal
colour **exactly when** their signatures differ. -/
theorem roundBy_ne_iff_sig_ne {β : Type*} {enc : β × Multiset (β × β) → β}
    (henc : Function.Injective enc) {f : Fin n → Fin n → β} {a b a' b' : Fin n}
    (hcol : f a b = f a' b') :
    roundBy enc f a b ≠ roundBy enc f a' b' ↔ sig f a b ≠ sig f a' b' := by
  constructor
  · intro hne hsig
    exact hne (roundBy_eq_of_sig_eq hcol hsig)
  · intro hsig hne
    exact hsig (congrArg Prod.snd (henc hne))

/-- The signatures differ exactly when some **triangle type** has a different count — the concrete
inequality the crux reduces to. -/
theorem sig_ne_iff_exists_triCount_ne {β : Type*} [DecidableEq β] {f : Fin n → Fin n → β}
    {a b a' b' : Fin n} :
    sig f a b ≠ sig f a' b' ↔ ∃ q, triCount f a b q ≠ triCount f a' b' q := by
  constructor
  · intro hne
    by_contra hall
    push Not at hall
    exact hne (Multiset.ext.mpr hall)
  · rintro ⟨q, hq⟩ h
    exact hq (by unfold triCount; rw [h])

/-- Through round 2 the row colours themselves agree — the colour-level form of §§3–5. -/
theorem round2_row_colour_eq {β : Type*} [Nonempty β]
    {enc : (β × Bool × Bool) × Multiset ((β × Bool × Bool) × (β × Bool × Bool)) → β × Bool × Bool}
    {f : Fin n → Fin n → β} (hc : Coherent f) (ht : Transposable f) {v u w : Fin n}
    (hd : DiagSep f v) (hu : u ≠ v) (hw : w ≠ v) (h : f v u = f v w) :
    roundBy enc (roundBy enc (ext0 f v)) v u = roundBy enc (roundBy enc (ext0 f v)) v w := by
  refine roundBy_eq_of_sig_eq ?_ (round2_barrier_real hc ht hd h)
  refine roundBy_eq_of_sig_eq ?_ (round1_barrier hc hu hw h)
  show (f v u, decide (v = v), decide (u = v)) = (f v w, decide (v = v), decide (w = v))
  rw [h]
  simp [hu, hw]

/-- **★★★ THE CRUX'S SUFFICIENT PIN — one inequality.** Under the coherent-configuration axioms and a
faithful re-encoding, the **round-3** row colours differ **iff** some triangle type of the round-2
colouring has a different count at `(v,u)` than at `(v,w)`.

Everything **up to round 3** — the rounds, the row, the first three steps of the closure — is
discharged; what remains at round 3 is exactly that one inequality between finite explicit counts.

⚠⚠ **Direction:** `triCount` differing is **sufficient** for the crux (refinement is monotone), not
equivalent to it — round 4+ can separate a row where round 3 does not. See this section's header. -/
theorem round3_separates_iff_triCount_ne {β : Type*} [Nonempty β] [DecidableEq β]
    {enc : (β × Bool × Bool) × Multiset ((β × Bool × Bool) × (β × Bool × Bool)) → β × Bool × Bool}
    (henc : Function.Injective enc) {f : Fin n → Fin n → β} (hc : Coherent f) (ht : Transposable f)
    {v u w : Fin n} (hd : DiagSep f v) (hu : u ≠ v) (hw : w ≠ v) (h : f v u = f v w) :
    roundBy enc (roundBy enc (roundBy enc (ext0 f v))) v u ≠
        roundBy enc (roundBy enc (roundBy enc (ext0 f v))) v w ↔
      ∃ q, triCount (roundBy enc (roundBy enc (ext0 f v))) v u q ≠
        triCount (roundBy enc (roundBy enc (ext0 f v))) v w q := by
  rw [roundBy_ne_iff_sig_ne henc (round2_row_colour_eq hc ht hd hu hw h),
    sig_ne_iff_exists_triCount_ne]

end CaoRound
end ChainDescent
