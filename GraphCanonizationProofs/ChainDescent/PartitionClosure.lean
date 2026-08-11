import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Iterate

/-!
# FT1 — refinement as a closure operator on partitions (`docs/chain-descent-cao-propagation.md` §15.3)

The **spine facts**, proved once, generically in the carrier: *the partition a descent reaches depends
only on the **set** of individualization/split operations performed, never on their order or on when
they were performed.*

## Why this file exists, and why it is generic in `V`

Two consumers, one theorem:

* `V = Fin n` — 1-WL, the refiner the shipped descent runs (`Refine.refineRound`);
* `V = Fin n × Fin n` — **2-WL**, whose closure is not currently a *function* anywhere in the project
  (`CaoRound` supplies `roundBy` / `iterRoundBy` but no stabilization theorem, so "the 2-WL closure"
  cannot be written down). FT2 instantiates this file there.

★ Genericity also **dissolves R1g** (doc §12.5a): every statement here is about the induced
*partition*, so the `Function.Injective enc` hypothesis that the real refiner does not satisfy never
appears. A round is asked for two properties and nothing else.

## The content

Write `wl F c = F^[card V] c`. A **round** `F` is anything that only *splits* (`Refines (F c) c`) and
is *monotone* (`Refines c d → Refines (F c) (F d)`); §3 shows `wl F` is then a genuine closure
operator — its value is `Stable`, and it is the **coarsest** stable refinement of `c` (§4). The
headline is §5:

> **`closure_meet` (K)** — `SamePart (wl F (meet (wl F c) ρ)) (wl F (meet c ρ))`, i.e. *refining early
> changes nothing.*

Every spine fact is (K) at a different `ρ`:

| `ρ` | the fact |
|---|---|
| a partition singling out points | cells depend only on the **set** individualized, not the order (`closure_meet_comm`) |
| a two-block partition `{S, Sᶜ}` | **cell splits** — individualize a group from everything except itself |
| anything | the operation may be performed at **any** point in the descent (`closure_meet` itself) |

## ★★ It is a proof lever, not plumbing

(K) gives `closure {v,u} = closure {u,v}`, so the CAO-propagation target is a **fixed point of
transposition** — which is exactly why the doc's §4.1 coset transfer is circular (*"the `Aut_u`-orbits
on `D` are the transpose of what is being proved"*). It also makes §12.5a's **R1b** (base-point
uniformity) a theorem rather than a measurement: CAO makes the base cell a single orbit, so all base
points are conjugate. ⟹ a proof must break the symmetry with a **third** point, which is the doc's
§15.3 arity-3 reading.

⚠ **Nothing here is refiner-specific and nothing here proves CAO propagation.** This is footing.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`.
-/

namespace ChainDescent
namespace PartitionClosure

variable {V : Type*}

/-! ## 1. The refinement preorder

A colouring is a `V → Nat`; only its **kernel** is ever read, so every statement below is invariant
under re-encoding. This is what makes the file refiner-agnostic (and what dissolves R1g). -/

/-- A colouring of `V`. Only its kernel matters. -/
abbrev Col (V : Type*) := V → Nat

/-- `c` **refines** `d`: `c`'s classes are contained in `d`'s. Note the direction — the *finer*
colouring is on the left. -/
def Refines (c d : Col V) : Prop := ∀ x y : V, c x = c y → d x = d y

/-- `c` and `d` induce the same partition. -/
def SamePart (c d : Col V) : Prop := ∀ x y : V, c x = c y ↔ d x = d y

theorem Refines.refl (c : Col V) : Refines c c := fun _ _ h => h

theorem Refines.trans {c d e : Col V} (h₁ : Refines c d) (h₂ : Refines d e) : Refines c e :=
  fun x y h => h₂ x y (h₁ x y h)

theorem SamePart.refl (c : Col V) : SamePart c c := fun _ _ => Iff.rfl

theorem SamePart.symm {c d : Col V} (h : SamePart c d) : SamePart d c := fun x y => (h x y).symm

theorem SamePart.trans {c d e : Col V} (h₁ : SamePart c d) (h₂ : SamePart d e) : SamePart c e :=
  fun x y => (h₁ x y).trans (h₂ x y)

theorem samePart_iff {c d : Col V} : SamePart c d ↔ Refines c d ∧ Refines d c :=
  ⟨fun h => ⟨fun x y hx => (h x y).mp hx, fun x y hx => (h x y).mpr hx⟩,
   fun h x y => ⟨fun hx => h.1 x y hx, fun hx => h.2 x y hx⟩⟩

theorem SamePart.refines {c d : Col V} (h : SamePart c d) : Refines c d := (samePart_iff.mp h).1

/-! ## 2. Cell counts

The only quantitative input: refining cannot lose classes, and *strict* refining gains one. This is
what bounds the number of non-trivial rounds by `card V`. -/

section Finite
variable [Fintype V] [DecidableEq V]

/-- The number of colour classes of `c`. -/
def ncell (c : Col V) : Nat := (Finset.univ.image c).card

omit [DecidableEq V] in
/-- A refinement **factors**: if `c` refines `d` then `d` is a function of `c`. Choice-based, and
that is the point — no canonical factorization is needed, only its existence. -/
theorem exists_factor {c d : Col V} (h : Refines c d) : ∃ g : Nat → Nat, ∀ x : V, g (c x) = d x := by
  classical
  refine ⟨fun k => if hk : ∃ x : V, c x = k then d hk.choose else 0, fun x => ?_⟩
  have hx : ∃ y : V, c y = c x := ⟨x, rfl⟩
  show (if hk : ∃ y : V, c y = c x then d hk.choose else 0) = d x
  rw [dif_pos hx]
  exact h _ _ hx.choose_spec

omit [DecidableEq V] in
/-- The coarser colouring's image is the `g`-image of the finer one's. -/
theorem image_eq_image_of_factor {c d : Col V} {g : Nat → Nat} (hg : ∀ x : V, g (c x) = d x) :
    Finset.univ.image d = (Finset.univ.image c).image g := by
  rw [Finset.image_image]
  exact Finset.image_congr (fun x _ => (hg x).symm)

omit [DecidableEq V] in
/-- **Refining cannot lose classes.** -/
theorem ncell_le_of_refines {c d : Col V} (h : Refines c d) : ncell d ≤ ncell c := by
  obtain ⟨g, hg⟩ := exists_factor h
  rw [ncell, ncell, image_eq_image_of_factor hg]
  exact Finset.card_image_le

omit [DecidableEq V] in
/-- **★ Strict refining gains a class.** The engine behind the `card V` round bound. -/
theorem ncell_lt_of_strict {c d : Col V} (h : Refines c d) (hne : ¬ Refines d c) :
    ncell d < ncell c := by
  obtain ⟨g, hg⟩ := exists_factor h
  rcases lt_or_eq_of_le (ncell_le_of_refines h) with hlt | heq
  · exact hlt
  · exfalso
    have hinj : Set.InjOn g (Finset.univ.image c : Finset Nat) := by
      refine Finset.injOn_of_card_image_eq ?_
      rw [← image_eq_image_of_factor hg]
      exact heq
    refine hne (fun x y hxy => ?_)
    have hx : (c x) ∈ (Finset.univ.image c : Finset Nat) := Finset.mem_image_of_mem c (by simp)
    have hy : (c y) ∈ (Finset.univ.image c : Finset Nat) := Finset.mem_image_of_mem c (by simp)
    exact hinj hx hy (by rw [hg x, hg y]; exact hxy)

omit [DecidableEq V] in
/-- An empty carrier makes every colouring refine every other, vacuously. -/
theorem refines_of_ncell_eq_zero {c : Col V} (h : ncell c = 0) {d e : Col V} : Refines d e := by
  intro x _ _
  exact absurd (Finset.card_eq_zero.mp h)
    (Finset.ne_empty_of_mem (Finset.mem_image_of_mem c (Finset.mem_univ x)))

omit [DecidableEq V] in
theorem ncell_le_card (c : Col V) : ncell c ≤ Fintype.card V := by
  refine le_trans Finset.card_image_le ?_
  simp [Finset.card_univ]

/-! ## 3. Rounds, stability, and the closure

A **round** is asked for exactly two properties. Everything else — that it is determined by the
partition, that it converges, that its limit is canonical — is derived. -/

/-- A **refinement round**: it only splits, and it is monotone for the refinement order. These are the
only two facts any consumer supplies. (Partition-determinacy is a consequence — `IsRound.congr`.) -/
structure IsRound (F : Col V → Col V) : Prop where
  /-- The round never merges two classes. -/
  splits : ∀ c, Refines (F c) c
  /-- A finer input gives a finer output. -/
  mono : ∀ {c d : Col V}, Refines c d → Refines (F c) (F d)

namespace IsRound

variable {F : Col V → Col V}

omit [Fintype V] [DecidableEq V] in
/-- **A round reads only the partition.** Not a hypothesis — it follows from monotonicity. -/
theorem congr (hF : IsRound F) {c d : Col V} (h : SamePart c d) : SamePart (F c) (F d) :=
  samePart_iff.mpr ⟨hF.mono (samePart_iff.mp h).1, hF.mono (samePart_iff.mp h).2⟩

omit [Fintype V] [DecidableEq V] in
theorem iterate_splits (hF : IsRound F) : ∀ (k : Nat) (c : Col V), Refines (F^[k] c) c
  | 0, _ => Refines.refl _
  | k + 1, c => by
      rw [Function.iterate_succ_apply']
      exact Refines.trans (hF.splits _) (hF.iterate_splits k c)

omit [Fintype V] [DecidableEq V] in
theorem iterate_mono (hF : IsRound F) : ∀ (k : Nat) {c d : Col V}, Refines c d →
    Refines (F^[k] c) (F^[k] d)
  | 0, _, _, h => h
  | k + 1, c, d, h => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hF.mono (hF.iterate_mono k h)

end IsRound

/-- `c` is **stable** for `F`: the round splits nothing further. With `IsRound.splits` this is
`SamePart c (F c)`. -/
def Stable (F : Col V → Col V) (c : Col V) : Prop := Refines c (F c)

omit [Fintype V] [DecidableEq V] in
theorem samePart_of_stable {F : Col V → Col V} (hF : IsRound F) {c : Col V} (h : Stable F c) :
    SamePart c (F c) := samePart_iff.mpr ⟨h, hF.splits c⟩

omit [Fintype V] [DecidableEq V] in
/-- **Stability persists.** -/
theorem stable_round {F : Col V → Col V} (hF : IsRound F) {c : Col V} (h : Stable F c) :
    Stable F (F c) := (hF.congr (samePart_of_stable hF h)).refines

omit [Fintype V] [DecidableEq V] in
theorem stable_iterate {F : Col V → Col V} (hF : IsRound F) {c : Col V} (h : Stable F c) :
    ∀ k : Nat, Stable F (F^[k] c)
  | 0 => h
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      exact stable_round hF (stable_iterate hF h k)

omit [DecidableEq V] in
/-- Either the iterate has already stabilized, or it has gained one class per round. -/
private theorem stable_or_ncell_ge {F : Col V → Col V} (hF : IsRound F) (c : Col V) :
    ∀ k : Nat, Stable F (F^[k] c) ∨ ncell c + k ≤ ncell (F^[k] c)
  | 0 => Or.inr (by simp)
  | k + 1 => by
      rcases stable_or_ncell_ge hF c k with hst | hgrow
      · exact Or.inl (by rw [Function.iterate_succ_apply']; exact stable_round hF hst)
      · by_cases hst : Stable F (F^[k] c)
        · exact Or.inl (by rw [Function.iterate_succ_apply']; exact stable_round hF hst)
        · refine Or.inr ?_
          rw [Function.iterate_succ_apply']
          have := ncell_lt_of_strict (hF.splits (F^[k] c)) hst
          omega

omit [DecidableEq V] in
/-- **★ CONVERGENCE.** `card V` rounds always suffice — the sharp bound, from strict class growth
(not the `card V ^ 2` pair-counting bound). -/
theorem stable_iterate_card {F : Col V → Col V} (hF : IsRound F) (c : Col V) :
    Stable F (F^[Fintype.card V] c) := by
  rcases stable_or_ncell_ge hF c (Fintype.card V) with h | h
  · exact h
  · have hle := ncell_le_card (F^[Fintype.card V] c)
    have hz : ncell c = 0 := by omega
    exact refines_of_ncell_eq_zero hz

/-- **The closure** — refine to stability. `card V` rounds, matching the project's `warmRefine`. -/
def wl (F : Col V → Col V) (c : Col V) : Col V := F^[Fintype.card V] c

variable {F : Col V → Col V}

omit [DecidableEq V] in
theorem wl_refines (hF : IsRound F) (c : Col V) : Refines (wl F c) c := hF.iterate_splits _ c

omit [DecidableEq V] in
theorem wl_stable (hF : IsRound F) (c : Col V) : Stable F (wl F c) := stable_iterate_card hF c

omit [DecidableEq V] in
theorem wl_mono (hF : IsRound F) {c d : Col V} (h : Refines c d) : Refines (wl F c) (wl F d) :=
  hF.iterate_mono _ h

omit [DecidableEq V] in
theorem wl_congr (hF : IsRound F) {c d : Col V} (h : SamePart c d) : SamePart (wl F c) (wl F d) :=
  samePart_iff.mpr ⟨wl_mono hF (samePart_iff.mp h).1, wl_mono hF (samePart_iff.mp h).2⟩

/-! ## 4. ★ The coarsest stable refinement

The characterization that makes `wl` canonical — and it needs no cardinality argument at all, only
monotonicity plus stability. -/

omit [Fintype V] [DecidableEq V] in
/-- **★ `wl F c` is the COARSEST stable refinement of `c`.** Any stable `s` refining `c` refines every
iterate, hence the closure. -/
theorem refines_iterate_of_stable (hF : IsRound F) {s c : Col V} (hs : Stable F s)
    (h : Refines s c) : ∀ k : Nat, Refines s (F^[k] c)
  | 0 => h
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      exact Refines.trans hs (hF.mono (refines_iterate_of_stable hF hs h k))

omit [DecidableEq V] in
theorem refines_wl_of_stable (hF : IsRound F) {s c : Col V} (hs : Stable F s) (h : Refines s c) :
    Refines s (wl F c) := refines_iterate_of_stable hF hs h _

omit [DecidableEq V] in
/-- **Idempotence.** -/
theorem wl_idem (hF : IsRound F) (c : Col V) : SamePart (wl F (wl F c)) (wl F c) :=
  samePart_iff.mpr
    ⟨wl_refines hF _, refines_wl_of_stable hF (wl_stable hF c) (Refines.refl _)⟩

omit [DecidableEq V] in
/-- A stable colouring is its own closure. -/
theorem wl_of_stable (hF : IsRound F) {c : Col V} (hs : Stable F c) : SamePart (wl F c) c :=
  samePart_iff.mpr ⟨wl_refines hF c, refines_wl_of_stable hF hs (Refines.refl c)⟩

/-! ## 5. ★★★ Common refinement, and (K)

`ρ` is an arbitrary partition — individualizing a point, individualizing a set pointwise, splitting a
cell off from everything but itself are all *the same operation* at different `ρ`. That is why one
theorem covers all three spine facts. -/

/-- `m` is the **common refinement** of `c` and `ρ`. -/
def IsMeet (m c ρ : Col V) : Prop := ∀ x y : V, m x = m y ↔ (c x = c y ∧ ρ x = ρ y)

/-- The canonical witness. -/
def meet (c ρ : Col V) : Col V := fun x => Nat.pair (c x) (ρ x)

omit [Fintype V] [DecidableEq V] in
theorem isMeet_meet (c ρ : Col V) : IsMeet (meet c ρ) c ρ := fun _ _ => Nat.pair_eq_pair

omit [Fintype V] [DecidableEq V] in
/-- The common refinement is unique up to partition — so consumers may present it any way they like
(`indivOne`'s `2χ+1` parity trick included). -/
theorem IsMeet.samePart {m m' c ρ : Col V} (h : IsMeet m c ρ) (h' : IsMeet m' c ρ) :
    SamePart m m' := fun x y => (h x y).trans (h' x y).symm

omit [Fintype V] [DecidableEq V] in
theorem IsMeet.refines_left {m c ρ : Col V} (h : IsMeet m c ρ) : Refines m c :=
  fun x y hxy => ((h x y).mp hxy).1

omit [Fintype V] [DecidableEq V] in
theorem IsMeet.refines_right {m c ρ : Col V} (h : IsMeet m c ρ) : Refines m ρ :=
  fun x y hxy => ((h x y).mp hxy).2

omit [Fintype V] [DecidableEq V] in
/-- The meet is **commutative** at the partition level. -/
theorem IsMeet.comm {m m' c ρ : Col V} (h : IsMeet m c ρ) (h' : IsMeet m' ρ c) : SamePart m m' :=
  fun x y => (h x y).trans (and_comm.trans (h' x y).symm)

omit [Fintype V] [DecidableEq V] in
/-- Meeting a finer colouring gives a finer meet. -/
theorem IsMeet.mono {m m' c c' ρ : Col V} (h : IsMeet m c ρ) (h' : IsMeet m' c' ρ)
    (hcc : Refines c c') : Refines m m' := by
  intro x y hxy
  obtain ⟨h1, h2⟩ := (h x y).mp hxy
  exact (h' x y).mpr ⟨hcc x y h1, h2⟩

omit [DecidableEq V] in
/-- **★★★ (K) — REFINING EARLY CHANGES NOTHING.**

`wl (wl c ⊓ ρ) = wl (c ⊓ ρ)` as partitions. This is the whole of §15.3: individualization and cell
splitting may be interleaved with refinement in any way, and the reached partition is the same.

The `←` half is the substantive one: `wl F m₂` is stable and refines `c`, so by
`refines_wl_of_stable` it refines `wl F c`, hence refines `m₁`, hence refines `wl F m₁`. -/
theorem closure_meet (hF : IsRound F) {c ρ m₁ m₂ : Col V}
    (h₁ : IsMeet m₁ (wl F c) ρ) (h₂ : IsMeet m₂ c ρ) :
    SamePart (wl F m₁) (wl F m₂) := by
  have hfwd : Refines m₁ m₂ := h₁.mono h₂ (wl_refines hF c)
  -- `wl F m₂` is stable and refines both `wl F c` and `ρ`, hence refines `m₁`.
  have hstab : Stable F (wl F m₂) := wl_stable hF m₂
  have hm₂c : Refines (wl F m₂) c := Refines.trans (wl_refines hF m₂) h₂.refines_left
  have hwlc : Refines (wl F m₂) (wl F c) := refines_wl_of_stable hF hstab hm₂c
  have hρ : Refines (wl F m₂) ρ := Refines.trans (wl_refines hF m₂) h₂.refines_right
  have hback : Refines (wl F m₂) m₁ := fun x y hxy => (h₁ x y).mpr ⟨hwlc x y hxy, hρ x y hxy⟩
  exact samePart_iff.mpr
    ⟨wl_mono hF hfwd, refines_wl_of_stable hF hstab hback⟩

omit [DecidableEq V] in
/-- (K) at the canonical witness. -/
theorem closure_meet_meet (hF : IsRound F) (c ρ : Col V) :
    SamePart (wl F (meet (wl F c) ρ)) (wl F (meet c ρ)) :=
  closure_meet hF (isMeet_meet _ _) (isMeet_meet _ _)

/-! ## 6. The spine facts

All three are (K) at a different `ρ`. `ρ` is *arbitrary* — §7 supplies the concrete shapes. -/

omit [DecidableEq V] in
/-- **★★★ SPINE FACT 1 — ORDER-INDEPENDENCE.** Performing operation `ρ₁` then `ρ₂`, refining in
between, reaches the same partition as performing `ρ₂` then `ρ₁`.

With `ρᵢ` the partitions that single out points, this is *"the cells depend only on the **set** of
individualized vertices, regardless of order"*. With one of them a two-block partition it is the same
statement for a **cell split**. -/
theorem closure_meet_comm (hF : IsRound F) (c ρ₁ ρ₂ : Col V) :
    SamePart (wl F (meet (wl F (meet c ρ₁)) ρ₂)) (wl F (meet (wl F (meet c ρ₂)) ρ₁)) := by
  have e₁ : SamePart (wl F (meet (wl F (meet c ρ₁)) ρ₂)) (wl F (meet (meet c ρ₁) ρ₂)) :=
    closure_meet_meet hF (meet c ρ₁) ρ₂
  have e₂ : SamePart (wl F (meet (wl F (meet c ρ₂)) ρ₁)) (wl F (meet (meet c ρ₂) ρ₁)) :=
    closure_meet_meet hF (meet c ρ₂) ρ₁
  have hmid : SamePart (meet (meet c ρ₁) ρ₂) (meet (meet c ρ₂) ρ₁) := by
    intro x y
    simp only [meet, Nat.pair_eq_pair]
    tauto
  exact e₁.trans ((wl_congr hF hmid).trans e₂.symm)

omit [DecidableEq V] in
/-- **★★ SPINE FACT 2 — an operation may be performed at ANY time.** Doing `ρ` at the end, after `σ`
and a refinement, is the same as doing it at the start. (Immediate from `closure_meet_comm`; stated
separately because it is the form the descent consumes.) -/
theorem closure_defer (hF : IsRound F) (c ρ σ : Col V) :
    SamePart (wl F (meet (wl F (meet c σ)) ρ)) (wl F (meet (wl F (meet c ρ)) σ)) :=
  (closure_meet_comm hF c σ ρ)

omit [DecidableEq V] in
/-- **★★ SPINE FACT 3 — the whole sequence collapses to one meet.** Two intermediate refinements are
worth nothing beyond the final one. Stated at depth two; deeper cases iterate `closure_meet`. -/
theorem closure_collapse (hF : IsRound F) (c ρ₁ ρ₂ : Col V) :
    SamePart (wl F (meet (wl F (meet c ρ₁)) ρ₂)) (wl F (meet (meet c ρ₁) ρ₂)) :=
  closure_meet_meet hF (meet c ρ₁) ρ₂

/-! ## 7. The concrete operation shapes

`Discretizes ρ T` and `Splits ρ S` are the two `ρ`s the descent actually uses. They are stated as
**specifications**, not constructions, because the project already builds them in three different
encodings (`Descend.indivOne`'s `2χ+1` parity trick, `Spine.IndivStep`'s existential witness, a fresh
colour) and every one of them satisfies the same spec — §5's `IsMeet.samePart` then says they are
interchangeable.

⚠ Existence is **not** claimed generically here: a witness needs an injection `V → Nat`, which the
consumers have (`Fin n`) and the abstract carrier does not. -/

/-- `ρ` **discretizes `T`**: every element of `T` is a singleton class, and everything off `T` is one
class. This is exactly `Spine.IndivStep`'s pair of fields, at the `ρ` level. -/
def Discretizes (ρ : Col V) (T : Finset V) : Prop :=
  (∀ v ∈ T, ∀ u : V, u ≠ v → ρ u ≠ ρ v) ∧ (∀ x y : V, x ∉ T → y ∉ T → ρ x = ρ y)

/-- `ρ` **splits `S` off**: `S` is one class and its complement is one class — the "individualize a
group from everything except each other" operation. -/
def Splits (ρ : Col V) (S : Finset V) : Prop :=
  (∀ x y : V, x ∈ S → y ∈ S → ρ x = ρ y) ∧ (∀ x y : V, x ∉ S → y ∉ S → ρ x = ρ y) ∧
    (∀ x y : V, x ∈ S → y ∉ S → ρ x ≠ ρ y)

omit [Fintype V] in
/-- **The spec pins the partition.** Any two discretizers of `T` induce the same partition, so the
encoding is irrelevant — which is what lets `indivOne`, `IndivStep` and a fresh colour be used
interchangeably. -/
theorem Discretizes.samePart {ρ ρ' : Col V} {T : Finset V}
    (h : Discretizes ρ T) (h' : Discretizes ρ' T) : SamePart ρ ρ' := by
  intro x y
  by_cases hx : x ∈ T
  · by_cases hxy : x = y
    · subst hxy; exact ⟨fun _ => rfl, fun _ => rfl⟩
    · exact ⟨fun he => absurd he (h.1 x hx y (Ne.symm hxy) ∘ Eq.symm),
             fun he => absurd he (h'.1 x hx y (Ne.symm hxy) ∘ Eq.symm)⟩
  · by_cases hy : y ∈ T
    · exact ⟨fun he => absurd he.symm (h.1 y hy x (fun e => hx (e ▸ hy)) ∘ Eq.symm),
             fun he => absurd he.symm (h'.1 y hy x (fun e => hx (e ▸ hy)) ∘ Eq.symm)⟩
    · exact ⟨fun _ => h'.2 x y hx hy, fun _ => h.2 x y hx hy⟩

omit [Fintype V] in
/-- The same for a cell split. -/
theorem Splits.samePart {ρ ρ' : Col V} {S : Finset V}
    (h : Splits ρ S) (h' : Splits ρ' S) : SamePart ρ ρ' := by
  intro x y
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · exact ⟨fun _ => h'.1 x y hx hy, fun _ => h.1 x y hx hy⟩
  · exact ⟨fun he => absurd he (h.2.2 x y hx hy), fun he => absurd he (h'.2.2 x y hx hy)⟩
  · exact ⟨fun he => absurd he.symm (h.2.2 y x hy hx), fun he => absurd he.symm (h'.2.2 y x hy hx)⟩
  · exact ⟨fun _ => h'.2.1 x y hx hy, fun _ => h.2.1 x y hx hy⟩

/-- **★★★ THE CONSUMER FORM.** The reached partition depends only on the **set** `T` and the **set**
`S`, not on the order the two operations were performed in, nor on how either was encoded.

This is the statement the descent needs: *individualize `T`'s points, split `S` off, refine* — in
either order, with any refinement schedule, with any colour encoding — gives one partition. -/
theorem reached_partition_order_free (hF : IsRound F) (c : Col V) {T S : Finset V}
    {ρ ρ' : Col V} {σ σ' : Col V}
    (hρ : Discretizes ρ T) (hρ' : Discretizes ρ' T)
    (hσ : Splits σ S) (hσ' : Splits σ' S) :
    SamePart (wl F (meet (wl F (meet c ρ)) σ)) (wl F (meet (wl F (meet c σ')) ρ')) := by
  have hswap := closure_meet_comm hF c ρ σ
  have hmeet₁ : SamePart (meet c σ) (meet c σ') := by
    intro x y; simp only [meet, Nat.pair_eq_pair]
    exact and_congr Iff.rfl (hσ.samePart hσ' x y)
  have hstep : SamePart (meet (wl F (meet c σ)) ρ) (meet (wl F (meet c σ')) ρ') := by
    intro x y; simp only [meet, Nat.pair_eq_pair]
    exact and_congr (wl_congr hF hmeet₁ x y) (hρ.samePart hρ' x y)
  exact hswap.trans (wl_congr hF hstep)

end Finite

end PartitionClosure
end ChainDescent
