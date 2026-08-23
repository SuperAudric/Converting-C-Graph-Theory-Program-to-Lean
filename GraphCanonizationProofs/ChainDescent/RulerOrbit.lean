import ChainDescent.RulerLemma
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.DeriveFintype

/-!
# Does the Ruler Lemma extend from a **discrete** ruler to a **known-orbit** ruler?

(`docs/chain-descent-cao-carrier-falsifiers.md` §6e.4d; asked 2026-08-22.)

## The question

`RulerLemma.ruler` needs a member `ω₀` that is (i) **named by its tag** and (ii) **reads the slots
injectively**. Every consumer so far supplies both from *discreteness* of one copy
(`RulerAtEnsemble.tagIsolates_of_discrete`, `rulerRefines_of_discrete`). CAO propagation, however,
starts from the **orbit partition**: a section's cells are its orbits by hypothesis, and nothing is
discrete. Does the lemma survive that weakening?

## The answer, in one line

**Discreteness is doing two different jobs, and "known orbits" replaces exactly one of them.**

| job | what it is | known orbits? |
|---|---|---|
| **(i)** the tag class of `ω₀` is its orbit | `hiso` | ✅ **free** — that is literally the CAO hypothesis at `ω₀`'s cell |
| **(ii)** the ruler's fibres refine the decoded reading | `hinj` / `ruler'`'s `href` | ⛔ **NOT implied**, and §3 below is a machine-checked counterexample |

★ Equivariance already forces the ruler's fibres to be **at least** the orbits of `Stab Γ ω₀`
(`const_on_stab`), so *"fibres = those orbits"* is the strongest form the weakening could take. §3
shows even that form is false: `Γ = Z₂`, `|X| = 4`, `|Ω| = 5`.

## Why it fails, and the shape of the repair

`Align u (b ω₀)` reveals `u` only **fibrewise**, so it pins `u` up to the *fibrewise symmetric group*
`W = ∏ Sym(fibre)`. When the ruler's fibres are its `Stab`-orbits, `W` is generally **strictly larger**
than the stabiliser's image: a symmetry that moves two orbits **together** leaves `W` free to move
them **independently**. The counterexample is exactly that gap — `g = f ∘ (01)` with `(01) ∈ W \ Γ`.

⟹ the ruler may be blind, but **only in directions the decoded member is blind in too**. §2's
`ruler_gauge` is that as a theorem: if the ruler's fibres are the orbits of a group `K` that acts on
the slots while every reading is `K`-invariant — a **gauge** of the slot set, not a symmetry of one
member — the decode goes through with no injectivity anywhere.

★ That is precisely the ensemble's situation, and it is why the discharge there was possible at all:
`RulerAtEnsemble.twin_blind` and `deg_blind` are automorphisms **moving frame vertices while fixing
every payload vertex**, i.e. a gauge in this sense — *not* automorphisms of the ruler copy.

⛔ **So the extension does not reach 2-WL CAO propagation on a general carrier.** A general carrier
has no family-wide gauge to make (ii) free, and §3 shows a member's own symmetry will not do. This is
the algebraic form of the measured fact in that doc's §6e.4f #5 (a bolt-on ruler resolves nothing) and
of §8 row 11's null control (a *matching* scaffold — independent movement inside each cell — splits
0/4, while linked scaffolds split 4/4).

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
no `native_decide`.
-/

namespace ChainDescent
namespace RulerOrbit

open ChainDescent.RulerLemma

/-! ## 1. The free direction — equivariance already coarsens the ruler to its own orbits -/

section Free

variable {Γ : Type*} [Group Γ]
variable {X : Type*} [Fintype X] {C : Type*} {Ω : Type*} [Fintype Ω]
variable [MulAction Γ X] [MulAction Γ Ω]

omit [Fintype X] [Fintype Ω] in
/-- ★ **A reading is constant on the orbits of its own stabiliser.** So for a ruler with a non-trivial
stabiliser, *"the fibres are the `Stab`-orbits"* is the **finest** the reading can possibly be — which
is what makes it the natural candidate hypothesis, and §3 the interesting refutation. -/
theorem const_on_stab {b : Ω → X → C} (hb : Equivariant Γ b) {ω₀ : Ω} {γ : Γ}
    (hγ : γ • ω₀ = ω₀) (x : X) : b ω₀ (γ • x) = b ω₀ x := by
  calc b ω₀ (γ • x) = b (γ • ω₀) (γ • x) := by rw [hγ]
    _ = b ω₀ (γ⁻¹ • γ • x) := hb γ ω₀ (γ • x)
    _ = b ω₀ x := by rw [inv_smul_smul]

end Free

/-! ## 2. ★★★ The positive form — a **gauge**, not a member's own symmetry

`K` acts on the slots and *every* reading is blind to it. Then a ruler that separates the slots only
up to `K` still decodes, because the ambiguity it leaves is ambiguity nobody in the family can see. -/

section Gauge

variable {Γ : Type*} [Group Γ] {K : Type*} [Group K]
variable {X : Type*} [Fintype X] {C : Type*} {Ω : Type*} [Fintype Ω] {Y : Type*}
variable [MulAction Γ X] [MulAction Γ Ω] [MulAction K X]

/-- `K` is a **gauge of the slot set**: every reading is constant on `K`-orbits. ⚠ Note the quantifier
— over *all* `ω`, not over the ruler alone. That is the whole content. -/
def Gauge (K : Type*) [Group K] [MulAction K X] (b : Ω → X → C) : Prop :=
  ∀ (k : K) (ω : Ω) (x : X), b ω (k • x) = b ω x

/-- The ruler separates the slots **up to the gauge**: its fibres are contained in the `K`-orbits. -/
def SeparatesModGauge (K : Type*) [Group K] [MulAction K X] (b₀ : X → C) : Prop :=
  ∀ x x' : X, b₀ x = b₀ x' → ∃ k : K, x' = k • x

/-- ### ★★★ THE RULER LEMMA WITH A BLIND RULER.
No injectivity, and no discreteness: the ruler need only separate the slots **modulo a gauge the whole
family is blind to**. `RulerLemma.ruler` is the case `K = 1`.

▶ This is the honest generalisation, and it is also the exact boundary: §3 shows that replacing the
gauge by the ruler's *own* stabiliser — the "known orbits" reading — makes the statement false. -/
theorem ruler_gauge {b : Ω → X → C} {y : Ω → Y}
    (hb : Equivariant Γ b) (ω₀ : Ω)
    (hiso : ∀ ω', y ω' = y ω₀ → ∃ γ : Γ, ω' = γ • ω₀)
    (hgauge : Gauge K b) (hsep : SeparatesModGauge K (b ω₀))
    {ω₁ ω₂ : Ω} (h : Phi b y ω₁ = Phi b y ω₂) :
    ∃ γ : Γ, ∀ x, b ω₂ x = b ω₁ (γ • x) :=
  ruler' hb ω₀ hiso
    (fun x x' hx => by
      obtain ⟨k, rfl⟩ := hsep x x' hx
      exact (hgauge k ω₂ x).symm) h

end Gauge

/-! ## 3. ⛔ THE COUNTEREXAMPLE — a known-orbit ruler is **not** enough

`Γ = S₂` acting on `X = Fin 4` by `(01)(23)` and on `Ω = Fin 5` by `(12)(34)`.

* `ω₀ = 0` is a **fixed point**, so `Stab Γ ω₀ = Γ`, whose orbits on `X` are `{0,1}` and `{2,3}`;
* its reading `(8,8,9,9)` has **exactly** those fibres — the finest an equivariant reading can be
  (§1), i.e. hypothesis (ii) holds in its strongest "known orbits" form;
* its tag is unique, so hypothesis (i) holds;
* `ω₁ = 1` reads `(0,1,2,3)` and `ω₂ = 3` reads `(1,0,2,3) = (0,1,2,3) ∘ (01)`. The transposition
  `(01)` permutes **one** fibre while fixing the other, so it is not in `Γ` — the two lie in different
  orbits — but no contingency table against `(8,8,9,9)` can see the difference.

⟹ `Φ ω₁ = Φ ω₂` with `ω₁`, `ω₂` in different `Γ`-orbits. -/

namespace Counterexample

/-- `S₂`, as a concrete two-element group. ⚠ **Not** `Equiv.Perm (Fin 2)`: its `Fintype` instance goes
through `List.Nodup.getEquivOfForallMemList`, which the kernel does not reduce, so every `decide` below
would get stuck. This one is an enum, and everything reduces. -/
inductive G2 where
  /-- the identity -/
  | e : G2
  /-- the involution -/
  | s : G2
  deriving DecidableEq, Fintype

/-- the group law -/
def G2.mul : G2 → G2 → G2
  | e, x => x
  | s, e => s
  | s, s => e

instance : Mul G2 := ⟨G2.mul⟩
instance : One G2 := ⟨G2.e⟩
instance : Inv G2 := ⟨id⟩

instance : Group G2 where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

/-- `true` exactly on the non-identity element. -/
def flip : G2 → Bool
  | .e => false
  | .s => true

/-- The slot action of the generator: `(01)(23)`. -/
def sX : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- The index action of the generator: `(12)(34)`, fixing `ω₀ = 0`. -/
def sO : Fin 5 → Fin 5 := ![0, 2, 1, 4, 3]

instance : SMul G2 (Fin 4) := ⟨fun γ x => if flip γ then sX x else x⟩
instance : SMul G2 (Fin 5) := ⟨fun γ w => if flip γ then sO w else w⟩

instance : MulAction G2 (Fin 4) where
  one_smul := by decide
  mul_smul := by decide

instance : MulAction G2 (Fin 5) where
  one_smul := by decide
  mul_smul := by decide

/-- The readings. Row `0` is the ruler; rows `1,2` and `3,4` are the two `Γ`-orbits.
⚠ Values live in `Fin 4` and the tag in `Bool` — as in `RulerLemma.Witness`, and for the same reason:
`decide` on a `Multiset` of `Nat`-valued tables does not reduce in the kernel. -/
def bC : Fin 5 → Fin 4 → Fin 4 :=
  ![![2, 2, 3, 3], ![0, 1, 2, 3], ![1, 0, 3, 2], ![1, 0, 2, 3], ![0, 1, 3, 2]]

/-- The tag: the ruler gets its own value, everybody else shares one. -/
def yC : Fin 5 → Bool := ![false, true, true, true, true]

theorem bC_equivariant : Equivariant G2 bC := by
  show ∀ (γ : G2) (ω : Fin 5) (x : Fin 4), bC (γ • ω) x = bC ω (γ⁻¹ • x)
  decide

theorem yC_invariant : Invariant G2 yC := by
  show ∀ (γ : G2) (ω : Fin 5), yC (γ • ω) = yC ω
  decide

/-- Hypothesis **(i)** holds: the tag names `ω₀`'s orbit. -/
theorem tag_isolates : ∀ w : Fin 5, yC w = yC 0 → ∃ γ : G2, w = γ • (0 : Fin 5) := by decide

/-- Hypothesis **(ii) in its "known orbits" form** holds: the ruler's fibres are **exactly** the
orbits of its own stabiliser — the finest an equivariant reading with this stabiliser can have. -/
theorem fibres_eq_stab_orbits :
    ∀ x x' : Fin 4, bC 0 x = bC 0 x' ↔ ∃ γ : G2, γ • (0 : Fin 5) = 0 ∧ x' = γ • x := by decide

/-- ⛔ And the conclusion **fails**: two members with the same observable in different orbits. -/
theorem phi_collides : Phi bC yC 1 = Phi bC yC 3 := by decide

theorem not_translate : ¬ ∃ γ : G2, ∀ x, bC 3 x = bC 1 (γ • x) := by decide

/-- ### ⛔ **THE RULER LEMMA DOES NOT EXTEND TO KNOWN-ORBIT RULERS.**
All of `ruler`'s hypotheses except injectivity hold, with (ii) weakened to *"the ruler's fibres are its
stabiliser's orbits"* — and the conclusion is false. -/
theorem no_ruler_from_known_orbits :
    Equivariant G2 bC ∧
    Invariant G2 yC ∧
    (∀ w : Fin 5, yC w = yC 0 → ∃ γ : G2, w = γ • (0 : Fin 5)) ∧
    (∀ x x' : Fin 4, bC 0 x = bC 0 x' ↔ ∃ γ : G2, γ • (0 : Fin 5) = 0 ∧ x' = γ • x) ∧
    Phi bC yC 1 = Phi bC yC 3 ∧
    ¬ ∃ γ : G2, ∀ x, bC 3 x = bC 1 (γ • x) :=
  ⟨bC_equivariant, yC_invariant, tag_isolates, fibres_eq_stab_orbits, phi_collides, not_translate⟩

/-- ★ **Exactly one hypothesis of `ruler'` fails, and this is it**: the ruler's fibre `{0,1}` is split
by the decoded member's own reading. So the counterexample is not a failure of some side condition —
it isolates `href`, the one thing *"known orbits"* does not supply. -/
theorem href_fails : ∃ x x' : Fin 4, bC 0 x = bC 0 x' ∧ bC 3 x ≠ bC 3 x' := by decide

/-- ★ And the gauge hypothesis fails for the same reason: the generator's slot action is a symmetry of
the **ruler** but not of the family — reading `1` separates the two slots the ruler's fibre merges.
⚠ This is the exact quantifier that `Gauge` gets right and *"known orbits"* gets wrong. -/
theorem not_gauge : ¬ (∀ (γ : G2) (w : Fin 5) (x : Fin 4), bC w (γ • x) = bC w x) := by decide

end Counterexample

end RulerOrbit
end ChainDescent
