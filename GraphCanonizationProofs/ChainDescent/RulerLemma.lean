import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Common

/-!
# The Ruler Lemma — carrier-generic

(`docs/chain-descent-cao-carrier-falsifiers.md` §6e.4d, and §6e.4g **item 1**.)

## What this settles

The CAO carrier track is stuck on a two-way disjunction (that doc's top box):

* **(A)** the cross-copy channel of the ensemble supplies each payload vertex's `S_L`-orbit, so no
  mixed cell ever exists and Construction C dies;
* **(B)** it supplies nothing the within-copy channel cannot, the ensemble collapses to the poly-size
  encoding, and a CFI payload merges — Construction C works.

(A)'s **engine** is the argument below: an equivariant family of *readings* of a common set of slots,
compared pairwise by a contingency table, against one member that is (i) named by its own invariant
tag and (ii) reads the slots injectively. §6e.4g item 1 asks for exactly this to be machine-checked,
because it is the one part of (A) that is pure algebra — no graphs, no WL, no ensemble — and so can be
removed from dispute at low cost. **It is now checked.** ⚠ That does *not* decide the disjunction:
items 2 and 3 (the hypotheses `(LB)`, `(P1)`, `(P2)`, which are about the ensemble) remain open, and
`ruler` is useless without them.

## The statement

`Γ` acts on a finite slot set `X` and on a finite index set `Ω`. Each `ω : Ω` carries a **reading**
`b ω : X → C`, equivariantly (`b (γ • ω) = b ω ∘ γ⁻¹`), and an invariant **tag** `y ω`. The observable
is

    Φ(ω) = {{ (y ω', Align (b ω) (b ω')) : ω' ∈ Ω }},   Align u v = {{ (u x, v x) : x ∈ X }}

— a multiset of tagged contingency tables, which is the shape a coherent (2-WL-stable) colouring hands
you for free at a vertex once the fibres are pinned (that is the `⟹` chain of §6e.4d.3, whose other
arrows are bookkeeping).

**`ruler`:** if some `ω₀` has an isolating tag and an injective reading, then `Φ ω₁ = Φ ω₂` forces
`ω₂`'s reading to be a `Γ`-translate of `ω₁`'s. `phi_smul` is the converse half — `Φ` is `Γ`-invariant,
so it never over-separates. Together: **`Φ` computes the orbit exactly**, on the nose.

★ **What the proof does not need**, and this is the whole point: it never separates the members of
`Γ·ω₀` from one another, and it says nothing about any other tag class. The mixed tag classes that
make the invariant incomplete are simply never read. That is why the argument is not circular — it
consumes only a *lower* bound on the colouring, never the completeness it is trying to establish.

## ⚠ Two corrections to the doc's prose, both in the safe direction

1. The doc says `Φ` determines *the multiset* `{{ b_ω ∘ γ : γ ∈ Γ }}`. As multisets that is loose: the
   tag block enumerates `Γ·ω₀` once per **element**, whereas `{{ b_ω ∘ γ : γ }}` enumerates once per
   **group element**, so the two differ by the stabiliser multiplicity. Only the *orbit* is used
   downstream (§6e.4d.3's last arrow), and the orbit is what is proved here.
2. Hypothesis (i) is used in one direction only — *tag equal ⟹ in the orbit*. Invariance of `y` (the
   converse) is needed for `phi_smul`, not for `ruler`.

## ⚠ Non-vacuity

§7's standing filter. `Witness` below is a real instance with `Φ` **strictly finer than the tag**:
`Ω = (Fin 3 → Fin 3)` under `S₃`, tag = *"is this reading injective?"* (2 classes), orbits = value
multisets (10 classes). `witness_tag_coarser` exhibits two same-tag, different-orbit members that `Φ`
separates, so the lemma's conclusion is not obtainable from `y` alone.
⚠ It is also a **degenerate-witness check** in the sense of §7: `b` is not discrete on `Ω` (many `ω`
share no separating structure), and the isolating member `ω₀ = id` is one of `6` in its class, not a
lone fixed point.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
no `native_decide`.
-/

namespace ChainDescent
namespace RulerLemma

/-! ## 1. The observable -/

variable {Γ : Type*} [Group Γ]
variable {X : Type*} [Fintype X]
variable {C : Type*}
variable {Ω : Type*} [Fintype Ω]
variable {Y : Type*}

/-- The contingency table of two readings of the same slot set: `{{ (u x, v x) : x ∈ X }}`.
⚠ A multiset, not a function — the slot names `x` are *not* part of it. Recovering the function is
exactly what an injective `v` buys (`eq_of_align_eq`). -/
def Align (u v : X → C) : Multiset (C × C) :=
  (Finset.univ : Finset X).val.map (fun x => (u x, v x))

/-- The observable at `ω`: every other member's tag, paired with the alignment of the two readings. -/
def Phi (b : Ω → X → C) (y : Ω → Y) (ω : Ω) : Multiset (Y × Multiset (C × C)) :=
  (Finset.univ : Finset Ω).val.map (fun ω' => (y ω', Align (b ω) (b ω')))

/-- The readings are equivariant: relabelling the index relabels the slots. -/
def Equivariant (Γ : Type*) [Group Γ] [MulAction Γ X] [MulAction Γ Ω] (b : Ω → X → C) : Prop :=
  ∀ (γ : Γ) (ω : Ω) (x : X), b (γ • ω) x = b ω (γ⁻¹ • x)

/-- The tag is a `Γ`-invariant. -/
def Invariant (Γ : Type*) [Group Γ] [MulAction Γ Ω] (y : Ω → Y) : Prop :=
  ∀ (γ : Γ) (ω : Ω), y (γ • ω) = y ω

/-! ## 2. The two mechanical steps -/

/-- Translating a finite `Γ`-set permutes it, so the underlying multiset of `univ` is unchanged. -/
theorem map_univ_smul {A : Type*} [Fintype A] [MulAction Γ A] (γ : Γ) :
    (Finset.univ : Finset A).val.map (fun a => γ • a) = (Finset.univ : Finset A).val := by
  have h : (Finset.univ : Finset A).map (MulAction.toPerm γ : A ≃ A).toEmbedding = Finset.univ :=
    Finset.map_univ_equiv _
  calc (Finset.univ : Finset A).val.map (fun a => γ • a)
      = ((Finset.univ : Finset A).map (MulAction.toPerm γ : A ≃ A).toEmbedding).val := by
        rw [Finset.map_val]; rfl
    _ = (Finset.univ : Finset A).val := by rw [h]

/-- ★ **The decode.** Against an injective ruler the contingency table *is* the graph of the function:
the ruler's marks are pairwise distinct, so each pair names the slot it came from. -/
theorem eq_of_align_eq {u u' v : X → C} (hv : Function.Injective v)
    (h : Align u v = Align u' v) : u = u' := by
  funext x
  have hx : (u x, v x) ∈ Align u v :=
    Multiset.mem_map_of_mem _ ((Finset.mem_univ x))
  rw [h] at hx
  obtain ⟨x', -, hx'⟩ := Multiset.mem_map.1 hx
  have hxx : x' = x := hv (congrArg Prod.snd hx')
  subst hxx
  exact (congrArg Prod.fst hx').symm

/-- Equivariance moves a translation from the right argument of `Align` to the left. This is the step
that turns *"compare `ω` with every member of `ω₀`'s orbit"* into *"compare every translate of `ω`
with the fixed ruler `ω₀`"*. -/
theorem align_smul [MulAction Γ X] [MulAction Γ Ω] {b : Ω → X → C}
    (hb : Equivariant Γ b) (γ : Γ) (ω ω₀ : Ω) :
    Align (b ω) (b (γ • ω₀)) = Align (b (γ⁻¹ • ω)) (b ω₀) := by
  have h : ((Finset.univ : Finset X).val.map (fun x => γ⁻¹ • x)).map
        (fun x => (b (γ⁻¹ • ω) x, b ω₀ x))
      = (Finset.univ : Finset X).val.map (fun x => (b (γ⁻¹ • ω) x, b ω₀ x)) := by
    rw [map_univ_smul]
  simp only [Align]
  rw [← h, Multiset.map_map]
  refine Multiset.map_congr rfl (fun x _ => ?_)
  have h₁ : b (γ⁻¹ • ω) (γ⁻¹ • x) = b ω x := by
    rw [hb γ⁻¹ ω (γ⁻¹ • x), inv_inv, smul_inv_smul]
  have h₂ : b ω₀ (γ⁻¹ • x) = b (γ • ω₀) x := (hb γ ω₀ x).symm
  simp [Function.comp, h₁, h₂]

/-! ## 3. The Ruler Lemma -/

/-- ### ★★★ THE RULER LEMMA.
If one member `ω₀` is **named by its tag** (`hiso`: nothing outside `ω₀`'s orbit carries `ω₀`'s tag)
and **reads the slots injectively** (`hinj`), then the observable `Φ` determines the `Γ`-orbit of the
reading: equal observables force the two readings to be translates.

⚠ The hypotheses are about `ω₀` **only**. No assumption whatsoever is made about `ω₁`, `ω₂`, or about
any other tag class — in the intended application those are the CFI-like members the whole question is
about, and the argument never touches them. -/
theorem ruler [MulAction Γ X] [MulAction Γ Ω] {b : Ω → X → C} {y : Ω → Y}
    (hb : Equivariant Γ b) (ω₀ : Ω)
    (hiso : ∀ ω', y ω' = y ω₀ → ∃ γ : Γ, ω' = γ • ω₀)
    (hinj : Function.Injective (b ω₀))
    {ω₁ ω₂ : Ω} (h : Phi b y ω₁ = Phi b y ω₂) :
    ∃ γ : Γ, ∀ x, b ω₂ x = b ω₁ (γ • x) := by
  have hmem : (y ω₀, Align (b ω₂) (b ω₀)) ∈ Phi b y ω₂ :=
    Multiset.mem_map_of_mem _ ((Finset.mem_univ ω₀))
  rw [← h] at hmem
  obtain ⟨ω', -, hω'⟩ := Multiset.mem_map.1 hmem
  obtain ⟨γ, rfl⟩ := hiso ω' (congrArg Prod.fst hω')
  have halign : Align (b (γ⁻¹ • ω₁)) (b ω₀) = Align (b ω₂) (b ω₀) := by
    rw [← align_smul hb]; exact congrArg Prod.snd hω'
  have hfun : b (γ⁻¹ • ω₁) = b ω₂ := eq_of_align_eq hinj halign
  refine ⟨γ, fun x => ?_⟩
  rw [← hfun, hb γ⁻¹ ω₁ x, inv_inv]

/-- The converse half: `Φ` is itself a `Γ`-invariant, so it can never *over*-separate. With `ruler`
this makes `Φ`'s classes **exactly** the orbits of the reading. -/
theorem phi_smul [MulAction Γ X] [MulAction Γ Ω] {b : Ω → X → C} {y : Ω → Y}
    (hb : Equivariant Γ b) (hy : Invariant Γ y) (δ : Γ) (ω : Ω) :
    Phi b y (δ • ω) = Phi b y ω := by
  have h : ((Finset.univ : Finset Ω).val.map (fun ω' => δ • ω')).map
        (fun ω' => (y ω', Align (b (δ • ω)) (b ω')))
      = (Finset.univ : Finset Ω).val.map (fun ω' => (y ω', Align (b (δ • ω)) (b ω'))) := by
    rw [map_univ_smul]
  rw [Phi, ← h, Multiset.map_map]
  refine Multiset.map_congr rfl (fun ω' _ => ?_)
  have hA : Align (b (δ • ω)) (b (δ • ω')) = Align (b ω) (b ω') := by
    rw [align_smul hb, inv_smul_smul]
  simp [Function.comp, hy δ ω', hA]

/-- ▶ The two halves as one statement, at the level the doc's §6e.4d.3 chain consumes it:
**`Φ` is a complete invariant of the reading's orbit.** -/
theorem phi_eq_iff_orbit [MulAction Γ X] [MulAction Γ Ω] {b : Ω → X → C} {y : Ω → Y}
    (hb : Equivariant Γ b) (hy : Invariant Γ y) (ω₀ : Ω)
    (hiso : ∀ ω', y ω' = y ω₀ → ∃ γ : Γ, ω' = γ • ω₀)
    (hinj : Function.Injective (b ω₀)) (ω₁ ω₂ : Ω) :
    Phi b y ω₁ = Phi b y ω₂ ↔ ∃ γ : Γ, ∀ x, b ω₂ x = b ω₁ (γ • x) := by
  refine ⟨ruler hb ω₀ hiso hinj, ?_⟩
  rintro ⟨γ, hγ⟩
  have hb₂ : b ω₂ = b (γ⁻¹ • ω₁) := by
    funext x; rw [hb γ⁻¹ ω₁ x, inv_inv]; exact hγ x
  -- `Φ` depends on `ω` only through `b ω`.
  have hdep : ∀ ω ω' : Ω, b ω = b ω' → Phi b y ω = Phi b y ω' := by
    intro ω ω' hbb; simp [Phi, hbb]
  rw [hdep ω₂ (γ⁻¹ • ω₁) hb₂, phi_smul hb hy]

/-! ## 4. ⚠ Non-vacuity — the tag is strictly coarser than `Φ`

`Ω = (Fin 3 → Fin 3)` with `S₃` permuting the slots. The tag records only *"is this reading
injective?"*, so it has **two** classes while the orbits (= value multisets) number **ten**. `ω₀ = id`
is isolated by its tag and reads injectively, so `ruler` applies; `witness_tag_coarser` then shows the
conclusion genuinely exceeds what the tag alone gives. -/

namespace Witness

abbrev Sl := Equiv.Perm (Fin 3)

/-- A reading of the three slots. ⚠ **Wrapped in a structure on purpose**: on the bare function type
`Pi.instSMul` already supplies an `S₃`-action — the one permuting the *values* — and that is not the
slot action this lemma is about. -/
structure Rd where
  /-- the reading itself -/
  rd : Fin 3 → Fin 3
  deriving DecidableEq

instance : Fintype Rd :=
  Fintype.ofEquiv (Fin 3 → Fin 3) ⟨Rd.mk, Rd.rd, fun _ => rfl, fun _ => rfl⟩

theorem rd_ext {f g : Rd} (h : f.rd = g.rd) : f = g := by
  cases f; cases g; simpa only [Rd.mk.injEq] using h

instance : SMul Sl Rd := ⟨fun γ f => ⟨fun x => f.rd (γ⁻¹ x)⟩⟩

@[simp] theorem smul_rd (γ : Sl) (f : Rd) (x : Fin 3) : (γ • f).rd x = f.rd (γ⁻¹ x) := rfl

instance : MulAction Sl Rd where
  one_smul f := rd_ext (funext fun x => by simp)
  mul_smul γ δ f := rd_ext (funext fun x => by simp [mul_inv_rev])

/-- Kept as a lemma so no `Equiv.Perm.inv_apply_self`-style name is needed anywhere below. -/
theorem inv_app (γ : Sl) (x : Fin 3) : γ⁻¹ (γ x) = x := by simp

/-- The reading of `f` is `f` itself. -/
def bw : Rd → Fin 3 → Fin 3 := Rd.rd

/-- The tag: *"is this reading injective?"* — two classes. -/
def yw (f : Rd) : Bool := decide (Function.Injective f.rd)

/-- The ruler: the identity reading. -/
def rul : Rd := ⟨id⟩

theorem bw_equivariant : Equivariant Sl bw := fun _ _ _ => rfl

theorem yw_invariant : Invariant Sl yw := by
  intro γ f
  show decide (Function.Injective fun x => f.rd (γ⁻¹ x)) = decide (Function.Injective f.rd)
  refine decide_eq_decide.2 ⟨fun h a c hac => ?_, fun h a c hac => ?_⟩
  · exact γ.injective (@h (γ a) (γ c) (by simpa only [inv_app] using hac))
  · exact (γ⁻¹).injective (h hac)

theorem yw_isolates : ∀ f : Rd, yw f = yw rul → ∃ γ : Sl, f = γ • rul := by
  intro f hf
  have hinj : Function.Injective f.rd := by
    have h1 : yw rul = true := by simp [yw, rul, Function.injective_id]
    have h2 : yw f = true := hf.trans h1
    simpa only [yw, decide_eq_true_eq] using h2
  have hbij := Finite.injective_iff_bijective.1 hinj
  refine ⟨(Equiv.ofBijective f.rd hbij)⁻¹, rd_ext (funext fun x => ?_)⟩
  show f.rd x = rul.rd (((Equiv.ofBijective f.rd hbij)⁻¹)⁻¹ x)
  rw [inv_inv]
  rfl

theorem bw_rul_injective : Function.Injective (bw rul) := Function.injective_id

/-- ★ `ruler` applies to this instance, with no hypothesis on `f` or `g`. -/
theorem witness_ruler {f g : Rd} (h : Phi bw yw f = Phi bw yw g) :
    ∃ γ : Sl, ∀ x, g.rd x = f.rd (γ • x) :=
  ruler bw_equivariant rul yw_isolates bw_rul_injective h

/-- reading `(0,0,1)` -/
def r001 : Rd := ⟨fun x => if x = 2 then 1 else 0⟩
/-- reading `(0,1,1)` -/
def r011 : Rd := ⟨fun x => if x = 0 then 0 else 1⟩

/-- ⚠ **`Φ` is strictly finer than the tag.** `(0,0,1)` and `(0,1,1)` are both non-injective — same
tag — but lie in different `S₃`-orbits, and `Φ` separates them. So the orbit information in `ruler`'s
conclusion is genuinely not already present in `y`, and the lemma is not vacuous here. -/
theorem witness_tag_coarser :
    yw r001 = yw r011 ∧ Phi bw yw r001 ≠ Phi bw yw r011 := by
  refine ⟨by decide, by decide⟩

end Witness

end RulerLemma
end ChainDescent
