import ChainDescent.RulerOrbit
import ChainDescent.CaoTarget

/-!
# Can the Ruler Lemma be reworked to drive **2-WL CAO propagation**?

(`docs/chain-descent-cao-carrier-falsifiers.md` §6e.4d; `docs/chain-descent-cao-propagation.md` §12.3.
Asked 2026-08-23, as the follow-up to `RulerOrbit`.)

## The question, and the answer

`RulerOrbit` settled the *narrow* form: a **known-orbit** ruler gives hypothesis **(i)** (`hiso`, the tag
names the ruler's orbit — that is literally the CAO hypothesis) for free, but **not (ii)** (`ruler'`'s
`href`, the decode), and the only proved repair is a **family-wide gauge**, which a general carrier
does not have. This file asks the wider question the user posed: *does a **larger logical rework** of
the lemma reach CAO propagation, using the equal-orbit copies CAO supplies in place of the ensemble's
discrete ruler?*

**Yes to the rework; no to the target.** Three results, all machine-checked here:

| | |
|---|---|
| ★★★ **§3 the rework** | `ruler_diag` — `href` is replaced by **`Isolates`** (*the ruler's row singles out the one member being decoded*), which is **strictly weaker** (§2, §6), and the conclusion is upgraded from *"the readings are translates"* to **`γ • ω₁ = ω₂`, an equation between members**. |
| ⛔ **§4 seed starvation** | `singleton_transports_to_singleton` — resolution transports **only along thin classes**, and a thin class out of a **singleton** cell lands in a singleton cell. The only free seeds are singletons ⟹ the calculus never leaves them. |
| ⛔ **§5 the arity-3 escape is worse** | `ruler_pair` — reading against **two** rulers jointly does break the valency-1 threshold, but (a) its observable `Phi₂` is a **triple count**, not 2-WL-available, and (b) its `hiso₂` is *"the pair class is an orbital"* = **schurity**, which is measurably **false** at CAO nodes (Shrikhande: 3 classes vs 4 orbits). |

⟹ the rework is real and strictly stronger than `ruler'`, and it still does not reach
`CaoTarget.Separates`. What kills it is **not** the decode being unavailable — §3 makes the decode
almost free — but that the only thing it can *transport* is resolution already held by a cell of at
least the same size, and CAO hands out no non-singleton seed at the extension.

## What changes when the slots **are** the members

Every earlier consumer of `RulerLemma` has `X ≠ Ω`: payload indices read *frame* slots. The CAO
setting is the degenerate one — a vertex reads the vertex set, `X = Ω = V`, `b u x = X_v(u, x)` — and
that single identification does all the work here, through one hypothesis:

**`DiagClosed`** — *a pair coloured like a diagonal pair **is** diagonal*. It is the coherent-
configuration axiom "a class meeting the diagonal lies in it" (`CaoRound.DiagSep`'s content), and §7
shows it is **free at the real object**: any colouring refining `CaoTarget.initCol2` has it, which
includes `ext (rootPair adj) v`. Three consequences, in increasing order of importance:

* ⛔ **the gauge repair dies here** — `gauge_trivial`: a gauge of a `DiagClosed` family is the trivial
  group, so `RulerOrbit.ruler_gauge` collapses back to *"the ruler's row is injective"*
  (`injective_of_separatesModGauge`). The one proved escape from discreteness is unavailable.
* ✅ **the 4b3 gap closes for free** — the ensemble's open input *"the reading determines the vertex"*
  is `DiagClosed` here, so §3 concludes an equation between **members**, not between readings.
* ★ **the decode is exactly a valency-1 condition** — `isolates_of_refines` shows `href` **implies**
  `Isolates`, and §6's `Counterexample` shows the threshold is sharp: at valency 2 the conclusion is
  false. ⚠ This is the theorem-form of the 2026-08-22b measurement (*112 carriers, 0 sections with
  `href` and a non-discrete row*): `href` against every member forces the row to be **injective**
  (`injective_of_isolates_all`), i.e. discreteness, and nothing weaker survives except per-member
  thinness.

## ⚠ Scope

§1–§6 are carrier-generic algebra, as `RulerLemma` is. §7 anchors the running hypothesis at the real
object; the **positive** theorem §3 additionally needs *"the tag determines `Phi`"* (coherence — the
`Coherence.phi_determined` of this setting), which is carried as an explicit hypothesis `hφ` and is
**not** discharged here. The **negative** results §4/§5/§6 do not use it, so no wiring can rescue
them. ⛔ Do not quote this file as *"CAO propagation is refuted"* — it refutes **this route**, and the
target `CaoTarget.Separates` remains open, as `project_cao_2wl_footing_2026-08-11` records.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
no `native_decide`.
-/

namespace ChainDescent
namespace RulerCao

open ChainDescent.RulerLemma

/-! ## 1. The setting: the slots **are** the members -/

section Setting

variable {V : Type*} [Fintype V] {C : Type*}

/-- ★ **The diagonal axiom.** *A pair whose colour is some diagonal colour is itself diagonal.* In a
coherent configuration this is "a class meeting the diagonal lies in it"; §7 shows it is free at the
real object. It is the whole difference between this file and `RulerOrbit`. -/
def DiagClosed (b : V → V → C) : Prop := ∀ a x z : V, b a x = b z z → a = x

/-- ★ **The reworked decode hypothesis**: the ruler's row **singles out** the member being decoded.
⚠ Note what it is *not*: it says nothing about the rest of the row, whereas `ruler'`'s `href` asks the
ruler to refine the decoded member's whole reading. §2 proves `href ⟹ Isolates`, §6 that the converse
fails. -/
def Isolates (b₀ : V → C) (u : V) : Prop := ∀ x : V, b₀ x = b₀ u → x = u

omit [Fintype V] in
/-- Every member's own row isolates it. ⚠ **This is why the lemma has no content at `ω₀ = ω₂`**: the
decode is free there, and `hiso` then *is* the conclusion. All the content is in transporting `hiso`
from a **different** member. -/
theorem isolates_self {b : V → V → C} (hd : DiagClosed b) (u : V) : Isolates (b u) u :=
  fun x h => (hd u x u h).symm

/-! ## 2. ⚠ `href` collapses — it is discreteness in disguise -/

omit [Fintype V] in
/-- ★ **`ruler'`'s decode hypothesis implies the new one.** So §3 is a genuine weakening, not a
sideways move. -/
theorem isolates_of_refines {b : V → V → C} (hd : DiagClosed b) {ω₀ ω₂ : V}
    (href : ∀ x x' : V, b ω₀ x = b ω₀ x' → b ω₂ x = b ω₂ x') : Isolates (b ω₀) ω₂ :=
  fun x h => (hd ω₂ x ω₂ (href x ω₂ h)).symm

omit [Fintype V] in
/-- ⛔ **The theorem behind the 0/112 measurement.** Asking the ruler to isolate *every* member — which
is what decoding a whole configuration with one ruler needs — **is** asking its row to be injective,
i.e. asking individualization at `ω₀` to discretize. There is no intermediate regime. -/
theorem injective_of_isolates_all {b₀ : V → C} (h : ∀ u : V, Isolates b₀ u) :
    Function.Injective b₀ := fun x x' hx => h x' x hx

omit [Fintype V] in
theorem isolates_all_of_injective {b₀ : V → C} (h : Function.Injective b₀) (u : V) :
    Isolates b₀ u := fun _ hx => h hx

/-! ### ⛔ …and the gauge escape is unavailable here

`RulerOrbit.ruler_gauge` is the one proved way to keep the decode without discreteness: the ruler may
be blind in directions **the whole family** is blind in. On a `DiagClosed` family there are no such
directions. -/

variable {K : Type*} [Group K] [MulAction K V]

omit [Fintype V] in
/-- ★★ **A gauge of a `DiagClosed` family is trivial.** Every member's own diagonal pins every slot. -/
theorem gauge_trivial {b : V → V → C} (hd : DiagClosed b) (hg : RulerOrbit.Gauge K b)
    (k : K) (x : V) : k • x = x := (hd x (k • x) x (hg k x x)).symm

omit [Fintype V] in
/-- ⛔ **So `ruler_gauge` collapses to `ruler`.** Separating the slots modulo a gauge *is* separating
them, and the file's headline weakening cannot come from that direction. -/
theorem injective_of_separatesModGauge {b : V → V → C} {ω₀ : V} (hd : DiagClosed b)
    (hg : RulerOrbit.Gauge K b) (hsep : RulerOrbit.SeparatesModGauge K (b ω₀)) :
    Function.Injective (b ω₀) := by
  intro x x' hx
  obtain ⟨k, rfl⟩ := hsep x x' hx
  exact (gauge_trivial hd hg k x).symm

end Setting

/-! ## 3. ★★★ THE REWORK — decode a **member**, not a reading -/

section Rework

variable {Γ : Type*} [Group Γ] {V : Type*} [Fintype V] [MulAction Γ V] {C : Type*} {Y : Type*}

/-- The cell of `u` is a single `Γ`-orbit — `RulerLemma.ruler`'s `hiso`, named. At the root of a CAO
node this holds at **every** `u` by hypothesis; at the one-point extension it is exactly what
`CaoTarget.Separates` asserts, which is why transporting it is the whole game. -/
def CellIsOrbit (Γ : Type*) [Group Γ] [MulAction Γ V] (y : V → Y) (u : V) : Prop :=
  ∀ u' : V, y u' = y u → ∃ γ : Γ, u' = γ • u

/-- ### ★★★ THE RULER LEMMA, REWORKED FOR `X = Ω`.
`RulerLemma.ruler'` with two changes, both forced by `DiagClosed` and both improvements:

* the decode hypothesis drops from `href` (*"the ruler refines the decoded reading"*) to **`Isolates`**
  (*"the ruler's row singles the decoded member out"*) — strictly weaker by §2 and §6;
* the conclusion rises from *"the readings are `Γ`-translates"* to **`γ • ω₁ = ω₂`** — the ensemble's
  open input 4b3 (*"the reading determines the vertex"*) is free here.

⚠ As in `ruler`, nothing whatsoever is assumed about `ω₁` or `ω₂` beyond the single isolation fact. -/
theorem ruler_diag {b : V → V → C} {y : V → Y}
    (hb : Equivariant Γ b) (hd : DiagClosed b) {ω₀ : V}
    (hiso : CellIsOrbit Γ y ω₀) {ω₁ ω₂ : V} (hIso : Isolates (b ω₀) ω₂)
    (h : Phi b y ω₁ = Phi b y ω₂) :
    ∃ γ : Γ, γ • ω₁ = ω₂ := by
  have hmem : (y ω₀, Align (b ω₂) (b ω₀)) ∈ Phi b y ω₂ :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ ω₀)
  rw [← h] at hmem
  obtain ⟨ω', -, hω'⟩ := Multiset.mem_map.1 hmem
  obtain ⟨γ, rfl⟩ := hiso ω' (congrArg Prod.fst hω')
  have halign : Align (b (γ⁻¹ • ω₁)) (b ω₀) = Align (b ω₂) (b ω₀) := by
    rw [← align_smul hb]; exact congrArg Prod.snd hω'
  -- The decode, at one slot only: read the entry of the table that sits over `ω₂`'s own diagonal.
  have hx : (b ω₂ ω₂, b ω₀ ω₂) ∈ Align (b ω₂) (b ω₀) :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ ω₂)
  rw [← halign] at hx
  obtain ⟨x, -, hx'⟩ := Multiset.mem_map.1 hx
  have hxx : x = ω₂ := hIso x (congrArg Prod.snd hx')
  subst hxx
  exact ⟨γ⁻¹, hd _ _ _ (congrArg Prod.fst hx')⟩

/-- ▶ **The rule, in the form a propagation calculus would use.** *Resolution transports along a thin
class*: if `ω₀`'s cell is a single orbit and `ω₀`'s row singles out `ω₂`, then `ω₂`'s **whole** cell is
a single orbit.

`hφ` is *"the tag determines `Phi`"* — coherence, i.e. this setting's `Coherence.phi_determined`. It is
carried, not discharged (see the header's scope note). -/
theorem cellIsOrbit_transport {b : V → V → C} {y : V → Y}
    (hb : Equivariant Γ b) (hd : DiagClosed b)
    (hφ : ∀ u u' : V, y u = y u' → Phi b y u = Phi b y u')
    {ω₀ ω₂ : V} (hiso : CellIsOrbit Γ y ω₀) (hIso : Isolates (b ω₀) ω₂) :
    CellIsOrbit Γ y ω₂ := by
  intro u' hu'
  obtain ⟨γ, hγ⟩ := ruler_diag hb hd hiso hIso (hφ u' ω₂ hu')
  exact ⟨γ⁻¹, by rw [← hγ, inv_smul_smul]⟩

/-! ## 4. ⛔ SEED STARVATION — the rework cannot bootstrap

The rule of §3 moves resolution from `ω₀`'s cell to `ω₂`'s cell **along a thin class**, and a thin
class is a contraction: from a cell of size `k` it can only reach cells of size `≤ k`
(`cell_card_le`). The only cells a one-point extension hands over as *known* orbits are the
**singletons** (`{v}` itself), and `singleton_transports_to_singleton` is the `k = 1` case. So the
calculus, seeded with everything CAO actually gives at the extension, produces nothing but the
singleton cells it started with.

★ **This is also the answer to *"how small can the ruler be?"*** — two independent bounds, and both
say *small rulers are the useless ones*:

| | |
|---|---|
| `isolated_card_le` | a ruler whose row shows `k` distinct **marks** isolates at most `k` members. A "length-2 ruler on a 16-vertex carrier" decodes at most two of them. |
| `cell_card_le` | ★★ a ruler resolves **no cell larger than its own**. |

⚠ And in this setting the ruler's row `b ω₀ = X_v(ω₀, ·)` **is** a 2-WL pair colour, and `Φ` is
determined by the tag (`hφ`), so the ruler contributes **no separation at all** — it is a converter
from *"same colour"* to *"same orbit"*, never a source of colour. That is why a short ruler "resembles
the pairwise path calculations 2-WL already applies": it does not resemble them, it **is** them.
⚠⚠ A ruler *attached* to the carrier as a gadget is a different object — there `X ≠ Ω` and the bounds
below do not apply; see the doc's §6e.4f rows 9/11. -/

omit [Fintype V] in
/-- The stabiliser of the ruler fixes everything the ruler's row isolates. -/
theorem stab_fixes_isolated {b : V → V → C} (hb : Equivariant Γ b) {ω₀ ω₂ : V}
    (hIso : Isolates (b ω₀) ω₂) {γ : Γ} (hγ : γ • ω₀ = ω₀) : γ • ω₂ = ω₂ :=
  hIso _ (RulerOrbit.const_on_stab hb hγ ω₂)

/-- ### ⛔ **THE OBSTRUCTION.** A **singleton** cell transports only to a **singleton** cell.

⟹ starting from the individualized point — the one cell of `ext c v` that is free — §3's rule never
resolves a cell that was not already trivial, and `CaoTarget.Separates` is untouched. -/
theorem singleton_transports_to_singleton {b : V → V → C} {y : V → Y}
    (hb : Equivariant Γ b) (hd : DiagClosed b) (hy : Invariant Γ y)
    (hφ : ∀ u u' : V, y u = y u' → Phi b y u = Phi b y u')
    {ω₀ ω₂ : V} (hsing : ∀ u : V, y u = y ω₀ → u = ω₀) (hIso : Isolates (b ω₀) ω₂) :
    ∀ u : V, y u = y ω₂ → u = ω₂ := by
  intro u hu
  obtain ⟨γ, hγ⟩ := ruler_diag hb hd (fun u' h => ⟨1, by rw [one_smul]; exact hsing u' h⟩) hIso
    (hφ u ω₂ hu)
  have hfix : γ • ω₀ = ω₀ := hsing _ (hy γ ω₀)
  have hinv : γ⁻¹ • ω₀ = ω₀ := by
    conv_lhs => rw [← hfix]
    rw [inv_smul_smul]
  calc u = γ⁻¹ • γ • u := (inv_smul_smul γ u).symm
    _ = γ⁻¹ • ω₂ := by rw [hγ]
    _ = ω₂ := stab_fixes_isolated hb hIso hinv

/-! ### ★ How small can a ruler be? Two bounds -/

omit [MulAction Γ V] in
open scoped Classical in
/-- ★ **A `k`-mark ruler isolates at most `k` members.** The isolated members inject into the row's
image, so a ruler that shows few distinct colours decodes correspondingly few members — whatever else
it does. (`Isolates` is *necessary* for §3's decode by `isolates_of_refines`, so this bounds the
rework's reach directly.) -/
theorem isolated_card_le (b₀ : V → C) :
    (Finset.univ.filter (fun u : V => Isolates b₀ u)).card ≤ (Finset.univ.image b₀).card :=
  Finset.card_le_card_of_injOn b₀ (fun u _ => Finset.mem_image_of_mem _ (Finset.mem_univ u))
    (fun _ hu _ _ h => ((Finset.mem_filter.mp hu).2 _ h.symm).symm)

variable [DecidableEq Y]

/-- The cell of `u` — the tag class, as a `Finset`. -/
def cell (y : V → Y) (u : V) : Finset V := Finset.univ.filter (fun z => y z = y u)

theorem mem_cell {y : V → Y} {u z : V} : z ∈ cell y u ↔ y z = y u := by
  simp [cell]

/-- ### ★★ **A RULER RESOLVES NO CELL LARGER THAN ITS OWN.**
The thin class out of `ω₀` is a **contraction**: `ω₀`'s cell surjects onto `ω₂`'s.

⟹ this is the quantitative form of §4's obstruction, and the honest answer to *"how small can the
ruler be?"* — a small ruler cell resolves only small cells, and the free seeds (singletons) are the
smallest there are. `singleton_transports_to_singleton` is the case `card = 1`. -/
theorem cell_card_le {b : V → V → C} {y : V → Y}
    (hb : Equivariant Γ b) (hd : DiagClosed b) (hy : Invariant Γ y)
    (hφ : ∀ u u' : V, y u = y u' → Phi b y u = Phi b y u')
    {ω₀ ω₂ : V} (hiso : CellIsOrbit Γ y ω₀) (hIso : Isolates (b ω₀) ω₂) :
    (cell y ω₂).card ≤ (cell y ω₀).card := by
  classical
  -- the transport map: `γ • ω₀ ↦ γ • ω₂`, well defined because `Stab ω₀` fixes `ω₂`
  set f : V → V := fun a =>
    if h : ∃ γ : Γ, a = γ • ω₀ then (Classical.choose h) • ω₂ else ω₂ with hf
  -- ★ well-definedness: any two group elements carrying `ω₀` to the same place agree on `ω₂`
  have key : ∀ (δ γ : Γ), δ • ω₀ = γ • ω₀ → γ • ω₂ = δ • ω₂ := by
    intro δ γ hγ
    have hstab : (γ⁻¹ * δ) • ω₀ = ω₀ := by rw [mul_smul, hγ, inv_smul_smul]
    have h2 : γ⁻¹ • δ • ω₂ = ω₂ := by
      rw [← mul_smul]; exact stab_fixes_isolated hb hIso hstab
    calc γ • ω₂ = γ • (γ⁻¹ • δ • ω₂) := by rw [h2]
      _ = δ • ω₂ := smul_inv_smul γ _
  have hsub : cell y ω₂ ⊆ (cell y ω₀).image f := by
    intro u hu
    obtain ⟨δ, rfl⟩ := cellIsOrbit_transport hb hd hφ hiso hIso u (mem_cell.mp hu)
    refine Finset.mem_image.mpr ⟨δ • ω₀, mem_cell.mpr (hy δ ω₀), ?_⟩
    have hex : ∃ γ : Γ, δ • ω₀ = γ • ω₀ := ⟨δ, rfl⟩
    rw [hf]
    simp only [dif_pos hex]
    exact key δ _ (Classical.choose_spec hex)
  calc (cell y ω₂).card ≤ ((cell y ω₀).image f).card := Finset.card_le_card hsub
    _ ≤ (cell y ω₀).card := Finset.card_image_le

end Rework

/-! ## 5. ⛔ THE ARITY-3 ESCAPE, AND WHY IT IS WORSE

The threshold of §3/§6 is *"one ruler pins the member"*. The obvious rework is to let **several**
rulers read the slots **jointly**: two rulers can pin a member neither pins alone. That rework is
sound — `ruler_pair` below — and it is the wrong door twice over:

1. its observable `Phi₂` is a multiset of **triples**, i.e. a triple count. 2-WL supplies `Align`
   (`CaoTarget.pairSig`) and nothing of arity 3. ⟹ this is the *same* arity-3 wall the landed
   barriers already pin (`CaoRound.round3_separates_iff_triCount_ne`), reached from a new direction;
2. worse, its `hiso₂` is *"the pair class of `(ω₀, ω₀')` is a `Γ`-orbital"* — **schurity**, not CAO.
   That is measurably false at CAO nodes (Shrikhande: 3 pair classes, 4 orbitals; the 22 S-failures),
   so the hypothesis is not merely unavailable, it is **wrong**.

⟹ ⛔ the multi-ruler rework is dead on a named counterexample, not open. -/

section Pair

variable {Γ : Type*} [Group Γ] {V : Type*} [Fintype V] [MulAction Γ V] {C : Type*} {Y : Type*}

/-- The three-way contingency table — the joint reading of the slots by a member and two rulers.
⚠ **A triple count**: this is what 2-WL does not have. -/
def Align₂ (u v w : V → C) : Multiset (C × C × C) :=
  (Finset.univ : Finset V).val.map (fun x => (u x, v x, w x))

/-- The observable of the two-ruler rework: every **ordered pair** of members, tagged by its pair
class, with the joint table. -/
def Phi₂ (b : V → V → C) (y₂ : V × V → Y) (u : V) : Multiset (Y × Multiset (C × C × C)) :=
  (Finset.univ : Finset (V × V)).val.map (fun q => (y₂ q, Align₂ (b u) (b q.1) (b q.2)))

/-- **Joint** isolation: the two rulers together single `u` out, though neither need do so alone. -/
def IsolatesPair (b₀ b₁ : V → C) (u : V) : Prop :=
  ∀ x : V, b₀ x = b₀ u → b₁ x = b₁ u → x = u

/-- `align_smul` for the joint table. -/
theorem align₂_smul {b : V → V → C} (hb : Equivariant Γ b) (γ : Γ) (u ω₀ ω₀' : V) :
    Align₂ (b u) (b (γ • ω₀)) (b (γ • ω₀')) = Align₂ (b (γ⁻¹ • u)) (b ω₀) (b ω₀') := by
  have h : ((Finset.univ : Finset V).val.map (fun x => γ⁻¹ • x)).map
        (fun x => (b (γ⁻¹ • u) x, b ω₀ x, b ω₀' x))
      = (Finset.univ : Finset V).val.map (fun x => (b (γ⁻¹ • u) x, b ω₀ x, b ω₀' x)) := by
    rw [map_univ_smul]
  simp only [Align₂]
  rw [← h, Multiset.map_map]
  refine Multiset.map_congr rfl (fun x _ => ?_)
  have h₁ : b (γ⁻¹ • u) (γ⁻¹ • x) = b u x := by
    rw [hb γ⁻¹ u (γ⁻¹ • x), inv_inv, smul_inv_smul]
  have h₂ : ∀ z : V, b z (γ⁻¹ • x) = b (γ • z) x := fun z => (hb γ z x).symm
  simp [Function.comp, h₁, h₂]

/-- ### THE TWO-RULER REWORK.
Sound, and useless twice: `Phi₂` is a triple count (not 2-WL), and `hiso₂` is **schurity** at the pair
class of `(ω₀, ω₀')`, which CAO does not give and which is measured false at CAO nodes. -/
theorem ruler_pair {b : V → V → C} {y₂ : V × V → Y}
    (hb : Equivariant Γ b) (hd : DiagClosed b) {ω₀ ω₀' : V}
    (hiso₂ : ∀ q : V × V, y₂ q = y₂ (ω₀, ω₀') → ∃ γ : Γ, q = (γ • ω₀, γ • ω₀'))
    {ω₁ ω₂ : V} (hIso : IsolatesPair (b ω₀) (b ω₀') ω₂)
    (h : Phi₂ b y₂ ω₁ = Phi₂ b y₂ ω₂) :
    ∃ γ : Γ, γ • ω₁ = ω₂ := by
  have hmem : (y₂ (ω₀, ω₀'), Align₂ (b ω₂) (b ω₀) (b ω₀')) ∈ Phi₂ b y₂ ω₂ :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ (ω₀, ω₀'))
  rw [← h] at hmem
  obtain ⟨q, -, hq⟩ := Multiset.mem_map.1 hmem
  obtain ⟨γ, rfl⟩ := hiso₂ q (congrArg Prod.fst hq)
  have halign : Align₂ (b (γ⁻¹ • ω₁)) (b ω₀) (b ω₀') = Align₂ (b ω₂) (b ω₀) (b ω₀') := by
    rw [← align₂_smul hb]; exact congrArg Prod.snd hq
  have hx : (b ω₂ ω₂, b ω₀ ω₂, b ω₀' ω₂) ∈ Align₂ (b ω₂) (b ω₀) (b ω₀') :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ ω₂)
  rw [← halign] at hx
  obtain ⟨x, -, hx'⟩ := Multiset.mem_map.1 hx
  have h1 : b ω₀ x = b ω₀ ω₂ := congrArg (fun t => t.2.1) hx'
  have h2 : b ω₀' x = b ω₀' ω₂ := congrArg (fun t => t.2.2) hx'
  have hxx : x = ω₂ := hIso x h1 h2
  subst hxx
  exact ⟨γ⁻¹, hd _ _ _ (congrArg Prod.fst hx')⟩

end Pair

/-! ## 6. ⛔ THE THRESHOLD IS SHARP — valency 2 already breaks it

`Γ` acting **trivially** on `V = Fin 3` — the abstract shape of a **rigid** carrier whose 2-WL closure
is not discrete (measured: the `m = 10` multipede, `Aut = 1`, 20 non-singleton cells). Member `0` is a
singleton cell, so `hiso` holds at it; `1` and `2` share a cell; and `0`'s row gives **both** the same
colour, so its class has valency `2`.

Everything `ruler_diag` asks for holds except `Isolates`, and the conclusion is false. ⟹ the decode
cannot be weakened past *"valency 1"*: at valency `≥ 2` the table only places the decoded member
**somewhere in the ruler's fibre**, which is free. -/

namespace Counterexample

open ChainDescent.RulerOrbit.Counterexample (G2)

/-- `Γ` acts trivially — the rigid case. -/
instance : SMul G2 (Fin 3) := ⟨fun _ x => x⟩

instance : MulAction G2 (Fin 3) where
  one_smul := by decide
  mul_smul := by decide

/-- Row `0` is the ruler; `1` and `2` are the cell it fails to split. Values in `Fin 6`, and the
diagonal colours `0, 1` occur nowhere off the diagonal. -/
def bV : Fin 3 → Fin 3 → Fin 6 := ![![0, 3, 3], ![4, 1, 5], ![4, 5, 1]]

/-- The tag is the member's own diagonal colour. -/
def yV : Fin 3 → Fin 6 := fun u => bV u u

theorem bV_diagClosed : DiagClosed bV := by
  show ∀ a x z : Fin 3, bV a x = bV z z → a = x
  decide

theorem bV_equivariant : Equivariant G2 bV := by
  show ∀ (γ : G2) (ω : Fin 3) (x : Fin 3), bV (γ • ω) x = bV ω (γ⁻¹ • x)
  decide

theorem yV_invariant : Invariant G2 yV := by
  show ∀ (γ : G2) (ω : Fin 3), yV (γ • ω) = yV ω
  decide

/-- Hypothesis **(i)** holds — and in its strongest form: the ruler's cell is a **singleton**. -/
theorem cell_isOrbit : CellIsOrbit G2 yV 0 := by
  show ∀ u' : Fin 3, yV u' = yV 0 → ∃ γ : G2, u' = γ • (0 : Fin 3)
  decide

/-- ⛔ The one broken hypothesis: the ruler's row gives `1` and `2` the same colour. -/
theorem not_isolates : ¬ Isolates (bV 0) 1 := by
  show ¬ ∀ x : Fin 3, bV 0 x = bV 0 1 → x = 1
  decide

/-- The observable still collides… -/
theorem phi_collides : Phi bV yV 1 = Phi bV yV 2 := by decide

/-- …and here the tag determines `Phi` outright, so the coherence hypothesis `hφ` is not what fails. -/
theorem tag_determines_phi : ∀ u u' : Fin 3, yV u = yV u' → Phi bV yV u = Phi bV yV u' := by decide

/-- ⛔ …while the conclusion is false. -/
theorem not_same_orbit : ¬ ∃ γ : G2, γ • (1 : Fin 3) = 2 := by decide

/-- ### ⛔ **THE DECODE CANNOT GO BELOW VALENCY 1.**
All of `ruler_diag`'s hypotheses hold — equivariance, `DiagClosed`, a **singleton** ruler cell, and the
observable collision, which here follows from the tag alone — except `Isolates`, and the conclusion
fails. -/
theorem no_ruler_at_valency_two :
    Equivariant G2 bV ∧ DiagClosed bV ∧ Invariant G2 yV ∧
    CellIsOrbit G2 yV 0 ∧
    (∀ u u' : Fin 3, yV u = yV u' → Phi bV yV u = Phi bV yV u') ∧
    ¬ Isolates (bV 0) 1 ∧
    Phi bV yV 1 = Phi bV yV 2 ∧
    ¬ ∃ γ : G2, γ • (1 : Fin 3) = 2 :=
  ⟨bV_equivariant, bV_diagClosed, yV_invariant, cell_isOrbit, tag_determines_phi,
    not_isolates, phi_collides, not_same_orbit⟩

end Counterexample

/-! ### ★ …and the rework is not the old lemma in disguise

`Γ = Z₂` on `V = Fin 6`: a resolved orbit-cell `{0,1}`, the cell `{2,3}` to be resolved, and a third
cell `{4,5}` that the ruler's row **merges** while member `2` splits it. So `ruler'`'s `href` fails at
this ruler, `Isolates` holds, and §3 still resolves `{2,3}`.

⚠ This is also §4's boundary from the other side: the ruler's cell here has **size 2**, not 1 — which
is exactly the seed CAO does not hand over at a one-point extension. -/

namespace Strict

open ChainDescent.RulerOrbit.Counterexample (G2 flip)

/-- `(01)(23)(45)`. -/
def sV : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]

instance : SMul G2 (Fin 6) := ⟨fun γ x => if flip γ then sV x else x⟩

instance : MulAction G2 (Fin 6) where
  one_smul := by decide
  mul_smul := by decide

/-- Rows `1, 3, 5` are the `σ`-images of rows `0, 2, 4`. Diagonal colours `0, 1, 2`. -/
def bS : Fin 6 → Fin 6 → Fin 17 :=
  ![![0, 3, 4, 5, 6, 6], ![3, 0, 5, 4, 6, 6],
    ![7, 8, 1, 9, 10, 11], ![8, 7, 9, 1, 11, 10],
    ![12, 13, 14, 15, 2, 16], ![13, 12, 15, 14, 16, 2]]

def yS : Fin 6 → Fin 17 := fun u => bS u u

theorem bS_diagClosed : DiagClosed bS := by
  show ∀ a x z : Fin 6, bS a x = bS z z → a = x
  decide

theorem bS_equivariant : Equivariant G2 bS := by
  show ∀ (γ : G2) (ω : Fin 6) (x : Fin 6), bS (γ • ω) x = bS ω (γ⁻¹ • x)
  decide

theorem yS_invariant : Invariant G2 yS := by
  show ∀ (γ : G2) (ω : Fin 6), yS (γ • ω) = yS ω
  decide

/-- The ruler's cell is `{0,1}` — a genuine, **non-singleton** orbit. -/
theorem cell_isOrbit : CellIsOrbit G2 yS 0 := by
  show ∀ u' : Fin 6, yS u' = yS 0 → ∃ γ : G2, u' = γ • (0 : Fin 6)
  decide

/-- ✅ The new hypothesis holds — at both members of the target cell. -/
theorem isolates : Isolates (bS 0) 3 := by
  show ∀ x : Fin 6, bS 0 x = bS 0 3 → x = 3
  decide

theorem isolates' : Isolates (bS 0) 2 := by
  show ∀ x : Fin 6, bS 0 x = bS 0 2 → x = 2
  decide

/-- ⛔ The old one does not: the ruler merges slots `4, 5`, which the decoded member separates. -/
theorem href_fails : ¬ (∀ x x' : Fin 6, bS 0 x = bS 0 x' → bS 3 x = bS 3 x') := by decide

/-- The collision comes from `phi_smul`, so no coherence assumption is smuggled in. -/
theorem phi_collides : Phi bS yS 2 = Phi bS yS 3 := by
  have h := phi_smul bS_equivariant yS_invariant G2.s 2
  have hs : (G2.s • (2 : Fin 6)) = 3 := by decide
  rw [hs] at h
  exact h.symm

/-- The conclusion is real content: the cell `{2,3}` is **not** a singleton, and §3 proves it is one
orbit. -/
theorem cell_two_nontrivial : yS 2 = yS 3 ∧ (2 : Fin 6) ≠ 3 := by decide

/-- ### ★ **THE REWORK IS STRICTLY STRONGER THAN `ruler'`.**
At this ruler `href` fails, so `RulerLemma.ruler'` does not apply — and `ruler_diag` still resolves the
target cell. -/
theorem strictly_stronger :
    ¬ (∀ x x' : Fin 6, bS 0 x = bS 0 x' → bS 3 x = bS 3 x') ∧
      Isolates (bS 0) 3 ∧
      ∃ γ : G2, γ • (2 : Fin 6) = 3 :=
  ⟨href_fails, isolates, ruler_diag bS_equivariant bS_diagClosed cell_isOrbit isolates phi_collides⟩

end Strict

/-! ## 7. ✅ `DiagClosed` IS FREE AT THE REAL OBJECT

The running hypothesis costs nothing where it matters: any pair colouring that refines
`CaoTarget.initCol2` — which the 2-WL closure and every one-point extension of it does — satisfies it,
because `initCol2` carries the diagonal flag. ⟹ §2's gauge collapse and §4/§6's obstructions are
statements about `ext (rootPair adj) v`, not about an idealisation. -/

section RealObject

open ChainDescent.PartitionClosure ChainDescent.CaoTarget

variable {n : Nat}

/-- ★ **The diagonal axiom, at any colouring that refines the 2-WL start.** -/
theorem diagClosed_of_refines_init {adj : AdjMatrix n} {f : Col2 n}
    (h : PartitionClosure.Refines f (initCol2 adj)) : DiagClosed (fun a x => f (a, x)) := by
  intro a x z hax
  have h2 := h (a, x) (z, z) hax
  have hflag := (Nat.pair_eq_pair.mp h2).2
  have hz : (if z = z then 1 else 0) = 1 := if_pos rfl
  by_contra hne
  rw [if_neg hne, hz] at hflag
  exact absurd hflag (by decide)

/-- The meet of two colourings refines its left factor. -/
theorem refines_meet_left (c d : Col2 n) : PartitionClosure.Refines (meet c d) c :=
  fun _ _ h => (Nat.pair_eq_pair.mp h).1

/-- ### ★ **THE ONE-POINT EXTENSION OF A ROOT CLOSURE IS `DiagClosed`.**
So this file's whole analysis applies to `CaoTarget.ext (rootPair adj) v`, the object
`CaoTarget.Separates` is stated at. -/
theorem diagClosed_ext (adj : AdjMatrix n) (v : Fin n) :
    DiagClosed (fun a x => ext (rootPair adj) v (a, x)) := by
  refine diagClosed_of_refines_init (adj := adj) (fun p q hpq => ?_)
  exact wl2_refines (initCol2 adj) _ _
    (refines_meet_left (rootPair adj) (ptsPair v) _ _
      (wl2_refines (meet (rootPair adj) (ptsPair v)) p q hpq))

end RealObject

end RulerCao
end ChainDescent
