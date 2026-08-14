import ChainDescent.FrameEncoding
import ChainDescent.CaoEnsemble

/-!
# The gauge ensemble **as a graph**, and the triangle frame

(`docs/chain-descent-cao-carrier-falsifiers.md` §3, §6, and §6f.4d caveat 3 — which is the gap this
file closes.)

## Why this file exists

`CaoEnsemble.lean` is the *index* layer: copies as `Slot → Bool`, the gauge action, T1/T2⁻. It has **no
graph and no adjacency**, so the sentence the whole programme is aimed at — *"`E(L)`'s 2-WL closure has
a cell containing two payload vertices from different orbits"* — was **not expressible in Lean at
all**. This file builds the object and makes it a statement.

| | |
|---|---|
| **§1** | an invariance layer for the generic 2-WL round: a bijection preserving the atoms preserves the closure |
| **§2** | `EVert`/`eAdj`/`eInit`/`eRoot` — the ensemble with the base central vertex individualized |
| **§3** | the label action as an `Equiv`, and that it fixes the individualized vertex |
| **§4** | ★ `orbit_not_split` (the free half) · **`MixedCell`** · `not_propagates_of_mixed` |
⛔ **§5 (the triangle frame `TF(E)`) is NOT here** — out of budget this pass, and queued. ⚠ Note when it
lands: its WL dimension is **inherited** from the payload (bounded above by §6f's interpretation
argument, below by §6b's), so it **transports** hardness rather than creating it, and it needs a
high-WL payload family as input — the same unformalized literature input. ★ Its value is as the
**poly-size** object grounding §6g, not as a new hardness source.

## ⚠ What this does NOT do

It does **not** refute CAO propagation, and it does not bring that any closer except by making the
statement expressible. Still open and untouched here: the **collapse** (§6e.4), **CFI's WL-blindness**
(literature), and **T2⁺** (`Aut_{m(base)}` is *exactly* the label group — only `⊇` is available, which
is why §4 states the target against the **label** orbits and is careful about which direction that
weakens).

★ Direction, and it is the one that matters: §4's `orbit_not_split` is the **free** half (an orbit is
never split, from invariance alone). The half that would refute propagation is a **merge**, and that is
`MixedCell` — stated, never proved.

## ⚠ Two modelling notes

1. **Ordered slots**, as in `FrameEncoding`: a slot is an ordered pair, so `(a,b)` and `(b,a)` carry twin
   frame vertices. Harmless for everything here (twins never separate), but it means `Aut` contains
   those twin swaps — ⛔ so this file must not be used to claim `Aut = ` the label group.
2. **Frame types are earned, not given.** `eInit` gives every frame vertex the *same* sort; the type
   becomes readable only through the individualized central vertex (§6b). That is the honest model, and
   the opposite of `FrameEncoding.mInit`'s deliberate over-provision.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`.
-/

namespace ChainDescent
namespace Ensemble

open ChainDescent.PartitionClosure
open ChainDescent.FrameEncoding

/-! ## 1. Invariance for the generic 2-WL round

`CaoTarget` has this at `V = Fin n`; the ensemble's carrier is a sum of products, so it is needed at a
generic carrier. Nothing here is specific to the ensemble. -/

section Inv
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `c` is invariant under the bijection `e`. -/
def InvG (e : V ≃ V) (c : Col (V × V)) : Prop := ∀ p : V × V, c (e p.1, e p.2) = c p

omit [DecidableEq V] in
private theorem map_univ_equiv (e : V ≃ V) :
    Multiset.map e (Finset.univ : Finset V).val = (Finset.univ : Finset V).val := by
  have h : (Finset.univ : Finset V).map e.toEmbedding = Finset.univ := Finset.map_univ_equiv e
  calc Multiset.map e (Finset.univ : Finset V).val
      = ((Finset.univ : Finset V).map e.toEmbedding).val := rfl
    _ = (Finset.univ : Finset V).val := by rw [h]

omit [DecidableEq V] in
theorem pairSigG_congr {e : V ≃ V} {c : Col (V × V)} (h : InvG e c) (p : V × V) :
    pairSigG c (e p.1, e p.2) = pairSigG c p := by
  unfold pairSigG
  calc (Finset.univ : Finset V).val.map (fun x => (c (e p.1, x), c (x, e p.2)))
      = (Multiset.map e (Finset.univ : Finset V).val).map
          (fun x => (c (e p.1, x), c (x, e p.2))) := by rw [map_univ_equiv e]
    _ = (Finset.univ : Finset V).val.map
          (fun y => (c (e p.1, e y), c (e y, e p.2))) := by rw [Multiset.map_map]; rfl
    _ = (Finset.univ : Finset V).val.map (fun y => (c (p.1, y), c (y, p.2))) := by
          refine Multiset.map_congr rfl (fun y _ => ?_)
          rw [h (p.1, y), h (y, p.2)]

omit [DecidableEq V] in
theorem invG_roundG {e : V ≃ V} {c : Col (V × V)} (h : InvG e c) : InvG e (roundG c) := by
  intro p
  have hkey : pairKeyG c (e p.1, e p.2) = pairKeyG c p :=
    (pairKeyG_eq_iff c _ _).mpr ⟨h p, pairSigG_congr h p⟩
  show CaoTarget.rankOf (pairKeyG c) (e p.1, e p.2) = CaoTarget.rankOf (pairKeyG c) p
  unfold CaoTarget.rankOf
  rw [hkey]

omit [DecidableEq V] in
theorem invG_iterate {e : V ≃ V} : ∀ (k : Nat) {c : Col (V × V)}, InvG e c →
    InvG e ((roundG (V := V))^[k] c)
  | 0, _, h => h
  | k + 1, c, h => by
      rw [Function.iterate_succ_apply']
      exact invG_roundG (invG_iterate k h)

omit [DecidableEq V] in
/-- **★ The closure inherits every symmetry of the atoms.** -/
theorem invG_wl2G {e : V ≃ V} {c : Col (V × V)} (h : InvG e c) : InvG e (wl2G c) :=
  invG_iterate _ h

end Inv

/-! ## 2. The ensemble as a graph -/

variable {L : Nat}

/-- A slot: an ordered pair of labels (modelling note 1). -/
abbrev ESlot (L : Nat) : Type := Fin L × Fin L

/-- A copy, equally a gauge choice: a type assignment to every slot. -/
abbrev EColr (L : Nat) : Type := ESlot L → Bool

/-- The ensemble's vertices: payload copies, the shared frame, and the central gauge vertices. -/
abbrev EVert (L : Nat) : Type :=
  (EColr L × Fin L) ⊕ ((ESlot L × Bool) ⊕ EColr L)

/-- The payload vertex `p(c,i)`. -/
abbrev epay (c : EColr L) (i : Fin L) : EVert L := Sum.inl (c, i)
/-- The frame vertex `f(k,t)`. -/
abbrev efrm (k : ESlot L) (t : Bool) : EVert L := Sum.inr (Sum.inl (k, t))
/-- The central vertex `m(g)`. -/
abbrev ecen (g : EColr L) : EVert L := Sum.inr (Sum.inr g)

/-- The base gauge — the central vertex that gets individualized. -/
def ebase (L : Nat) : EColr L := fun _ => false

/-- `i` is an endpoint of the (non-degenerate) slot `k`. -/
def inSlot (k : ESlot L) (i : Fin L) : Bool := decide (k.1 ≠ k.2 ∧ (i = k.1 ∨ i = k.2))

/-- **The ensemble's adjacency.** Each copy is a clique; a payload vertex meets the frame corner whose
type its copy assigns to each slot it lies in; the two corners of a slot are joined; a central vertex
meets the corner its gauge selects. -/
def eAdj (x y : EVert L) : Bool :=
  match x, y with
  | Sum.inl (c, i), Sum.inl (c', j) => decide (c = c' ∧ i ≠ j)
  | Sum.inl (c, i), Sum.inr (Sum.inl (k, t)) => inSlot k i && decide (c k = t)
  | Sum.inr (Sum.inl (k, t)), Sum.inl (c, i) => inSlot k i && decide (c k = t)
  | Sum.inr (Sum.inl (k, t)), Sum.inr (Sum.inl (k', t')) => decide (k = k' ∧ t ≠ t')
  | Sum.inr (Sum.inl (k, t)), Sum.inr (Sum.inr g) => decide (g k = t)
  | Sum.inr (Sum.inr g), Sum.inr (Sum.inl (k, t)) => decide (g k = t)
  | _, _ => false

/-- The sort of a vertex: payload, frame, central, and — separately — **the individualized central**.
⚠ Every frame vertex gets the same sort: the type is *earned* (modelling note 2). -/
def esort (x : EVert L) : Nat :=
  match x with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr g) => if g = ebase L then 3 else 2

/-- **The atomic pair colouring, with `m(base)` individualized.** -/
def eInit (L : Nat) : Col (EVert L × EVert L) := fun p =>
  Nat.pair (Nat.pair (esort p.1) (esort p.2))
    (Nat.pair (if p.1 = p.2 then 1 else 0) (if eAdj p.1 p.2 then 1 else 0))

/-- **★ THE OBJECT: the ensemble's 2-WL closure after individualizing the base central vertex.** -/
def eRoot (L : Nat) : Col (EVert L × EVert L) := wl2G (eInit L)

/-! ## 3. The label action -/

/-- A label permutation acting on slots. -/
def sact (σ : Equiv.Perm (Fin L)) : Equiv.Perm (ESlot L) := σ.prodCongr σ

/-- A label permutation acting on copies and gauges: reindex by the inverse slot action. -/
def cact (σ : Equiv.Perm (Fin L)) : EColr L ≃ EColr L :=
  Equiv.arrowCongr (sact σ) (Equiv.refl Bool)

theorem cact_apply (σ : Equiv.Perm (Fin L)) (c : EColr L) (k : ESlot L) :
    cact σ c k = c ((sact σ).symm k) := rfl

/-- **The gauge base is fixed by every label permutation.** This is `CaoEnsemble.lact_base` at the
graph, and it is what survives individualizing `m(base)`. -/
theorem cact_base (σ : Equiv.Perm (Fin L)) : cact σ (ebase L) = ebase L := rfl

/-- **The label action on vertices, as a bijection.** Assembled from `Equiv` combinators, so both
inverse laws are free — the direct definition needs `Prod.map` bookkeeping that does not discharge by
`rfl`. -/
def eact (σ : Equiv.Perm (Fin L)) : EVert L ≃ EVert L :=
  ((cact σ).prodCongr σ).sumCongr
    (((sact σ).prodCongr (Equiv.refl Bool)).sumCongr (cact σ))

@[simp] theorem eact_pay (σ : Equiv.Perm (Fin L)) (c : EColr L) (i : Fin L) :
    eact σ (epay c i) = epay (cact σ c) (σ i) := rfl

@[simp] theorem eact_frm (σ : Equiv.Perm (Fin L)) (k : ESlot L) (t : Bool) :
    eact σ (efrm k t) = efrm (sact σ k) t := rfl

@[simp] theorem eact_cen (σ : Equiv.Perm (Fin L)) (g : EColr L) :
    eact σ (ecen g) = ecen (cact σ g) := rfl

/-- **The action fixes the individualized vertex** — T4 at the graph. Without it the construction loses
its symmetry the moment `m(base)` is individualized, which is exactly the failure mode §3.2a records. -/
theorem eact_base (σ : Equiv.Perm (Fin L)) : eact σ (ecen (ebase L)) = ecen (ebase L) := by
  rw [eact_cen, cact_base]

/-! ## 3a. The action is a symmetry of the atoms — hence of the closure -/

theorem inSlot_sact (σ : Equiv.Perm (Fin L)) (k : ESlot L) (i : Fin L) :
    inSlot (sact σ k) (σ i) = inSlot k i := by
  simp only [inSlot, sact, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, ne_eq,
    Equiv.apply_eq_iff_eq]

theorem cact_sact (σ : Equiv.Perm (Fin L)) (c : EColr L) (k : ESlot L) :
    cact σ c (sact σ k) = c k := by
  rw [cact_apply, Equiv.symm_apply_apply]

theorem cact_eq_base_iff (σ : Equiv.Perm (Fin L)) (g : EColr L) :
    cact σ g = ebase L ↔ g = ebase L := by
  refine ⟨fun h => ?_, fun h => by rw [h, cact_base]⟩
  exact (Equiv.apply_eq_iff_eq (cact σ)).mp (h.trans (cact_base σ).symm)

/-- **The label action preserves adjacency** — i.e. it really is an automorphism of the ensemble. -/
theorem eAdj_eact (σ : Equiv.Perm (Fin L)) (x y : EVert L) :
    eAdj (eact σ x) (eact σ y) = eAdj x y := by
  rcases x with ⟨c, i⟩ | ⟨k, t⟩ | g <;> rcases y with ⟨c', j⟩ | ⟨k', t'⟩ | g' <;>
    simp only [eact_pay, eact_frm, eact_cen, eAdj, inSlot_sact, cact_sact, ne_eq,
      Equiv.apply_eq_iff_eq]

theorem esort_eact (σ : Equiv.Perm (Fin L)) (x : EVert L) : esort (eact σ x) = esort x := by
  rcases x with ⟨c, i⟩ | ⟨k, t⟩ | g <;> simp [esort, cact_eq_base_iff]

/-- **The atoms are invariant** — adjacency, sorts, and the individualization all survive. -/
theorem invG_eInit (σ : Equiv.Perm (Fin L)) : InvG (eact σ) (eInit L) := by
  intro p
  simp only [eInit, esort_eact, eAdj_eact, Equiv.apply_eq_iff_eq]

/-- **★ Hence the closure is invariant**, by §1. -/
theorem invG_eRoot (σ : Equiv.Perm (Fin L)) : InvG (eact σ) (eRoot L) :=
  invG_wl2G (invG_eInit σ)

/-! ## 4. The target, at the object

★ `orbit_not_split` is free from invariance. `MixedCell` is the refutation shape, and it is **stated,
not proved** — per the standing steer that a pinned statement nobody has proved can be false. -/

/-- Two vertices are in the same **label** orbit. ⚠ Contained in the `Aut_{m(base)}`-orbit relation;
equality of the two is T2⁺, which is **not** available (see the header). -/
def SameLabelOrbit (x y : EVert L) : Prop := ∃ σ : Equiv.Perm (Fin L), eact σ x = y

/-- **⛔ THE REFUTATION SHAPE.** Two payload vertices in *different* label orbits sharing a cell of the
ensemble's 2-WL closure. Stated so the programme has a target at a real object; **not proved**. -/
def MixedCell (L : Nat) : Prop :=
  ∃ c c' : EColr L, ∃ i j : Fin L,
    eRoot L (epay c i, epay c i) = eRoot L (epay c' j, epay c' j) ∧
      ¬ SameLabelOrbit (epay c i) (epay c' j)

/-- CAO propagation at the ensemble, in the only form available without T2⁺: the closure's payload
cells do not merge distinct label orbits. -/
def LabelPropagates (L : Nat) : Prop :=
  ∀ c c' : EColr L, ∀ i j : Fin L,
    eRoot L (epay c i, epay c i) = eRoot L (epay c' j, epay c' j) →
      SameLabelOrbit (epay c i) (epay c' j)

/-- **★ THE FREE HALF — a label orbit is never split.** From invariance alone; no hypothesis. This is
the direction that is *not* in question, and stating it is what makes clear that the open content is
entirely the **merge**. -/
theorem orbit_not_split {x y : EVert L} (h : SameLabelOrbit x y) :
    eRoot L (x, x) = eRoot L (y, y) := by
  obtain ⟨σ, hσ⟩ := h
  have h2 := invG_eRoot (L := L) σ (x, x)
  rw [hσ] at h2
  exact h2.symm

/-- **The bridge**: a mixed cell refutes propagation at this object. -/
theorem not_labelPropagates_of_mixed (h : MixedCell L) : ¬ LabelPropagates L := by
  obtain ⟨c, c', i, j, hcell, hne⟩ := h
  exact fun hp => hne (hp c c' i j hcell)

end Ensemble
end ChainDescent
