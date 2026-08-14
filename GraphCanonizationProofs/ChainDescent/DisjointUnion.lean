import ChainDescent.FrameEncoding

/-!
# 2-WL on a disjoint union — the block lemma, and the single-graph merge it buys

(`docs/chain-descent-cao-carrier-falsifiers.md` §6f.3 and the 2026-08-14 review. Read
`FrameEncoding`'s `GenericRound` section first — this file is built entirely on it.)

## Why this file exists

`FrameTransfer.merge_of_tuple_merge` fixes **one** graph `E` and merges two vertices of `M(E)`.
The refutation template in §6f.3 instead wants

> `CFI(X,0)` and `CFI(X,1)` are `m`-WL-equivalent ⟹ their encodings are 2-WL-equivalent
> ⟹ a mixed cell,

which is a statement about **two** graphs, and worse, one whose premise compares `rankOf` colours
across two separate runs — colours that are not on speaking terms.

★ **This file removes the mismatch instead of patching it.** Both halves of the difficulty are the
same fact: *how 2-WL behaves on a disjoint union.* Once that is settled,

* the two graphs become **one graph** `A ⊔ B`, so `merge_of_tuple_merge`'s single-carrier shape is
  already the right shape; and
* the components of `A ⊔ B` are non-isomorphic, so **no automorphism crosses them** — while 2-WL
  merges across them. That is a mixed cell in a *single* graph, which is the form
  *"`k`-WL fails to distinguish orbits"* takes in the literature.

## What is proved

The method is §6d.1's throughout: **WL is the coarsest stable refinement of the atoms**, so
*exhibiting* a stable colouring bounds the closure from above, and an upper bound carries **merges**
(never separations — `FrameEncoding`'s direction discipline applies verbatim).

`Blocked A B u κ` says `u` is assembled from block data: intra-side pairs carry whatever their own
side's run gives them, **cross** pairs carry only the two endpoint diagonal colours (through `κ`),
cross colours are never confused with intra ones, a pair's colour determines its endpoints'
diagonals, the two sides' own-side signatures agree, and the two sides carry the **same multiset of
diagonal colours**. `stable_of_blocked` proves such a `u` is `roundG`-stable; `merge_of_blocked` is
the consumer.

⚠ `diagEq` is not decoration — it is exactly where *"the two sides are WL-equivalent"* enters, and
the proof of case A2 below is the only place it is used.

## ⚠ What this does NOT establish

1. It does not supply a `Blocked` witness for a CFI pair — that is input (iii), literature.
2. It says nothing about the collapse (i), §6e.4.
3. ⛔ It does **not** bridge `roundTS` to standard `k`-WL. §6f.4c put covariance *into the round*, so
   `roundTS` is finer than `roundT`; the CFI input is a statement about standard `k`-WL, and that
   bridge is still owed. Restating (iii) in pebble-game form gets the input in the door but does not
   discharge the bridge back out.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`.
-/

namespace ChainDescent
namespace DisjointUnion

open ChainDescent.PartitionClosure
open ChainDescent.FrameEncoding

variable {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]

/-! ## 1. The disjoint union, and the side function -/

/-- The carrier of the disjoint union. -/
abbrev DV (V₁ V₂ : Type*) : Type _ := V₁ ⊕ V₂

/-- Adjacency of `A ⊔ B`: no edge crosses. -/
def dAdj (A : V₁ → V₁ → Bool) (B : V₂ → V₂ → Bool) : DV V₁ V₂ → DV V₁ V₂ → Bool
  | Sum.inl a, Sum.inl a' => A a a'
  | Sum.inr b, Sum.inr b' => B b b'
  | Sum.inl _, Sum.inr _ => false
  | Sum.inr _, Sum.inl _ => false

/-- The atoms of `A ⊔ B`. ⚠ **Deliberately side-blind**: equality and adjacency only. Tagging the
sides here would make a cross-component merge impossible by fiat, which is the whole question. -/
def dInit (A : V₁ → V₁ → Bool) (B : V₂ → V₂ → Bool) : Col (DV V₁ V₂ × DV V₁ V₂) := fun p =>
  Nat.pair (if p.1 = p.2 then 1 else 0) (if dAdj A B p.1 p.2 then 1 else 0)

/-- Which side a vertex is on. Used only in *hypotheses* and in the guessed colouring's shape — never
handed to the refiner. -/
def side : DV V₁ V₂ → Bool := Sum.elim (fun _ => true) (fun _ => false)

omit [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂] in
@[simp] theorem side_inl (a : V₁) : side (V₂ := V₂) (Sum.inl a) = true := rfl

omit [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂] in
@[simp] theorem side_inr (b : V₂) : side (V₁ := V₁) (Sum.inr b) = false := rfl

/-- Two vertices lie on the same side. -/
def SameSide (x y : DV V₁ V₂) : Prop := side x = side y

omit [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂] in
theorem sameSide_rfl (x : DV V₁ V₂) : SameSide x x := rfl

/-! ## 2. Splitting a signature along the two sides -/

/-- The part of a pair's 2-WL signature contributed by the **left** side. -/
def sigL (u : Col (DV V₁ V₂ × DV V₁ V₂)) (p : DV V₁ V₂ × DV V₁ V₂) : Multiset (Nat × Nat) :=
  (Finset.univ : Finset V₁).val.map (fun a => (u (p.1, Sum.inl a), u (Sum.inl a, p.2)))

/-- The part contributed by the **right** side. -/
def sigR (u : Col (DV V₁ V₂ × DV V₁ V₂)) (p : DV V₁ V₂ × DV V₁ V₂) : Multiset (Nat × Nat) :=
  (Finset.univ : Finset V₂).val.map (fun b => (u (p.1, Sum.inr b), u (Sum.inr b, p.2)))

omit [DecidableEq V₁] [DecidableEq V₂] in
theorem sig_split (u : Col (DV V₁ V₂ × DV V₁ V₂)) (p : DV V₁ V₂ × DV V₁ V₂) :
    pairSigG u p = sigL u p + sigR u p := by
  unfold pairSigG sigL sigR
  have h : (Finset.univ : Finset (DV V₁ V₂)).val
      = (Finset.univ : Finset V₁).val.map Sum.inl + (Finset.univ : Finset V₂).val.map Sum.inr := rfl
  rw [h, Multiset.map_add, Multiset.map_map, Multiset.map_map]
  rfl

/-- The half of the signature contributed by the side of the pair's **first** vertex. -/
def ownSig (u : Col (DV V₁ V₂ × DV V₁ V₂)) (p : DV V₁ V₂ × DV V₁ V₂) : Multiset (Nat × Nat) :=
  cond (side p.1) (sigL u p) (sigR u p)

/-- The multiset of diagonal colours on the left side. -/
def diagL (u : Col (DV V₁ V₂ × DV V₁ V₂)) : Multiset Nat :=
  (Finset.univ : Finset V₁).val.map (fun a => u (Sum.inl a, Sum.inl a))

/-- The multiset of diagonal colours on the right side. -/
def diagR (u : Col (DV V₁ V₂ × DV V₁ V₂)) : Multiset Nat :=
  (Finset.univ : Finset V₂).val.map (fun b => u (Sum.inr b, Sum.inr b))

/-- Left-side pairs `(x, ·)` with the second endpoint replaced by its diagonal colour. -/
def PL (u : Col (DV V₁ V₂ × DV V₁ V₂)) (x : DV V₁ V₂) : Multiset (Nat × Nat) :=
  (Finset.univ : Finset V₁).val.map (fun a => (u (x, Sum.inl a), u (Sum.inl a, Sum.inl a)))

/-- Right-side pairs `(x, ·)` with the second endpoint replaced by its diagonal colour. -/
def PR (u : Col (DV V₁ V₂ × DV V₁ V₂)) (x : DV V₁ V₂) : Multiset (Nat × Nat) :=
  (Finset.univ : Finset V₂).val.map (fun b => (u (x, Sum.inr b), u (Sum.inr b, Sum.inr b)))

/-- `PL`/`PR` at `x`'s own side. -/
def ownP (u : Col (DV V₁ V₂ × DV V₁ V₂)) (x : DV V₁ V₂) : Multiset (Nat × Nat) :=
  cond (side x) (PL u x) (PR u x)

/-- Left-side pairs `(·, y)` with the first endpoint replaced by its diagonal colour. -/
def QL (u : Col (DV V₁ V₂ × DV V₁ V₂)) (y : DV V₁ V₂) : Multiset (Nat × Nat) :=
  (Finset.univ : Finset V₁).val.map (fun a => (u (Sum.inl a, Sum.inl a), u (Sum.inl a, y)))

/-- Right-side pairs `(·, y)` with the first endpoint replaced by its diagonal colour. -/
def QR (u : Col (DV V₁ V₂ × DV V₁ V₂)) (y : DV V₁ V₂) : Multiset (Nat × Nat) :=
  (Finset.univ : Finset V₂).val.map (fun b => (u (Sum.inr b, Sum.inr b), u (Sum.inr b, y)))

/-- `QL`/`QR` at `y`'s own side. -/
def ownQ (u : Col (DV V₁ V₂ × DV V₁ V₂)) (y : DV V₁ V₂) : Multiset (Nat × Nat) :=
  cond (side y) (QL u y) (QR u y)

/-! ## 3. The block hypothesis -/

/-- **`u` is assembled blockwise from the two sides' runs.**

`κ` is the function that builds a cross-pair colour out of the two endpoint diagonal colours. It is
a parameter rather than an existential so the lemmas below can name it. -/
structure Blocked (A : V₁ → V₁ → Bool) (B : V₂ → V₂ → Bool)
    (u : Col (DV V₁ V₂ × DV V₁ V₂)) (κ : Nat → Nat → Nat) : Prop where
  /-- `u` sees the disjoint union's atoms — equality and adjacency. -/
  atoms : PartitionClosure.Refines u (dInit A B)
  /-- ⚠ A cross pair never shares a colour with an intra pair. Not implied by `atoms`: both kinds
  can be distinct and non-adjacent. -/
  sep : ∀ x y z w : DV V₁ V₂, SameSide x y → ¬ SameSide z w → u (x, y) ≠ u (z, w)
  /-- A pair's colour determines its first endpoint's diagonal colour. -/
  endFst : ∀ p q : DV V₁ V₂ × DV V₁ V₂, u p = u q → u (p.1, p.1) = u (q.1, q.1)
  /-- A pair's colour determines its second endpoint's diagonal colour. -/
  endSnd : ∀ p q : DV V₁ V₂ × DV V₁ V₂, u p = u q → u (p.2, p.2) = u (q.2, q.2)
  /-- A cross pair carries **exactly** the two endpoint diagonal colours. -/
  cross : ∀ x y : DV V₁ V₂, ¬ SameSide x y → u (x, y) = κ (u (x, x)) (u (y, y))
  /-- Equal-coloured intra pairs have equal **own-side** signatures — including across the two
  sides, which is what *"a common colour vocabulary"* means. -/
  sideDet : ∀ p q : DV V₁ V₂ × DV V₁ V₂, SameSide p.1 p.2 → SameSide q.1 q.2 →
      u p = u q → ownSig u p = ownSig u q
  /-- ★ The two sides carry the same multiset of diagonal colours. This is where *"`A` and `B` are
  WL-equivalent"* enters, and it is used in exactly one case below. -/
  diagEq : diagL u = diagR u

/-! ## 4. How the four blocks of a signature read -/

variable {A : V₁ → V₁ → Bool} {B : V₂ → V₂ → Bool}
  {u : Col (DV V₁ V₂ × DV V₁ V₂)} {κ : Nat → Nat → Nat}

theorem sigR_of_bothL (h : Blocked A B u κ) {x y : DV V₁ V₂}
    (hx : side x = true) (hy : side y = true) :
    sigR u (x, y) = (diagR u).map (fun m => (κ (u (x, x)) m, κ m (u (y, y)))) := by
  unfold sigR diagR
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun b _ => ?_)
  have h1 : ¬ SameSide x (Sum.inr b) := by simp [SameSide, hx]
  have h2 : ¬ SameSide (Sum.inr b) y := by simp [SameSide, hy]
  show (u (x, Sum.inr b), u (Sum.inr b, y)) = _
  rw [h.cross _ _ h1, h.cross _ _ h2]
  rfl

theorem sigL_of_bothR (h : Blocked A B u κ) {x y : DV V₁ V₂}
    (hx : side x = false) (hy : side y = false) :
    sigL u (x, y) = (diagL u).map (fun m => (κ (u (x, x)) m, κ m (u (y, y)))) := by
  unfold sigL diagL
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun a _ => ?_)
  have h1 : ¬ SameSide x (Sum.inl a) := by simp [SameSide, hx]
  have h2 : ¬ SameSide (Sum.inl a) y := by simp [SameSide, hy]
  show (u (x, Sum.inl a), u (Sum.inl a, y)) = _
  rw [h.cross _ _ h1, h.cross _ _ h2]
  rfl

theorem sigL_of_sndR (h : Blocked A B u κ) {x y : DV V₁ V₂} (hy : side y = false) :
    sigL u (x, y) = (PL u x).map (fun t => (t.1, κ t.2 (u (y, y)))) := by
  unfold sigL PL
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun a _ => ?_)
  have h2 : ¬ SameSide (Sum.inl a) y := by simp [SameSide, hy]
  show (u (x, Sum.inl a), u (Sum.inl a, y)) = _
  rw [h.cross _ _ h2]
  rfl

theorem sigR_of_sndL (h : Blocked A B u κ) {x y : DV V₁ V₂} (hy : side y = true) :
    sigR u (x, y) = (PR u x).map (fun t => (t.1, κ t.2 (u (y, y)))) := by
  unfold sigR PR
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun b _ => ?_)
  have h2 : ¬ SameSide (Sum.inr b) y := by simp [SameSide, hy]
  show (u (x, Sum.inr b), u (Sum.inr b, y)) = _
  rw [h.cross _ _ h2]
  rfl

theorem sigR_of_fstL (h : Blocked A B u κ) {x y : DV V₁ V₂} (hx : side x = true) :
    sigR u (x, y) = (QR u y).map (fun t => (κ (u (x, x)) t.1, t.2)) := by
  unfold sigR QR
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun b _ => ?_)
  have h1 : ¬ SameSide x (Sum.inr b) := by simp [SameSide, hx]
  show (u (x, Sum.inr b), u (Sum.inr b, y)) = _
  rw [h.cross _ _ h1]
  rfl

theorem sigL_of_fstR (h : Blocked A B u κ) {x y : DV V₁ V₂} (hx : side x = false) :
    sigL u (x, y) = (QL u y).map (fun t => (κ (u (x, x)) t.1, t.2)) := by
  unfold sigL QL
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun a _ => ?_)
  have h1 : ¬ SameSide x (Sum.inl a) := by simp [SameSide, hx]
  show (u (x, Sum.inl a), u (Sum.inl a, y)) = _
  rw [h.cross _ _ h1]
  rfl

/-! ## 5. Transporting the intra halves — the two `exists_factor` steps -/

/-- ★ Equal diagonal colours ⟹ equal own-side profiles. This is `sideDet` at the diagonal, with the
second endpoint's colour replaced by its diagonal colour through a **single** function, which is
what makes the two sides comparable. -/
theorem ownP_eq (h : Blocked A B u κ) {x z : DV V₁ V₂} (hd : u (x, x) = u (z, z)) :
    ownP u x = ownP u z := by
  obtain ⟨f, hf⟩ := exists_factor (c := u) (d := fun p => u (p.1, p.1)) h.endFst
  have key : ∀ v : DV V₁ V₂, ownP u v = (ownSig u (v, v)).map (fun t => (t.1, f t.2)) := by
    intro v
    unfold ownP ownSig
    cases hv : side v
    · show PR u v = (sigR u (v, v)).map _
      unfold PR sigR
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl (fun b _ => ?_)
      show (u (v, Sum.inr b), u (Sum.inr b, Sum.inr b)) = _
      simp only [Function.comp_apply]
      rw [hf (Sum.inr b, v)]
    · show PL u v = (sigL u (v, v)).map _
      unfold PL sigL
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl (fun a _ => ?_)
      show (u (v, Sum.inl a), u (Sum.inl a, Sum.inl a)) = _
      simp only [Function.comp_apply]
      rw [hf (Sum.inl a, v)]
  rw [key x, key z, h.sideDet _ _ (sameSide_rfl x) (sameSide_rfl z) hd]

/-- The mirror of `ownP_eq`, with the **first** endpoint diagonalized. -/
theorem ownQ_eq (h : Blocked A B u κ) {y w : DV V₁ V₂} (hd : u (y, y) = u (w, w)) :
    ownQ u y = ownQ u w := by
  obtain ⟨g, hg⟩ := exists_factor (c := u) (d := fun p => u (p.2, p.2)) h.endSnd
  have key : ∀ v : DV V₁ V₂, ownQ u v = (ownSig u (v, v)).map (fun t => (g t.1, t.2)) := by
    intro v
    unfold ownQ ownSig
    cases hv : side v
    · show QR u v = (sigR u (v, v)).map _
      unfold QR sigR
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl (fun b _ => ?_)
      show (u (Sum.inr b, Sum.inr b), u (Sum.inr b, v)) = _
      simp only [Function.comp_apply]
      rw [hg (v, Sum.inr b)]
    · show QL u v = (sigL u (v, v)).map _
      unfold QL sigL
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl (fun a _ => ?_)
      show (u (Sum.inl a, Sum.inl a), u (Sum.inl a, v)) = _
      simp only [Function.comp_apply]
      rw [hg (v, Sum.inl a)]
  rw [key y, key w, h.sideDet _ _ (sameSide_rfl y) (sameSide_rfl w) hd]

/-! ## 6. ★★★ The block colouring is stable -/

/-- **★★★ A blocked colouring is `roundG`-stable.**

Case A (both pairs intra) uses `sideDet` on the own halves and `κ` + `diagEq` on the other halves;
case B (both cross) uses `ownP_eq`/`ownQ_eq`. `sep` is what forbids the mixed case. -/
theorem stable_of_blocked (h : Blocked A B u κ) : Stable (roundG (V := DV V₁ V₂)) u := by
  rw [stable_iff_sig]
  rintro ⟨x, y⟩ ⟨z, w⟩ hpq
  by_cases hp : SameSide x y
  · by_cases hq : SameSide z w
    · -- CASE A: both pairs intra.
      have hf : u (x, x) = u (z, z) := h.endFst (x, y) (z, w) hpq
      have hs : u (y, y) = u (w, w) := h.endSnd (x, y) (z, w) hpq
      have hown : ownSig u (x, y) = ownSig u (z, w) := h.sideDet _ _ hp hq hpq
      rw [sig_split, sig_split]
      cases hx : side x with
      | false =>
        have hy : side y = false := by rw [← hx]; exact (hp).symm
        have hL : sigL u (x, y) = (diagL u).map (fun m => (κ (u (x, x)) m, κ m (u (y, y)))) :=
          sigL_of_bothR h hx hy
        have hoxy : ownSig u (x, y) = sigR u (x, y) := by simp [ownSig, hx]
        cases hz : side z with
        | false =>
          have hw : side w = false := by rw [← hz]; exact (hq).symm
          have hL' : sigL u (z, w) = (diagL u).map (fun m => (κ (u (z, z)) m, κ m (u (w, w)))) :=
            sigL_of_bothR h hz hw
          have hozw : ownSig u (z, w) = sigR u (z, w) := by simp [ownSig, hz]
          rw [hL, hL', hf, hs, ← hoxy, ← hozw, hown]
        | true =>
          have hw : side w = true := by rw [← hz]; exact (hq).symm
          have hR' : sigR u (z, w) = (diagR u).map (fun m => (κ (u (z, z)) m, κ m (u (w, w)))) :=
            sigR_of_bothL h hz hw
          have hozw : ownSig u (z, w) = sigL u (z, w) := by simp [ownSig, hz]
          rw [hL, hR', hf, hs, h.diagEq, ← hoxy, ← hozw, hown, add_comm]
      | true =>
        have hy : side y = true := by rw [← hx]; exact (hp).symm
        have hR : sigR u (x, y) = (diagR u).map (fun m => (κ (u (x, x)) m, κ m (u (y, y)))) :=
          sigR_of_bothL h hx hy
        have hoxy : ownSig u (x, y) = sigL u (x, y) := by simp [ownSig, hx]
        cases hz : side z with
        | false =>
          have hw : side w = false := by rw [← hz]; exact (hq).symm
          have hL' : sigL u (z, w) = (diagL u).map (fun m => (κ (u (z, z)) m, κ m (u (w, w)))) :=
            sigL_of_bothR h hz hw
          have hozw : ownSig u (z, w) = sigR u (z, w) := by simp [ownSig, hz]
          rw [hR, hL', hf, hs, ← h.diagEq, ← hoxy, ← hozw, hown, add_comm]
        | true =>
          have hw : side w = true := by rw [← hz]; exact (hq).symm
          have hR' : sigR u (z, w) = (diagR u).map (fun m => (κ (u (z, z)) m, κ m (u (w, w)))) :=
            sigR_of_bothL h hz hw
          have hozw : ownSig u (z, w) = sigL u (z, w) := by simp [ownSig, hz]
          rw [hR, hR', hf, hs, ← hoxy, ← hozw, hown]
    · exact absurd hpq (h.sep x y z w hp hq)
  · by_cases hq : SameSide z w
    · exact absurd hpq.symm (h.sep z w x y hq hp)
    · -- CASE B: both pairs cross.
      have hf : u (x, x) = u (z, z) := h.endFst (x, y) (z, w) hpq
      have hs : u (y, y) = u (w, w) := h.endSnd (x, y) (z, w) hpq
      have hP : ownP u x = ownP u z := ownP_eq h hf
      have hQ : ownQ u y = ownQ u w := ownQ_eq h hs
      rw [sig_split, sig_split]
      cases hx : side x with
      | false =>
        have hy : side y = true := by
          cases hy : side y with
          | false => exact absurd (hx.trans hy.symm) hp
          | true => rfl
        have e1 : sigR u (x, y) = (PR u x).map (fun t => (t.1, κ t.2 (u (y, y)))) :=
          sigR_of_sndL h hy
        have e2 : sigL u (x, y) = (QL u y).map (fun t => (κ (u (x, x)) t.1, t.2)) :=
          sigL_of_fstR h hx
        have hpx : ownP u x = PR u x := by simp [ownP, hx]
        have hqy : ownQ u y = QL u y := by simp [ownQ, hy]
        cases hz : side z with
        | false =>
          have hw : side w = true := by
            cases hw : side w with
            | false => exact absurd (hz.trans hw.symm) hq
            | true => rfl
          have e1' : sigR u (z, w) = (PR u z).map (fun t => (t.1, κ t.2 (u (w, w)))) :=
            sigR_of_sndL h hw
          have e2' : sigL u (z, w) = (QL u w).map (fun t => (κ (u (z, z)) t.1, t.2)) :=
            sigL_of_fstR h hz
          have hpz : ownP u z = PR u z := by simp [ownP, hz]
          have hqw : ownQ u w = QL u w := by simp [ownQ, hw]
          rw [e1, e2, e1', e2', hf, hs, ← hpx, ← hpz, hP, ← hqy, ← hqw, hQ]
        | true =>
          have hw : side w = false := by
            cases hw : side w with
            | false => rfl
            | true => exact absurd (hz.trans hw.symm) hq
          have e1' : sigL u (z, w) = (PL u z).map (fun t => (t.1, κ t.2 (u (w, w)))) :=
            sigL_of_sndR h hw
          have e2' : sigR u (z, w) = (QR u w).map (fun t => (κ (u (z, z)) t.1, t.2)) :=
            sigR_of_fstL h hz
          have hpz : ownP u z = PL u z := by simp [ownP, hz]
          have hqw : ownQ u w = QR u w := by simp [ownQ, hw]
          rw [e1, e2, e1', e2', hf, hs, ← hpx, ← hpz, hP, ← hqy, ← hqw, hQ, add_comm]
      | true =>
        have hy : side y = false := by
          cases hy : side y with
          | false => rfl
          | true => exact absurd (hx.trans hy.symm) hp
        have e1 : sigL u (x, y) = (PL u x).map (fun t => (t.1, κ t.2 (u (y, y)))) :=
          sigL_of_sndR h hy
        have e2 : sigR u (x, y) = (QR u y).map (fun t => (κ (u (x, x)) t.1, t.2)) :=
          sigR_of_fstL h hx
        have hpx : ownP u x = PL u x := by simp [ownP, hx]
        have hqy : ownQ u y = QR u y := by simp [ownQ, hy]
        cases hz : side z with
        | false =>
          have hw : side w = true := by
            cases hw : side w with
            | false => exact absurd (hz.trans hw.symm) hq
            | true => rfl
          have e1' : sigR u (z, w) = (PR u z).map (fun t => (t.1, κ t.2 (u (w, w)))) :=
            sigR_of_sndL h hw
          have e2' : sigL u (z, w) = (QL u w).map (fun t => (κ (u (z, z)) t.1, t.2)) :=
            sigL_of_fstR h hz
          have hpz : ownP u z = PR u z := by simp [ownP, hz]
          have hqw : ownQ u w = QL u w := by simp [ownQ, hw]
          rw [e1, e2, e1', e2', hf, hs, ← hpx, ← hpz, hP, ← hqy, ← hqw, hQ, add_comm]
        | true =>
          have hw : side w = false := by
            cases hw : side w with
            | false => rfl
            | true => exact absurd (hz.trans hw.symm) hq
          have e1' : sigL u (z, w) = (PL u z).map (fun t => (t.1, κ t.2 (u (w, w)))) :=
            sigL_of_sndR h hw
          have e2' : sigR u (z, w) = (QR u w).map (fun t => (κ (u (z, z)) t.1, t.2)) :=
            sigR_of_fstL h hz
          have hpz : ownP u z = PL u z := by simp [ownP, hz]
          have hqw : ownQ u w = QR u w := by simp [ownQ, hw]
          rw [e1, e2, e1', e2', hf, hs, ← hpx, ← hpz, hP, ← hqy, ← hqw, hQ]

/-! ## 7. The consumer -/

/-- The blocked colouring bounds the disjoint union's 2-WL closure **above**. -/
theorem refines_wl2G_of_blocked (h : Blocked A B u κ) :
    PartitionClosure.Refines u (wl2G (dInit A B)) :=
  refines_wl2G_of_stable (stable_of_blocked h) h.atoms

/-- **★★★ THE CONSUMER — a cross-component merge in a single graph.**

If the block colouring gives a left vertex and a right vertex the same colour, then 2-WL on the
**single graph** `A ⊔ B` cannot tell them apart. ⚠ Direction discipline: this carries **merges**
only; a separation under `u` says nothing. -/
theorem merge_of_blocked (h : Blocked A B u κ) {a : V₁} {b : V₂}
    (hab : u (Sum.inl a, Sum.inl a) = u (Sum.inr b, Sum.inr b)) :
    wl2G (dInit A B) (Sum.inl a, Sum.inl a) = wl2G (dInit A B) (Sum.inr b, Sum.inr b) :=
  refines_wl2G_of_blocked h _ _ hab


/-! ## 8. ⚠ Non-vacuity — and it is a **merging** witness, not a discrete one

A `Blocked` predicate with no inhabitant proves nothing, and an inhabitant that merges nothing (the
discrete bound, `FrameEncoding` §5) proves almost nothing. The witness here does merge: it glues
`A ⊔ A` copy-to-copy, so `merge_of_blocked` actually fires on it.

★ Note what is *not* needed: the per-side colouring may be **discrete**. The merge comes from the
block structure alone, which is the point — the cross channel of a disjoint union carries only the
two endpoint diagonal colours, however fine the sides' own runs are. -/

section Witness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Forget which copy a vertex is in. -/
def fold : DV V V → V := Sum.elim id id

omit [Fintype V] [DecidableEq V] in
@[simp] theorem fold_inl (a : V) : fold (Sum.inl a) = a := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem fold_inr (a : V) : fold (Sum.inr a) = a := rfl

/-- The doubling colouring: intra pairs carry `e`'s values on both endpoints, cross pairs carry only
the two endpoint diagonal colours. -/
def dblCol (e : V → Nat) : Col (DV V V × DV V V) := fun p =>
  if side p.1 = side p.2
  then Nat.pair 0 (Nat.pair (e (fold p.1)) (e (fold p.2)))
  else Nat.pair 1 (Nat.pair (Nat.pair 0 (Nat.pair (e (fold p.1)) (e (fold p.1))))
                            (Nat.pair 0 (Nat.pair (e (fold p.2)) (e (fold p.2)))))

omit [Fintype V] [DecidableEq V] in
theorem dblCol_same (e : V → Nat) (x y : DV V V) (h : side x = side y) :
    dblCol e (x, y) = Nat.pair 0 (Nat.pair (e (fold x)) (e (fold y))) := by
  unfold dblCol; rw [if_pos h]

omit [Fintype V] [DecidableEq V] in
theorem dblCol_diag (e : V → Nat) (x : DV V V) :
    dblCol e (x, x) = Nat.pair 0 (Nat.pair (e (fold x)) (e (fold x))) :=
  dblCol_same e x x rfl

omit [Fintype V] [DecidableEq V] in
theorem dblCol_cross (e : V → Nat) (x y : DV V V) (h : ¬ side x = side y) :
    dblCol e (x, y) = Nat.pair 1 (Nat.pair (dblCol e (x, x)) (dblCol e (y, y))) := by
  rw [dblCol_diag, dblCol_diag]
  unfold dblCol; rw [if_neg h]

omit [Fintype V] in
theorem dInit_same (A : V → V → Bool) (x y : DV V V) (h : side x = side y) :
    dInit A A (x, y)
      = Nat.pair (if fold x = fold y then 1 else 0) (if A (fold x) (fold y) then 1 else 0) := by
  rcases x with a | a <;> rcases y with b | b <;> simp [side] at h ⊢ <;>
    simp [dInit, dAdj]

omit [Fintype V] in
theorem dInit_cross (A : V → V → Bool) (x y : DV V V) (h : ¬ side x = side y) :
    dInit A A (x, y) = Nat.pair 0 0 := by
  rcases x with a | a <;> rcases y with b | b <;> simp [side] at h ⊢ <;>
    simp [dInit, dAdj]

/-- **★ `Blocked` is inhabited by a colouring that merges the two copies.** -/
theorem blocked_dblCol (A : V → V → Bool) {e : V → Nat} (he : Function.Injective e) :
    Blocked A A (dblCol e) (fun m n => Nat.pair 1 (Nat.pair m n)) where
  atoms := by
    rintro ⟨x, y⟩ ⟨z, w⟩ hxy
    by_cases h1 : side x = side y <;> by_cases h2 : side z = side w
    · rw [dblCol_same e x y h1, dblCol_same e z w h2] at hxy
      obtain ⟨-, h⟩ := Nat.pair_eq_pair.mp hxy
      obtain ⟨ha, hb⟩ := Nat.pair_eq_pair.mp h
      rw [dInit_same A x y h1, dInit_same A z w h2, he ha, he hb]
    · rw [dblCol_same e x y h1, dblCol_cross e z w h2] at hxy
      exact absurd (Nat.pair_eq_pair.mp hxy).1 (by decide)
    · rw [dblCol_cross e x y h1, dblCol_same e z w h2] at hxy
      exact absurd (Nat.pair_eq_pair.mp hxy).1 (by decide)
    · rw [dInit_cross A x y h1, dInit_cross A z w h2]
  sep := by
    intro x y z w hs hc hcon
    rw [dblCol_same e x y hs, dblCol_cross e z w hc] at hcon
    exact absurd (Nat.pair_eq_pair.mp hcon).1 (by decide)
  endFst := by
    rintro ⟨x, y⟩ ⟨z, w⟩ hxy
    by_cases h1 : side x = side y <;> by_cases h2 : side z = side w
    · rw [dblCol_same e x y h1, dblCol_same e z w h2] at hxy
      obtain ⟨-, h⟩ := Nat.pair_eq_pair.mp hxy
      rw [dblCol_diag, dblCol_diag, (Nat.pair_eq_pair.mp h).1]
    · rw [dblCol_same e x y h1, dblCol_cross e z w h2] at hxy
      exact absurd (Nat.pair_eq_pair.mp hxy).1 (by decide)
    · rw [dblCol_cross e x y h1, dblCol_same e z w h2] at hxy
      exact absurd (Nat.pair_eq_pair.mp hxy).1 (by decide)
    · rw [dblCol_cross e x y h1, dblCol_cross e z w h2] at hxy
      exact (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp hxy).2).1
  endSnd := by
    rintro ⟨x, y⟩ ⟨z, w⟩ hxy
    by_cases h1 : side x = side y <;> by_cases h2 : side z = side w
    · rw [dblCol_same e x y h1, dblCol_same e z w h2] at hxy
      obtain ⟨-, h⟩ := Nat.pair_eq_pair.mp hxy
      rw [dblCol_diag, dblCol_diag, (Nat.pair_eq_pair.mp h).2]
    · rw [dblCol_same e x y h1, dblCol_cross e z w h2] at hxy
      exact absurd (Nat.pair_eq_pair.mp hxy).1 (by decide)
    · rw [dblCol_cross e x y h1, dblCol_same e z w h2] at hxy
      exact absurd (Nat.pair_eq_pair.mp hxy).1 (by decide)
    · rw [dblCol_cross e x y h1, dblCol_cross e z w h2] at hxy
      exact (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp hxy).2).2
  cross := fun x y h => dblCol_cross e x y h
  sideDet := by
    have gen : ∀ v v' : DV V V, side v = side v' →
        ownSig (dblCol e) (v, v') = (Finset.univ : Finset V).val.map
          (fun a => (Nat.pair 0 (Nat.pair (e (fold v)) (e a)),
                     Nat.pair 0 (Nat.pair (e a) (e (fold v'))))) := by
      intro v v' hs
      unfold ownSig
      cases hv : side v with
      | false =>
        have hv' : side v' = false := hs ▸ hv
        show sigR (dblCol e) (v, v') = _
        unfold sigR
        refine Multiset.map_congr rfl (fun a _ => ?_)
        show (dblCol e (v, Sum.inr a), dblCol e (Sum.inr a, v')) = _
        rw [dblCol_same e v (Sum.inr a) hv, dblCol_same e (Sum.inr a) v' hv'.symm]
        simp only [fold_inr]
      | true =>
        have hv' : side v' = true := hs ▸ hv
        show sigL (dblCol e) (v, v') = _
        unfold sigL
        refine Multiset.map_congr rfl (fun a _ => ?_)
        show (dblCol e (v, Sum.inl a), dblCol e (Sum.inl a, v')) = _
        rw [dblCol_same e v (Sum.inl a) hv, dblCol_same e (Sum.inl a) v' hv'.symm]
        simp only [fold_inl]
    rintro ⟨x, y⟩ ⟨z, w⟩ h1 h2 hxy
    rw [dblCol_same e x y h1, dblCol_same e z w h2] at hxy
    obtain ⟨-, h⟩ := Nat.pair_eq_pair.mp hxy
    obtain ⟨ha, hb⟩ := Nat.pair_eq_pair.mp h
    rw [gen x y h1, gen z w h2, he ha, he hb]
  diagEq := by
    unfold diagL diagR
    refine Multiset.map_congr rfl (fun a _ => ?_)
    rw [dblCol_diag, dblCol_diag]
    simp only [fold_inl, fold_inr]

/-- **★★★ 2-WL cannot separate the two copies of `A ⊔ A`** — a genuine cross-component merge in a
single graph, obtained from `merge_of_blocked`. This is the non-vacuity witness for `Blocked`.

⚠ It is *not* a CAO statement: the two copies of `A ⊔ A` **are** in one `Aut`-orbit, so nothing is
mixed here. What it demonstrates is that the interface fires. -/
theorem wl2G_double_merge (A : V → V → Bool) (a : V) :
    wl2G (dInit A A) (Sum.inl a, Sum.inl a) = wl2G (dInit A A) (Sum.inr a, Sum.inr a) := by
  have he : Function.Injective (fun v : V => ((Fintype.equivFin V) v : Nat)) := fun x y h =>
    (Fintype.equivFin V).injective (Fin.val_injective h)
  refine merge_of_blocked (blocked_dblCol A he) ?_
  rw [dblCol_diag, dblCol_diag]
  simp only [fold_inl, fold_inr]

end Witness

end DisjointUnion
end ChainDescent
