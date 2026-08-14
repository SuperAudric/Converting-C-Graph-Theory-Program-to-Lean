import ChainDescent.FrameEncoding
import ChainDescent.TupleWL

/-!
# The assembly — discharging `FrameEncoding.Adequate` from a tuple colouring

(`docs/chain-descent-cao-carrier-falsifiers.md` §6f.4a–§6f.4c. Read `FrameEncoding`'s header first for
the direction discipline, and `TupleWL` §4 for why covariance had to go into the round.)

## What this file does

`FrameEncoding` reduced the transfer bound to one clause, `Adequate.blocks`; `TupleWL` proved the two
generic ingredients (`substPair1_of_stableS` for one fresh label, `substPair2_of_stableS` for two).
This file supplies the remaining *plumbing* and closes the clause:

* `mk6` and the four reindexings `σA1 σA2 σB1 σB2` — a coded pair spends four labels, and a fresh
  `z` spends one (payload) or two (frame), so everything lives in a **six-label** tuple;
* `bOf s` — the bounding colouring: a finite **decoration** (both sorts, both type bits) paired with
  `s` at the padded six-tuple;
* `blocks_bOf` / `adequate_bOf` — `Adequate` for `bOf s`, from `roundTS`-stability alone.

★ Composing with `FrameEncoding.merge_of_adequate`: **a merge under a bounded-arity tuple colouring is
a merge in the encoding's 2-WL closure.** That is §6f's bound, machine-checked.

## ⚠ What this does NOT establish

Three things, and none of them is here:

1. **The collapse (i)** — that the *ensemble's* 2-WL is coarser than the encoding's — is open
   mathematically (§6e.4). Without it nothing links `M(E)` to `E(L)`.
2. **CFI's WL-blindness (iii)** is literature, not formalized; it stays a named hypothesis.
3. **The ensemble is not constructed in Lean at all**, so *"`E(L)` has a mixed cell"* is not yet a
   statement about an object.

⟹ what is proved here is the **transfer**, at `k = 2`, and nothing more. ⛔ Do not quote it as a
refutation of CAO propagation.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`.
-/

namespace ChainDescent
namespace FrameTransfer

open ChainDescent.PartitionClosure
open ChainDescent.FrameEncoding
open ChainDescent.TupleWL

variable {L : Nat}

/-! ## 1. Six-label tuples, the four reindexings, and the two updates -/

/-- A six-label tuple, written out. -/
def mk6 (x0 x1 x2 x3 x4 x5 : Fin L) : Tup 6 L := ![x0, x1, x2, x3, x4, x5]

/-- `(P₁, z)` with `z` a **payload** vertex: `z`'s single label lands in both middle slots. -/
def σA1 : Fin 6 → Fin 6 := ![0, 1, 4, 4, 0, 1]
/-- `(z, P₂)` with `z` a **payload** vertex. -/
def σA2 : Fin 6 → Fin 6 := ![4, 4, 2, 3, 4, 4]
/-- `(P₁, z)` with `z` a **frame** vertex: `z`'s two labels land in the middle slots. -/
def σB1 : Fin 6 → Fin 6 := ![0, 1, 4, 5, 0, 1]
/-- `(z, P₂)` with `z` a **frame** vertex. -/
def σB2 : Fin 6 → Fin 6 := ![4, 5, 2, 3, 4, 5]

theorem comp_σA1 (a b c d u v : Fin L) : mk6 a b c d u v ∘ σA1 = mk6 a b u u a b := by
  funext i; fin_cases i <;> rfl

theorem comp_σA2 (a b c d u v : Fin L) : mk6 a b c d u v ∘ σA2 = mk6 u u c d u u := by
  funext i; fin_cases i <;> rfl

theorem comp_σB1 (a b c d u v : Fin L) : mk6 a b c d u v ∘ σB1 = mk6 a b u v a b := by
  funext i; fin_cases i <;> rfl

theorem comp_σB2 (a b c d u v : Fin L) : mk6 a b c d u v ∘ σB2 = mk6 u v c d u v := by
  funext i; fin_cases i <;> rfl

theorem update4 (a b c d u v w : Fin L) :
    Function.update (mk6 a b c d u v) 4 w = mk6 a b c d w v := by
  funext i; fin_cases i <;> simp [mk6, Function.update]

theorem update5 (a b c d u v w : Fin L) :
    Function.update (mk6 a b c d u v) 5 w = mk6 a b c d u w := by
  funext i; fin_cases i <;> simp [mk6, Function.update]

/-! ## 2. The bounding colouring `bOf` -/

/-- The finite decoration of a coded pair: both sorts and both type bits. It is what the tuple cannot
carry, and it is constant across the sums below. -/
def dec (P : TCode L × TCode L) : Nat :=
  Nat.pair (Nat.pair P.1.1 (cond P.1.2.2.2 1 0)) (Nat.pair P.2.1 (cond P.2.2.2.2 1 0))

/-- The four labels of a coded pair, padded to six by repeating the first two. -/
def tup6 (P : TCode L × TCode L) : Tup 6 L :=
  mk6 P.1.2.1 P.1.2.2.1 P.2.2.1 P.2.2.2.1 P.1.2.1 P.1.2.2.1

/-- **The bounding colouring.** Decoration, then the tuple colouring at the padded six-tuple. -/
def bOf (s : Col (Tup 6 L)) : Col (TCode L × TCode L) :=
  fun P => Nat.pair (dec P) (s (tup6 P))

theorem bOf_eq_iff (s : Col (Tup 6 L)) (P Q : TCode L × TCode L) :
    bOf s P = bOf s Q ↔ (dec P = dec Q ∧ s (tup6 P) = s (tup6 Q)) := by
  unfold bOf; exact Nat.pair_eq_pair

/-! ## 3. Rewriting the two sums

`FrameEncoding.pairSigG_split` splits the signature into a payload sum over one fresh label and a
frame sum over two labels plus a bit. §3 puts each in the shape `TupleWL` §5 discharges. -/

private theorem univ_prod_bind {α β γ : Type*} [Fintype α] [Fintype β] (F : α × β → γ) :
    (Finset.univ : Finset (α × β)).val.map F
      = (Finset.univ : Finset α).val.bind
          (fun a => (Finset.univ : Finset β).val.map (fun b => F (a, b))) := by
  have h : (Finset.univ : Finset (α × β)).val
      = (Finset.univ : Finset α).val.bind
          (fun a => (Finset.univ : Finset β).val.map (Prod.mk a)) := rfl
  rw [h, Multiset.map_bind]
  simp only [Multiset.map_map, Function.comp_def]

/-- The decoration of `(P₁, payload)` — independent of which payload vertex. -/
def D1 (p : MVert L × MVert L) : Nat :=
  Nat.pair (Nat.pair (code p.1).1 (cond (code p.1).2.2.2 1 0)) (Nat.pair 0 0)

/-- The decoration of `(payload, P₂)`. -/
def D2 (p : MVert L × MVert L) : Nat :=
  Nat.pair (Nat.pair 0 0) (Nat.pair (code p.2).1 (cond (code p.2).2.2.2 1 0))

/-- The decoration of `(P₁, frame of type `t`)`. -/
def E1 (p : MVert L × MVert L) (t : Bool) : Nat :=
  Nat.pair (Nat.pair (code p.1).1 (cond (code p.1).2.2.2 1 0)) (Nat.pair 1 (cond t 1 0))

/-- The decoration of `(frame of type `t`, P₂)`. -/
def E2 (p : MVert L × MVert L) (t : Bool) : Nat :=
  Nat.pair (Nat.pair 1 (cond t 1 0)) (Nat.pair (code p.2).1 (cond (code p.2).2.2.2 1 0))

/-- **The payload half**, as a map over a ONE-coordinate substitution multiset. -/
theorem payload_sum (s : Col (Tup 6 L)) (p : MVert L × MVert L) :
    (Finset.univ : Finset (Fin L)).val.map
        (fun i => (pull (bOf s) (p.1, pay i), pull (bOf s) (pay i, p.2)))
      = ((Finset.univ : Finset (Fin L)).val.map (fun i =>
          (s (Function.update (tup6 (code p.1, code p.2)) 4 i ∘ σA1),
           s (Function.update (tup6 (code p.1, code p.2)) 4 i ∘ σA2)))).map
        (fun w => (Nat.pair (D1 p) w.1, Nat.pair (D2 p) w.2)) := by
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun i _ => ?_)
  simp only [pull, bOf, tup6, update4, comp_σA1, comp_σA2, Function.comp_apply, code, dec, D1, D2]
  cases p.1 <;> cases p.2 <;> rfl

/-- **The frame half**, as a `bind` over a TWO-coordinate substitution multiset: the two fresh labels
give the multiset, and the type bit contributes a fixed two-element fan-out. -/
theorem frame_sum (s : Col (Tup 6 L)) (p : MVert L × MVert L) :
    (Finset.univ : Finset (Fin L × Fin L × Bool)).val.map
        (fun w => (pull (bOf s) (p.1, Sum.inr w), pull (bOf s) (Sum.inr w, p.2)))
      = Multiset.bind
          (Multiset.join ((Finset.univ : Finset (Fin L)).val.map (fun u =>
            (Finset.univ : Finset (Fin L)).val.map (fun v =>
              (s (Function.update (Function.update (tup6 (code p.1, code p.2)) 4 u) 5 v ∘ σB1),
               s (Function.update (Function.update (tup6 (code p.1, code p.2)) 4 u) 5 v ∘ σB2))))))
          (fun w => (Finset.univ : Finset Bool).val.map
            (fun t => (Nat.pair (E1 p t) w.1, Nat.pair (E2 p t) w.2))) := by
  rw [univ_prod_bind]
  show (Finset.univ : Finset (Fin L)).val.bind _
      = Multiset.bind (Multiset.bind (Finset.univ : Finset (Fin L)).val _) _
  rw [Multiset.bind_assoc]
  refine congrArg _ (funext (fun u => ?_))
  rw [univ_prod_bind]
  show Multiset.bind (Finset.univ : Finset (Fin L)).val _
      = Multiset.bind ((Finset.univ : Finset (Fin L)).val.map _) _
  unfold Multiset.bind
  rw [Multiset.map_map]
  refine congrArg Multiset.join (Multiset.map_congr rfl (fun v _ => ?_))
  simp only [Function.comp_apply]
  refine Multiset.map_congr rfl (fun t _ => ?_)
  simp only [pull, bOf, tup6, update4, update5, comp_σB1, comp_σB2, code, dec, E1, E2]

/-! ## 4. ★★★ `Adequate`, discharged -/

/-- **★★★ THE CRUX, CLOSED.** A `roundTS`-stable tuple colouring satisfies `FrameEncoding`'s open
clause: equal pullback colours force equal 2-WL signatures on the encoding. -/
theorem blocks_bOf {s : Col (Tup 6 L)} (hs : Stable (roundTS (k := 6) (L := L)) s)
    (p q : MVert L × MVert L) (h : pull (bOf s) p = pull (bOf s) q) :
    pairSigG (pull (bOf s)) p = pairSigG (pull (bOf s)) q := by
  obtain ⟨hdec, hs6⟩ := (bOf_eq_iff s _ _).mp h
  have hD1 : D1 p = D1 q := by
    simp only [dec, Nat.pair_eq_pair] at hdec; simp only [D1]; rw [hdec.1.1, hdec.1.2]
  have hD2 : D2 p = D2 q := by
    simp only [dec, Nat.pair_eq_pair] at hdec; simp only [D2]; rw [hdec.2.1, hdec.2.2]
  have hE1 : ∀ t, E1 p t = E1 q t := by
    intro t; simp only [dec, Nat.pair_eq_pair] at hdec; simp only [E1]; rw [hdec.1.1, hdec.1.2]
  have hE2 : ∀ t, E2 p t = E2 q t := by
    intro t; simp only [dec, Nat.pair_eq_pair] at hdec; simp only [E2]; rw [hdec.2.1, hdec.2.2]
  rw [pairSigG_split, pairSigG_split, payload_sum, payload_sum, frame_sum, frame_sum,
    hD1, hD2, substPair1_of_stableS hs hs6 4 σA1 σA2,
    substPair2_of_stableS hs hs6 4 5 σB1 σB2]
  refine congrArg _ (congrArg _ ?_)
  funext w
  exact Multiset.map_congr rfl (fun t _ => by rw [hE1, hE2])

/-- **`Adequate`, from tuple stability.** The atoms clause stays a side condition: it says the tuple
colouring is fine enough to see `E`'s adjacency, and is satisfied by closing an `E`-dependent start
colouring under `roundTS`. -/
theorem adequate_bOf {E : Fin L → Fin L → Bool} {s : Col (Tup 6 L)}
    (hs : Stable (roundTS (k := 6) (L := L)) s)
    (hat : PartitionClosure.Refines (pull (bOf s)) (mInit E)) : Adequate E (bOf s) where
  refinesAtoms := hat
  blocks := blocks_bOf hs

/-- **★★★ THE TRANSFER, END TO END.** A merge under a bounded-arity tuple colouring is a merge in the
encoding's 2-WL closure — §6f's bound, machine-checked. ⛔ Not a refutation of CAO propagation: see
the header's three caveats. -/
theorem merge_of_tuple_merge {E : Fin L → Fin L → Bool} {s : Col (Tup 6 L)}
    (hs : Stable (roundTS (k := 6) (L := L)) s)
    (hat : PartitionClosure.Refines (pull (bOf s)) (mInit E)) {x y : MVert L}
    (hb : bOf s (code x, code x) = bOf s (code y, code y)) :
    wl2G (mInit E) (x, x) = wl2G (mInit E) (y, y) :=
  merge_of_adequate (adequate_bOf hs hat) hb

end FrameTransfer
end ChainDescent
