import ChainDescent.CaoTarget

/-!
# The frame encoding, and the transfer bound on its 2-WL

(`docs/chain-descent-cao-carrier-falsifiers.md` **§6f**, and §6d.6 for the object. Read §6d.1 first —
it is the *method*, and it is why a **guess** proves an upper bound.)

## What this file is

§6f argues that the frame encoding's WL gain is **bounded by a constant, uniformly in `L`**: `M(G)` is
a fixed-dimension interpretation of `G`, so `2`-WL on `M(G)` cannot exceed bounded-dimension WL on `G`.
That is the step which takes the whole payload search off the critical path — a CFI pair over a large
enough base is then *guaranteed* to merge under `M`, with no computation.

This file builds the object and the transfer skeleton:

| | |
|---|---|
| **§1** | the 2-WL round at a **generic** finite carrier — `CaoTarget.round2` is the `Fin n` case, and `MVert` is a sum type, so forcing it into `Fin n` would be pure index pain |
| **§2** | `MVert`, `mAdj`, `mInit` — the encoding of §6d.6: clique payload, two typed frame vertices per slot, `p(i) ~ f(k, G_k)` |
| **§3** | the **coding** `MVert L → TCode L` into bounded tuples over `Fin L`, and `Adequate` |
| **§4** | ★★★ **the transfer theorem** — an adequate `b` bounds `wl2G (mInit E)` from above, hence carries **merges** |

## ⚠ What is deliberately NOT here

**The bound is not instantiated.** `Adequate.blocks` is exactly §6f's block-sum obligation — *the
multiset over `z : MVert L` of the two half-colours is determined by the pair's own colour* — and
discharging it for `k`-WL on tuples over `Fin L` is the next increment (it needs a tuple-WL layer and
the "multiset over `j` fresh coordinates" lemma). Until then this file proves the **skeleton**, and
`§4`'s theorems are only as strong as the `b` handed to them.

⚠ Per the standing steer, a pinned statement nobody has proved can be false, so `Adequate` is a
hypothesis carried in the open, and §5 records a witness so the skeleton is **not vacuous** — ⚠⚠ that
witness is **degenerate** (discrete), and a discrete `b` merges nothing. The theorems bite only for a
`b` coarse enough to merge; that is the whole point and it is what increment 2 must supply.

## ★ Direction discipline (§6d.1)

The bound says the closure is **coarser** than the guess. A **merge** in the guess forces a merge in
the closure — which is what refutes CAO propagation — while a **separation** in the guess implies
nothing whatever. `merge_of_adequate` is the only consumer form; use it and you cannot get this
backwards.

## ⚠ Three modelling choices, recorded because they are load-bearing

1. **Unfrozen.** §6d.6's model freezes frame–frame pairs at their 12 orbit classes. This file uses the
   **plain** round. Stability against it is *strictly stronger*, and since the unfrozen closure refines
   the frozen one, the frozen conclusion follows by transitivity. It also makes the collapse pin
   **weaker**, hence safer to carry.
2. **Ordered slots.** A slot is an *ordered* pair, so each unordered slot carries two twin frame
   vertices per type. Harmless — twins never separate anything — and it buys free `Fintype`/`DecidableEq`
   instead of a bijection into `Fin N`. ⚠ Degenerate `frm a a t` vertices exist; they form a constant
   perfect matching independent of `E`, so they are inert.
3. **Types are atomic.** `mInit` hands each frame vertex its type `t`. In the ensemble the type is
   *earned* from the individualized central vertex (§6b) rather than given. Handing it makes the
   guess's target **finer**, hence makes the collapse pin **stronger** — the honest direction, and it
   matches what §6d.6's model measures.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`.
-/

namespace ChainDescent
namespace FrameEncoding

open ChainDescent.PartitionClosure
open ChainDescent.CaoTarget (rankOf rankOf_eq_iff)

/-! ## 1. The 2-WL round at a generic carrier

`CaoTarget` builds this at `V = Fin n`; only `pairSig`'s `Finset.univ` mentions the carrier, so the
whole of §2 there transposes verbatim. `rankOf` is already carrier-generic, which is why no encoding
hypothesis appears here either. -/

section GenericRound

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The multiset of triangle types at `p` — the round's entire content, at a generic carrier. -/
def pairSigG (c : Col (V × V)) (p : V × V) : Multiset (Nat × Nat) :=
  (Finset.univ : Finset V).val.map (fun x => (c (p.1, x), c (x, p.2)))

/-- The 2-WL key of a pair: its own colour, then its sorted triangle-type multiset. -/
def pairKeyG (c : Col (V × V)) (p : V × V) : List Nat :=
  c p :: Multiset.sort ((pairSigG c p).map (fun t => Nat.pair t.1 t.2)) (· ≤ ·)

private theorem natPair_inj : Function.Injective (fun t : Nat × Nat => Nat.pair t.1 t.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp h
  simp only [Prod.mk.injEq]
  exact ⟨h1, h2⟩

omit [DecidableEq V] in
theorem pairKeyG_eq_iff (c : Col (V × V)) (p q : V × V) :
    pairKeyG c p = pairKeyG c q ↔ (c p = c q ∧ pairSigG c p = pairSigG c q) := by
  unfold pairKeyG
  rw [List.cons.injEq]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro hsort
    have hmap : (pairSigG c p).map (fun t => Nat.pair t.1 t.2)
        = (pairSigG c q).map (fun t => Nat.pair t.1 t.2) := by
      have := congrArg (fun l : List Nat => (↑l : Multiset Nat)) hsort
      simpa only [Multiset.sort_eq] using this
    exact Multiset.map_injective natPair_inj hmap
  · intro h; rw [h]

/-- **One 2-WL refinement round**, at a generic carrier. -/
def roundG (c : Col (V × V)) : Col (V × V) := rankOf (pairKeyG c)

omit [DecidableEq V] in
theorem roundG_eq_iff (c : Col (V × V)) (p q : V × V) :
    roundG c p = roundG c q ↔ (c p = c q ∧ pairSigG c p = pairSigG c q) :=
  (rankOf_eq_iff _ p q).trans (pairKeyG_eq_iff c p q)

omit [DecidableEq V] in
theorem pairSigG_map_of_factor {c d : Col (V × V)} {g : Nat → Nat} (hg : ∀ p, g (c p) = d p)
    (p : V × V) : pairSigG d p = (pairSigG c p).map (fun t => (g t.1, g t.2)) := by
  unfold pairSigG
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun x _ => ?_)
  show (d (p.1, x), d (x, p.2)) = (g (c (p.1, x)), g (c (x, p.2)))
  rw [hg, hg]

omit [DecidableEq V] in
/-- **The generic 2-WL round is an `IsRound`** — so every FT1 theorem is available at any carrier. -/
theorem isRound_roundG : IsRound (roundG (V := V)) where
  splits := fun c p q h => ((roundG_eq_iff c p q).mp h).1
  mono := by
    intro c d hcd p q h
    obtain ⟨hc, hs⟩ := (roundG_eq_iff c p q).mp h
    obtain ⟨g, hg⟩ := exists_factor hcd
    refine (roundG_eq_iff d p q).mpr ⟨hcd p q hc, ?_⟩
    rw [pairSigG_map_of_factor hg p, pairSigG_map_of_factor hg q, hs]

/-- The 2-WL closure at a generic carrier. -/
def wl2G (c : Col (V × V)) : Col (V × V) := wl roundG c

omit [DecidableEq V] in
/-- **★ The generic form of the method (§6d.1).** A stable guess refining the atoms is refined by
nothing coarser than the closure. -/
theorem refines_wl2G_of_stable {s c : Col (V × V)} (hs : Stable (roundG (V := V)) s)
    (h : PartitionClosure.Refines s c) : PartitionClosure.Refines s (wl2G c) :=
  refines_wl_of_stable isRound_roundG hs h

omit [DecidableEq V] in
/-- ★ **Stability is exactly the signature condition** — the form every consumer below uses. -/
theorem stable_iff_sig {s : Col (V × V)} :
    Stable (roundG (V := V)) s ↔ ∀ p q : V × V, s p = s q → pairSigG s p = pairSigG s q := by
  constructor
  · intro hs p q h; exact ((roundG_eq_iff s p q).mp (hs p q h)).2
  · intro h p q hpq; exact (roundG_eq_iff s p q).mpr ⟨hpq, h p q hpq⟩

end GenericRound

/-! ## 2. The encoding `M(E)` of §6d.6

A payload of `L` labels forming a clique, plus two typed frame vertices per ordered slot, with
`p(i) ~ f(a,b,t)` exactly when `i` is an endpoint of the slot and `t` is the slot's type in `E`. -/

variable {L : Nat}

/-- The carrier of `M(E)`: payload labels, plus a typed vertex per ordered slot. -/
abbrev MVert (L : Nat) : Type := Fin L ⊕ (Fin L × Fin L × Bool)

/-- A payload vertex. -/
abbrev pay (i : Fin L) : MVert L := Sum.inl i

/-- A frame vertex: the type-`t` corner of the ordered slot `(a,b)`. -/
abbrev frm (a b : Fin L) (t : Bool) : MVert L := Sum.inr (a, b, t)

/-- **The encoding's adjacency.** Payload is a clique; a payload vertex meets the frame corner whose
type agrees with `E` on its slot; the two corners of a slot are joined. -/
def mAdj (E : Fin L → Fin L → Bool) : MVert L → MVert L → Bool
  | Sum.inl i, Sum.inl j => i ≠ j
  | Sum.inl i, Sum.inr (a, b, t) => (a ≠ b) && (i == a || i == b) && (E a b == t)
  | Sum.inr (a, b, t), Sum.inl i => (a ≠ b) && (i == a || i == b) && (E a b == t)
  | Sum.inr (a, b, t), Sum.inr (a', b', t') => (a == a') && (b == b') && (t != t')

/-- The sort of a vertex: payload, or frame carrying its type. ⚠ Handing the type atomically is
modelling choice 3 in the header. -/
def sortOf : MVert L → Nat
  | Sum.inl _ => 0
  | Sum.inr (_, _, t) => if t then 1 else 2

/-- **The atomic pair colouring of `M(E)`**: the two sorts, the diagonal flag, and adjacency. -/
def mInit (E : Fin L → Fin L → Bool) : Col (MVert L × MVert L) := fun p =>
  Nat.pair (Nat.pair (sortOf p.1) (sortOf p.2))
    (Nat.pair (if p.1 = p.2 then 1 else 0) (if mAdj E p.1 p.2 then 1 else 0))

/-! ## 3. The coding, and what a bound has to satisfy

§6f codes `M(E)`'s universe inside bounded tuples over `Fin L`: a payload vertex costs one label, a
frame vertex two labels and a bit. `TCode` is that tuple space, tagged by sort so the coding is
injective. -/

/-- The tuple space `M(E)`'s universe is coded into: `(sort, a, b, type)`. -/
abbrev TCode (L : Nat) : Type := Nat × Fin L × Fin L × Bool

/-- **The coding.** A payload vertex spends one label, a frame vertex two and a bit. -/
def code : MVert L → TCode L
  | Sum.inl i => (0, i, i, false)
  | Sum.inr (a, b, t) => (1, a, b, t)

theorem code_injective : Function.Injective (code (L := L)) := by
  rintro (i | ⟨a, b, t⟩) (j | ⟨a', b', t'⟩) h <;> simp only [code, Prod.mk.injEq] at h
  · rw [h.2.1]
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · rw [h.2.1, h.2.2.1, h.2.2.2]

/-- The pullback of a colouring of coded pairs to a colouring of `M(E)`'s pairs. -/
def pull (b : Col (TCode L × TCode L)) : Col (MVert L × MVert L) :=
  fun p => b (code p.1, code p.2)

/-- **★★★ WHAT A BOUND HAS TO SATISFY.** `b` is *adequate* for `E` when its pullback refines the
atoms and is 2-WL-stable on `M(E)`.

⚠ `blocks` **is** §6f's obligation, and it is the whole open content of the transfer: *the multiset
over `z : MVert L` of the two half-colours is determined by the pair's own colour.* Since `z` ranges
over payload **and** frame, discharging it for a `k`-WL `b` means summing over one label and over two
labels plus a bit — which is where §6f's dimension count comes from. `pairSigG_split` below is the
handle that decomposition needs. -/
structure Adequate (E : Fin L → Fin L → Bool) (b : Col (TCode L × TCode L)) : Prop where
  /-- The pullback separates at least as much as the encoding's atoms do. -/
  refinesAtoms : PartitionClosure.Refines (pull b) (mInit E)
  /-- ⛔ **The crux.** Equal pullback colours force equal triangle-type multisets. -/
  blocks : ∀ p q : MVert L × MVert L, pull b p = pull b q → pairSigG (pull b) p = pairSigG (pull b) q

/-- **The decomposition `blocks` has to be checked against.** The sum over `M(E)`'s vertices splits
into a sum over payload labels and a sum over typed slots — one fresh label, then two plus a bit.
This is the concrete handle for the tuple-WL layer, and the source of §6f's dimension count. -/
theorem pairSigG_split (c : Col (MVert L × MVert L)) (p : MVert L × MVert L) :
    pairSigG c p
      = (Finset.univ : Finset (Fin L)).val.map (fun i => (c (p.1, pay i), c (pay i, p.2)))
        + (Finset.univ : Finset (Fin L × Fin L × Bool)).val.map
            (fun w => (c (p.1, Sum.inr w), c (Sum.inr w, p.2))) := by
  unfold pairSigG
  rw [show (Finset.univ : Finset (MVert L)).val
        = ((Finset.univ : Finset (Fin L)).val.map Sum.inl
            + (Finset.univ : Finset (Fin L × Fin L × Bool)).val.map Sum.inr) from rfl]
  rw [Multiset.map_add, Multiset.map_map, Multiset.map_map]
  rfl

/-! ## 4. ★★★ The transfer theorem

Everything above exists so that this is a consequence of FT1's *coarsest stable refinement* and
nothing else. -/

/-- An adequate `b` is 2-WL-stable on `M(E)`. -/
theorem stable_of_adequate {E : Fin L → Fin L → Bool} {b : Col (TCode L × TCode L)}
    (h : Adequate E b) : Stable (roundG (V := MVert L)) (pull b) :=
  stable_iff_sig.mpr h.blocks

/-- **★★★ THE TRANSFER BOUND.** An adequate `b` bounds `M(E)`'s 2-WL closure from above: the closure
is **coarser** than the pullback. No computation on `M(E)` is involved — only stability. -/
theorem refines_wl2G_of_adequate {E : Fin L → Fin L → Bool} {b : Col (TCode L × TCode L)}
    (h : Adequate E b) : PartitionClosure.Refines (pull b) (wl2G (mInit E)) :=
  refines_wl2G_of_stable (stable_of_adequate h) h.refinesAtoms

/-- **★★★ THE ONLY CONSUMER FORM — merges transfer.** If the bound gives two vertices of `M(E)` the
same colour, so does `M(E)`'s 2-WL closure.

★ This is the direction §6d.1 licenses, and the direction the refutation needs: a **merge** in a
bound is a merge in the object. The converse says nothing, which is why `Refines` is never used the
other way round here. -/
theorem merge_of_adequate {E : Fin L → Fin L → Bool} {b : Col (TCode L × TCode L)}
    (h : Adequate E b) {x y : MVert L}
    (hb : b (code x, code x) = b (code y, code y)) :
    wl2G (mInit E) (x, x) = wl2G (mInit E) (y, y) :=
  refines_wl2G_of_adequate h (x, x) (y, y) hb

/-! ## 5. Non-vacuity — ⚠ and why the witness is not enough

The standing steer is that a pinned predicate must be checked against a witness *and* the witness
checked for degeneracy. `Adequate` is inhabited; the witness is discrete, and a discrete bound merges
nothing, so it establishes only that §4 is not vacuous. -/

/-- An injection of the coding space into `Nat`. -/
def encTCode : TCode L → Nat
  | (s, a, b, t) => Nat.pair s (Nat.pair a.val (Nat.pair b.val (if t then 1 else 0)))

theorem encTCode_injective : Function.Injective (encTCode (L := L)) := by
  rintro ⟨s, a, b, t⟩ ⟨s', a', b', t'⟩ h
  simp only [encTCode, Nat.pair_eq_pair] at h
  obtain ⟨hs, ha, hb, ht⟩ := h
  have hab : a = a' := Fin.val_injective ha
  have hbb : b = b' := Fin.val_injective hb
  have htt : t = t' := by cases t <;> cases t' <;> simp_all
  rw [hs, hab, hbb, htt]

/-- The discrete bound. -/
def bDiscrete : Col (TCode L × TCode L) :=
  fun p => Nat.pair (encTCode p.1) (encTCode p.2)

theorem pull_bDiscrete_injective {x y : MVert L × MVert L}
    (h : pull (bDiscrete (L := L)) x = pull bDiscrete y) : x = y := by
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp h
  exact Prod.ext (code_injective (encTCode_injective h1)) (code_injective (encTCode_injective h2))

/-- **⚠ `Adequate` is inhabited — and the witness is DEGENERATE.** The discrete bound is adequate for
every `E`, which shows §4 is not vacuous and **nothing more**: it merges no two vertices, so
`merge_of_adequate` at it has no instances. ▶ The theorems bite only for a `b` coarse enough to merge,
and supplying one is exactly what the `k`-WL instantiation (§6f, next increment) is for. -/
theorem adequate_bDiscrete (E : Fin L → Fin L → Bool) : Adequate E (bDiscrete (L := L)) where
  refinesAtoms := fun x y h => by rw [pull_bDiscrete_injective h]
  blocks := fun p q h => by rw [pull_bDiscrete_injective h]

end FrameEncoding
end ChainDescent
