import ChainDescent.PartitionClosureWL
import ChainDescent.CaoRound

/-!
# FT2 — the 2-WL closure as a function, and the CAO-propagation target stated at it

(`docs/chain-descent-cao-propagation.md` §15.4. Read **§15.0's three statement traps first.**)

## The gap this closes

Until now the target was **not statable in Lean**. `CaoRound` supplies `roundBy` / `iterRoundBy` /
`ext0`, but no stabilization theorem — so *"the 2-WL closure"* was not a function, `CAO` had no
definition, and the crux `hsep` was carried as a hypothesis on an **abstract** `f` with an abstract
`enc` whose injectivity the real refiner does not satisfy (doc R1g).

This file instantiates FT1 at `V = Fin n × Fin n` and gets all of it:

| | |
|---|---|
| `round2` | one 2-WL round, ranked (no `Encodable.encode`, no `enc` hypothesis — **R1g dissolved**) |
| **`isRound_round2`** | it is a `PartitionClosure.IsRound` ⟹ `wl2` converges, is stable, and is **coarsest** |
| **`wl2`** | ★ *the 2-WL closure*, as a function, for the first time |
| `ext c v` | the **one-point extension**: `wl2 (meet c (ptsPair v))` — individualize `v`, re-close |
| **`Propagates`** / **`Separates`** | the target, and its crux, at that object |
| **`propagates_iff_separates`** | ★★★ the reduction, wired to the landed `CaoRound.levelSet_iff_stabOrbit_of_separatesAt` |
| **`ext_comm`** | ★★★ the transposition symmetry — a one-liner from FT1's (K) |

## ⛔ What is NOT here, deliberately

`Separates` itself (doc R1f — the open crux), any per-family certificate (§12.4 R2/R3), and the
refiner swap (§13, suspended). ⛔ Also **not** *"pair classes = orbitals"*: that is full schurity,
measured false at CAO nodes (Shrikhande 3 vs 4; §12.5b's E2 = 477). The target is **fibres only**, and
here that is `v`'s row — which is what `CaoFibring`'s bijection is about.

★ Per §4.2, nothing here concludes *"an automorphism exists"* from a count: `Separates` concludes
**separation**, and the group element comes from the CAO hypothesis via `CaoFibring`.

Axiom target `[propext, Classical.choice, Quot.sound]`.
-/

namespace ChainDescent
namespace CaoTarget

open ChainDescent.PartitionClosure
open ChainDescent.Consume (IsColAut)

variable {n : Nat}

/-- A colouring of **ordered pairs** — the 2-WL carrier. -/
abbrev Col2 (n : Nat) := Col (Fin n × Fin n)

/-! ## 1. Ranking a key

The encode-free trick `Refine.refineRound` uses, extracted so the 2-WL round can reuse it verbatim:
recolour by the **rank of the key** under `Refine.keyLt`. Carrier-generic, so it needs no `Fin n`
structure — and it is why no `enc` hypothesis (R1g) ever appears. -/

section Rank
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The rank of `v`'s key among all keys. -/
def rankOf (k : V → List Nat) (v : V) : Nat :=
  (Finset.univ.filter (fun u => Refine.keyLt (k u) (k v) = true)).card

omit [DecidableEq V] in
theorem rankOf_strict_mono {k : V → List Nat} {v w : V}
    (h : Refine.keyLt (k v) (k w) = true) : rankOf k v < rankOf k w := by
  apply Finset.card_lt_card
  refine ⟨fun u hu => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, Refine.keyLt_trans hu.2 h⟩
  · have hvf : v ∈ Finset.univ.filter (fun u => Refine.keyLt (k u) (k w) = true) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
    have hnotv : v ∉ Finset.univ.filter (fun u => Refine.keyLt (k u) (k v) = true) := by
      rw [Finset.mem_filter]; intro hh
      exact absurd hh.2 (by rw [Refine.keyLt_irrefl]; simp)
    exact hnotv (hsub hvf)

omit [DecidableEq V] in
/-- **The rank has the same partition as the key.** -/
theorem rankOf_eq_iff (k : V → List Nat) (v w : V) : rankOf k v = rankOf k w ↔ k v = k w := by
  constructor
  · intro h
    by_contra hne
    rcases Refine.keyLt_of_ne hne with hlt | hgt
    · exact absurd h (Nat.ne_of_lt (rankOf_strict_mono hlt))
    · exact absurd h.symm (Nat.ne_of_lt (rankOf_strict_mono hgt))
  · intro h
    unfold rankOf
    rw [h]

end Rank

/-! ## 2. The 2-WL round

`pairSig` is the multiset of **triangle types** `(c (a,x), c (x,b))` over intermediate points `x` —
literally `CaoRound.sig`, at `Nat` colours. -/

private theorem map_univ_perm (σ : Equiv.Perm (Fin n)) :
    Multiset.map σ (Finset.univ : Finset (Fin n)).val = (Finset.univ : Finset (Fin n)).val := by
  have h : (Finset.univ : Finset (Fin n)).map σ.toEmbedding = Finset.univ :=
    Finset.map_univ_equiv σ
  calc Multiset.map σ (Finset.univ : Finset (Fin n)).val
      = ((Finset.univ : Finset (Fin n)).map σ.toEmbedding).val := rfl
    _ = (Finset.univ : Finset (Fin n)).val := by rw [h]

/-- The multiset of triangle types at `p` — the round's entire content. -/
def pairSig (c : Col2 n) (p : Fin n × Fin n) : Multiset (Nat × Nat) :=
  (Finset.univ : Finset (Fin n)).val.map (fun x => (c (p.1, x), c (x, p.2)))

/-- The 2-WL key of a pair: its own colour, then its sorted triangle-type multiset. -/
def pairKey (c : Col2 n) (p : Fin n × Fin n) : List Nat :=
  c p :: Multiset.sort ((pairSig c p).map (fun t => Nat.pair t.1 t.2)) (· ≤ ·)

private theorem natPair_injective : Function.Injective (fun t : Nat × Nat => Nat.pair t.1 t.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp h
  simp only [Prod.mk.injEq]
  exact ⟨h1, h2⟩

theorem pairKey_eq_iff (c : Col2 n) (p q : Fin n × Fin n) :
    pairKey c p = pairKey c q ↔ (c p = c q ∧ pairSig c p = pairSig c q) := by
  unfold pairKey
  rw [List.cons.injEq]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro hsort
    have hmap : (pairSig c p).map (fun t => Nat.pair t.1 t.2)
        = (pairSig c q).map (fun t => Nat.pair t.1 t.2) := by
      have := congrArg (fun l : List Nat => (↑l : Multiset Nat)) hsort
      simpa only [Multiset.sort_eq] using this
    exact Multiset.map_injective natPair_injective hmap
  · intro h; rw [h]

/-- **One 2-WL refinement round.** Ranked, so colours stay bounded and no encoding hypothesis
is ever needed. -/
def round2 (c : Col2 n) : Col2 n := rankOf (pairKey c)

theorem round2_eq_iff (c : Col2 n) (p q : Fin n × Fin n) :
    round2 c p = round2 c q ↔ (c p = c q ∧ pairSig c p = pairSig c q) :=
  (rankOf_eq_iff _ p q).trans (pairKey_eq_iff c p q)

/-- Triangle types push forward along a coarsening — the 2-WL analogue of
`PartitionClosure.signature_map_of_factor`, and the substantive half of `mono`. -/
theorem pairSig_map_of_factor {c d : Col2 n} {g : Nat → Nat} (hg : ∀ p, g (c p) = d p)
    (p : Fin n × Fin n) :
    pairSig d p = (pairSig c p).map (fun t => (g t.1, g t.2)) := by
  unfold pairSig
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun x _ => ?_)
  show (d (p.1, x), d (x, p.2)) = (g (c (p.1, x)), g (c (x, p.2)))
  rw [hg, hg]

/-- **★★★ THE 2-WL ROUND IS AN `IsRound`.** Everything FT1 proves is now available at arity 2. -/
theorem isRound_round2 : IsRound (round2 (n := n)) where
  splits := fun c p q h => ((round2_eq_iff c p q).mp h).1
  mono := by
    intro c d hcd p q h
    obtain ⟨hc, hs⟩ := (round2_eq_iff c p q).mp h
    obtain ⟨g, hg⟩ := exists_factor hcd
    refine (round2_eq_iff d p q).mpr ⟨hcd p q hc, ?_⟩
    rw [pairSig_map_of_factor hg p, pairSig_map_of_factor hg q, hs]

/-- ★ **This IS the shipped round.** `pairSig` is `CaoRound.sig` — definitionally — so `round2` is
`CaoRound.roundBy` with the *rank* as its `enc`, and every theorem proved about `CaoRound.sig`
applies to it. -/
theorem pairSig_eq_sig (c : Col2 n) (p : Fin n × Fin n) :
    pairSig c p = CaoRound.sig (fun a b => c (a, b)) p.1 p.2 := rfl

/-- **★★ A STABLE COLOURING IS COHERENT.** `PartitionClosure.Stable` at `round2` is exactly
`CaoRound.Coherent` — equal colours force equal triangle-type multisets.

⟹ the **landed barriers** (`CaoRound.round1_barrier`, `round2_barrier_real`), whose hypothesis is
`Coherent`, apply verbatim to `wl2`'s output. That is the wiring FT2 exists for: the crux is pinned to
round 3 at the *real* object, not at an abstract `f`. -/
theorem coherent_of_stable {c : Col2 n} (hs : Stable (round2 (n := n)) c) :
    CaoRound.Coherent (fun a b => c (a, b)) := fun a b a' b' h =>
  ((round2_eq_iff c (a, b) (a', b')).mp (hs (a, b) (a', b') h)).2

/-- **★ THE 2-WL CLOSURE**, as a function. `n²` rounds, which is `Fintype.card (Fin n × Fin n)`. -/
def wl2 (c : Col2 n) : Col2 n := wl round2 c

theorem wl2_stable (c : Col2 n) : Stable (round2 (n := n)) (wl2 c) := wl_stable isRound_round2 c

/-- **The 2-WL closure is COHERENT** — the form the barriers consume. -/
theorem coherent_wl2 (c : Col2 n) : CaoRound.Coherent (fun a b => wl2 c (a, b)) :=
  coherent_of_stable (wl2_stable c)

theorem wl2_refines (c : Col2 n) : PartitionClosure.Refines (wl2 c) c := wl_refines isRound_round2 c

/-- **The 2-WL closure is the COARSEST 2-WL-stable refinement.** -/
theorem refines_wl2_of_stable {s c : Col2 n} (hs : Stable (round2 (n := n)) s)
    (h : PartitionClosure.Refines s c) : PartitionClosure.Refines s (wl2 c) := refines_wl_of_stable isRound_round2 hs h

/-! ## 3. Individualization at the pair level

★ Individualizing `v` is a **meet with a partition** — exactly the `ρ` FT1 quantifies over. That is
what makes §5's transposition theorem a one-liner instead of an induction. -/

/-- The partition that marks `v` in each coordinate. `CaoRound.ext0`'s two flags, as a `Col2`. -/
def ptsPair (v : Fin n) : Col2 n :=
  fun p => Nat.pair (if p.1 = v then 1 else 0) (if p.2 = v then 1 else 0)

/-- **The one-point extension `X_v`**: individualize `v`, then re-close. -/
def ext (c : Col2 n) (v : Fin n) : Col2 n := wl2 (meet c (ptsPair v))

/-- The 2-WL start colouring of a graph: adjacency plus the diagonal flag. -/
def initCol2 (adj : AdjMatrix n) : Col2 n :=
  fun p => Nat.pair (adj.adj p.1 p.2) (if p.1 = p.2 then 1 else 0)

/-- The root 2-WL closure of a graph. -/
def rootPair (adj : AdjMatrix n) : Col2 n := wl2 (initCol2 adj)

/-! ## 4. Invariance

Everything in this section is bookkeeping: the closure inherits whatever symmetry the start has. It is
needed because `CaoRound`'s Step 2 asks for `PairInvariantAt`. -/

/-- `c` is invariant under relabelling by `σ`. -/
def Inv2 (σ : Equiv.Perm (Fin n)) (c : Col2 n) : Prop := ∀ p : Fin n × Fin n, c (σ p.1, σ p.2) = c p

theorem pairSig_congr {σ : Equiv.Perm (Fin n)} {c : Col2 n} (h : Inv2 σ c) (p : Fin n × Fin n) :
    pairSig c (σ p.1, σ p.2) = pairSig c p := by
  unfold pairSig
  calc (Finset.univ : Finset (Fin n)).val.map (fun x => (c (σ p.1, x), c (x, σ p.2)))
      = (Multiset.map σ (Finset.univ : Finset (Fin n)).val).map
          (fun x => (c (σ p.1, x), c (x, σ p.2))) := by rw [map_univ_perm σ]
    _ = (Finset.univ : Finset (Fin n)).val.map
          (fun y => (c (σ p.1, σ y), c (σ y, σ p.2))) := by rw [Multiset.map_map]; rfl
    _ = (Finset.univ : Finset (Fin n)).val.map (fun y => (c (p.1, y), c (y, p.2))) := by
          refine Multiset.map_congr rfl (fun y _ => ?_)
          rw [h (p.1, y), h (y, p.2)]

/-- **A round preserves invariance.** -/
theorem inv2_round2 {σ : Equiv.Perm (Fin n)} {c : Col2 n} (h : Inv2 σ c) : Inv2 σ (round2 c) := by
  intro p
  have hkey : pairKey c (σ p.1, σ p.2) = pairKey c p := by
    refine (pairKey_eq_iff c _ _).mpr ⟨h p, pairSig_congr h p⟩
  show rankOf (pairKey c) (σ p.1, σ p.2) = rankOf (pairKey c) p
  unfold rankOf
  rw [hkey]

theorem inv2_iterate {σ : Equiv.Perm (Fin n)} : ∀ (k : Nat) {c : Col2 n}, Inv2 σ c →
    Inv2 σ ((round2 (n := n))^[k] c)
  | 0, _, h => h
  | k + 1, c, h => by
      rw [Function.iterate_succ_apply']
      exact inv2_round2 (inv2_iterate k h)

theorem inv2_wl2 {σ : Equiv.Perm (Fin n)} {c : Col2 n} (h : Inv2 σ c) : Inv2 σ (wl2 c) :=
  inv2_iterate _ h

theorem inv2_meet {σ : Equiv.Perm (Fin n)} {c d : Col2 n} (hc : Inv2 σ c) (hd : Inv2 σ d) :
    Inv2 σ (meet c d) := fun p => by
  show Nat.pair (c (σ p.1, σ p.2)) (d (σ p.1, σ p.2)) = Nat.pair (c p) (d p)
  rw [hc p, hd p]

/-- The mark is invariant under anything fixing `v` — the only place `σ v = v` is used. -/
theorem inv2_ptsPair {σ : Equiv.Perm (Fin n)} {v : Fin n} (hv : σ v = v) : Inv2 σ (ptsPair v) := by
  intro p
  have key : ∀ x : Fin n, (if σ x = v then 1 else 0) = (if x = v then 1 else 0) := by
    intro x
    by_cases hx : x = v
    · simp [hx, hv]
    · have : σ x ≠ v := by rw [← hv]; exact fun he => hx (σ.injective he)
      simp [hx, this]
  show Nat.pair (if σ p.1 = v then 1 else 0) (if σ p.2 = v then 1 else 0)
      = Nat.pair (if p.1 = v then 1 else 0) (if p.2 = v then 1 else 0)
  rw [key p.1, key p.2]

/-- **The extension inherits the stabilizer's symmetry.** -/
theorem inv2_ext {σ : Equiv.Perm (Fin n)} {c : Col2 n} {v : Fin n} (hc : Inv2 σ c) (hv : σ v = v) :
    Inv2 σ (ext c v) := inv2_wl2 (inv2_meet hc (inv2_ptsPair hv))

/-- `c` is invariant under the whole colour-preserving automorphism group — what the root closure of a
coloured node satisfies. -/
def PairInv (adj : AdjMatrix n) (χ : Colouring n) (c : Col2 n) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → Inv2 σ c

/-- The bridge to `CaoRound`'s hypothesis. -/
theorem pairInvariantAt_ext {adj : AdjMatrix n} {χ : Colouring n} {c : Col2 n}
    (hc : PairInv adj χ c) (v : Fin n) :
    CaoRound.PairInvariantAt adj χ v (fun a b => ext c v (a, b)) := by
  intro σ hσ hv a b
  exact inv2_ext (hc σ hσ) hv (a, b)

/-! ## 5. ★★★ The target, and its crux

`Propagates` is the doc's §2 statement at the object the algorithm would build. `Separates` is the
crux (§12.3 / R1f). ⚠ Both are stated on **`v`'s row** — that is the object `CaoFibring`'s bijection
`{K-orbitals in D × C} ≃ {K_v-orbits on C}` is about, and it is *fibre* accuracy, **not** schurity. -/

/-- **THE TARGET.** After individualizing `v` and re-closing, `v`'s row classes are **exactly** the
orbits of the point stabilizer `K_v` — *"CAO in, CAO out"*. -/
def Propagates (adj : AdjMatrix n) (χ : Colouring n) (c : Col2 n) : Prop :=
  ∀ v u w : Fin n, ext c v (v, u) = ext c v (v, w) ↔ CaoFibring.SameStabOrbit adj χ v u w

/-- **THE CRUX** (doc §12.3, R1f) — the one implication that is not free. Per §4.2 this is a
*separation* statement; the group element is produced by `CaoFibring`, never by a count. -/
def Separates (adj : AdjMatrix n) (χ : Colouring n) (c : Col2 n) : Prop :=
  ∀ v u w : Fin n, ext c v (v, u) = ext c v (v, w) → CaoFibring.SameStabOrbit adj χ v u w

/-- **★★★ THE REDUCTION, AT THE REAL OBJECT.** The target is *equivalent* to the crux — the converse
half (an orbit never gets split) is free from invariance alone.

This is what the project previously had only as `CaoRound.step2_closure`, a statement about an
abstract `f` with an abstract `enc`. Here `f` is `ext c v`, a function, built by `round2`. -/
theorem propagates_iff_separates {adj : AdjMatrix n} {χ : Colouring n} {c : Col2 n}
    (hc : PairInv adj χ c) : Propagates adj χ c ↔ Separates adj χ c := by
  constructor
  · intro h v u w hbase; exact (h v u w).mp hbase
  · intro h v u w
    exact CaoRound.levelSet_iff_stabOrbit_of_separatesAt (pairInvariantAt_ext hc v) (h v) u w

/-- **Soundness is unconditional** — the half that never needed a hypothesis: an orbit of `K_v` is
never split by the extension. -/
theorem ext_eq_of_sameStabOrbit {adj : AdjMatrix n} {χ : Colouring n} {c : Col2 n}
    (hc : PairInv adj χ c) {v u w : Fin n} (h : CaoFibring.SameStabOrbit adj χ v u w) :
    ext c v (v, u) = ext c v (v, w) :=
  CaoRound.pairInvariantAt_eq_of_sameStabOrbit (pairInvariantAt_ext hc v) h

/-! ## 6. ★★★ Where CAO enters — and the transposition symmetry

Two consequences of FT1 that were the reason to build it. -/

/-- **CAO makes `v`'s row a complete transversal of the orbitals.** This is `CaoFibring`'s
`exists_row_transport`, and it is the *only* place the CAO hypothesis is consumed: it is what makes
the row-form of `Propagates` say something about **every** cell rather than just `v`'s.

`Deepen.CellSingleOrbit adj χ (χ v)` is the shipped predicate — "`v`'s cell is one orbit". -/
theorem row_complete_of_cao {adj : AdjMatrix n} {χ : Colouring n} {v : Fin n}
    (hD : Deepen.CellSingleOrbit adj χ (χ v)) (a b : Fin n) (ha : χ a = χ v) :
    ∃ u : Fin n, CaoFibring.SameOrbital adj χ a b v u ∧ χ u = χ b :=
  CaoFibring.exists_row_transport hD ha b

/-- **★★★ THE TRANSPOSITION SYMMETRY.** Individualizing `u` then `v` and individualizing `v` then `u`
reach the **same** 2-WL closure.

⟹ *the CAO-propagation target is a fixed point of transposition*, which is exactly why the doc's §4.1
coset transfer is circular (*"the `Aut_u`-orbits on `D` are the transpose of what is being proved"*),
and why §12.5a's **R1b** (base-point uniformity) is a theorem rather than a measurement.

⟹ **no argument reading only `u` and `v` can break the tie: a proof must consume a third point.** That
is the doc §15.3 arity-3 reading, and it is one line from FT1's (K). -/
theorem ext_comm (c : Col2 n) (u v : Fin n) :
    SamePart (ext (ext c u) v) (ext (ext c v) u) :=
  closure_meet_comm isRound_round2 c (ptsPair u) (ptsPair v)

/-- The two-step extension collapses: the intermediate closure is worth nothing beyond the final one,
so *"individualize `{u,v}`"* is a single meet. -/
theorem ext_collapse (c : Col2 n) (u v : Fin n) :
    SamePart (ext (ext c u) v) (wl2 (meet (meet c (ptsPair u)) (ptsPair v))) :=
  closure_collapse isRound_round2 c (ptsPair u) (ptsPair v)

end CaoTarget
end ChainDescent
