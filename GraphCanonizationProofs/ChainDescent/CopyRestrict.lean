import ChainDescent.Ensemble

/-!
# (LB) — the ensemble's colouring, restricted to one copy, refines that copy's own 2-WL

(`docs/chain-descent-cao-carrier-falsifiers.md` §6e.4d.1 and §6e.4g **item 2**; §6b for the
encoded-edge readout.)

## What this file is for

The carrier track is stuck on a two-way disjunction — (A) the cross-copy channel supplies the
`S_L`-orbit, so Construction C dies; (B) it supplies nothing the within-copy channel cannot, so the
construction works. (A)'s **engine** is `RulerLemma.ruler`, machine-checked and carrier-generic. (A)'s
**single load-bearing structural claim** is `(LB)`:

> the ensemble's stable pair colouring, restricted to the payload vertices of one copy, refines that
> copy's own bare 2-WL closure

— because `(P1)` (*the tag isolates a refinement-discrete copy*) and `(P2)` (*such a copy's slot
profile is injective*) are read off from it, and they are exactly the Ruler Lemma's two hypotheses.
Until this pass `(LB)` was proved on paper and **measured only at `L = 4`** (`probe_cao_lowerbound.py`,
64/64 copies). It is now a theorem, at every `L`, at the real object `Ensemble.eRoot`.

⚠⚠ **This does not decide the disjunction.** `(LB)` is a *lower* bound: it says the ensemble sees at
least what one copy sees on its own. (A) additionally needs `(P1)`/`(P2)` (§6e.4g item 3) and the
coherence chain of §6e.4d.3. What `(LB)` does remove is (B)'s cheapest possible escape — *"the
ensemble's uniform averaging washes the within-copy structure out"*. It does not.

## The three ingredients, and which one was the actual work

| | |
|---|---|
| **§1** | ★★★ **restriction of stability** — carrier-generic. If a colour predicate cuts a sub-carrier out of the WL sum, the restricted colouring is stable. This is the *"E-stability restricts"* step, and it is the only genuinely new lemma here |
| **§2** | the individualized centre is the **unique** sort-3 vertex, so `col_E(u,v)` determines `col_E(u, m(base))` — the singleton case of §1. ⟹ **a frame vertex's type is readable from any pair colour it occurs in** |
| **§3** | ★ **§6b at the object**: within a copy, `col_E(p(c,i), p(c,j))` determines the *encoded* edge `c(i,j)`. Proof: the frame corner both endpoints meet has type `c(i,j)`, and §2 reads that type off |
| **§4** | `(LB)` itself, by `FrameEncoding.refines_wl2G_of_stable` |

★ Note what §1 does **not** assume: nothing about the ensemble, no equivariance, no group. The
sub-carrier only has to be recognisable *from the colouring itself*, which is what makes the step
non-circular — the recognition is bought by the atoms (payload cliques are adjacent within a copy and
non-adjacent across copies), never by the completeness the disjunction is about.

## ⚠ Two modelling notes that bound what may be quoted

1. **Ordered slots** (`Ensemble`'s note 1). §3 recovers the type of *some* frame corner joining `i`
   and `j`, and there are two — `(i,j)` and `(j,i)`. So the encoded edge is pinned only for copies
   satisfying `SymCopy`, which is the faithful reading of the doc's unordered slots. Every theorem
   below that needs it carries it explicitly.
2. **`(LB)` is stated against the copy's `wl2G`, not against its `Aut`-orbits.** That is the honest
   direction: it is a lower bound on the ensemble, so it cannot be weakened by the ensemble being
   larger, coarser elsewhere, or more symmetric. ⛔ It says nothing whatever about whether a *mixed
   cell* exists — see the doc's §6e.4e.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
no `native_decide`.
-/

namespace ChainDescent
namespace CopyRestrict

open ChainDescent.PartitionClosure
open ChainDescent.FrameEncoding
open ChainDescent.Ensemble

/-! ## 1. ★★★ Restriction of stability to a colour-definable sub-carrier -/

section Restrict

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem filter_map_comm {α β : Type*} (f : α → β) (P : β → Prop) [DecidablePred P]
    (m : Multiset α) :
    Multiset.filter P (m.map f) = (m.filter (fun a => P (f a))).map f := by
  refine Multiset.induction_on m (by simp) (fun a m ih => ?_)
  by_cases h : P (f a) <;> simp [h, ih]

/-- The triangle-type multiset, cut down to the `z` whose half-colour satisfies `P`. -/
theorem filter_pairSigG (s : Col (V × V)) (P : Nat → Bool) (u v : V) :
    Multiset.filter (fun t => P t.1 = true) (pairSigG s (u, v))
      = (((Finset.univ : Finset V).filter (fun z => P (s (u, z)) = true)).val).map
          (fun z => (s (u, z), s (z, v))) := by
  rw [pairSigG, filter_map_comm, Finset.filter_val]

/-- ★ **The restricted signature.** If `P` recognises exactly the image of an injection `ι`, the
filtered triangle-type multiset *is* the signature computed inside the sub-carrier. -/
theorem sig_restrict {W : Type*} [Fintype W] [DecidableEq W]
    (s : Col (V × V)) (P : Nat → Bool) (ι : W → V) (hinj : Function.Injective ι) (u v : V)
    (hP : ∀ z : V, (P (s (u, z)) = true) ↔ ∃ y, ι y = z) :
    Multiset.filter (fun t => P t.1 = true) (pairSigG s (u, v))
      = (Finset.univ : Finset W).val.map (fun y => (s (u, ι y), s (ι y, v))) := by
  have hset : (Finset.univ : Finset V).filter (fun z => P (s (u, z)) = true)
      = Finset.map ⟨ι, hinj⟩ Finset.univ := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    exact hP z
  rw [filter_pairSigG, hset, Finset.map_val, Multiset.map_map]
  rfl

/-- The singleton case: `P` picks out one vertex, so the pair colour determines the two half-colours
against it. -/
theorem sig_singleton (s : Col (V × V)) (P : Nat → Bool) (u v : V) (z₀ : V)
    (hP : ∀ z : V, (P (s (u, z)) = true) ↔ z = z₀) :
    Multiset.filter (fun t => P t.1 = true) (pairSigG s (u, v)) = {(s (u, z₀), s (z₀, v))} := by
  have hset : (Finset.univ : Finset V).filter (fun z => P (s (u, z)) = true) = {z₀} := by
    ext z; simpa using hP z
  rw [filter_pairSigG, hset]
  rfl

/-- ★★★ **STABILITY RESTRICTS.** Two pairs with the same colour have the same *restricted* signature,
even when the two sub-carriers are different — which is the form §4 needs, since two copies are
different sub-carriers of the same ensemble. -/
theorem restrict_sig_eq {W : Type*} [Fintype W] [DecidableEq W] {s : Col (V × V)}
    (hs : Stable (roundG (V := V)) s) (P : Nat → Bool)
    {ι κ : W → V} (hι : Function.Injective ι) (hκ : Function.Injective κ) {u v u' v' : V}
    (hp : ∀ z : V, (P (s (u, z)) = true) ↔ ∃ y, ι y = z)
    (hq : ∀ z : V, (P (s (u', z)) = true) ↔ ∃ y, κ y = z)
    (h : s (u, v) = s (u', v')) :
    (Finset.univ : Finset W).val.map (fun y => (s (u, ι y), s (ι y, v)))
      = (Finset.univ : Finset W).val.map (fun y => (s (u', κ y), s (κ y, v'))) := by
  rw [← sig_restrict s P ι hι u v hp, ← sig_restrict s P κ hκ u' v' hq]
  exact congrArg _ (stable_iff_sig.mp hs (u, v) (u', v') h)

end Restrict

/-! ## 2. Decoding the ensemble's atoms, and the individualized centre -/

variable {L : Nat}

/-- The ensemble's closure is stable. -/
theorem eRoot_stable : Stable (roundG (V := EVert L)) (eRoot L) :=
  wl_stable isRound_roundG _

/-- The ensemble's closure refines its atoms. -/
theorem eRoot_refines : PartitionClosure.Refines (eRoot L) (eInit L) :=
  wl_refines isRound_roundG _

/-- second sort, from an `eInit` value -/
def dSort2 (n : Nat) : Nat := (Nat.unpair (Nat.unpair n).1).2
/-- diagonal flag, from an `eInit` value -/
def dEq (n : Nat) : Nat := (Nat.unpair (Nat.unpair n).2).1
/-- adjacency flag, from an `eInit` value -/
def dAdj (n : Nat) : Nat := (Nat.unpair (Nat.unpair n).2).2

@[simp] theorem dSort2_eInit (p : EVert L × EVert L) : dSort2 (eInit L p) = esort p.2 := by
  simp [dSort2, eInit]

@[simp] theorem dEq_eInit (p : EVert L × EVert L) :
    dEq (eInit L p) = (if p.1 = p.2 then 1 else 0) := by
  simp [dEq, eInit]

@[simp] theorem dAdj_eInit (p : EVert L × EVert L) :
    dAdj (eInit L p) = (if eAdj p.1 p.2 then 1 else 0) := by
  simp [dAdj, eInit]

/-- Equal closure colours force equal adjacency. -/
theorem eAdj_eq_of_eRoot_eq {p q : EVert L × EVert L} (h : eRoot L p = eRoot L q) :
    eAdj p.1 p.2 = eAdj q.1 q.2 := by
  have h2 : dAdj (eInit L p) = dAdj (eInit L q) := congrArg dAdj (eRoot_refines p q h)
  rw [dAdj_eInit, dAdj_eInit] at h2
  cases hp : eAdj p.1 p.2 <;> cases hq : eAdj q.1 q.2 <;> simp_all

/-- Equal closure colours force the same diagonal flag. -/
theorem diag_eq_of_eRoot_eq {p q : EVert L × EVert L} (h : eRoot L p = eRoot L q) :
    (p.1 = p.2) ↔ (q.1 = q.2) := by
  have h2 : dEq (eInit L p) = dEq (eInit L q) := congrArg dEq (eRoot_refines p q h)
  rw [dEq_eInit, dEq_eInit] at h2
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;> simp_all

/-- Equal closure colours force the same second sort. -/
theorem sort2_eq_of_eRoot_eq {p q : EVert L × EVert L} (h : eRoot L p = eRoot L q) :
    esort p.2 = esort q.2 := by
  have h2 : dSort2 (eInit L p) = dSort2 (eInit L q) := congrArg dSort2 (eRoot_refines p q h)
  rwa [dSort2_eInit, dSort2_eInit] at h2

/-- **The individualized centre is the unique vertex of sort 3.** -/
theorem esort_eq_three_iff (z : EVert L) : esort z = 3 ↔ z = ecen (ebase L) := by
  rcases z with ⟨c, i⟩ | ⟨k, t⟩ | g
  · simp [esort]
  · simp [esort]
  · by_cases hg : g = ebase L <;> simp [esort, hg]

/-- ★ **The centre readout.** Because `m(base)` is the only sort-3 vertex, a pair's colour determines
both of its colours against `m(base)`. This is `sig_singleton` at the ensemble, and it is what makes a
frame vertex's *type* readable — the type is exactly adjacency to `m(base)`. -/
theorem centre_readout {u v u' v' : EVert L} (h : eRoot L (u, v) = eRoot L (u', v')) :
    eRoot L (u, ecen (ebase L)) = eRoot L (u', ecen (ebase L)) ∧
      eRoot L (ecen (ebase L), v) = eRoot L (ecen (ebase L), v') := by
  obtain ⟨g, hg⟩ := exists_factor (eRoot_refines (L := L))
  set P : Nat → Bool := fun n => decide (dSort2 (g n) = 3) with hPdef
  have hP : ∀ (w : EVert L) (z : EVert L), (P (eRoot L (w, z)) = true) ↔ z = ecen (ebase L) := by
    intro w z
    have : P (eRoot L (w, z)) = decide (esort z = 3) := by
      rw [hPdef]; simp only [hg (w, z), dSort2_eInit]
    rw [this, decide_eq_true_iff]
    exact esort_eq_three_iff z
  have h1 := sig_singleton (eRoot L) P u v (ecen (ebase L)) (hP u)
  have h2 := sig_singleton (eRoot L) P u' v' (ecen (ebase L)) (hP u')
  have hsig : Multiset.filter (fun t => P t.1 = true) (pairSigG (eRoot L) (u, v))
      = Multiset.filter (fun t => P t.1 = true) (pairSigG (eRoot L) (u', v')) :=
    congrArg _ (stable_iff_sig.mp eRoot_stable (u, v) (u', v') h)
  rw [h1, h2] at hsig
  have := Multiset.singleton_inj.mp hsig
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- ★★ **A frame vertex's type is readable from any pair colour it heads.** The type is precisely
adjacency to the individualized centre, and §2's readout delivers that. -/
theorem frame_type_eq {k k' : ESlot L} {t t' : Bool} {v v' : EVert L}
    (h : eRoot L (efrm k t, v) = eRoot L (efrm k' t', v')) : t = t' := by
  have h1 := (centre_readout h).1
  have h2 := eAdj_eq_of_eRoot_eq h1
  simp only [eAdj, ebase] at h2
  cases t <;> cases t' <;> simp_all

/-! ## 3. ★ §6b at the object — the encoded edge is readable inside a copy

A payload vertex `p(c,i)` and the frame corner `f((i,j), c(i,j))` are adjacent exactly when `i` is an
endpoint of the slot and the corner carries the copy's type there. So for `i ≠ j` **both** endpoints
meet that one corner, its contribution sits in the pair's triangle-type multiset, and §2 reads its
type — which *is* the encoded edge. -/

/-- The copy `c`'s own graph on `Fin L`: the encoded adjacency, no self-loops. -/
def hAdj (c : EColr L) (i j : Fin L) : Bool := decide (i ≠ j) && c.val (i, j)

/-- ⚠ Slots are **ordered** in this model (`Ensemble`'s note 1), so the two corners joining `i` and
`j` sit on the slots `(i,j)` and `(j,i)`. Pinning *the* encoded edge therefore needs the copy to agree
on the two. ✅ Since 2026-08-16c an `Ensemble.EColr` **is** a graph, so this holds of every copy
(`symCopy_all`); the hypothesis is kept in signatures so they still state what they use. -/
def SymCopy (c : EColr L) : Prop := ∀ a b : Fin L, c.val (a, b) = c.val (b, a)

/-- ✅ **Now automatic** — a copy *is* a graph (`Ensemble.EColr`), so the hypothesis every theorem
below carries is discharged once and for all. ⚠ The hypotheses are kept in the signatures so the
statements still say what they depend on. -/
theorem symCopy_all (c : EColr L) : SymCopy c := c.2.1

theorem esort_eq_one_iff (z : EVert L) : esort z = 1 ↔ ∃ k t, z = efrm k t := by
  rcases z with ⟨c, i⟩ | ⟨k, t⟩ | g
  · simp [esort]
  · exact ⟨fun _ => ⟨k, t, rfl⟩, fun _ => rfl⟩
  · by_cases hg : g = ebase L <;> simp [esort, hg]

/-- ★★ **§6b, at the real object.** Within a copy the closure's pair colour determines the *encoded*
edge — not merely the payload clique's edge, which is constant. This is what makes *"the copy's own
2-WL"* the right lower bound in §4. -/
theorem encoded_edge_eq {c c' : EColr L} (hsym : SymCopy c') {i j i' j' : Fin L}
    (hij : i ≠ j) (hij' : i' ≠ j')
    (h : eRoot L (epay c i, epay c j) = eRoot L (epay c' i', epay c' j')) :
    c.val (i, j) = c'.val (i', j') := by
  set z₀ : EVert L := efrm (i, j) (c.val (i, j)) with hz₀
  -- the corner both endpoints meet
  have hadj1 : eAdj (epay c i) z₀ = true := by
    simp [hz₀, eAdj, inSlot, hij]
  have hadj2 : eAdj z₀ (epay c j) = true := by
    simp [hz₀, eAdj, inSlot, hij, Ne.symm hij]
  -- its contribution sits in the triangle-type multiset, hence in the other pair's
  have hmem : (eRoot L (epay c i, z₀), eRoot L (z₀, epay c j))
      ∈ pairSigG (eRoot L) (epay c i, epay c j) :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ z₀)
  rw [stable_iff_sig.mp eRoot_stable _ _ h] at hmem
  obtain ⟨z, -, hz⟩ := Multiset.mem_map.1 hmem
  have hz1 : eRoot L (epay c' i', z) = eRoot L (epay c i, z₀) := congrArg Prod.fst hz
  have hz2 : eRoot L (z, epay c' j') = eRoot L (z₀, epay c j) := congrArg Prod.snd hz
  -- `z` is a frame vertex
  have hsz : esort z = 1 := by
    have := sort2_eq_of_eRoot_eq (p := (epay c' i', z)) (q := (epay c i, z₀)) hz1
    simpa [hz₀, esort] using this
  obtain ⟨k, t, rfl⟩ := (esort_eq_one_iff z).mp hsz
  -- it is adjacent to both endpoints of the other pair
  have ha1 : eAdj (epay c' i') (efrm k t) = true := by
    have := eAdj_eq_of_eRoot_eq (p := (epay c' i', efrm k t)) (q := (epay c i, z₀)) hz1
    simpa [hadj1] using this
  have ha2 : eAdj (efrm k t) (epay c' j') = true := by
    have := eAdj_eq_of_eRoot_eq (p := (efrm k t, epay c' j')) (q := (z₀, epay c j)) hz2
    simpa [hadj2] using this
  have hki' : (k.1 ≠ k.2 ∧ (i' = k.1 ∨ i' = k.2)) ∧ c'.val k = t := by
    simpa [eAdj, inSlot, Bool.and_eq_true, decide_eq_true_iff] using ha1
  have hkj' : (k.1 ≠ k.2 ∧ (j' = k.1 ∨ j' = k.2)) := by
    have := ha2
    simp only [eAdj, Bool.and_eq_true, decide_eq_true_iff] at this
    simpa [inSlot, decide_eq_true_iff] using this.1
  -- §2 reads its type, which is the encoded edge of the first copy
  have ht : t = c.val (i, j) := frame_type_eq (v := epay c' j') (v' := epay c j) hz2
  -- ordered slots: the corner sits on `(i',j')` or on `(j',i')`, and `SymCopy` closes the gap
  have hk : c'.val k = c'.val (i', j') := by
    obtain ⟨⟨-, hi1⟩, -⟩ := hki'
    obtain ⟨-, hj1⟩ := hkj'
    rcases hi1 with hi1 | hi1 <;> rcases hj1 with hj1 | hj1
    · exact absurd (hi1.trans hj1.symm) hij'
    · have hkk : k = (i', j') := by rw [hi1, hj1]
      rw [hkk]
    · have hkk : k = (j', i') := by rw [hj1, hi1]
      rw [hkk]; exact hsym j' i'
    · exact absurd (hi1.trans hj1.symm) hij'
  rw [← ht, ← hk, hki'.2]

/-! ## 4. ★★★ (LB) -/

/-- The ensemble's closure, restricted to the payload vertices of one copy. -/
def eCopy (L : Nat) (c : EColr L) : Col (Fin L × Fin L) :=
  fun p => eRoot L (epay c p.1, epay c p.2)

/-- The atoms of the copy's **own** graph — the encoded one. -/
def hInit (c : EColr L) : Col (Fin L × Fin L) := fun p =>
  Nat.pair (if p.1 = p.2 then 1 else 0) (if hAdj c p.1 p.2 then 1 else 0)

theorem epay_injective (c : EColr L) : Function.Injective (fun i => epay c i) := by
  intro i j h
  simpa [epay, Prod.mk.injEq] using h

/-- ★★★ **THE COPY IS COLOUR-RECOGNISABLE.** *"`z` is in the same copy as `u`"* is decided by the
atoms — payload vertices of one copy are pairwise adjacent, those of different copies never are — so
the ensemble's WL sum can be cut down to one copy. ⚠ **One predicate serves every copy**, which is
what lets §5 compare *two different* copies through the same filter.

★ This is the step (B) would have to break, and it is bought by a **lower** bound on the colouring:
adjacency is atomic. No completeness is assumed anywhere. -/
theorem exists_copy_pred (L : Nat) :
    ∃ P : Nat → Bool, ∀ (c : EColr L) (m : Fin L) (z : EVert L),
      (P (eRoot L (epay c m, z)) = true) ↔ ∃ y, epay c y = z := by
  obtain ⟨g, hg⟩ := exists_factor (eRoot_refines (L := L))
  refine ⟨fun n => decide (dSort2 (g n) = 0 ∧ (dEq (g n) = 1 ∨ dAdj (g n) = 1)), ?_⟩
  intro c m z
  show (decide _ = true) ↔ _
  · simp only [hg (epay c m, z), dSort2_eInit, dEq_eInit, dAdj_eInit, decide_eq_true_iff]
    constructor
    · rintro ⟨hs, hd⟩
      rcases z with ⟨c₂, n⟩ | ⟨k, t⟩ | gg
      · refine ⟨n, ?_⟩
        have hcc : c = c₂ := by
          rcases hd with hd | hd
          · by_cases hh : (epay c m : EVert L) = Sum.inl (c₂, n)
            · exact congrArg Prod.fst (Sum.inl.inj hh)
            · rw [if_neg hh] at hd; simp at hd
          · cases hb : eAdj (epay c m) (Sum.inl (c₂, n) : EVert L) with
            | false => rw [hb] at hd; simp at hd
            | true => simp [eAdj] at hb; exact hb.1
        rw [hcc]
      · exact absurd hs (by simp [esort])
      · by_cases hgg : gg = ebase L <;> exact absurd hs (by simp [esort, hgg])
    · rintro ⟨y, rfl⟩
      refine ⟨rfl, ?_⟩
      by_cases hy : m = y
      · left; simp [hy]
      · right
        have : eAdj (epay c m) (epay c y) = true := by simp [eAdj, hy]
        simp [this]

/-- ★★★ **E-STABILITY RESTRICTS.** The restriction of the ensemble's closure to one copy is a stable
colouring of that copy's own carrier. -/
theorem eCopy_stable (c : EColr L) : Stable (roundG (V := Fin L)) (eCopy L c) := by
  refine stable_iff_sig.mpr (fun p q hpq => ?_)
  obtain ⟨P, hP⟩ := exists_copy_pred L
  exact restrict_sig_eq eRoot_stable P (epay_injective c) (epay_injective c)
    (u := epay c p.1) (v := epay c p.2) (u' := epay c q.1) (v' := epay c q.2)
    (hP c p.1) (hP c q.1) hpq

/-- The restriction refines the copy's own atoms: the diagonal is free, and the encoded edge is §3. -/
theorem eCopy_refines_hInit (c : EColr L) (hsym : SymCopy c) :
    PartitionClosure.Refines (eCopy L c) (hInit c) := by
  intro p q h
  have hdiag : (p.1 = p.2) ↔ (q.1 = q.2) := by
    have := diag_eq_of_eRoot_eq (p := (epay c p.1, epay c p.2)) (q := (epay c q.1, epay c q.2)) h
    simpa [epay, Prod.mk.injEq] using this
  have hd : (if p.1 = p.2 then 1 else 0) = (if q.1 = q.2 then (1 : Nat) else 0) := by
    by_cases hp : p.1 = p.2
    · simp [hp, hdiag.mp hp]
    · have hq : ¬ q.1 = q.2 := fun hh => hp (hdiag.mpr hh)
      simp [hp, hq]
  have hadj : hAdj c p.1 p.2 = hAdj c q.1 q.2 := by
    by_cases hp : p.1 = p.2
    · simp [hAdj, hp, hdiag.mp hp]
    · have hq : ¬ q.1 = q.2 := fun hh => hp (hdiag.mpr hh)
      have := encoded_edge_eq hsym hp hq h
      simp [hAdj, hp, hq, this]
  simp only [hInit, hd, hadj]

/-- ### ★★★ (LB) — §6e.4g **item 2**, discharged.
The ensemble's stable colouring, restricted to the payload vertices of a copy, **refines that copy's
own bare 2-WL closure**. Every `L`, at the real object.

⚠ Read the direction: this bounds the ensemble from **below**. It cannot be weakened by the ensemble
being larger, coarser elsewhere, or more symmetric — which is exactly the property (A)'s argument
needs and (B)'s washout claim would have to contradict. ⛔ It does **not** say the ensemble is finer
than anything else, and it does not by itself exclude a mixed cell. -/
theorem lb (c : EColr L) (hsym : SymCopy c) :
    PartitionClosure.Refines (eCopy L c) (wl2G (hInit c)) :=
  refines_wl2G_of_stable (eCopy_stable c) (eCopy_refines_hInit c hsym)

/-- ▶ **The form (P1)/(P2) consume.** A copy whose own refinement is discrete has its ensemble
restriction discrete too — which is the *"chosen probe"* of §6e.4d.1, and the Ruler Lemma's
hypothesis (ii) is then one step away. -/
theorem eCopy_injective_of_discrete (c : EColr L) (hsym : SymCopy c)
    (hdisc : ∀ p q : Fin L × Fin L, wl2G (hInit c) p = wl2G (hInit c) q → p = q) :
    Function.Injective (eCopy L c) :=
  fun p q h => hdisc p q (lb c hsym p q h)

end CopyRestrict
end ChainDescent
