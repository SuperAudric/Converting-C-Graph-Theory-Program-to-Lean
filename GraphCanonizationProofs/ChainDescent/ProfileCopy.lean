import ChainDescent.RulerAtEnsemble

/-!
# 4b3 — *"the reading determines the copy"*, and the last arrow

(`docs/chain-descent-cao-carrier-falsifiers.md` §6e.4a and §6e.4g **item 4b3**.)

## What was missing

`RulerAtEnsemble.readings_translate_of_wl2G_discrete` concludes that two payload vertices sharing a
2-WL colour have `S_L`-**translate readings** of the frame. `Ensemble.MixedCell` is about the
**vertices**. §6e.4a bridges the two with *"`a` determines `c`"* — argued and measured, never proved.

★ By equivariance (`bE_equivariant`), *"`b ω₂` is the `σ`-translate of `b ω₁`"* is literally
`b ω₂ = b (σ⁻¹ • ω₁)`, so the bridge is exactly **injectivity of the reading map**
`bE L : PayIdx L → (SlotIdx L → Nat)`. That is `profile_determines` below.

## The mechanism, and why the atomic part is not enough

The atomic colour of `(p(c,i), f(k,t))` is `inSlot k i ∧ c k = t`, so it reveals `c` **only on slots
incident to `i`** — which is why this was a real claim and not bookkeeping. The extra step is §6e.4a's
**clique mechanism**, and one round of 2-WL delivers it:

> `p(c,i)`'s payload neighbours are exactly the rest of *its own copy* (a copy is a clique, and no
> payload edge crosses copies). `f(k,t)`'s payload neighbours are the endpoints of `k` in copies whose
> type at `k` is `t`. So the two have a **common payload neighbour iff `c k = t`**, for every
> non-degenerate `k` — with no reference to `i`.

Common neighbours are counted by the payload-filtered signature (`Coherence.payload_readout`), which a
stable colouring hands over, so the pair colour determines `c k = t` at every slot. `type_transfer` is
that sentence.

⚠ It does **not** say a single pair colour determines `c`: it determines the *boolean* `c k = t`, not
which `k` is meant. Recovering `c` needs the reading as a **function on slots**, which is precisely
what the Ruler Lemma supplies and why the ruler is doing real work.

## ★★★★ What this closes

With `profile_determines`, the chain runs end to end:

```
 one copy with a discrete own-2-WL closure
   =(LB)=>  its ensemble restriction is injective
   =====>   TagIsolates (i) + RulerRefines (R)                 [RulerAtEnsemble]
   =====>   equal diagonal colour ==> translate readings       [RulerLemma + Coherence]
   =(4b3)=> equal diagonal colour ==> same label orbit         [this file]
   =====>   LabelPropagates,  hence NOT MixedCell              [this file]
```

**`not_mixedCell`**: if `E(L)` (`L ≥ 3`) contains one copy whose own 2-WL closure is discrete, then its
2-WL closure has **no mixed cell at all**. ⛔ **One input remains — 4c**: that such a copy exists, which
is also this theorem's non-vacuity (below `L = 6` no graph is rigid, so the hypothesis is empty there).

⚠ `L ≥ 3` is needed only to pin the *mark*: at `L = 2` both payload vertices of a copy are genuine
twins, so the reading cannot separate them — harmlessly, since they are then in one label orbit anyway.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
no `native_decide`.
-/

namespace ChainDescent
namespace ProfileCopy

open ChainDescent.PartitionClosure
open ChainDescent.FrameEncoding
open ChainDescent.Ensemble
open ChainDescent.CopyRestrict
open ChainDescent.CopyProbe
open ChainDescent.Coherence
open ChainDescent.RulerAtEnsemble

variable {L : Nat}

/-! ## 1. ★★★ The clique mechanism — a pair colour determines the copy's type at its slot -/

/-- ★★★ **§6e.4a's clique mechanism, as a theorem.** If `(p(c,i), f(k,t))` and `(p(c',i'), f(k',t'))`
have the same closure colour and the first copy carries type `t` at `k`, then the second carries `t'`
at `k'`. ★ The witness is a **common payload neighbour**, which exists exactly when the copy carries
the type — and it never mentions the mark `i`, which is what takes this past the atomic colour. -/
theorem type_transfer {c c' : EColr L} {i i' : Fin L} {k k' : ESlot L} {t t' : Bool}
    (hk : k.1 ≠ k.2) (hct : c.val k = t)
    (h : eRoot L (epay c i, efrm k t) = eRoot L (epay c' i', efrm k' t')) :
    c'.val k' = t' := by
  -- an endpoint of `k` other than the mark
  obtain ⟨j, hj1, hj2⟩ : ∃ j : Fin L, inSlot k j = true ∧ j ≠ i := by
    by_cases hi : i = k.1
    · refine ⟨k.2, by simp [inSlot, hk], ?_⟩
      rw [hi]; exact fun hh => hk hh.symm
    · exact ⟨k.1, by simp [inSlot, hk], fun hh => hi hh.symm⟩
  have hadj1 : eAdj (epay c i) (epay c j) = true := by simp [eAdj, Ne.symm hj2]
  have hadj2 : eAdj (epay c j) (efrm k t) = true := by simp [eAdj, hj1, hct]
  -- its contribution sits in the payload-filtered signature, hence in the other pair's
  have hmem : (eRoot L (epay c i, epayI ((c, j) : PayIdx L)),
        eRoot L (epayI ((c, j) : PayIdx L), efrm k t))
      ∈ (Finset.univ : Finset (PayIdx L)).val.map
          (fun w => (eRoot L (epay c i, epayI w), eRoot L (epayI w, efrm k t))) :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ ((c, j) : PayIdx L))
  rw [payload_readout h] at hmem
  obtain ⟨w, -, hw⟩ := Multiset.mem_map.1 hmem
  obtain ⟨a, b⟩ := w
  have e1 : eAdj (epay c' i') (epay a b) = true := by
    rw [eAdj_eq_of_eRoot_eq (p := (epay c' i', epay a b)) (q := (epay c i, epay c j))
      (congrArg Prod.fst hw)]
    exact hadj1
  have e2 : eAdj (epay a b) (efrm k' t') = true := by
    rw [eAdj_eq_of_eRoot_eq (p := (epay a b, efrm k' t')) (q := (epay c j, efrm k t))
      (congrArg Prod.snd hw)]
    exact hadj2
  have hca : c' = a := (by simpa [eAdj] using e1 : c' = a ∧ ¬ i' = b).1
  have hb : a.val k' = t' := (by simpa [eAdj, Bool.and_eq_true] using e2 :
    inSlot k' b = true ∧ a.val k' = t').2
  rw [hca]; exact hb

/-! ## 2. ★★★★ 4b3 — the reading determines the payload vertex -/

/-- ### ★★★★ **4b3.** The slot profile of a payload vertex determines that vertex: its copy, by the
clique mechanism at every slot, and its mark, by which slots it is incident to.

⚠ `3 ≤ L` pins the mark; at `L = 2` the two payload vertices of a copy are genuine twins. -/
theorem profile_determines (hL : 3 ≤ L) {w w' : PayIdx L} (h : bE L w = bE L w') : w = w' := by
  -- the copy, at every slot
  have hcc : w.1 = w'.1 := by
    refine Subtype.ext (funext fun k => ?_)
    by_cases hk : k.1 = k.2
    · rw [colr_diag w.1 k hk, colr_diag w'.1 k hk]
    · exact (type_transfer hk rfl (congrFun h (k, w.1.val k))).symm
  -- the mark, from the slots it is incident to
  refine Prod.ext hcc ?_
  have h0 : (0 : Nat) < L := by omega
  have h1 : (1 : Nat) < L := by omega
  have h2 : (2 : Nat) < L := by omega
  obtain ⟨j, hj, hj'⟩ : ∃ j : Fin L, j ≠ w.2 ∧ j ≠ w'.2 := by
    by_contra hcon
    push_neg at hcon
    have hsub : ∀ x : Fin L, x = w.2 ∨ x = w'.2 := by
      intro x
      by_cases hx : x = w.2
      · exact Or.inl hx
      · exact Or.inr (hcon x hx)
    have d01 : (⟨0, h0⟩ : Fin L) ≠ ⟨1, h1⟩ := by simp [Fin.ext_iff]
    have d02 : (⟨0, h0⟩ : Fin L) ≠ ⟨2, h2⟩ := by simp [Fin.ext_iff]
    have d12 : (⟨1, h1⟩ : Fin L) ≠ ⟨2, h2⟩ := by simp [Fin.ext_iff]
    rcases hsub ⟨0, h0⟩ with e0 | e0 <;> rcases hsub ⟨1, h1⟩ with e1 | e1 <;>
      rcases hsub ⟨2, h2⟩ with e2 | e2 <;> simp_all
  have hkne : ((w.2, j) : ESlot L).1 ≠ ((w.2, j) : ESlot L).2 := fun hh => hj hh.symm
  have hadj := eAdj_eq_of_eRoot_eq
    (p := (epay w.1 w.2, efrm ((w.2, j) : ESlot L) (w.1.val (w.2, j))))
    (q := (epay w'.1 w'.2, efrm ((w.2, j) : ESlot L) (w.1.val (w.2, j))))
    (congrFun h (((w.2, j) : ESlot L), w.1.val (w.2, j)))
  rw [← hcc] at hadj
  have hLt : eAdj (epay w.1 w.2) (efrm ((w.2, j) : ESlot L) (w.1.val (w.2, j))) = true := by
    simp [eAdj, inSlot, hkne]
  have hRt : eAdj (epay w.1 w'.2) (efrm ((w.2, j) : ESlot L) (w.1.val (w.2, j))) = true := by
    rw [← hadj]; exact hLt
  have hexp : (w.2 ≠ j) ∧ (w'.2 = w.2 ∨ w'.2 = j) := by
    have hin : inSlot ((w.2, j) : ESlot L) w'.2 = true := by simpa [eAdj] using hRt
    simpa only [inSlot, decide_eq_true_iff] using hin
  rcases hexp.2 with hh | hh
  · exact hh.symm
  · exact absurd hh.symm hj'

/-! ## 3. ★★★★ (A) AT THE OBJECT — no mixed cell -/

/-- The last arrow: equal diagonal colour ⟹ same **label orbit**, not merely translate readings. -/
theorem sameLabelOrbit_of_diag (hL : 3 ≤ L) {c : EColr L}
    (hd : Function.Injective (eCopy L c)) (i : Fin L) {w₁ w₂ : PayIdx L} (h : yE L w₁ = yE L w₂) :
    SameLabelOrbit (epayI w₁) (epayI w₂) := by
  obtain ⟨σ, hσ⟩ := readings_translate_of_discrete hd i h
  have hfun : bE L w₂ = bE L (σ⁻¹ • w₁) := by
    funext s
    rw [hσ s, bE_equivariant σ⁻¹ w₁ s, inv_inv]
  have hw : w₂ = σ⁻¹ • w₁ := profile_determines hL hfun
  exact ⟨σ⁻¹, by rw [hw, epayI_smul]⟩

/-- ### ★★★★ **CAO PROPAGATION HOLDS AT THE ENSEMBLE, GIVEN ONE DISCRETE COPY.** -/
theorem labelPropagates_of_discrete (hL : 3 ≤ L) {c : EColr L}
    (hdisc : ∀ p q : Fin L × Fin L, wl2G (hInit c) p = wl2G (hInit c) q → p = q) (i : Fin L) :
    LabelPropagates L := fun c₁ c₂ i₁ i₂ h =>
  sameLabelOrbit_of_diag hL (eCopy_injective_of_discrete c (symCopy_all c) hdisc) i
    (w₁ := (c₁, i₁)) (w₂ := (c₂, i₂)) h

/-- ### ⛔★★★★ **NO MIXED CELL.**
If `E(L)` (`L ≥ 3`) contains **one** copy whose own 2-WL closure is discrete, the ensemble's 2-WL
closure never merges two payload vertices from different label orbits — so the refutation shape
`Ensemble.MixedCell` is unavailable.

⚠⚠ **One input remains: 4c**, that such a copy exists — which is also this theorem's **non-vacuity**.
Below `L = 6` no graph is rigid, so the hypothesis is empty there and the statement says nothing; at
`L = 6` it is measured (5760/32768) and not formalized. ⚠ And the conclusion is stated against the
**label** orbits, not `Aut_{m(base)}`-orbits; equality of the two is **T2⁺**, which is not available
(`Ensemble`'s header). -/
theorem not_mixedCell (hL : 3 ≤ L) {c : EColr L}
    (hdisc : ∀ p q : Fin L × Fin L, wl2G (hInit c) p = wl2G (hInit c) q → p = q) (i : Fin L) :
    ¬ MixedCell L := fun hm =>
  not_labelPropagates_of_mixed hm (labelPropagates_of_discrete hL hdisc i)

end ProfileCopy
end ChainDescent
