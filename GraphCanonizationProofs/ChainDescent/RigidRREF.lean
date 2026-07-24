import ChainDescent.KernelGauss
import Mathlib.Data.List.GetD

/-!
# P3-F₂ / `gen` sub-brick (A) — the canonical column-ordered F₂ RREF

The first brick of the concrete rigid labelling `gen` (`docs/chain-descent-rigid-seal.md` §8.2 P3-F₂,
"wire the unique solve under an iso-invariant frame into `gen`"). The executable F₂ reduced-row-echelon
*algorithm* already exists — `Kernel.echelon` (`KernelSupply.lean`) produces a reduced echelon pivot list,
and `Kernel.pivInv_echelon` (`KernelGauss.lean`) proves it satisfies `PivInv`: the pivots are unit at their
own column, zero at every other pivot column, columns distinct, and — the load-bearing part — the pivot rows
and the input rows **span each other** (same row space, both directions).

What that algorithm does *not* give directly is a **canonical** object: `echelon` returns the pivots in the
(reverse) order they were discovered by the fold, so it is a function of the generating *list*, not yet
presented in a canonical shape. This module reorders it into the **column order** `0, 1, …, m-1`:

* `rrefCanon m rows` — `echelon rows` with its pivots emitted in increasing column order (canonical shape).
* `mem_rrefCanon_iff` — it has exactly the same pivots as `echelon rows` (a reordering, no loss).
* `pivInv_rrefCanon` — so it inherits `PivInv`: **the canonical form preserves the row space** (both
  directions) and is a genuine reduced echelon system.

This is the object the next brick (B) shows is canonical *as a function of the row space* (RREF is unique
given the column order), which is what an iso-invariant `gen` will read once the column order is supplied by
the (equivariant) χ-frame (brick C). Here everything is per a **fixed** column order `0 … m-1`; the frame is
where iso-invariance enters (`GenEquivariant` is *not* free on raw indices — permuting columns changes the
pivot set — which is exactly why the order must come from χ, not the vertex labels).
-/

namespace ChainDescent
namespace RigidRREF

open ChainDescent.Kernel

/-- **The canonical column-ordered RREF.** `echelon rows` reordered so its pivots are listed in increasing
column order `0, 1, …, m-1` (scanning the columns and picking each one's pivot, if present). A canonical
*shape*; canonicity as a function of the row space is brick (B). -/
def rrefCanon (m : Nat) (rows : List (List Bool)) : List (Nat × List Bool) :=
  (List.range m).filterMap (fun c =>
    ((echelon rows).find? (fun cp => cp.1 == c)).map (fun cp => (c, cp.2)))

-- smoke test: two rows over 3 columns → 2 pivots at columns 0,1, in column order.
-- #eval rrefCanon 3 [[true, true, false], [false, true, true]]

/-- Every pivot of the canonical form is a pivot of `echelon rows` (the reorder loses nothing). -/
theorem mem_echelon_of_mem_rrefCanon {m : Nat} {rows : List (List Bool)} {cp : Nat × List Bool}
    (h : cp ∈ rrefCanon m rows) : cp ∈ echelon rows := by
  rw [rrefCanon, List.mem_filterMap] at h
  obtain ⟨c, _, hc⟩ := h
  rw [Option.map_eq_some_iff] at hc
  obtain ⟨cq, hfind, hcpeq⟩ := hc
  have hmem : cq ∈ echelon rows := List.mem_of_find?_eq_some hfind
  have hcol : cq.1 = c := by simpa using List.find?_some hfind
  have : cp = cq := by
    rw [← hcpeq]; ext <;> simp [hcol]
  rwa [this]

/-- Conversely, every pivot of `echelon rows` appears in the canonical form (at its own column). Needs the
input rows uniform-length so `pivInv_echelon` supplies `col_lt` (columns in range) and column-`Nodup`. -/
theorem mem_rrefCanon_of_mem_echelon {m : Nat} {rows : List (List Bool)}
    (h : ∀ r ∈ rows, r.length = m) {cp : Nat × List Bool} (hcp : cp ∈ echelon rows) :
    cp ∈ rrefCanon m rows := by
  have hpiv := pivInv_echelon h
  have hlt : cp.1 < m := hpiv.col_lt cp hcp
  have hnd : ((echelon rows).map (·.1)).Nodup := hpiv.nodup
  rw [rrefCanon, List.mem_filterMap]
  refine ⟨cp.1, List.mem_range.mpr hlt, ?_⟩
  have hfind : (echelon rows).find? (fun cq => cq.1 == cp.1) = some cp := by
    have := find?_col_eq (P := echelon rows) hnd (c := cp.1) (ρ := cp.2) (by simpa using hcp)
    simpa using this
  rw [hfind]; simp

/-- The canonical form and `echelon rows` have exactly the same pivots. -/
theorem mem_rrefCanon_iff {m : Nat} {rows : List (List Bool)} (h : ∀ r ∈ rows, r.length = m)
    {cp : Nat × List Bool} : cp ∈ rrefCanon m rows ↔ cp ∈ echelon rows :=
  ⟨mem_echelon_of_mem_rrefCanon, mem_rrefCanon_of_mem_echelon h⟩

/-- The canonical form is duplicate-free (as a list of pivots): distinct columns are scanned once. -/
theorem rrefCanon_nodup (m : Nat) (rows : List (List Bool)) : (rrefCanon m rows).Nodup := by
  apply List.Nodup.filterMap _ (List.nodup_range)
  intro a a' b hb hb'
  rw [Option.mem_def, Option.map_eq_some_iff] at hb hb'
  obtain ⟨_, _, rfl⟩ := hb
  obtain ⟨_, _, hb'eq⟩ := hb'
  simpa using (congrArg (·.1) hb'eq).symm

/-- The canonical form's pivot **columns** are distinct — the `PivInv.nodup` field, transported. -/
theorem rrefCanon_cols_nodup {m : Nat} {rows : List (List Bool)} (h : ∀ r ∈ rows, r.length = m) :
    ((rrefCanon m rows).map (·.1)).Nodup := by
  have hpiv := pivInv_echelon h
  refine (rrefCanon_nodup m rows).map_on ?_
  intro x hx y hy hxy
  have hx' : x ∈ echelon rows := mem_echelon_of_mem_rrefCanon hx
  have hy' : y ∈ echelon rows := mem_echelon_of_mem_rrefCanon hy
  exact List.inj_on_of_nodup_map hpiv.nodup hx' hy' hxy

/-- **★ Row-space preservation for the canonical form.** `rrefCanon m rows` satisfies the echelon invariant:
it is a reduced echelon system with **the same row space as the input** (both directions), inherited from
`pivInv_echelon` through the column-order reordering. This is the foundation the canonicity brick (B) and the
`gen` labelling (brick D) build on. -/
theorem pivInv_rrefCanon {m : Nat} {rows : List (List Bool)} (h : ∀ r ∈ rows, r.length = m) :
    PivInv m rows (rrefCanon m rows) := by
  have hpiv := pivInv_echelon h
  have hmem := fun (cp : Nat × List Bool) => (mem_rrefCanon_iff h (cp := cp))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro cp hcp; exact hpiv.col_lt cp ((hmem cp).mp hcp)
  · intro cp hcp; exact hpiv.len cp ((hmem cp).mp hcp)
  · intro cp hcp; exact hpiv.unit cp ((hmem cp).mp hcp)
  · intro cp hcp cq hcq hne; exact hpiv.cross cp ((hmem cp).mp hcp) cq ((hmem cq).mp hcq) hne
  · exact rrefCanon_cols_nodup h
  · intro cp hcp; exact hpiv.spanned cp ((hmem cp).mp hcp)
  · intro r hr
    refine Spans.mono ?_ (hpiv.covers r hr)
    intro b hb
    obtain ⟨cp, hcpE, rfl⟩ := List.mem_map.mp hb
    exact List.mem_map.mpr ⟨cp, (hmem cp).mpr hcpE, rfl⟩

/-! ## 2. Kernel triviality — the transversal property (brick (B) foundation)

RREF uniqueness rests on: **a row-space vector that is zero at every pivot column is zero** — the pivot rows
form a transversal (are linearly independent). `PivInv`'s `unit` + `cross` + `nodup` give exactly this, once a
span element is written as an XOR of a **Nodup subset** of the pivot rows (dedup mod 2, `spans_nodup_combo`).
⚠ Note this is *stronger* than `PivInv` alone can be used for pivot-column determination — `PivInv` does not pin
the pivot columns to leading positions (`span{[1,1]}` admits both column 0 and column 1 as valid `PivInv`
pivots); that gap is brick (B)'s pivot-column step, separate from this kernel lemma. -/

/-- `xorRow` is left-commutative on equal-length rows. -/
theorem xorRow_left_comm {m : Nat} {a b c : List Bool}
    (ha : a.length = m) (hb : b.length = m) (hc : c.length = m) :
    xorRow a (xorRow b c) = xorRow b (xorRow a c) := by
  rw [← xorRow_assoc ha hb hc, xorRow_comm a b, xorRow_assoc hb ha hc]

/-- `combo` is invariant under permutation of an equal-length row list (XOR is comm/assoc). -/
theorem combo_perm {m : Nat} : ∀ {ws ws' : List (List Bool)}, ws.Perm ws' →
    (∀ x ∈ ws, x.length = m) → combo m ws = combo m ws' := by
  intro ws ws' hp
  induction hp with
  | nil => intro _; rfl
  | cons x _ ih =>
      intro h
      rw [combo_cons, combo_cons, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
  | swap x y l =>
      intro h
      rw [combo_cons, combo_cons, combo_cons, combo_cons]
      exact xorRow_left_comm (h y (by simp)) (h x (by simp))
        (combo_length (fun z hz => h z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))))
  | trans p1 _ ih1 ih2 =>
      intro h
      rw [ih1 h, ih2 (fun x hx => h x (p1.mem_iff.mpr hx))]

/-- **Dedup to a Nodup subset.** Every span element is the XOR of a *duplicate-free* subset of the generators
(over F₂, repeats cancel). -/
theorem spans_nodup_combo {m : Nat} {B : List (List Bool)} (hB : ∀ b ∈ B, b.length = m)
    {w : List Bool} (hw : Spans m B w) :
    ∃ S : List (List Bool), (∀ x ∈ S, x ∈ B) ∧ S.Nodup ∧ combo m S = w := by
  induction hw with
  | zero => exact ⟨[], by simp, List.nodup_nil, rfl⟩
  | @step b w' hb _ ih =>
      obtain ⟨S, hSsub, hSnd, hScombo⟩ := ih
      have hlenS : ∀ x ∈ S, x.length = m := fun x hx => hB x (hSsub x hx)
      have hbl : b.length = m := hB b hb
      by_cases hbS : b ∈ S
      · refine ⟨S.erase b, fun x hx => hSsub x (List.mem_of_mem_erase hx), hSnd.erase b, ?_⟩
        have hperm : S.Perm (b :: S.erase b) := List.perm_cons_erase hbS
        have hcomboS : combo m S = xorRow b (combo m (S.erase b)) := by
          rw [combo_perm hperm hlenS, combo_cons]
        have hcl : (combo m (S.erase b)).length = m :=
          combo_length (fun x hx => hlenS x (List.mem_of_mem_erase hx))
        have hbw : xorRow b (combo m (S.erase b)) = w' := by rw [← hcomboS, hScombo]
        rw [← hbw, xorRow_self_cancel hbl hcl]
      · refine ⟨b :: S, ?_, List.nodup_cons.mpr ⟨hbS, hSnd⟩, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hb
          · exact hSsub x hx
        · rw [combo_cons, hScombo]

/-- `xorList` counts `true`s mod 2, so it is permutation-invariant. -/
theorem xorList_perm {l l' : List Bool} (h : l.Perm l') : xorList l = xorList l' := by
  rw [xorList_eq_count, xorList_eq_count, h.count_eq]

/-- `xorList` of an all-`false` list is `false`. -/
theorem xorList_all_false {l : List Bool} (h : ∀ a ∈ l, a = false) : xorList l = false := by
  rw [xorList_eq_count]
  have : l.count true = 0 := by
    rw [List.count_eq_zero]
    intro hc; exact Bool.noConfusion (h _ hc)
  simp [this]

/-- **Single-support XOR parity.** If `g` is `true` on exactly one member `x` of a `Nodup` list, the XOR of
`g` over the list is `true`. -/
theorem xorList_map_single {α : Type*} [DecidableEq α] {S : List α} (hSnd : S.Nodup) {x : α} (hx : x ∈ S)
    {g : α → Bool} (hgx : g x = true) (hsupp : ∀ y ∈ S, g y = true → y = x) :
    xorList (S.map g) = true := by
  have hperm : S.Perm (x :: S.erase x) := List.perm_cons_erase hx
  rw [xorList_perm (hperm.map g), List.map_cons, xorList_cons, hgx]
  have hrest : xorList ((S.erase x).map g) = false := by
    refine xorList_all_false ?_
    intro a ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
    have hyne : y ≠ x := (hSnd.mem_erase_iff.mp hy).1
    by_contra hg
    exact hyne (hsupp y (List.mem_of_mem_erase hy) (by simpa using hg))
  simp [hrest]

/-- **★★ Kernel triviality (the transversal property).** A row-space vector `w` that is `false` at every pivot
column is the zero row. The pivot rows are linearly independent: represent `w` as a Nodup XOR of pivot rows;
any pivot row used would make `w` nonzero at its own column. This is the workhorse of pivot-row uniqueness. -/
theorem combo_eq_zero_of_pivots_zero {m : Nat} {P : List (Nat × List Bool)} {w : List Bool}
    (hcol_lt : ∀ cp ∈ P, cp.1 < m) (hlen : ∀ cp ∈ P, cp.2.length = m)
    (hunit : ∀ cp ∈ P, cp.2.getD cp.1 false = true)
    (hcross : ∀ cp ∈ P, ∀ cq ∈ P, cp.1 ≠ cq.1 → cp.2.getD cq.1 false = false)
    (hnodup : (P.map (·.1)).Nodup) (hw : Spans m (P.map (·.2)) w)
    (hz : ∀ cp ∈ P, w.getD cp.1 false = false) : w = zeroW m := by
  have hB : ∀ b ∈ P.map (·.2), b.length = m := by
    intro b hb; obtain ⟨cp, hcp, rfl⟩ := List.mem_map.mp hb; exact hlen cp hcp
  obtain ⟨S, hSsub, hSnd, hScombo⟩ := spans_nodup_combo hB hw
  have hlenS : ∀ x ∈ S, x.length = m := fun x hx => hB x (hSsub x hx)
  have hSnil : S = [] := by
    by_contra hne
    obtain ⟨x, hxS⟩ := List.exists_mem_of_ne_nil S hne
    obtain ⟨cq, hcq, hxeq⟩ := List.mem_map.mp (hSsub x hxS)
    -- `x = cq.2`; evaluate `w` at pivot column `cq.1`, get `true`, contradicting `hz`.
    have hval : w.getD cq.1 false = true := by
      rw [← hScombo, getD_combo hlenS (hcol_lt cq hcq)]
      refine xorList_map_single hSnd hxS (g := fun y => y.getD cq.1 false) ?_ ?_
      · rw [← hxeq]; exact hunit cq hcq
      · intro y hy hgy
        obtain ⟨cd, hcd, rfl⟩ := List.mem_map.mp (hSsub y hy)
        by_cases hcol : cd.1 = cq.1
        · rw [← hxeq]
          exact congrArg (·.2) (List.inj_on_of_nodup_map hnodup hcd hcq hcol)
        · exact absurd (hgy.symm.trans (hcross cd hcd cq hcq hcol)) (by decide)
    rw [hz cq hcq] at hval
    exact Bool.noConfusion hval
  rw [hSnil] at hScombo
  simpa using hScombo.symm

/-! ## 3. The leading-position invariant (brick (B-cols) linchpin)

`PivInv` does not pin the pivot columns (§2 finding). The missing structural fact is that `echelon`'s pivot
rows are **false strictly below their pivot column** — the pivot is the *leading* (leftmost) nonzero entry, a
consequence of `findIdx?` picking the leftmost true and back-reduction only touching columns `≥` the new
pivot. This is a fresh fold invariant, parallel to `pivInv_echelon`. With it, pivot columns = the row space's
leading positions (intrinsic), which gives column determination for RREF uniqueness. -/

/-- **Leading position**: every pivot row is `false` strictly below its own pivot column. -/
def LeadInv (P : List (Nat × List Bool)) : Prop :=
  ∀ cp ∈ P, ∀ j, j < cp.1 → cp.2.getD j false = false

/-- `echStep` preserves uniform row length. -/
theorem len_echStep {m : Nat} {P : List (Nat × List Bool)} {r : List Bool}
    (hlen : ∀ cp ∈ P, cp.2.length = m) (hr : r.length = m) :
    ∀ cp ∈ echStep P r, cp.2.length = m := by
  cases hfind : (reduceRow P r).findIdx? id with
  | none =>
      have hEs : echStep P r = P := by unfold echStep; rw [hfind]
      rw [hEs]; exact hlen
  | some c =>
      have hr'len : (reduceRow P r).length = m := reduceRow_length P r hlen hr
      have hEs : echStep P r = (c, reduceRow P r) :: P.map (fun cp =>
          (cp.1, if cp.2.getD c false then xorRow cp.2 (reduceRow P r) else cp.2)) := by
        unfold echStep; rw [hfind]
      rw [hEs]
      intro cp hcp
      rcases List.mem_cons.mp hcp with rfl | hcp
      · exact hr'len
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcp
        dsimp only
        split
        · rw [length_xorRow, hlen q hq, hr'len]; omega
        · exact hlen q hq

/-- **★ The step preserves the leading-position invariant.** The new pivot row is `false` below its column by
`findIdx?` (leftmost true); a *triggered* back-reduction has `c ≥ cp.1` (else the old pivot would be nonzero
below its own column), so it only alters columns `≥ c ≥ cp.1`, never below `cp.1`. -/
theorem leadInv_echStep {m : Nat} {P : List (Nat × List Bool)} {r : List Bool}
    (hlen : ∀ cp ∈ P, cp.2.length = m) (hr : r.length = m) (hlead : LeadInv P) :
    LeadInv (echStep P r) := by
  cases hfind : (reduceRow P r).findIdx? id with
  | none =>
      have hEs : echStep P r = P := by unfold echStep; rw [hfind]
      rw [hEs]; exact hlead
  | some c =>
      set r' := reduceRow P r with hr'def
      have hr'len : r'.length = m := reduceRow_length P r hlen hr
      obtain ⟨hclt, -, hbefore⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
      have hcm : c < m := hr'len ▸ hclt
      have hr'below : ∀ j, j < c → r'.getD j false = false := by
        intro j hj
        rw [getD_in (Nat.lt_trans hj hclt)]
        simpa using hbefore j hj
      have hEs : echStep P r = (c, r') :: P.map (fun cp =>
          (cp.1, if cp.2.getD c false then xorRow cp.2 r' else cp.2)) := by
        unfold echStep; rw [hfind]
      rw [hEs]
      intro cp hcp j hj
      rcases List.mem_cons.mp hcp with rfl | hcp
      · exact hr'below j hj
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcp
        have hqbelow : ∀ j', j' < q.1 → q.2.getD j' false = false := hlead q hq
        dsimp only
        split
        · rename_i hb
          have hq1c : q.1 ≤ c := by
            by_contra hlt
            push_neg at hlt
            have := hqbelow c hlt
            rw [hb] at this
            exact absurd this (by decide)
          have hjc : j < c := Nat.lt_of_lt_of_le hj hq1c
          have hjm : j < m := Nat.lt_trans hjc hcm
          rw [getD_xorRow (by rw [hlen q hq]; exact hjm) (by rw [hr'len]; exact hjm),
            hqbelow j hj, hr'below j hjc]
          rfl
        · exact hqbelow j hj

/-- The joint `length` + `LeadInv` invariant, folded over the rows. -/
theorem lead_foldl {m : Nat} : ∀ (rows : List (List Bool)), (∀ r ∈ rows, r.length = m) →
    ∀ (P : List (Nat × List Bool)), (∀ cp ∈ P, cp.2.length = m) → LeadInv P →
      (∀ cp ∈ rows.foldl echStep P, cp.2.length = m) ∧ LeadInv (rows.foldl echStep P) := by
  intro rows
  induction rows with
  | nil => intro _ P hlen hlead; exact ⟨hlen, hlead⟩
  | cons r rs ih =>
      intro hrows P hlen hlead
      have hr : r.length = m := hrows r (List.mem_cons_self ..)
      have hrows' : ∀ x ∈ rs, x.length = m := fun x hx => hrows x (List.mem_cons_of_mem _ hx)
      simp only [List.foldl_cons]
      exact ih hrows' (echStep P r) (len_echStep hlen hr) (leadInv_echStep hlen hr hlead)

/-- **★★ Leading position for `echelon`.** Every pivot row of `echelon rows` is `false` strictly below its
pivot column — the structural fact `PivInv` lacks, and the basis for pivot-column determination (brick B-cols). -/
theorem leadInv_echelon {m : Nat} {rows : List (List Bool)} (h : ∀ r ∈ rows, r.length = m) :
    LeadInv (echelon rows) := by
  rw [echelon_eq_foldl]
  exact (lead_foldl rows h [] (by simp) (by intro cp hcp; simp at hcp)).2

/-! ## 4. Reconstruction + pivot columns are intrinsic (brick (B-cols))

With kernel triviality (§2) and leading position (§3): a row-space vector is the XOR of the pivot rows at the
columns where it is set (`reconstruction`), from which the pivot **columns** are exactly the row space's
**leading positions** (`pivotCol_isLeading` / `leading_isPivotCol`) — an intrinsic characterization, so two
RREFs of the same space have the same pivot columns. -/

/-- Reconstruct `w` from its pivot coordinates: XOR the pivot rows at columns where `w` is set. -/
def recon (m : Nat) (P : List (Nat × List Bool)) (w : List Bool) : List Bool :=
  combo m ((P.filter (fun cp => w.getD cp.1 false)).map (·.2))

/-- **Pivot-coordinate evaluation.** `recon` agrees with `w` at every pivot column (the coordinate map is the
identity on pivot coordinates). -/
theorem recon_getD_pivot {m : Nat} {rows : List (List Bool)} {P : List (Nat × List Bool)}
    (hpiv : PivInv m rows P) {w : List Bool} {cp : Nat × List Bool} (hcp : cp ∈ P) :
    (recon m P w).getD cp.1 false = w.getD cp.1 false := by
  have hPnd : P.Nodup := List.Nodup.of_map _ hpiv.nodup
  have hfnd : (P.filter (fun q => w.getD q.1 false)).Nodup := hPnd.filter _
  have hlenL : ∀ x ∈ (P.filter (fun q => w.getD q.1 false)).map (·.2), x.length = m := by
    intro x hx; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact hpiv.len q (List.mem_of_mem_filter hq)
  have hkey : ∀ q ∈ P, q.2.getD cp.1 false = true → q = cp := by
    intro q hqP hq
    by_contra hne
    have hcolne : q.1 ≠ cp.1 := fun hcol => hne (List.inj_on_of_nodup_map hpiv.nodup hqP hcp hcol)
    rw [hpiv.cross q hqP cp hcp hcolne] at hq
    exact absurd hq (by decide)
  rw [recon, getD_combo hlenL (hpiv.col_lt cp hcp), List.map_map]
  show xorList ((P.filter (fun q => w.getD q.1 false)).map (fun q => q.2.getD cp.1 false))
      = w.getD cp.1 false
  by_cases hwc : w.getD cp.1 false = true
  · rw [hwc]
    refine xorList_map_single hfnd (List.mem_filter.mpr ⟨hcp, hwc⟩) (hpiv.unit cp hcp) ?_
    intro q hq hgq; exact hkey q (List.mem_of_mem_filter hq) hgq
  · rw [Bool.not_eq_true] at hwc
    rw [hwc]
    refine xorList_all_false ?_
    intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    by_cases hg : q.2.getD cp.1 false = true
    · have hpq : w.getD q.1 false = true := (List.mem_filter.mp hq).2
      rw [hkey q (List.mem_of_mem_filter hq) hg] at hpq
      exact absurd (hpq.symm.trans hwc) (by decide)
    · simpa using hg

/-- `recon m P w` lies in the row space `span(P)`. -/
theorem recon_mem_span {m : Nat} {rows : List (List Bool)} {P : List (Nat × List Bool)}
    (hpiv : PivInv m rows P) (w : List Bool) : Spans m (P.map (·.2)) (recon m P w) := by
  rw [recon]
  refine spans_combo ?_
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨q, List.mem_of_mem_filter hq, rfl⟩

/-- **★★ The reconstruction identity.** A row-space vector equals the XOR of the pivot rows at the columns where
it is set. (`xorRow w (recon w)` lies in the space and is zero at every pivot column, so kernel triviality
forces it to zero.) -/
theorem reconstruction {m : Nat} {rows : List (List Bool)} {P : List (Nat × List Bool)}
    (hpiv : PivInv m rows P) {w : List Bool} (hw : Spans m (P.map (·.2)) w) : w = recon m P w := by
  have hBlen : ∀ b ∈ P.map (·.2), b.length = m := by
    intro b hb; obtain ⟨cp, hcp, rfl⟩ := List.mem_map.mp hb; exact hpiv.len cp hcp
  have hwlen : w.length = m := hw.length hBlen
  have hrlen : (recon m P w).length = m := (recon_mem_span hpiv w).length hBlen
  have hu : xorRow w (recon m P w) = zeroW m := by
    refine combo_eq_zero_of_pivots_zero hpiv.col_lt hpiv.len hpiv.unit hpiv.cross hpiv.nodup
      (Spans.xor_closed hBlen hw (recon_mem_span hpiv w)) ?_
    intro cp hcp
    rw [getD_xorRow (by rw [hwlen]; exact hpiv.col_lt cp hcp) (by rw [hrlen]; exact hpiv.col_lt cp hcp),
      recon_getD_pivot hpiv hcp]
    cases w.getD cp.1 false <;> rfl
  calc w = xorRow w (zeroW m) := (xorRow_zeroW_right hwlen).symm
    _ = xorRow w (xorRow w (recon m P w)) := by rw [hu]
    _ = recon m P w := xorRow_self_cancel hwlen hrlen

/-- **(B-cols) forward.** Every pivot column is a **leading position** of the row space — witnessed by its own
pivot row (`unit` at the column, `false` strictly below by leading position). -/
theorem pivotCol_isLeading {m : Nat} {rows : List (List Bool)} {P : List (Nat × List Bool)}
    (hpiv : PivInv m rows P) (hlead : LeadInv P) {cp : Nat × List Bool} (hcp : cp ∈ P) :
    ∃ w, Spans m (P.map (·.2)) w ∧ w.getD cp.1 false = true ∧ ∀ j, j < cp.1 → w.getD j false = false := by
  have hBlen : ∀ b ∈ P.map (·.2), b.length = m := by
    intro b hb; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb; exact hpiv.len q hq
  exact ⟨cp.2, Spans.mem hBlen (List.mem_map.mpr ⟨cp, hcp, rfl⟩), hpiv.unit cp hcp,
    fun j hj => hlead cp hcp j hj⟩

/-- **★★ (B-cols) backward.** Every leading position of the row space is a pivot column. If `c` were not a
pivot, reconstruction would write `w` (a codeword with leading position `c`) as an XOR of pivot rows whose
columns are all `> c` (none below `c` since `w` is `false` there, none at `c` since `c` isn't a pivot); those
are all `false` at `c` by leading position, so `w.getD c = false` — contradicting `w.getD c = true`. -/
theorem leading_isPivotCol {m : Nat} {rows : List (List Bool)} {P : List (Nat × List Bool)}
    (hpiv : PivInv m rows P) (hlead : LeadInv P) {w : List Bool} {c : Nat}
    (hw : Spans m (P.map (·.2)) w) (hc : w.getD c false = true)
    (hbelow : ∀ j, j < c → w.getD j false = false) : c ∈ P.map (·.1) := by
  have hBlen : ∀ b ∈ P.map (·.2), b.length = m := by
    intro b hb; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb; exact hpiv.len q hq
  have hwlen : w.length = m := hw.length hBlen
  have hcm : c < m := by
    by_contra h
    rw [List.getD_eq_default _ _ (by omega)] at hc
    exact absurd hc (by decide)
  by_contra hcnot
  have hlenL : ∀ x ∈ (P.filter (fun q => w.getD q.1 false)).map (·.2), x.length = m := by
    intro x hx; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact hpiv.len q (List.mem_of_mem_filter hq)
  have hzero : xorList (((P.filter (fun q => w.getD q.1 false)).map (·.2)).map
      (fun x => x.getD c false)) = false := by
    refine xorList_all_false ?_
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    have hqP : q ∈ P := List.mem_of_mem_filter hq
    have hqsel : w.getD q.1 false = true := (List.mem_filter.mp hq).2
    have hcq : c < q.1 := by
      rcases Nat.lt_trichotomy c q.1 with h | h | h
      · exact h
      · exact absurd (h ▸ List.mem_map.mpr ⟨q, hqP, rfl⟩) hcnot
      · rw [hbelow q.1 h] at hqsel; exact absurd hqsel (by decide)
    exact hlead q hqP c hcq
  have := reconstruction hpiv hw
  rw [this, recon, getD_combo hlenL hcm] at hc
  rw [hzero] at hc
  exact absurd hc (by decide)

/-- **★★★ (B-cols) — pivot columns are determined by the row space.** Two reduced-echelon systems with the same
row space have the same pivot columns: each side's pivot columns are exactly that space's leading positions
(`pivotCol_isLeading` / `leading_isPivotCol`), transported across equal spans. The column half of RREF
uniqueness. -/
theorem pivotCols_eq {m : Nat} {rows₁ rows₂ : List (List Bool)} {P₁ P₂ : List (Nat × List Bool)}
    (hpiv₁ : PivInv m rows₁ P₁) (hlead₁ : LeadInv P₁) (hpiv₂ : PivInv m rows₂ P₂) (hlead₂ : LeadInv P₂)
    (hspan : ∀ w, Spans m (P₁.map (·.2)) w ↔ Spans m (P₂.map (·.2)) w) {c : Nat} :
    c ∈ P₁.map (·.1) ↔ c ∈ P₂.map (·.1) := by
  constructor
  · intro hc
    obtain ⟨cp, hcp, rfl⟩ := List.mem_map.mp hc
    obtain ⟨w, hwspan, hwc, hwbelow⟩ := pivotCol_isLeading hpiv₁ hlead₁ hcp
    exact leading_isPivotCol hpiv₂ hlead₂ ((hspan w).mp hwspan) hwc hwbelow
  · intro hc
    obtain ⟨cp, hcp, rfl⟩ := List.mem_map.mp hc
    obtain ⟨w, hwspan, hwc, hwbelow⟩ := pivotCol_isLeading hpiv₂ hlead₂ hcp
    exact leading_isPivotCol hpiv₁ hlead₁ ((hspan w).mpr hwspan) hwc hwbelow

end RigidRREF
end ChainDescent
