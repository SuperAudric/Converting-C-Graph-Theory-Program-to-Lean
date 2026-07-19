import ChainDescent.KernelSupply

/-!
# `C3a` tranche 2, part I — F₂ correctness of the kernel toolkit

The elimination-correctness layer under the kernel supply's ① story (`KernelSupply.lean` header,
remaining-work §1C C3 ii-b): `span (kernelBasis) = L`, stated over the executable `List Bool` toolkit
exactly as built (no re-formulation of the landed pipeline — the correctness comes to the code).

* **Soundness** (`dotB_nullBasis`): every emitted basis word is orthogonal to every input row —
  `nullBasis` really lands in the null space.
* **Completeness** (`spans_nullBasis`): every null-space word is an XOR-combination (`Spans`) of the
  emitted basis — nothing in `L` is missed, which is what the reference-supply reduction consumes
  (each `L`-word's flip is then the *product* of basis flips).

The proofs run on a parity-count view of the F₂ dot product (`dotOn_eq_countP`): all support-splitting
becomes `countP` bookkeeping over `Nodup` index lists, and the echelon fold carries the invariant
`PivInv` (pivot entries are unit at their column, zero at every other pivot column, columns `Nodup`,
every pivot row spanned by the input rows, every input row spanned by the pivot rows).
-/

namespace ChainDescent
namespace Kernel

/-! ## 1. XOR-fold and the F₂ dot product -/

/-- XOR-fold of a Bool list — the parity of its `true` count (`xorList_eq_count`). -/
def xorList (l : List Bool) : Bool := l.foldr (· != ·) false

@[simp] theorem xorList_nil : xorList [] = false := rfl

@[simp] theorem xorList_cons (a : Bool) (l : List Bool) : xorList (a :: l) = (a != xorList l) :=
  rfl

theorem xorList_eq_count (l : List Bool) : xorList l = (l.count true % 2 == 1) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases a
      · simpa [List.count_cons] using ih
      · have hpar : ∀ k : Nat, ((k + 1) % 2 == 1) = !(k % 2 == 1) := by
          intro k
          rcases Nat.mod_two_eq_zero_or_one k with h | h
          · have h1 : (k + 1) % 2 = 1 := by omega
            simp [h, h1]
          · have h1 : (k + 1) % 2 = 0 := by omega
            simp [h, h1]
        rw [xorList_cons, ih, List.count_cons]
        simp only [BEq.rfl, if_pos, hpar]
        cases (l.count true % 2 == 1) <;> rfl

/-- `getD` at an in-range index is `getElem` (the form every pointwise computation uses). -/
theorem getD_in {l : List Bool} {j : Nat} (h : j < l.length) : l.getD j false = l[j] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The F₂ dot product: parity of the common support. -/
def dotB (r w : List Bool) : Bool := xorList (List.zipWith (· && ·) r w)

/-- The dot product over an explicit index list (`getD`-indexed). -/
def dotOn (js : List Nat) (r w : List Bool) : Bool :=
  xorList (js.map (fun j => r.getD j false && w.getD j false))

/-- XOR over a mapped list is a `countP` parity. -/
theorem xorList_map_eq_countP {α : Type} (l : List α) (p : α → Bool) :
    xorList (l.map p) = (l.countP p % 2 == 1) := by
  rw [xorList_eq_count, List.count_eq_countP, List.countP_map]
  have hc : List.countP ((fun x => x == true) ∘ p) l = List.countP p l := by
    refine List.countP_congr (fun j _ => ?_)
    simp [Function.comp]
  rw [hc]

/-- **The workhorse view**: `dotOn` is a `countP` parity — all support-splitting becomes counting. -/
theorem dotOn_eq_countP (js : List Nat) (r w : List Bool) :
    dotOn js r w = (js.countP (fun j => r.getD j false && w.getD j false) % 2 == 1) :=
  xorList_map_eq_countP js _

/-- A length-`m` zip-with-`&&` list is the range-map of its pointwise values. -/
theorem zipWith_and_eq_range_map {m : Nat} {r w : List Bool}
    (hr : r.length = m) (hw : w.length = m) :
    List.zipWith (· && ·) r w
      = (List.range m).map (fun j => r.getD j false && w.getD j false) := by
  refine List.ext_getElem (by simp [hr, hw]) (fun j h1 h2 => ?_)
  have hj : j < m := by simpa [hr, hw] using h1
  have hjr : j < r.length := by omega
  have hjw : j < w.length := by omega
  simp [List.getElem_zipWith, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hjr, List.getElem?_eq_getElem hjw]

/-- `dotB` over length-`m` operands is `dotOn` over `range m`. -/
theorem dotB_eq_dotOn {m : Nat} {r w : List Bool} (hr : r.length = m) (hw : w.length = m) :
    dotB r w = dotOn (List.range m) r w := by
  rw [dotB, zipWith_and_eq_range_map hr hw, dotOn]

theorem dotB_comm (r w : List Bool) : dotB r w = dotB w r := by
  unfold dotB
  congr 1
  refine List.ext_getElem (by simp [Nat.min_comm]) (fun j h1 h2 => ?_)
  simp [List.getElem_zipWith, Bool.and_comm]

/-! ## 2. Linearity -/

theorem xorList_zipWith_bne {u v : List Bool} (h : u.length = v.length) :
    xorList (List.zipWith (· != ·) u v) = (xorList u != xorList v) := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => rfl
      | cons b v => simp at h
  | cons a u ih =>
      cases v with
      | nil => simp at h
      | cons b v =>
          have h' : u.length = v.length := by simpa using h
          rw [List.zipWith_cons_cons, xorList_cons, xorList_cons, xorList_cons, ih h']
          cases a <;> cases b <;> cases xorList u <;> cases xorList v <;> rfl

private theorem and_bne_distrib (r x y : Bool) : (r && (x != y)) = ((r && x) != (r && y)) := by
  cases r <;> cases x <;> cases y <;> rfl

/-- `dotB` is linear in the right argument (over equal-length words). -/
theorem dotB_xorRow_right {a b : List Bool} (r : List Bool) (h : a.length = b.length) :
    dotB r (xorRow a b) = (dotB r a != dotB r b) := by
  have hkey : List.zipWith (· && ·) r (xorRow a b)
      = List.zipWith (· != ·) (List.zipWith (· && ·) r a) (List.zipWith (· && ·) r b) := by
    refine List.ext_getElem (by simp [xorRow]; omega) (fun j h1 h2 => ?_)
    simp only [List.getElem_zipWith, xorRow]
    exact and_bne_distrib _ _ _
  rw [dotB, hkey, xorList_zipWith_bne (by simp [h])]
  rfl

/-- `dotB` is linear in the left argument. -/
theorem dotB_xorRow_left {a b : List Bool} (w : List Bool) (h : a.length = b.length) :
    dotB (xorRow a b) w = (dotB a w != dotB b w) := by
  rw [dotB_comm, dotB_xorRow_right w h, dotB_comm a w, dotB_comm b w]

/-- The zero word. -/
def zeroW (m : Nat) : List Bool := List.replicate m false

@[simp] theorem length_zeroW (m : Nat) : (zeroW m).length = m := List.length_replicate

@[simp] theorem getElem_zeroW {m j : Nat} (h : j < (zeroW m).length) : (zeroW m)[j] = false := by
  simp [zeroW]

theorem dotB_zeroW_right (r : List Bool) (m : Nat) : dotB r (zeroW m) = false := by
  have hz : List.zipWith (· && ·) r (zeroW m) = List.replicate (min r.length m) false := by
    refine List.ext_getElem (by simp) (fun j h1 h2 => ?_)
    simp [List.getElem_zipWith]
  rw [dotB, hz, xorList_eq_count]
  simp [List.count_replicate]

/-! ## 3. `xorRow` algebra -/

theorem length_xorRow (a b : List Bool) : (xorRow a b).length = min a.length b.length := by
  simp [xorRow]

theorem xorRow_zeroW_left {m : Nat} {w : List Bool} (h : w.length = m) :
    xorRow (zeroW m) w = w := by
  refine List.ext_getElem (by simp [xorRow, h]) (fun j h1 h2 => ?_)
  simp [xorRow, List.getElem_zipWith]

theorem xorRow_zeroW_right {m : Nat} {b : List Bool} (h : b.length = m) :
    xorRow b (zeroW m) = b := by
  refine List.ext_getElem (by simp [xorRow, h]) (fun j h1 h2 => ?_)
  simp [xorRow, List.getElem_zipWith]

theorem xorRow_self_cancel {m : Nat} {b w : List Bool} (hb : b.length = m) (hw : w.length = m) :
    xorRow b (xorRow b w) = w := by
  refine List.ext_getElem (by rw [length_xorRow, length_xorRow, hb, hw]; omega)
    (fun j h1 h2 => ?_)
  have hj : j < m := by rw [hw] at h2; exact h2
  simp only [xorRow, List.getElem_zipWith]
  cases b[j]'(by omega) <;> cases w[j]'h2 <;> rfl

theorem xorRow_assoc {m : Nat} {a b c : List Bool}
    (ha : a.length = m) (hb : b.length = m) (hc : c.length = m) :
    xorRow (xorRow a b) c = xorRow a (xorRow b c) := by
  refine List.ext_getElem (by simp [xorRow, ha, hb, hc]) (fun j h1 h2 => ?_)
  have hj : j < m := by simpa [xorRow, ha, hb, hc] using h1
  simp only [xorRow, List.getElem_zipWith]
  cases a[j]'(by omega) <;> cases b[j]'(by omega) <;> cases c[j]'(by omega) <;> rfl

theorem getD_xorRow {a b : List Bool} {j : Nat} (hj : j < a.length) (hj' : j < b.length) :
    (xorRow a b).getD j false = (a.getD j false != b.getD j false) := by
  have hjm : j < (xorRow a b).length := by rw [length_xorRow]; omega
  rw [getD_in hjm, getD_in hj, getD_in hj']
  simp [xorRow, List.getElem_zipWith]

/-! ## 4. `Spans` — XOR-combinations of a basis -/

/-- `w` is an XOR-combination of members of `B` (all words length `m`). -/
inductive Spans (m : Nat) (B : List (List Bool)) : List Bool → Prop
  | zero : Spans m B (zeroW m)
  | step {b w : List Bool} : b ∈ B → Spans m B w → Spans m B (xorRow b w)

theorem Spans.length {m : Nat} {B : List (List Bool)} {w : List Bool} (h : Spans m B w)
    (hB : ∀ b ∈ B, b.length = m) : w.length = m := by
  induction h with
  | zero => simp
  | step hb _ ih => rw [length_xorRow, hB _ hb, ih]; omega

theorem Spans.mem {m : Nat} {B : List (List Bool)} (hB : ∀ b ∈ B, b.length = m)
    {b : List Bool} (hb : b ∈ B) : Spans m B b := by
  have h0 := Spans.step hb (Spans.zero (m := m) (B := B))
  rwa [xorRow_zeroW_right (hB _ hb)] at h0

/-- Spans are closed under XOR (derivations concatenate through associativity). -/
theorem Spans.xor_closed {m : Nat} {C : List (List Bool)} (hC : ∀ b ∈ C, b.length = m)
    {a w : List Bool} (haS : Spans m C a) (hwS : Spans m C w) :
    Spans m C (xorRow a w) := by
  induction haS with
  | zero => rwa [xorRow_zeroW_left (hwS.length hC)]
  | step hb ha ih =>
      rw [xorRow_assoc (hC _ hb) (ha.length hC) (hwS.length hC)]
      exact Spans.step hb ih

/-- Monotonicity: a span over pointwise-spanned generators is spanned. -/
theorem Spans.trans_basis {m : Nat} {B C : List (List Bool)}
    (hC : ∀ b ∈ C, b.length = m) (hBC : ∀ b ∈ B, Spans m C b)
    {w : List Bool} (h : Spans m B w) : Spans m C w := by
  induction h with
  | zero => exact Spans.zero
  | step hb _ ih => exact Spans.xor_closed hC (hBC _ hb) ih

/-- Orthogonality extends over a span (`dotB`-linearity folded along the derivation). -/
theorem dotB_eq_false_of_spans {m : Nat} {B : List (List Bool)} (hB : ∀ b ∈ B, b.length = m)
    {r w : List Bool} (hw : Spans m B w) (hr : ∀ b ∈ B, dotB r b = false) :
    dotB r w = false := by
  induction hw with
  | zero => exact dotB_zeroW_right r m
  | step hb hw ih =>
      rw [dotB_xorRow_right r (by rw [hB _ hb, hw.length hB]), hr _ hb, ih]
      rfl

/-! ## 5. Counting helpers — parity over small supports -/

theorem parity_add (a b : Nat) : ((a + b) % 2 == 1) = ((a % 2 == 1) != (b % 2 == 1)) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · have h : (a + b) % 2 = 0 := by omega
    simp [ha, hb, h]
  · have h : (a + b) % 2 = 1 := by omega
    simp [ha, hb, h]
  · have h : (a + b) % 2 = 1 := by omega
    simp [ha, hb, h]
  · have h : (a + b) % 2 = 0 := by omega
    simp [ha, hb, h]

theorem countP_eq_zero_of_support {l : List Nat} {p : Nat → Bool}
    (h : ∀ j ∈ l, p j = false) : l.countP p = 0 := by
  rw [List.countP_eq_zero]
  intro a ha
  simp [h a ha]

/-- Parity of a count supported on a single element. -/
theorem countP_parity_single {l : List Nat} (hl : l.Nodup) {a : Nat} (ha : a ∈ l)
    {p : Nat → Bool} (hsupp : ∀ j ∈ l, p j = true → j = a) :
    (l.countP p % 2 == 1) = p a := by
  have hperm : l.Perm (a :: l.erase a) := List.perm_cons_erase ha
  rw [hperm.countP_eq, List.countP_cons]
  have hz : (l.erase a).countP p = 0 := by
    refine countP_eq_zero_of_support (fun j hj => ?_)
    have hmem := hl.mem_erase_iff.mp hj
    cases hpj : p j
    · rfl
    · exact absurd (hsupp j hmem.2 hpj) hmem.1
  rw [hz]
  cases hpa : p a <;> simp [hpa]

/-- Parity of a count supported on two distinct elements. -/
theorem countP_parity_pair {l : List Nat} (hl : l.Nodup) {a b : Nat} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) {p : Nat → Bool} (hsupp : ∀ j ∈ l, p j = true → j = a ∨ j = b) :
    (l.countP p % 2 == 1) = (p a != p b) := by
  have hperm : l.Perm (a :: l.erase a) := List.perm_cons_erase ha
  have hb' : b ∈ l.erase a := hl.mem_erase_iff.mpr ⟨Ne.symm hab, hb⟩
  rw [hperm.countP_eq, List.countP_cons, parity_add]
  have hsingle : ((l.erase a).countP p % 2 == 1) = p b := by
    refine countP_parity_single (hl.erase a) hb' (fun j hj hpj => ?_)
    have hmem := hl.mem_erase_iff.mp hj
    rcases hsupp j hmem.2 hpj with h | h
    · exact absurd h hmem.1
    · exact h
  rw [hsingle]
  cases hpa : p a <;> cases hpb : p b <;> simp

/-! ## 6. `combo` — folding a word list into its XOR -/

theorem xorRow_comm (a b : List Bool) : xorRow a b = xorRow b a := by
  refine List.ext_getElem (by simp [xorRow, Nat.min_comm]) (fun j h1 h2 => ?_)
  have hj1 : j < a.length := by simp [xorRow] at h1; omega
  have hj2 : j < b.length := by simp [xorRow] at h1; omega
  simp only [xorRow, List.getElem_zipWith]
  cases a[j]'hj1 <;> cases b[j]'hj2 <;> rfl

theorem xorRow_cancel_right {m : Nat} {a b : List Bool} (ha : a.length = m)
    (hb : b.length = m) : xorRow (xorRow a b) b = a := by
  rw [xorRow_comm, xorRow_comm a b]
  exact xorRow_self_cancel hb ha

/-- The XOR of a list of words. -/
def combo (m : Nat) (ws : List (List Bool)) : List Bool := ws.foldr xorRow (zeroW m)

@[simp] theorem combo_nil (m : Nat) : combo m [] = zeroW m := rfl

theorem combo_cons (m : Nat) (x : List Bool) (ws : List (List Bool)) :
    combo m (x :: ws) = xorRow x (combo m ws) := rfl

theorem combo_length {m : Nat} {ws : List (List Bool)} (h : ∀ x ∈ ws, x.length = m) :
    (combo m ws).length = m := by
  induction ws with
  | nil => simp
  | cons x ws ih =>
      rw [combo_cons, length_xorRow, h x (List.mem_cons_self ..),
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      omega

theorem spans_combo {m : Nat} {B : List (List Bool)} {ws : List (List Bool)}
    (h : ∀ x ∈ ws, x ∈ B) : Spans m B (combo m ws) := by
  induction ws with
  | nil => exact Spans.zero
  | cons x ws ih =>
      rw [combo_cons]
      exact Spans.step (h x (List.mem_cons_self ..))
        (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem getD_combo {m : Nat} {ws : List (List Bool)} (h : ∀ x ∈ ws, x.length = m)
    {j : Nat} (hj : j < m) :
    (combo m ws).getD j false = xorList (ws.map (fun x => x.getD j false)) := by
  induction ws with
  | nil =>
      show (zeroW m).getD j false = false
      rw [getD_in (by simp [hj])]
      exact getElem_zeroW _
  | cons x ws ih =>
      have hws : ∀ y ∈ ws, y.length = m := fun y hy => h y (List.mem_cons_of_mem _ hy)
      rw [combo_cons, getD_xorRow (by rw [h x (List.mem_cons_self ..)]; exact hj)
        (by rw [combo_length hws]; exact hj), ih hws]
      rfl

/-- Membership is monotone under generator-list inclusion. -/
theorem Spans.mono {m : Nat} {B B' : List (List Bool)} (h : ∀ b ∈ B, b ∈ B')
    {w : List Bool} (hw : Spans m B w) : Spans m B' w := by
  induction hw with
  | zero => exact Spans.zero
  | step hb _ ih => exact Spans.step (h _ hb) ih

/-! ## 7. The echelon invariant -/

/-- The echelon fold's invariant: pivot rows are unit at their own column, zero at every other pivot
column, columns distinct and in range; every pivot row is spanned by the processed rows and every
processed row by the pivot rows (both directions of "same row space"). -/
structure PivInv (m : Nat) (rows : List (List Bool)) (P : List (Nat × List Bool)) : Prop where
  col_lt : ∀ cp ∈ P, cp.1 < m
  len : ∀ cp ∈ P, cp.2.length = m
  unit : ∀ cp ∈ P, cp.2.getD cp.1 false = true
  cross : ∀ cp ∈ P, ∀ cq ∈ P, cp.1 ≠ cq.1 → cp.2.getD cq.1 false = false
  nodup : (P.map (·.1)).Nodup
  spanned : ∀ cp ∈ P, Spans m rows cp.2
  covers : ∀ r ∈ rows, Spans m (P.map (·.2)) r

theorem pivInv_nil (m : Nat) : PivInv m [] [] :=
  ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem reduceRow_cons (cp : Nat × List Bool) (P : List (Nat × List Bool)) (r : List Bool) :
    reduceRow (cp :: P) r = reduceRow P (if r.getD cp.1 false then xorRow r cp.2 else r) := rfl

theorem reduceRow_length {m : Nat} :
    ∀ (P : List (Nat × List Bool)) (r : List Bool), (∀ cp ∈ P, cp.2.length = m) →
      r.length = m → (reduceRow P r).length = m := by
  intro P
  induction P with
  | nil => intro r _ hr; exact hr
  | cons cp P ih =>
      intro r hP hr
      rw [reduceRow_cons]
      refine ih _ (fun x hx => hP x (List.mem_cons_of_mem _ hx)) ?_
      cases hc : r.getD cp.1 false
      · simpa [hc] using hr
      · simp only [reduceIte]
        rw [length_xorRow, hr, hP cp (List.mem_cons_self ..)]
        omega

/-- `reduceRow` XORs a span of the pivot rows into the row. -/
theorem reduceRow_spec {m : Nat} :
    ∀ (P : List (Nat × List Bool)) (r : List Bool), (∀ cp ∈ P, cp.2.length = m) →
      r.length = m →
      ∃ q, Spans m (P.map (·.2)) q ∧ q.length = m ∧ reduceRow P r = xorRow q r := by
  intro P
  induction P with
  | nil =>
      intro r _ hr
      exact ⟨zeroW m, Spans.zero, by simp, (xorRow_zeroW_left hr).symm⟩
  | cons cp P ih =>
      intro r hP hr
      have hcp : cp.2.length = m := hP cp (List.mem_cons_self ..)
      have hP' : ∀ x ∈ P, x.2.length = m := fun x hx => hP x (List.mem_cons_of_mem _ hx)
      have hlen' : ∀ b ∈ (cp :: P).map (·.2), b.length = m := by
        intro b hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
        exact hP x hx
      rw [reduceRow_cons]
      cases hc : r.getD cp.1 false
      · obtain ⟨q, hq, hqlen, heq⟩ := ih r hP' hr
        refine ⟨q, Spans.mono (fun b hb => List.mem_cons_of_mem _ hb) hq, hqlen, ?_⟩
        simpa [hc] using heq
      · have hr1 : (xorRow r cp.2).length = m := by
          rw [length_xorRow, hr, hcp]; omega
        obtain ⟨q, hq, hqlen, heq⟩ := ih (xorRow r cp.2) hP' hr1
        refine ⟨xorRow q cp.2, ?_, ?_, ?_⟩
        · exact Spans.xor_closed hlen'
            (Spans.mono (fun b hb => List.mem_cons_of_mem _ hb) hq)
            (Spans.mem hlen' (by exact List.mem_map.mpr ⟨cp, List.mem_cons_self .., rfl⟩))
        · rw [length_xorRow, hqlen, hcp]; omega
        · simp only [reduceIte]
          rw [heq, xorRow_comm r cp.2, ← xorRow_assoc hqlen hcp hr]

theorem reduceRow_getD_const {m c : Nat} (hc : c < m) :
    ∀ (P : List (Nat × List Bool)) (r : List Bool), (∀ cp ∈ P, cp.2.length = m) →
      r.length = m → (∀ cp ∈ P, cp.2.getD c false = false) →
      (reduceRow P r).getD c false = r.getD c false := by
  intro P
  induction P with
  | nil => intro r _ _ _; rfl
  | cons cp P ih =>
      intro r hP hr hz
      rw [reduceRow_cons]
      have hcp : cp.2.length = m := hP cp (List.mem_cons_self ..)
      have hP' : ∀ x ∈ P, x.2.length = m := fun x hx => hP x (List.mem_cons_of_mem _ hx)
      have hz' : ∀ x ∈ P, x.2.getD c false = false := fun x hx => hz x (List.mem_cons_of_mem _ hx)
      cases hb : r.getD cp.1 false
      · rw [if_neg (by simp)]
        exact ih r hP' hr hz'
      · rw [if_pos rfl]
        rw [ih _ hP' (by rw [length_xorRow, hr, hcp]; omega) hz']
        rw [getD_xorRow (by omega) (by rw [hcp]; omega), hz cp (List.mem_cons_self ..)]
        cases r.getD c false <;> rfl

/-- After reduction, the row vanishes at every pivot column (unit + cross + distinct columns). -/
theorem reduceRow_pivot_zero {m : Nat} :
    ∀ (P : List (Nat × List Bool)) (r : List Bool),
      (∀ cp ∈ P, cp.1 < m) → (∀ cp ∈ P, cp.2.length = m) →
      (∀ cp ∈ P, cp.2.getD cp.1 false = true) →
      (∀ cp ∈ P, ∀ cq ∈ P, cp.1 ≠ cq.1 → cp.2.getD cq.1 false = false) →
      (P.map (·.1)).Nodup → r.length = m →
      ∀ cp ∈ P, (reduceRow P r).getD cp.1 false = false := by
  intro P
  induction P with
  | nil => intro r _ _ _ _ _ _ cp h; exact absurd h (by simp)
  | cons cp₀ P ih =>
      intro r hlt hlen hunit hcross hnodup hr cq hcq
      have hc₀ : cp₀.2.length = m := hlen cp₀ (List.mem_cons_self ..)
      have hlt' : ∀ x ∈ P, x.1 < m := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
      have hlen' : ∀ x ∈ P, x.2.length = m := fun x hx => hlen x (List.mem_cons_of_mem _ hx)
      have hunit' : ∀ x ∈ P, x.2.getD x.1 false = true :=
        fun x hx => hunit x (List.mem_cons_of_mem _ hx)
      have hcross' : ∀ cp ∈ P, ∀ cq ∈ P, cp.1 ≠ cq.1 → cp.2.getD cq.1 false = false :=
        fun x hx y hy => hcross x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      have hnodup' : (P.map (·.1)).Nodup := (List.nodup_cons.mp hnodup).2
      have hc₀notin : cp₀.1 ∉ P.map (·.1) := (List.nodup_cons.mp hnodup).1
      rw [reduceRow_cons]
      rcases List.mem_cons.mp hcq with rfl | hq
      · have hPzero : ∀ x ∈ P, x.2.getD cq.1 false = false := by
          intro x hx
          refine hcross x (List.mem_cons_of_mem _ hx) cq (List.mem_cons_self ..) ?_
          intro hcol
          exact hc₀notin (hcol ▸ List.mem_map.mpr ⟨x, hx, rfl⟩)
        have hclt : cq.1 < m := hlt cq (List.mem_cons_self ..)
        cases hb : r.getD cq.1 false
        · rw [if_neg (by simp)]
          rw [reduceRow_getD_const hclt P r hlen' hr hPzero, hb]
        · rw [if_pos rfl]
          rw [reduceRow_getD_const hclt P _ hlen'
            (by rw [length_xorRow, hr, hc₀]; omega) hPzero]
          rw [getD_xorRow (by omega) (by rw [hc₀]; omega), hb,
            hunit cq (List.mem_cons_self ..)]
          rfl
      · cases hb : r.getD cp₀.1 false
        · rw [if_neg (by simp)]
          exact ih r hlt' hlen' hunit' hcross' hnodup' hr cq hq
        · rw [if_pos rfl]
          exact ih _ hlt' hlen' hunit' hcross' hnodup'
            (by rw [length_xorRow, hr, hc₀]; omega) cq hq

/-- `echelon`'s fold step, named (definitionally the lambda in `echelon`). -/
def echStep (pivots : List (Nat × List Bool)) (r : List Bool) : List (Nat × List Bool) :=
  match (reduceRow pivots r).findIdx? id with
  | some c =>
      (c, reduceRow pivots r) ::
        pivots.map (fun cp =>
          (cp.1, if cp.2.getD c false then xorRow cp.2 (reduceRow pivots r) else cp.2))
  | none => pivots

theorem echelon_eq_foldl (rows : List (List Bool)) : echelon rows = rows.foldl echStep [] := rfl

/-- **★ THE STEP PRESERVES THE INVARIANT** — the heart of the elimination correctness. -/
theorem pivInv_step {m : Nat} {done : List (List Bool)} {P : List (Nat × List Bool)}
    (hdone : ∀ x ∈ done, x.length = m) (hinv : PivInv m done P)
    {r : List Bool} (hr : r.length = m) :
    PivInv m (done ++ [r]) (echStep P r) := by
  have hdone' : ∀ x ∈ done ++ [r], x.length = m := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hdone x hx
    · rw [List.mem_singleton.mp hx]; exact hr
  have holdlen : ∀ b ∈ P.map (·.2), b.length = m := by
    intro b hb
    obtain ⟨cp, hcp, rfl⟩ := List.mem_map.mp hb
    exact hinv.len cp hcp
  have hspan_done : ∀ b ∈ P.map (·.2), Spans m done b := by
    intro b hb
    obtain ⟨cp, hcp, rfl⟩ := List.mem_map.mp hb
    exact hinv.spanned cp hcp
  have hr'len : (reduceRow P r).length = m := reduceRow_length P r hinv.len hr
  obtain ⟨q, hqspan, hqlen, hqeq⟩ := reduceRow_spec P r hinv.len hr
  have hrq : r = xorRow q (reduceRow P r) := by
    rw [hqeq, xorRow_self_cancel hqlen hr]
  have hzero : ∀ cp ∈ P, (reduceRow P r).getD cp.1 false = false :=
    reduceRow_pivot_zero P r hinv.col_lt hinv.len hinv.unit hinv.cross hinv.nodup hr
  have hq_done : Spans m (done ++ [r]) q :=
    Spans.mono (fun b hb => List.mem_append_left _ hb)
      (hqspan.trans_basis hdone hspan_done)
  have hr'span : Spans m (done ++ [r]) (reduceRow P r) := by
    rw [hqeq]
    exact Spans.xor_closed hdone' hq_done
      (Spans.mem hdone' (List.mem_append_right _ (by simp)))
  cases hfind : (reduceRow P r).findIdx? id with
  | none =>
      have hEs : echStep P r = P := by unfold echStep; rw [hfind]
      rw [hEs]
      have hall := List.findIdx?_eq_none_iff.mp hfind
      have hr'z : reduceRow P r = zeroW m := by
        refine List.ext_getElem (by simp [hr'len]) (fun j h1 h2 => ?_)
        have := hall _ (List.getElem_mem h1)
        simpa using this
      refine ⟨hinv.col_lt, hinv.len, hinv.unit, hinv.cross, hinv.nodup, ?_, ?_⟩
      · exact fun cp hcp =>
          Spans.mono (fun b hb => List.mem_append_left _ hb) (hinv.spanned cp hcp)
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hinv.covers x hx
        · rw [List.mem_singleton.mp hx, hrq, hr'z, xorRow_zeroW_right hqlen]
          exact hqspan
  | some c =>
      have hEs : echStep P r = (c, reduceRow P r) :: P.map (fun cp =>
          (cp.1, if cp.2.getD c false then xorRow cp.2 (reduceRow P r) else cp.2)) := by
        unfold echStep; rw [hfind]
      rw [hEs]
      obtain ⟨hclen, hcval, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
      have hcm : c < m := hr'len ▸ hclen
      have hcunit : (reduceRow P r).getD c false = true := by
        rw [getD_in hclen]
        simpa using hcval
      have hcnot : ∀ cp ∈ P, cp.1 ≠ c := by
        intro cp hcp hcol
        have h1 := hzero cp hcp
        rw [hcol] at h1
        exact Bool.noConfusion (hcunit.symm.trans h1)
      set r' := reduceRow P r with hr'def
      set updP := P.map (fun cp =>
        (cp.1, if cp.2.getD c false then xorRow cp.2 r' else cp.2)) with hupdP
      have hupdcols : updP.map (·.1) = P.map (·.1) := by
        rw [hupdP, List.map_map]
        rfl
      have hnewlen : ∀ b ∈ ((c, r') :: updP).map (·.2), b.length = m := by
        intro b hb
        obtain ⟨cp, hcp, rfl⟩ := List.mem_map.mp hb
        rcases List.mem_cons.mp hcp with rfl | hcp
        · exact hr'len
        · obtain ⟨cq, hcq, rfl⟩ := List.mem_map.mp hcp
          show (if cq.2.getD c false then xorRow cq.2 r' else cq.2).length = m
          cases hb2 : cq.2.getD c false
          · rw [if_neg (by simp)]
            exact hinv.len cq hcq
          · rw [if_pos rfl]
            rw [length_xorRow, hinv.len cq hcq, hr'len]
            omega
      have hr'mem : r' ∈ ((c, r') :: updP).map (·.2) :=
        List.mem_map.mpr ⟨(c, r'), List.mem_cons_self .., rfl⟩
      have hmem_upd : ∀ cq ∈ P,
          (if cq.2.getD c false then xorRow cq.2 r' else cq.2) ∈ ((c, r') :: updP).map (·.2) := by
        intro cq hcq
        exact List.mem_map.mpr
          ⟨_, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨cq, hcq, rfl⟩), rfl⟩
      have hold_in_new : ∀ cq ∈ P, Spans m (((c, r') :: updP).map (·.2)) cq.2 := by
        intro cq hcq
        have hmem := hmem_upd cq hcq
        cases hb2 : cq.2.getD c false
        · rw [hb2] at hmem
          rw [if_neg (by simp)] at hmem
          exact Spans.mem hnewlen hmem
        · rw [hb2] at hmem
          rw [if_pos rfl] at hmem
          have h1 : Spans m (((c, r') :: updP).map (·.2)) (xorRow cq.2 r') :=
            Spans.mem hnewlen hmem
          have h2 : Spans m (((c, r') :: updP).map (·.2)) r' := Spans.mem hnewlen hr'mem
          have h3 := Spans.xor_closed hnewlen h1 h2
          rwa [xorRow_cancel_right (hinv.len cq hcq) hr'len] at h3
      have hold_span_new : ∀ b ∈ P.map (·.2), Spans m (((c, r') :: updP).map (·.2)) b := by
        intro b hb
        obtain ⟨cq, hcq, rfl⟩ := List.mem_map.mp hb
        exact hold_in_new cq hcq
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- col_lt
        intro cp hcp
        rcases List.mem_cons.mp hcp with rfl | hcp
        · exact hcm
        · obtain ⟨cq, hcq, rfl⟩ := List.mem_map.mp hcp
          exact hinv.col_lt cq hcq
      · -- len
        intro cp hcp
        rcases List.mem_cons.mp hcp with rfl | hcp
        · exact hr'len
        · obtain ⟨cq, hcq, rfl⟩ := List.mem_map.mp hcp
          show (if cq.2.getD c false then xorRow cq.2 r' else cq.2).length = m
          cases hb2 : cq.2.getD c false
          · rw [if_neg (by simp)]
            exact hinv.len cq hcq
          · rw [if_pos rfl]
            rw [length_xorRow, hinv.len cq hcq, hr'len]
            omega
      · -- unit
        intro cp hcp
        rcases List.mem_cons.mp hcp with rfl | hcp
        · exact hcunit
        · obtain ⟨cq, hcq, rfl⟩ := List.mem_map.mp hcp
          show (if cq.2.getD c false then xorRow cq.2 r' else cq.2).getD cq.1 false = true
          cases hb2 : cq.2.getD c false
          · rw [if_neg (by simp)]
            exact hinv.unit cq hcq
          · rw [if_pos rfl]
            rw [getD_xorRow (by rw [hinv.len cq hcq]; exact hinv.col_lt cq hcq)
              (by rw [hr'len]; exact hinv.col_lt cq hcq)]
            rw [hinv.unit cq hcq, hzero cq hcq]
            rfl
      · -- cross
        intro cp hcp cq hcq hne
        rcases List.mem_cons.mp hcp with rfl | hcp
        · rcases List.mem_cons.mp hcq with rfl | hcq
          · exact absurd rfl hne
          · obtain ⟨cq₀, hcq₀, rfl⟩ := List.mem_map.mp hcq
            exact hzero cq₀ hcq₀
        · obtain ⟨cp₀, hcp₀, rfl⟩ := List.mem_map.mp hcp
          rcases List.mem_cons.mp hcq with rfl | hcq
          · show (if cp₀.2.getD c false then xorRow cp₀.2 r' else cp₀.2).getD c false = false
            cases hb2 : cp₀.2.getD c false
            · rw [if_neg (by simp)]
              exact hb2
            · rw [if_pos rfl]
              rw [getD_xorRow (by rw [hinv.len cp₀ hcp₀]; exact hcm)
                (by rw [hr'len]; exact hcm)]
              rw [hb2, hcunit]
              rfl
          · obtain ⟨cq₀, hcq₀, rfl⟩ := List.mem_map.mp hcq
            have hne' : cp₀.1 ≠ cq₀.1 := hne
            show (if cp₀.2.getD c false then xorRow cp₀.2 r' else cp₀.2).getD cq₀.1 false = false
            cases hb2 : cp₀.2.getD c false
            · rw [if_neg (by simp)]
              exact hinv.cross cp₀ hcp₀ cq₀ hcq₀ hne'
            · rw [if_pos rfl]
              rw [getD_xorRow (by rw [hinv.len cp₀ hcp₀]; exact hinv.col_lt cq₀ hcq₀)
                (by rw [hr'len]; exact hinv.col_lt cq₀ hcq₀)]
              rw [hinv.cross cp₀ hcp₀ cq₀ hcq₀ hne', hzero cq₀ hcq₀]
              rfl
      · -- nodup
        rw [List.map_cons, hupdcols]
        refine List.nodup_cons.mpr ⟨?_, hinv.nodup⟩
        intro hmem
        obtain ⟨cp, hcp, hcol⟩ := List.mem_map.mp hmem
        exact hcnot cp hcp hcol
      · -- spanned
        intro cp hcp
        rcases List.mem_cons.mp hcp with rfl | hcp
        · exact hr'span
        · obtain ⟨cq, hcq, rfl⟩ := List.mem_map.mp hcp
          have hbase : Spans m (done ++ [r]) cq.2 :=
            Spans.mono (fun b hb => List.mem_append_left _ hb) (hinv.spanned cq hcq)
          show Spans m (done ++ [r]) (if cq.2.getD c false then xorRow cq.2 r' else cq.2)
          cases hb2 : cq.2.getD c false
          · rw [if_neg (by simp)]
            exact hbase
          · rw [if_pos rfl]
            exact Spans.xor_closed hdone' hbase hr'span
      · -- covers
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact Spans.trans_basis hnewlen hold_span_new (hinv.covers x hx)
        · rw [List.mem_singleton.mp hx, hrq]
          refine Spans.xor_closed hnewlen ?_ (Spans.mem hnewlen hr'mem)
          exact Spans.trans_basis hnewlen hold_span_new hqspan

theorem pivInv_foldl {m : Nat} :
    ∀ (todo done : List (List Bool)) (P : List (Nat × List Bool)),
      (∀ r ∈ todo, r.length = m) → (∀ x ∈ done, x.length = m) → PivInv m done P →
      PivInv m (done ++ todo) (todo.foldl echStep P) := by
  intro todo
  induction todo with
  | nil => intro done P _ _ h; simpa using h
  | cons r todo ih =>
      intro done P htodo hdone hinv
      have hr : r.length = m := htodo r (List.mem_cons_self ..)
      have hstep := pivInv_step hdone hinv hr
      have hdone' : ∀ x ∈ done ++ [r], x.length = m := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hdone x hx
        · rw [List.mem_singleton.mp hx]; exact hr
      have hrest := ih (done ++ [r]) (echStep P r)
        (fun x hx => htodo x (List.mem_cons_of_mem _ hx)) hdone' hstep
      simpa [List.append_assoc] using hrest

/-- **★★ THE ECHELON INVARIANT** — for length-`m` input rows, the pivot list is a reduced echelon
system with the same row space as the input. -/
theorem pivInv_echelon {m : Nat} {rows : List (List Bool)} (h : ∀ r ∈ rows, r.length = m) :
    PivInv m rows (echelon rows) := by
  have hres := pivInv_foldl rows [] [] h (by simp) (pivInv_nil m)
  rw [echelon_eq_foldl]
  simpa using hres

/-! ## 8. `nullBasis` — the emitted words, characterized -/

/-- The word `nullBasis` emits for free column `f` (definitional refactoring of the map body). -/
def nbWord (m : Nat) (rows : List (List Bool)) (f : Nat) : List Bool :=
  (List.range m).map (fun j => if j == f then true
    else match (echelon rows).find? (fun cp => cp.1 == j) with
      | some cp => cp.2.getD f false
      | none => false)

/-- The free (non-pivot) columns. -/
def freeCols (m : Nat) (rows : List (List Bool)) : List Nat :=
  (List.range m).filter (fun c => !((echelon rows).map (·.1)).contains c)

theorem nullBasis_eq (m : Nat) (rows : List (List Bool)) :
    nullBasis m rows = (freeCols m rows).map (nbWord m rows) := rfl

@[simp] theorem length_nbWord (m : Nat) (rows : List (List Bool)) (f : Nat) :
    (nbWord m rows f).length = m := by simp [nbWord]

theorem getD_nbWord {m : Nat} {rows : List (List Bool)} {f j : Nat} (hj : j < m) :
    (nbWord m rows f).getD j false
      = if j == f then true
        else match (echelon rows).find? (fun cp => cp.1 == j) with
          | some cp => cp.2.getD f false
          | none => false := by
  rw [getD_in (by simp [hj])]
  simp [nbWord]

theorem mem_freeCols_iff {m : Nat} {rows : List (List Bool)} {f : Nat} :
    f ∈ freeCols m rows ↔ f < m ∧ f ∉ (echelon rows).map (·.1) := by
  simp [freeCols, List.mem_filter, List.contains_iff_mem]

theorem freeCols_nodup (m : Nat) (rows : List (List Bool)) : (freeCols m rows).Nodup :=
  (List.nodup_range).filter _

/-- `find?` at a pivot column returns exactly that pivot (column `Nodup`). -/
theorem find?_col_eq {P : List (Nat × List Bool)} (hnd : (P.map (·.1)).Nodup)
    {c : Nat} {ρ : List Bool} (hmem : (c, ρ) ∈ P) :
    P.find? (fun cp => cp.1 == c) = some (c, ρ) := by
  have hsome : (P.find? (fun cp => cp.1 == c)).isSome := by
    rw [List.find?_isSome]
    exact ⟨(c, ρ), hmem, by simp⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
  have hqmem : q ∈ P := List.mem_of_find?_eq_some hq
  have hqcol : q.1 = c := by simpa using List.find?_some hq
  have heq : q = (c, ρ) := List.inj_on_of_nodup_map hnd hqmem hmem (by simp [hqcol])
  rw [hq, heq]

theorem find?_col_none {P : List (Nat × List Bool)} {c : Nat}
    (h : c ∉ P.map (·.1)) : P.find? (fun cp => cp.1 == c) = none := by
  rw [List.find?_eq_none]
  intro x hx
  simp only [beq_iff_eq]
  intro hxc
  exact h (hxc ▸ List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem getD_nbWord_self {m : Nat} {rows : List (List Bool)} {f : Nat} (hf : f < m) :
    (nbWord m rows f).getD f false = true := by
  rw [getD_nbWord hf]
  simp

theorem getD_nbWord_pivot {m : Nat} {rows : List (List Bool)} {c : Nat} {ρ : List Bool}
    (hnd : ((echelon rows).map (·.1)).Nodup) (hmem : (c, ρ) ∈ echelon rows)
    {f : Nat} (hcf : c ≠ f) (hc : c < m) :
    (nbWord m rows f).getD c false = ρ.getD f false := by
  rw [getD_nbWord hc, if_neg (by simp [hcf]), find?_col_eq hnd hmem]

theorem getD_nbWord_free {m : Nat} {rows : List (List Bool)} {j f : Nat} (hj : j < m)
    (hjp : j ∉ (echelon rows).map (·.1)) (hjf : j ≠ f) :
    (nbWord m rows f).getD j false = false := by
  rw [getD_nbWord hj, if_neg (by simp [hjf]), find?_col_none hjp]

/-! ## 9. ★★ SOUNDNESS — the basis lands in the null space -/

theorem dotB_pivot_nbWord {m : Nat} {rows : List (List Bool)}
    (hrows : ∀ r ∈ rows, r.length = m) {c : Nat} {ρ : List Bool}
    (hmem : (c, ρ) ∈ echelon rows) {f : Nat} (hf : f ∈ freeCols m rows) :
    dotB ρ (nbWord m rows f) = false := by
  have hinv := pivInv_echelon hrows
  obtain ⟨hfm, hfp⟩ := mem_freeCols_iff.mp hf
  have hρlen : ρ.length = m := hinv.len (c, ρ) hmem
  have hcm : c < m := hinv.col_lt (c, ρ) hmem
  have hcf : c ≠ f := fun h => hfp (h ▸ List.mem_map.mpr ⟨(c, ρ), hmem, rfl⟩)
  rw [dotB_eq_dotOn hρlen (length_nbWord m rows f), dotOn_eq_countP]
  rw [countP_parity_pair List.nodup_range (List.mem_range.mpr hcm) (List.mem_range.mpr hfm) hcf
    ?hsupp]
  case hsupp =>
    intro j hj hp
    rw [Bool.and_eq_true] at hp
    by_cases hjp : j ∈ (echelon rows).map (·.1)
    · left
      obtain ⟨cq, hcq, hcqcol⟩ := List.mem_map.mp hjp
      by_contra hjc
      have hzero := hinv.cross (c, ρ) hmem cq hcq (by
        show c ≠ cq.1
        rw [hcqcol]
        exact fun h => hjc h.symm)
      rw [hcqcol] at hzero
      rw [hzero] at hp
      exact Bool.noConfusion hp.1
    · right
      by_contra hjf
      have hzero := getD_nbWord_free (List.mem_range.mp hj) hjp hjf
      rw [hzero] at hp
      exact Bool.noConfusion hp.2
  · have h1 : ρ.getD c false = true := hinv.unit (c, ρ) hmem
    have h2 : (nbWord m rows f).getD c false = ρ.getD f false :=
      getD_nbWord_pivot hinv.nodup hmem hcf hcm
    have h3 : (nbWord m rows f).getD f false = true := getD_nbWord_self hfm
    rw [h1, h2, h3]
    cases ρ.getD f false <;> rfl

/-- **★★ SOUNDNESS.** Every emitted basis word is orthogonal to every input row. -/
theorem dotB_nullBasis {m : Nat} {rows : List (List Bool)} (hrows : ∀ r ∈ rows, r.length = m)
    {r : List Bool} (hr : r ∈ rows) {b : List Bool} (hb : b ∈ nullBasis m rows) :
    dotB r b = false := by
  have hinv := pivInv_echelon hrows
  rw [nullBasis_eq] at hb
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
  have hpivlen : ∀ x ∈ (echelon rows).map (·.2), x.length = m := by
    intro x hx
    obtain ⟨cq, hcq, rfl⟩ := List.mem_map.mp hx
    exact hinv.len cq hcq
  rw [dotB_comm]
  refine dotB_eq_false_of_spans hpivlen (hinv.covers r hr) ?_
  intro ρ hρ
  obtain ⟨cq, hcq, rfl⟩ := List.mem_map.mp hρ
  rw [dotB_comm]
  exact dotB_pivot_nbWord hrows (by simpa using hcq) hf

/-- Basis words have length `m`. -/
theorem length_mem_nullBasis {m : Nat} {rows : List (List Bool)} {b : List Bool}
    (hb : b ∈ nullBasis m rows) : b.length = m := by
  rw [nullBasis_eq] at hb
  obtain ⟨f, _, rfl⟩ := List.mem_map.mp hb
  exact length_nbWord m rows f

/-! ## 10. ★★★ COMPLETENESS — every null word is spanned by the basis -/

private theorem bne_eq_false {a b : Bool} (h : (a != b) = false) : a = b := by
  cases a <;> cases b <;> simp_all

/-- **★★★ COMPLETENESS.** A word orthogonal to every input row is an XOR-combination of the
emitted basis: its free coordinates select the basis words, and the pivot coordinates are forced to
agree by the null conditions on the (reduced) pivot rows. With `dotB_nullBasis` this is
`span (nullBasis) = L` — the elimination loses nothing and invents nothing. -/
theorem spans_nullBasis {m : Nat} {rows : List (List Bool)} (hrows : ∀ r ∈ rows, r.length = m)
    {w : List Bool} (hw : w.length = m) (hnull : ∀ r ∈ rows, dotB r w = false) :
    Spans m (nullBasis m rows) w := by
  have hinv := pivInv_echelon hrows
  have hpivnull : ∀ cp ∈ echelon rows, dotB cp.2 w = false := by
    intro cp hcp
    rw [dotB_comm]
    refine dotB_eq_false_of_spans hrows (hinv.spanned cp hcp) ?_
    intro b hb
    rw [dotB_comm]
    exact hnull b hb
  set sel := (freeCols m rows).filter (fun f => w.getD f false) with hsel
  have hself : ∀ f ∈ sel, f ∈ freeCols m rows := fun f hf => (List.mem_filter.mp hf).1
  have hselnd : sel.Nodup := (freeCols_nodup m rows).filter _
  have hnblen : ∀ x ∈ sel.map (nbWord m rows), x.length = m := by
    intro x hx
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
    exact length_nbWord m rows f
  have hkey : w = combo m (sel.map (nbWord m rows)) := by
    refine List.ext_getElem (by rw [hw, combo_length hnblen]) (fun j h1 h2 => ?_)
    have hjm : j < m := hw ▸ h1
    rw [← getD_in h1, ← getD_in h2, getD_combo hnblen hjm, List.map_map]
    have hmapped : sel.map ((fun x => x.getD j false) ∘ nbWord m rows)
        = sel.map (fun f => (nbWord m rows f).getD j false) := rfl
    rw [hmapped, xorList_map_eq_countP]
    by_cases hjp : j ∈ (echelon rows).map (·.1)
    · -- pivot column: forced by the null condition on its pivot row
      obtain ⟨cρ, hcρ, hcol⟩ := List.mem_map.mp hjp
      have hmemj : (j, cρ.2) ∈ echelon rows := by
        rw [← hcol]
        simpa using hcρ
      have hval : ∀ f ∈ sel, (nbWord m rows f).getD j false = cρ.2.getD f false := by
        intro f hf
        obtain ⟨hfm, hfp⟩ := mem_freeCols_iff.mp (hself f hf)
        have hjf : j ≠ f := fun h => hfp (h ▸ hjp)
        exact getD_nbWord_pivot hinv.nodup hmemj hjf hjm
      have hcsel : sel.countP (fun f => (nbWord m rows f).getD j false)
          = sel.countP (fun f => cρ.2.getD f false) :=
        List.countP_congr (fun f hf => by rw [hval f hf])
      have hcfree : sel.countP (fun f => cρ.2.getD f false)
          = (freeCols m rows).countP (fun f => cρ.2.getD f false && w.getD f false) := by
        rw [hsel, List.countP_filter]
      -- split the null condition over pivot/free columns
      have hnullρ := hpivnull cρ hcρ
      rw [dotB_eq_dotOn (hinv.len cρ hcρ) hw, dotOn_eq_countP] at hnullρ
      have hperm : ((List.range m).filter (fun c => ((echelon rows).map (·.1)).contains c))
          ++ freeCols m rows |>.Perm (List.range m) := by
        simpa [freeCols] using
          List.filter_append_perm (fun c => ((echelon rows).map (·.1)).contains c) (List.range m)
      rw [← hperm.countP_eq, List.countP_append, parity_add] at hnullρ
      have hpivnd : ((List.range m).filter
          (fun c => ((echelon rows).map (·.1)).contains c)).Nodup :=
        (List.nodup_range).filter _
      have hjmem : j ∈ (List.range m).filter
          (fun c => ((echelon rows).map (·.1)).contains c) :=
        List.mem_filter.mpr ⟨List.mem_range.mpr hjm, by
          simpa [List.contains_iff_mem] using hjp⟩
      have hpivpart : (((List.range m).filter
            (fun c => ((echelon rows).map (·.1)).contains c)).countP
              (fun j' => cρ.2.getD j' false && w.getD j' false) % 2 == 1)
          = w.getD j false := by
        rw [countP_parity_single hpivnd hjmem ?hsupp]
        · have hunit : cρ.2.getD j false = true := by
            have := hinv.unit cρ hcρ
            rwa [hcol] at this
          rw [hunit]
          simp
        case hsupp =>
          intro j' hj' hpj'
          rw [Bool.and_eq_true] at hpj'
          have hj'p : j' ∈ (echelon rows).map (·.1) := by
            have := (List.mem_filter.mp hj').2
            simpa [List.contains_iff_mem] using this
          by_contra hne
          obtain ⟨cq', hcq', hcol'⟩ := List.mem_map.mp hj'p
          have hzero := hinv.cross cρ hcρ cq' hcq' (by
            show cρ.1 ≠ cq'.1
            rw [hcol, hcol']
            exact fun h => hne h.symm)
          rw [hcol'] at hzero
          rw [hzero] at hpj'
          exact Bool.noConfusion hpj'.1
      rw [hpivpart] at hnullρ
      have hfree_eq := bne_eq_false hnullρ
      rw [hcsel, hcfree, ← hfree_eq]
    · -- free column: the indicator of membership in `sel`
      have hsupp : ∀ f ∈ sel, (nbWord m rows f).getD j false = true → f = j := by
        intro f hf hval
        by_contra hne
        have := getD_nbWord_free hjm hjp (fun h => hne h.symm)
        rw [this] at hval
        exact Bool.noConfusion hval
      by_cases hjsel : j ∈ sel
      · rw [countP_parity_single hselnd hjsel hsupp, getD_nbWord_self hjm]
        have := (List.mem_filter.mp hjsel).2
        simpa using this.symm
      · have hz : sel.countP (fun f => (nbWord m rows f).getD j false) = 0 := by
          refine countP_eq_zero_of_support (fun f hf => ?_)
          cases hv : (nbWord m rows f).getD j false
          · rfl
          · exact absurd (hsupp f hf hv ▸ hf) hjsel
        rw [hz]
        have hwj : w.getD j false = false := by
          by_contra hcontra
          have hwj' : w.getD j false = true := by
            cases hv : w.getD j false
            · exact absurd hv hcontra
            · rfl
          have hjfree : j ∈ freeCols m rows := mem_freeCols_iff.mpr ⟨hjm, hjp⟩
          exact hjsel (List.mem_filter.mpr ⟨hjfree, by rw [hwj']⟩)
        rw [hwj]
        rfl
  rw [hkey]
  refine spans_combo ?_
  intro x hx
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
  rw [nullBasis_eq]
  exact List.mem_map.mpr ⟨f, hself f hf, rfl⟩
