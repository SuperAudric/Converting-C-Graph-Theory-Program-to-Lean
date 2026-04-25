import FullCorrectness.Equivariance.ComparisonSort

/-!
# `comparePathSegments` total preorder and `comparePathsBetween` lifting
(`FullCorrectness.Equivariance.ComparePathSegments`)

Proves that `comparePathSegments` is a total preorder (reflexive, both antisymmetries,
`≤`-transitive) after the algorithm refactor that replaced the `panic!` bottom/inner
mixed case with a fixed `bottom < inner` ordering.

Also provides the `orderInsensitiveListCmp` lifting helpers (reflexivity closed;
swap/trans sorry'd pending careful foldl-reduction handling) and states
`comparePathsBetween_total_preorder` (sorry'd: requires lifting through
`orderInsensitiveListCmp`).

## Sorry status
- `comparePathsBetween_total_preorder` : `sorry` — lifting `_swap` and `_trans` through
  `orderInsensitiveListCmp` requires foldl-induction with careful beta-reduced form
  matching (see the docstring for guidance).
-/

namespace Graph

variable {n : Nat}


/-- The cmp value for inner-inner pairs reduces to a 9-case classification on
trichotomies of `xR vs yR` and `xe vs ye`. This helper extracts each `.lt`/`.eq`/`.gt`
characterization in a uniform way so the surrounding total-preorder proof can chain them
with `omega`. -/
private theorem cmpInner_eq_lt (xR yR xe ye : Nat)
    (h : yR < xR ∨ (xR = yR ∧ ye < xe)) :
    (if xR != yR then compare yR xR else if xe != ye then compare ye xe else Ordering.eq)
      = Ordering.lt := by
  rcases h with h_lt | ⟨h_eq, h_e_lt⟩
  · have h_neq : xR ≠ yR := Ne.symm (Nat.ne_of_lt h_lt)
    rw [if_pos (by simp [h_neq])]
    exact Nat.compare_eq_lt.mpr h_lt
  · have h_neq : ¬ (xR != yR) = true := by simp [h_eq]
    have h_e_neq : xe ≠ ye := Ne.symm (Nat.ne_of_lt h_e_lt)
    rw [if_neg h_neq, if_pos (by simp [h_e_neq])]
    exact Nat.compare_eq_lt.mpr h_e_lt

private theorem cmpInner_eq_gt (xR yR xe ye : Nat)
    (h : xR < yR ∨ (xR = yR ∧ xe < ye)) :
    (if xR != yR then compare yR xR else if xe != ye then compare ye xe else Ordering.eq)
      = Ordering.gt := by
  rcases h with h_lt | ⟨h_eq, h_e_lt⟩
  · have h_neq : xR ≠ yR := Nat.ne_of_lt h_lt
    rw [if_pos (by simp [h_neq])]
    exact Nat.compare_eq_gt.mpr h_lt
  · have h_neq : ¬ (xR != yR) = true := by simp [h_eq]
    have h_e_neq : xe ≠ ye := Nat.ne_of_lt h_e_lt
    rw [if_neg h_neq, if_pos (by simp [h_e_neq])]
    exact Nat.compare_eq_gt.mpr h_e_lt

private theorem cmpInner_eq_eq (xR yR xe ye : Nat)
    (hR : xR = yR) (hE : xe = ye) :
    (if xR != yR then compare yR xR else if xe != ye then compare ye xe else Ordering.eq)
      = Ordering.eq := by
  rw [if_neg (by simp [hR]), if_neg (by simp [hE])]

/-- The cmp value for inner-inner pairs is exactly one of `.lt`/`.eq`/`.gt` — partition
into three exhaustive cases parameterized by trichotomy. -/
private theorem cmpInner_trichotomy (xR yR xe ye : Nat) :
    (xR < yR ∨ (xR = yR ∧ xe < ye)) ∨
    (xR = yR ∧ xe = ye) ∨
    (yR < xR ∨ (xR = yR ∧ ye < xe)) := by
  rcases Nat.lt_trichotomy xR yR with hR_lt | hR_eq | hR_gt
  · left; left; exact hR_lt
  · rcases Nat.lt_trichotomy xe ye with hE_lt | hE_eq | hE_gt
    · left; right; exact ⟨hR_eq, hE_lt⟩
    · right; left; exact ⟨hR_eq, hE_eq⟩
    · right; right; right; exact ⟨hR_eq, hE_gt⟩
  · right; right; left; exact hR_gt

/-- `comparePathSegments` is a total preorder (reflexive, antisymmetric in both
directions, `≤`-transitive). The four conjuncts are exactly the hypotheses needed by
`orderInsensitiveListCmp_perm` (via `sortedPerm_class_eq`).

The mixed `bottom`/`inner` cases are handled by the fixed ordering `.bottom < .inner`
that replaced the original `panic!` — see
[LeanGraphCanonizerV4.lean:119](LeanGraphCanonizerV4.lean#L119). For inner-inner the
`cmpInner_*` helpers reduce the comparator value to a Nat-tuple condition. -/
theorem comparePathSegments_total_preorder {vc : Nat}
    (vts : Array VertexType) (br : Nat → Nat → Nat → Nat) :
    (∀ a : PathSegment vc, comparePathSegments vts br a a = Ordering.eq) ∧
    (∀ a b : PathSegment vc, comparePathSegments vts br a b = Ordering.lt →
                              comparePathSegments vts br b a = Ordering.gt) ∧
    (∀ a b : PathSegment vc, comparePathSegments vts br a b = Ordering.gt →
                              comparePathSegments vts br b a = Ordering.lt) ∧
    (∀ a b c : PathSegment vc, comparePathSegments vts br a b ≠ Ordering.gt →
                                comparePathSegments vts br b c ≠ Ordering.gt →
                                comparePathSegments vts br a c ≠ Ordering.gt) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- refl
    intro a
    cases a with
    | bottom v =>
      show compare (vts.getD v.val 0) (vts.getD v.val 0) = Ordering.eq
      exact Nat.compare_eq_eq.mpr rfl
    | inner e d s e' => exact cmpInner_eq_eq _ _ _ _ rfl rfl
  · -- antisym₁: .lt → .gt
    intros a b h_lt
    cases a with
    | bottom xVI =>
      cases b with
      | bottom yVI =>
        show compare (vts.getD yVI.val 0) (vts.getD xVI.val 0) = Ordering.gt
        have h_xy_lt : compare (vts.getD xVI.val 0) (vts.getD yVI.val 0) = Ordering.lt := h_lt
        exact Nat.compare_eq_gt.mpr (Nat.compare_eq_lt.mp h_xy_lt)
      | inner _ _ _ _ =>
        simp only [comparePathSegments]
    | inner xe xd xs xend =>
      cases b with
      | bottom _ =>
        simp only [comparePathSegments] at h_lt
        exact Ordering.noConfusion h_lt
      | inner ye yd ys yend =>
        simp only [comparePathSegments] at h_lt
        simp only [comparePathSegments]
        rcases cmpInner_trichotomy (br xd xs.val xend.val) (br yd ys.val yend.val) xe ye
          with h_case | h_case | h_case
        · rw [cmpInner_eq_gt _ _ _ _ h_case] at h_lt; exact Ordering.noConfusion h_lt
        · rw [cmpInner_eq_eq _ _ _ _ h_case.1 h_case.2] at h_lt; exact Ordering.noConfusion h_lt
        · apply cmpInner_eq_gt
          rcases h_case with h | ⟨h1, h2⟩
          · left; exact h
          · right; exact ⟨h1.symm, h2⟩
  · -- antisym₂: .gt → .lt
    intros a b h_gt
    cases a with
    | bottom xVI =>
      cases b with
      | bottom yVI =>
        show compare (vts.getD yVI.val 0) (vts.getD xVI.val 0) = Ordering.lt
        have h_xy_gt : compare (vts.getD xVI.val 0) (vts.getD yVI.val 0) = Ordering.gt := h_gt
        exact Nat.compare_eq_lt.mpr (Nat.compare_eq_gt.mp h_xy_gt)
      | inner _ _ _ _ =>
        simp only [comparePathSegments] at h_gt
        exact Ordering.noConfusion h_gt
    | inner xe xd xs xend =>
      cases b with
      | bottom _ =>
        simp only [comparePathSegments]
      | inner ye yd ys yend =>
        simp only [comparePathSegments] at h_gt
        simp only [comparePathSegments]
        rcases cmpInner_trichotomy (br xd xs.val xend.val) (br yd ys.val yend.val) xe ye
          with h_case | h_case | h_case
        · apply cmpInner_eq_lt
          rcases h_case with h | ⟨h1, h2⟩
          · left; exact h
          · right; exact ⟨h1.symm, h2⟩
        · rw [cmpInner_eq_eq _ _ _ _ h_case.1 h_case.2] at h_gt; exact Ordering.noConfusion h_gt
        · rw [cmpInner_eq_lt _ _ _ _ h_case] at h_gt; exact Ordering.noConfusion h_gt
  · -- ≤-trans
    intros a b c hab hbc
    cases a with
    | bottom xVI =>
      cases b with
      | bottom yVI =>
        cases c with
        | bottom zVI =>
          show compare (vts.getD xVI.val 0) (vts.getD zVI.val 0) ≠ Ordering.gt
          have hab' : compare (vts.getD xVI.val 0) (vts.getD yVI.val 0) ≠ Ordering.gt := hab
          have hbc' : compare (vts.getD yVI.val 0) (vts.getD zVI.val 0) ≠ Ordering.gt := hbc
          intro h_gt
          have h_le_xy : (vts.getD xVI.val 0 : Nat) ≤ vts.getD yVI.val 0 := by
            by_contra h
            exact hab' (Nat.compare_eq_gt.mpr (Nat.lt_of_not_le h))
          have h_le_yz : (vts.getD yVI.val 0 : Nat) ≤ vts.getD zVI.val 0 := by
            by_contra h
            exact hbc' (Nat.compare_eq_gt.mpr (Nat.lt_of_not_le h))
          have h_lt_zx : (vts.getD zVI.val 0 : Nat) < vts.getD xVI.val 0 :=
            Nat.compare_eq_gt.mp h_gt
          exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans h_le_xy h_le_yz) h_lt_zx)
        | inner _ _ _ _ => intro h; cases h
      | inner be bd bs bend =>
        cases c with
        | bottom cVI =>
          have : comparePathSegments vts br (PathSegment.inner be bd bs bend)
                  (PathSegment.bottom cVI) = Ordering.gt := by
            simp only [comparePathSegments]
          exact absurd this hbc
        | inner _ _ _ _ => intro h; cases h
    | inner xe xd xs xend =>
      cases b with
      | bottom bVI =>
        have : comparePathSegments vts br (PathSegment.inner xe xd xs xend)
                (PathSegment.bottom bVI) = Ordering.gt := by
          simp only [comparePathSegments]
        exact absurd this hab
      | inner ye yd ys yend =>
        cases c with
        | bottom cVI =>
          have : comparePathSegments vts br (PathSegment.inner ye yd ys yend)
                  (PathSegment.bottom cVI) = Ordering.gt := by
            simp only [comparePathSegments]
          exact absurd this hbc
        | inner ze zd zs zend =>
          -- Inner-inner-inner trans by trichotomy.
          set xR := br xd xs.val xend.val
          set yR := br yd ys.val yend.val
          set zR := br zd zs.val zend.val
          change (if xR != yR then compare yR xR
                  else if xe != ye then compare ye xe else Ordering.eq) ≠ Ordering.gt at hab
          change (if yR != zR then compare zR yR
                  else if ye != ze then compare ze ye else Ordering.eq) ≠ Ordering.gt at hbc
          show (if xR != zR then compare zR xR
                else if xe != ze then compare ze xe else Ordering.eq) ≠ Ordering.gt
          intro h_gt
          -- Extract: ¬(cmp a b = .gt), ¬(cmp b c = .gt), cmp a c = .gt.
          -- By trichotomy on (xR, yR) and (xe, ye): cmp a b ∈ {.lt, .eq, .gt}.
          --   .gt forbidden by hab. So cmp a b ∈ {.lt, .eq}, i.e., (xR, xe) ≥_lex (yR, ye).
          rcases cmpInner_trichotomy xR yR xe ye with h_xy | ⟨h_xy_R, h_xy_e⟩ | h_xy
          · -- xR < yR ∨ (xR = yR ∧ xe < ye): cmp a b = .gt, contradicts hab.
            exact hab (cmpInner_eq_gt _ _ _ _ h_xy)
          · -- xR = yR ∧ xe = ye: rename.
            -- Use trichotomy on (yR, zR), (ye, ze).
            rcases cmpInner_trichotomy yR zR ye ze with h_yz | ⟨h_yz_R, h_yz_e⟩ | h_yz
            · exact hbc (cmpInner_eq_gt _ _ _ _ h_yz)
            · -- All equal. cmp a c should be eq.
              have h_xz : xR = zR ∧ xe = ze := ⟨h_xy_R.trans h_yz_R, h_xy_e.trans h_yz_e⟩
              rw [cmpInner_eq_eq _ _ _ _ h_xz.1 h_xz.2] at h_gt
              exact Ordering.noConfusion h_gt
            · -- yR < zR ∨ (yR = zR ∧ ze < ye): cmp b c = .lt.
              -- We have xR = yR, xe = ye, AND (zR < yR OR yR = zR ∧ ze < ye).
              -- Want contradiction with cmp a c = .gt, i.e., xR < zR ∨ (xR = zR ∧ xe < ze).
              rcases cmpInner_trichotomy xR zR xe ze with h_xz | ⟨h_xz_R, h_xz_e⟩ | h_xz
              · -- xR < zR ∨ ... : but rcases h_yz gives zR < yR or ye < ze with yR = zR.
                rcases h_yz with h | ⟨h1, h2⟩
                · -- zR < yR. With xR = yR: zR < xR. Combined with h_xz: contradiction.
                  rcases h_xz with h_xz_lt | ⟨h_xz_eq, h_xz_lt⟩
                  · omega
                  · omega
                · -- yR = zR ∧ ze < ye. With xR = yR: xR = zR, xe = ye > ze.
                  rcases h_xz with h_xz_lt | ⟨h_xz_eq, h_xz_lt⟩
                  · omega
                  · omega
              · -- xR = zR ∧ xe = ze: cmp a c = .eq, but h_gt says .gt.
                rw [cmpInner_eq_eq _ _ _ _ h_xz_R h_xz_e] at h_gt
                exact Ordering.noConfusion h_gt
              · -- zR < xR ∨ (xR = zR ∧ ze < xe): consistent with hab and hbc; not h_gt.
                rw [cmpInner_eq_lt _ _ _ _ h_xz] at h_gt
                exact Ordering.noConfusion h_gt
          · -- yR < xR ∨ (xR = yR ∧ ye < xe): cmp a b = .lt (consistent with hab).
            rcases cmpInner_trichotomy yR zR ye ze with h_yz | ⟨h_yz_R, h_yz_e⟩ | h_yz
            · exact hbc (cmpInner_eq_gt _ _ _ _ h_yz)
            · -- yR = zR ∧ ye = ze. So cmp b c = .eq. cmp a c = ?
              rcases cmpInner_trichotomy xR zR xe ze with h_xz | ⟨h_xz_R, h_xz_e⟩ | h_xz
              · -- xR < zR ∨ ... : with yR = zR and h_xy: yR < xR or (xR = yR ∧ ye < xe).
                rcases h_xy with h | ⟨h1, h2⟩
                · rcases h_xz with h_xz_lt | ⟨h_xz_eq, h_xz_lt⟩ <;> omega
                · rcases h_xz with h_xz_lt | ⟨h_xz_eq, h_xz_lt⟩
                  · omega
                  · -- h_yz_e : ye = ze, h2 : ye < xe, h_xz_lt : xe < ze. Contradiction.
                    omega
              · rw [cmpInner_eq_eq _ _ _ _ h_xz_R h_xz_e] at h_gt
                exact Ordering.noConfusion h_gt
              · rw [cmpInner_eq_lt _ _ _ _ h_xz] at h_gt
                exact Ordering.noConfusion h_gt
            · -- yR < zR ∨ (yR = zR ∧ ze < ye): cmp b c = .lt.
              -- Combine h_xy (yR < xR ∨ (xR = yR ∧ ye < xe)) and h_yz: derive cmp a c = .lt.
              rcases cmpInner_trichotomy xR zR xe ze with h_xz | ⟨h_xz_R, h_xz_e⟩ | h_xz
              · -- xR < zR ∨ (xR = zR ∧ xe < ze): wants cmp a c = .gt. Combined with h_xy + h_yz, contradiction.
                rcases h_xy with hh1 | ⟨hh1, hh2⟩
                · rcases h_yz with hh3 | ⟨hh3, hh4⟩
                  · rcases h_xz with h_xz_lt | ⟨h_xz_eq, h_xz_lt⟩ <;> omega
                  · rcases h_xz with h_xz_lt | ⟨h_xz_eq, h_xz_lt⟩ <;> omega
                · rcases h_yz with hh3 | ⟨hh3, hh4⟩
                  · rcases h_xz with h_xz_lt | ⟨h_xz_eq, h_xz_lt⟩ <;> omega
                  · rcases h_xz with h_xz_lt | ⟨h_xz_eq, h_xz_lt⟩ <;> omega
              · rw [cmpInner_eq_eq _ _ _ _ h_xz_R h_xz_e] at h_gt
                exact Ordering.noConfusion h_gt
              · rw [cmpInner_eq_lt _ _ _ _ h_xz] at h_gt
                exact Ordering.noConfusion h_gt

/-! #### `orderInsensitiveListCmp` total-preorder lifting helpers (partial)

These helpers lift total-preorder properties from the inner `cmp` to
`orderInsensitiveListCmp`. Currently `_refl` is closed; `_swap` and `_trans` are sorry'd
pending careful foldl-reduction handling. -/

/-- `orderInsensitiveListCmp cmp L L = .eq` when `cmp` is reflexive on (the elements of) `L`. -/
private theorem orderInsensitiveListCmp_refl {α : Type} (cmp : α → α → Ordering)
    (L : List α) (h_refl : ∀ a ∈ L, cmp a a = Ordering.eq) :
    orderInsensitiveListCmp cmp L L = Ordering.eq := by
  unfold orderInsensitiveListCmp
  rw [if_neg (by simp)]
  -- sortBy preserves elements (Perm), so reflexivity carries.
  have h_sort_refl : ∀ a ∈ sortBy cmp L, cmp a a = Ordering.eq := fun a ha =>
    h_refl a ((sortBy_perm cmp L).mem_iff.mp ha)
  -- Inner induction over (sortBy cmp L).
  suffices h_aux : ∀ (M : List α), (∀ a ∈ M, cmp a a = Ordering.eq) →
      (M.zip M).foldl
        (fun (currentOrder : Ordering) (x : α × α) =>
          if (currentOrder != Ordering.eq) = true then currentOrder
          else cmp x.1 x.2) Ordering.eq = Ordering.eq from
    h_aux _ h_sort_refl
  intro M
  induction M with
  | nil => intros; rfl
  | cons a M' ih =>
    intros h
    have h_a : cmp a a = Ordering.eq := h a List.mem_cons_self
    -- Compute the foldl one step: new init = cmp a a = .eq. Then recurse via ih.
    show ((a, a) :: M'.zip M').foldl
          (fun (currentOrder : Ordering) (x : α × α) =>
            if (currentOrder != Ordering.eq) = true then currentOrder
            else cmp x.1 x.2) Ordering.eq = Ordering.eq
    rw [List.foldl_cons]
    show (M'.zip M').foldl
          (fun (currentOrder : Ordering) (x : α × α) =>
            if (currentOrder != Ordering.eq) = true then currentOrder
            else cmp x.1 x.2) (cmp a a) = Ordering.eq
    rw [h_a]
    exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- `comparePathsBetween` is a total preorder on `PathsBetween`. The four conjuncts
match `orderInsensitiveListCmp_perm`'s requirements via `sortedPerm_class_eq`.

Closing this requires lifting the four total-preorder properties from
`comparePathSegments` (closed via `comparePathSegments_total_preorder`) through
`orderInsensitiveListCmp` (a foldl-based comparator). `_refl` lifts cleanly via
`orderInsensitiveListCmp_refl` above; `_swap` (for antisym) and `_trans` are tractable
by induction on the zipped `sortBy` outputs but require careful handling of the foldl
reduction. Left as future work. -/
theorem comparePathsBetween_total_preorder {vc : Nat}
    (vts : Array VertexType) (br : Nat → Nat → Nat → Nat) :
    (∀ a : PathsBetween vc, comparePathsBetween vts br a a = Ordering.eq) ∧
    (∀ a b : PathsBetween vc, comparePathsBetween vts br a b = Ordering.lt →
                               comparePathsBetween vts br b a = Ordering.gt) ∧
    (∀ a b : PathsBetween vc, comparePathsBetween vts br a b = Ordering.gt →
                               comparePathsBetween vts br b a = Ordering.lt) ∧
    (∀ a b c : PathsBetween vc, comparePathsBetween vts br a b ≠ Ordering.gt →
                                 comparePathsBetween vts br b c ≠ Ordering.gt →
                                 comparePathsBetween vts br a c ≠ Ordering.gt) := by
  sorry


end Graph
