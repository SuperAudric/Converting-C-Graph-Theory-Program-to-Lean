import FullCorrectness.Equivariance.ComparisonSort
import Mathlib.Data.List.Zip

/-!
# `comparePathSegments` total preorder and `comparePathsBetween` lifting
(`FullCorrectness.Equivariance.ComparePathSegments`)

Proves that `comparePathSegments` is a total preorder (reflexive, both antisymmetries,
`≤`-transitive) after the algorithm refactor that replaced the `panic!` bottom/inner
mixed case with a fixed `bottom < inner` ordering.

Provides the four `orderInsensitiveListCmp` lifting helpers (`_refl`, `_swap_lt`,
`_swap_gt`, `_trans`) and assembles `comparePathsBetween_total_preorder` on top of
them + `comparePathSegments_total_preorder` + `comparePathSegments_equivCompat`.

## Sorry status
- None — all four total-preorder lifters and `comparePathsBetween_total_preorder` are closed.
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

/-! #### `orderInsensitiveListCmp` total-preorder lifting helpers

These helpers lift the four total-preorder properties from the inner `cmp` to
`orderInsensitiveListCmp`: `_refl`, `_swap_lt` (antisym₁), `_swap_gt` (antisym₂), and
`_trans` (≤-trans). All closed. The `_trans` proof factors through `foldl_zip_trans` for
the equal-length case. -/

/-- `orderInsensitiveListCmp cmp L L = .eq` when `cmp` is reflexive on (the elements of) `L`. -/
theorem orderInsensitiveListCmp_refl {α : Type} (cmp : α → α → Ordering)
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

/-- `comparePathSegments` respects equivalence bilaterally: equivalent (`= .eq`) segments
compare the same way to every third segment, in either argument position. This is the
`h_compat` hypothesis required by the `_trans` lifter (and by `_perm`). -/
theorem comparePathSegments_equivCompat
    {vc : Nat} (vts : Array VertexType) (br : Nat → Nat → Nat → Nat)
    (p q : PathSegment vc) (h : comparePathSegments vts br p q = Ordering.eq) (r : PathSegment vc) :
    comparePathSegments vts br p r = comparePathSegments vts br q r ∧
    comparePathSegments vts br r p = comparePathSegments vts br r q := by
  cases p with
  | bottom xVI =>
    cases q with
    | bottom yVI =>
      have hvts_eq : vts.getD xVI.val 0 = vts.getD yVI.val 0 :=
        compare_eq_iff_eq.mp h
      cases r with
      | bottom zVI =>
        refine ⟨?_, ?_⟩
        · show compare (vts.getD xVI.val 0) (vts.getD zVI.val 0)
             = compare (vts.getD yVI.val 0) (vts.getD zVI.val 0)
          rw [hvts_eq]
        · show compare (vts.getD zVI.val 0) (vts.getD xVI.val 0)
             = compare (vts.getD zVI.val 0) (vts.getD yVI.val 0)
          rw [hvts_eq]
      | inner _ _ _ _ => exact ⟨rfl, rfl⟩
    | inner _ _ _ _ =>
      -- comparePathSegments .bottom .inner = .lt (by the new definition); contradicts h.
      exact Ordering.noConfusion h
  | inner xe xd xs xend =>
    cases q with
    | bottom _ =>
      -- comparePathSegments .inner .bottom = .gt; contradicts h.
      exact Ordering.noConfusion h
    | inner ye yd ys yend =>
      have hRank : br xd xs.val xend.val = br yd ys.val yend.val := by
        by_cases hxy : br xd xs.val xend.val = br yd ys.val yend.val
        · exact hxy
        · exfalso
          simp only [comparePathSegments, hxy, bne_iff_ne, ne_eq, not_false_eq_true,
            ↓reduceIte] at h
          exact hxy (compare_eq_iff_eq.mp h).symm
      have hEdge : xe = ye := by
        by_cases hxy : xe = ye
        · exact hxy
        · exfalso
          simp only [comparePathSegments, hRank, bne_self_eq_false, ↓reduceIte,
            hxy, bne_iff_ne, ne_eq, not_false_eq_true] at h
          exact hxy (compare_eq_iff_eq.mp h).symm
      cases r with
      | bottom _ => exact ⟨rfl, rfl⟩
      | inner ze zd zs zend =>
        refine ⟨?_, ?_⟩
        · show (let xR := br xd xs.val xend.val
                let zR := br zd zs.val zend.val
                if xR != zR then compare zR xR
                else if xe != ze then compare ze xe else .eq)
             = (let yR := br yd ys.val yend.val
                let zR := br zd zs.val zend.val
                if yR != zR then compare zR yR
                else if ye != ze then compare ze ye else .eq)
          rw [hRank, hEdge]
        · show (let zR := br zd zs.val zend.val
                let xR := br xd xs.val xend.val
                if zR != xR then compare xR zR
                else if ze != xe then compare xe ze else .eq)
             = (let zR := br zd zs.val zend.val
                let yR := br yd ys.val yend.val
                if zR != yR then compare yR zR
                else if ze != ye then compare ye ze else .eq)
          rw [hRank, hEdge]

/-! #### Foldl init preservation and antisymmetry-`.lt → .gt` lifter -/

/-- Once the accumulator of the `orderInsensitiveListCmp` foldl is non-`.eq` the foldl
preserves it: every subsequent step short-circuits via `if currentOrder != .eq then ...`.
Used by the `_swap_lt`/`_swap_gt` lifters to discharge the "first non-`.eq`" case. -/
private theorem orderInsensitiveListCmp_foldl_init_preserved {α : Type} (cmp : α → α → Ordering)
    (init : Ordering) (h : init ≠ Ordering.eq) (L : List (α × α)) :
    L.foldl (fun (currentOrder : Ordering) (x : α × α) =>
        if (currentOrder != Ordering.eq) = true then currentOrder
        else cmp x.1 x.2) init = init := by
  cases init with
  | eq => exact (h rfl).elim
  | lt =>
    induction L with
    | nil => rfl
    | cons x L ih =>
      show ((x :: L).foldl _ Ordering.lt) = Ordering.lt
      rw [List.foldl_cons]; exact ih
  | gt =>
    induction L with
    | nil => rfl
    | cons x L ih =>
      show ((x :: L).foldl _ Ordering.gt) = Ordering.gt
      rw [List.foldl_cons]; exact ih

/-- Antisymmetry-`.lt → .gt` lift for `orderInsensitiveListCmp`. In the lengths-equal case,
locate the first position whose cmp is `.lt`; antisym₁ swaps it to `.gt` for the swapped
zip; preceding `.eq` positions stay `.eq` under symmetry of `.eq`. The length-mismatch
branch flips by direct case analysis. -/
theorem orderInsensitiveListCmp_swap_lt {α : Type} (cmp : α → α → Ordering)
    (h_antisym₁ : ∀ a b, cmp a b = Ordering.lt → cmp b a = Ordering.gt)
    (h_antisym₂ : ∀ a b, cmp a b = Ordering.gt → cmp b a = Ordering.lt)
    (L₁ L₂ : List α) :
    orderInsensitiveListCmp cmp L₁ L₂ = Ordering.lt →
    orderInsensitiveListCmp cmp L₂ L₁ = Ordering.gt := by
  have h_eq_symm : ∀ a b, cmp a b = Ordering.eq → cmp b a = Ordering.eq := by
    intros a b hab
    match h_ba : cmp b a with
    | .eq => rfl
    | .lt =>
      have := h_antisym₁ b a h_ba; rw [hab] at this; exact Ordering.noConfusion this
    | .gt =>
      have := h_antisym₂ b a h_ba; rw [hab] at this; exact Ordering.noConfusion this
  unfold orderInsensitiveListCmp
  by_cases hLen : L₁.length = L₂.length
  · -- Equal lengths.
    have hLenSwap : L₂.length = L₁.length := hLen.symm
    have h_bne₁ : (L₁.length != L₂.length) = false := by
      rw [hLen]; exact bne_self_eq_false (a := L₂.length)
    have h_bne₂ : (L₂.length != L₁.length) = false := by
      rw [hLenSwap]; exact bne_self_eq_false (a := L₁.length)
    simp only [h_bne₁, h_bne₂, Bool.false_eq_true, ↓reduceIte]
    rw [show (sortBy cmp L₂).zip (sortBy cmp L₁)
          = ((sortBy cmp L₁).zip (sortBy cmp L₂)).map Prod.swap from
        (List.zip_swap (sortBy cmp L₁) (sortBy cmp L₂)).symm]
    intro h_lt
    suffices h_aux : ∀ (L : List (α × α)),
        L.foldl (fun (currentOrder : Ordering) (x : α × α) =>
            if (currentOrder != Ordering.eq) = true then currentOrder
            else cmp x.1 x.2) Ordering.eq = Ordering.lt →
        (L.map Prod.swap).foldl (fun (currentOrder : Ordering) (x : α × α) =>
            if (currentOrder != Ordering.eq) = true then currentOrder
            else cmp x.1 x.2) Ordering.eq = Ordering.gt from
      h_aux _ h_lt
    intro L
    induction L with
    | nil => intro h; exact Ordering.noConfusion h
    | cons x L ih =>
      intro h
      -- Reduce the head step on both sides: LHS init becomes `cmp x.1 x.2`,
      -- RHS init becomes `cmp x.2 x.1` (via Prod.swap).
      rw [List.foldl_cons] at h
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      show ((Prod.swap x) :: L.map Prod.swap).foldl _ Ordering.eq = Ordering.gt
      rw [List.foldl_cons]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                 Prod.fst_swap, Prod.snd_swap]
      match h_xy : cmp x.1 x.2 with
      | .eq =>
        rw [h_xy] at h
        rw [h_eq_symm _ _ h_xy]
        exact ih h
      | .lt =>
        rw [h_antisym₁ _ _ h_xy]
        exact orderInsensitiveListCmp_foldl_init_preserved cmp Ordering.gt
                (by intro hh; cases hh) (L.map Prod.swap)
      | .gt =>
        rw [h_xy] at h
        have h_pres := orderInsensitiveListCmp_foldl_init_preserved cmp Ordering.gt
                          (by intro hh; cases hh) L
        rw [h_pres] at h
        exact Ordering.noConfusion h
  · -- Unequal lengths: outer if takes the inner branch on both sides.
    have hLenSwap : ¬ L₂.length = L₁.length := fun h => hLen h.symm
    have h_bne₁ : (L₁.length != L₂.length) = true := bne_iff_ne.mpr hLen
    have h_bne₂ : (L₂.length != L₁.length) = true := bne_iff_ne.mpr hLenSwap
    rw [if_pos h_bne₁, if_pos h_bne₂]
    intro h
    by_cases h₁₂ : L₁.length < L₂.length
    · rw [if_pos h₁₂] at h; exact Ordering.noConfusion h
    · rw [if_pos (show L₂.length < L₁.length by omega)]

/-- Antisymmetry-`.gt → .lt` lift for `orderInsensitiveListCmp`. Mirror of `_swap_lt`:
the first non-`.eq` cmp becomes `.gt` (from antisym₂), preceding `.eq`s stay `.eq`. -/
theorem orderInsensitiveListCmp_swap_gt {α : Type} (cmp : α → α → Ordering)
    (h_antisym₁ : ∀ a b, cmp a b = Ordering.lt → cmp b a = Ordering.gt)
    (h_antisym₂ : ∀ a b, cmp a b = Ordering.gt → cmp b a = Ordering.lt)
    (L₁ L₂ : List α) :
    orderInsensitiveListCmp cmp L₁ L₂ = Ordering.gt →
    orderInsensitiveListCmp cmp L₂ L₁ = Ordering.lt := by
  have h_eq_symm : ∀ a b, cmp a b = Ordering.eq → cmp b a = Ordering.eq := by
    intros a b hab
    match h_ba : cmp b a with
    | .eq => rfl
    | .lt =>
      have := h_antisym₁ b a h_ba; rw [hab] at this; exact Ordering.noConfusion this
    | .gt =>
      have := h_antisym₂ b a h_ba; rw [hab] at this; exact Ordering.noConfusion this
  unfold orderInsensitiveListCmp
  by_cases hLen : L₁.length = L₂.length
  · have hLenSwap : L₂.length = L₁.length := hLen.symm
    have h_bne₁ : (L₁.length != L₂.length) = false := by
      rw [hLen]; exact bne_self_eq_false (a := L₂.length)
    have h_bne₂ : (L₂.length != L₁.length) = false := by
      rw [hLenSwap]; exact bne_self_eq_false (a := L₁.length)
    simp only [h_bne₁, h_bne₂, Bool.false_eq_true, ↓reduceIte]
    rw [show (sortBy cmp L₂).zip (sortBy cmp L₁)
          = ((sortBy cmp L₁).zip (sortBy cmp L₂)).map Prod.swap from
        (List.zip_swap (sortBy cmp L₁) (sortBy cmp L₂)).symm]
    intro h_gt
    suffices h_aux : ∀ (L : List (α × α)),
        L.foldl (fun (currentOrder : Ordering) (x : α × α) =>
            if (currentOrder != Ordering.eq) = true then currentOrder
            else cmp x.1 x.2) Ordering.eq = Ordering.gt →
        (L.map Prod.swap).foldl (fun (currentOrder : Ordering) (x : α × α) =>
            if (currentOrder != Ordering.eq) = true then currentOrder
            else cmp x.1 x.2) Ordering.eq = Ordering.lt from
      h_aux _ h_gt
    intro L
    induction L with
    | nil => intro h; exact Ordering.noConfusion h
    | cons x L ih =>
      intro h
      rw [List.foldl_cons] at h
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      show ((Prod.swap x) :: L.map Prod.swap).foldl _ Ordering.eq = Ordering.lt
      rw [List.foldl_cons]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                 Prod.fst_swap, Prod.snd_swap]
      match h_xy : cmp x.1 x.2 with
      | .eq =>
        rw [h_xy] at h
        rw [h_eq_symm _ _ h_xy]
        exact ih h
      | .gt =>
        rw [h_antisym₂ _ _ h_xy]
        exact orderInsensitiveListCmp_foldl_init_preserved cmp Ordering.lt
                (by intro hh; cases hh) (L.map Prod.swap)
      | .lt =>
        rw [h_xy] at h
        have h_pres := orderInsensitiveListCmp_foldl_init_preserved cmp Ordering.lt
                          (by intro hh; cases hh) L
        rw [h_pres] at h
        exact Ordering.noConfusion h
  · have hLenSwap : ¬ L₂.length = L₁.length := fun h => hLen h.symm
    have h_bne₁ : (L₁.length != L₂.length) = true := bne_iff_ne.mpr hLen
    have h_bne₂ : (L₂.length != L₁.length) = true := bne_iff_ne.mpr hLenSwap
    rw [if_pos h_bne₁, if_pos h_bne₂]
    intro h
    by_cases h₁₂ : L₁.length < L₂.length
    · -- result .gt holds for hyp; for swap, ¬ L₂.length < L₁.length, so result is .lt.
      rw [if_neg (by omega : ¬ L₂.length < L₁.length)]
    · rw [if_neg h₁₂] at h; exact Ordering.noConfusion h

/-- Three-list foldl-trans helper: for sorted lists `A`, `B`, `C` of equal length, if both
`(zip A B).foldl ≠ .gt` and `(zip B C).foldl ≠ .gt`, then `(zip A C).foldl ≠ .gt`. The
case analysis is on the head pair `(cmp a b, cmp b c)`; bilateral compatibility on `.eq`
collapses the `.eq` cases, antisym₁ collapses `(.lt, .lt)` to `cmp a c = .lt`, and the
`.gt` cases discharge the relevant hypothesis via init preservation. -/
private theorem foldl_zip_trans {α : Type} (cmp : α → α → Ordering)
    (h_antisym₁ : ∀ a b, cmp a b = Ordering.lt → cmp b a = Ordering.gt)
    (h_trans : ∀ a b c, cmp a b ≠ Ordering.gt → cmp b c ≠ Ordering.gt → cmp a c ≠ Ordering.gt)
    (h_compat : ∀ a b, cmp a b = Ordering.eq → ∀ c, cmp a c = cmp b c ∧ cmp c a = cmp c b) :
    ∀ (A B C : List α),
      A.length = B.length → B.length = C.length →
      (A.zip B).foldl (fun (currentOrder : Ordering) (x : α × α) =>
          if (currentOrder != Ordering.eq) = true then currentOrder
          else cmp x.1 x.2) Ordering.eq ≠ Ordering.gt →
      (B.zip C).foldl (fun (currentOrder : Ordering) (x : α × α) =>
          if (currentOrder != Ordering.eq) = true then currentOrder
          else cmp x.1 x.2) Ordering.eq ≠ Ordering.gt →
      (A.zip C).foldl (fun (currentOrder : Ordering) (x : α × α) =>
          if (currentOrder != Ordering.eq) = true then currentOrder
          else cmp x.1 x.2) Ordering.eq ≠ Ordering.gt := by
  intro A
  induction A with
  | nil =>
    intros B C _ _ _ _ h
    exact Ordering.noConfusion h
  | cons a A' ih =>
    intros B C h_AB h_BC h₁ h₂
    cases B with
    | nil => simp at h_AB
    | cons b B' =>
      cases C with
      | nil => simp at h_BC
      | cons c C' =>
        have h_AB' : A'.length = B'.length := by
          have : A'.length + 1 = B'.length + 1 := by simpa using h_AB
          omega
        have h_BC' : B'.length = C'.length := by
          have : B'.length + 1 = C'.length + 1 := by simpa using h_BC
          omega
        -- Step the head off all three foldls. The new init becomes the head cmp.
        rw [show ((a :: A').zip (b :: B')) = (a, b) :: (A'.zip B') from rfl] at h₁
        rw [List.foldl_cons] at h₁
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h₁
        rw [show ((b :: B').zip (c :: C')) = (b, c) :: (B'.zip C') from rfl] at h₂
        rw [List.foldl_cons] at h₂
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h₂
        show ((a :: A').zip (c :: C')).foldl _ Ordering.eq ≠ Ordering.gt
        rw [show ((a :: A').zip (c :: C')) = (a, c) :: (A'.zip C') from rfl]
        rw [List.foldl_cons]
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        match h_ab : cmp a b, h_bc : cmp b c with
        | .eq, .eq =>
          rw [h_ab] at h₁; rw [h_bc] at h₂
          have h_ac : cmp a c = Ordering.eq := by
            rw [(h_compat a b h_ab c).1, h_bc]
          rw [h_ac]
          exact ih B' C' h_AB' h_BC' h₁ h₂
        | .eq, .lt =>
          have h_ac : cmp a c = Ordering.lt := by
            rw [(h_compat a b h_ab c).1, h_bc]
          rw [h_ac]
          intro h_gt
          rw [orderInsensitiveListCmp_foldl_init_preserved cmp Ordering.lt
                (by intro hh; cases hh) (A'.zip C')] at h_gt
          exact Ordering.noConfusion h_gt
        | .eq, .gt =>
          rw [h_bc] at h₂
          have h_pres := orderInsensitiveListCmp_foldl_init_preserved cmp Ordering.gt
                            (by intro hh; cases hh) (B'.zip C')
          rw [h_pres] at h₂
          exact (h₂ rfl).elim
        | .lt, .eq =>
          have h_ac : cmp a c = Ordering.lt := by
            -- h_compat (b, c, .eq, a).2 : cmp a b = cmp a c
            rw [← (h_compat b c h_bc a).2]; exact h_ab
          rw [h_ac]
          intro h_gt
          rw [orderInsensitiveListCmp_foldl_init_preserved cmp Ordering.lt
                (by intro hh; cases hh) (A'.zip C')] at h_gt
          exact Ordering.noConfusion h_gt
        | .lt, .lt =>
          have h_ac_le : cmp a c ≠ Ordering.gt :=
            h_trans a b c (by rw [h_ab]; intro h; cases h)
                          (by rw [h_bc]; intro h; cases h)
          have h_ac_ne_eq : cmp a c ≠ Ordering.eq := by
            intro h_eq
            -- cmp a c = .eq → (h_compat a c .eq b).1: cmp a b = cmp c b → cmp c b = .lt
            -- → cmp b c = .gt (antisym₁) → contradicts h_bc = .lt.
            have h := (h_compat a c h_eq b).1
            rw [h_ab] at h
            have h_bc_gt : cmp b c = Ordering.gt := h_antisym₁ c b h.symm
            rw [h_bc] at h_bc_gt
            exact Ordering.noConfusion h_bc_gt
          have h_ac : cmp a c = Ordering.lt := by
            match h_ac_val : cmp a c with
            | .lt => rfl
            | .eq => exact (h_ac_ne_eq h_ac_val).elim
            | .gt => exact (h_ac_le h_ac_val).elim
          rw [h_ac]
          intro h_gt
          rw [orderInsensitiveListCmp_foldl_init_preserved cmp Ordering.lt
                (by intro hh; cases hh) (A'.zip C')] at h_gt
          exact Ordering.noConfusion h_gt
        | .lt, .gt =>
          rw [h_bc] at h₂
          have h_pres := orderInsensitiveListCmp_foldl_init_preserved cmp Ordering.gt
                            (by intro hh; cases hh) (B'.zip C')
          rw [h_pres] at h₂
          exact (h₂ rfl).elim
        | .gt, _ =>
          rw [h_ab] at h₁
          have h_pres := orderInsensitiveListCmp_foldl_init_preserved cmp Ordering.gt
                            (by intro hh; cases hh) (A'.zip B')
          rw [h_pres] at h₁
          exact (h₁ rfl).elim

/-- Transitivity lift for `orderInsensitiveListCmp`. Length-mismatch cases reduce to
length comparisons; the fully-equal-length case delegates to `foldl_zip_trans` after
sorting all three lists. -/
theorem orderInsensitiveListCmp_trans {α : Type} (cmp : α → α → Ordering)
    (h_antisym₁ : ∀ a b, cmp a b = Ordering.lt → cmp b a = Ordering.gt)
    (h_trans : ∀ a b c, cmp a b ≠ Ordering.gt → cmp b c ≠ Ordering.gt → cmp a c ≠ Ordering.gt)
    (h_compat : ∀ a b, cmp a b = Ordering.eq → ∀ c, cmp a c = cmp b c ∧ cmp c a = cmp c b)
    (L₁ L₂ L₃ : List α) :
    orderInsensitiveListCmp cmp L₁ L₂ ≠ Ordering.gt →
    orderInsensitiveListCmp cmp L₂ L₃ ≠ Ordering.gt →
    orderInsensitiveListCmp cmp L₁ L₃ ≠ Ordering.gt := by
  unfold orderInsensitiveListCmp
  -- Helper: `(L_a.length != L_b.length) = false ↔ L_a.length = L_b.length`,
  -- and `... = true ↔ L_a.length ≠ L_b.length`. We thread the bne form through.
  intros h₁ h₂
  -- We need to case-analyze the lengths of L₁, L₂, L₃ and the foldls' results.
  by_cases hL₁₂ : L₁.length = L₂.length
  · by_cases hL₂₃ : L₂.length = L₃.length
    · -- All equal lengths: reduce to foldl_zip_trans.
      have hL₁₃ : L₁.length = L₃.length := hL₁₂.trans hL₂₃
      have h_bne₁₂ : (L₁.length != L₂.length) = false := by
        rw [hL₁₂]; exact bne_self_eq_false (a := L₂.length)
      have h_bne₂₃ : (L₂.length != L₃.length) = false := by
        rw [hL₂₃]; exact bne_self_eq_false (a := L₃.length)
      have h_bne₁₃ : (L₁.length != L₃.length) = false := by
        rw [hL₁₃]; exact bne_self_eq_false (a := L₃.length)
      simp only [h_bne₁₂, Bool.false_eq_true, ↓reduceIte] at h₁
      simp only [h_bne₂₃, Bool.false_eq_true, ↓reduceIte] at h₂
      simp only [h_bne₁₃, Bool.false_eq_true, ↓reduceIte]
      have hSort₁₂ : (sortBy cmp L₁).length = (sortBy cmp L₂).length := by
        rw [(sortBy_perm cmp L₁).length_eq, (sortBy_perm cmp L₂).length_eq, hL₁₂]
      have hSort₂₃ : (sortBy cmp L₂).length = (sortBy cmp L₃).length := by
        rw [(sortBy_perm cmp L₂).length_eq, (sortBy_perm cmp L₃).length_eq, hL₂₃]
      exact foldl_zip_trans cmp h_antisym₁ h_trans h_compat
        (sortBy cmp L₁) (sortBy cmp L₂) (sortBy cmp L₃) hSort₁₂ hSort₂₃ h₁ h₂
    · -- L₁.length = L₂.length but L₂.length ≠ L₃.length.
      -- Either L₂ < L₃ (Hyp2 false) or L₂ > L₃ (conclusion length-based .lt).
      have h_bne₂₃ : (L₂.length != L₃.length) = true := bne_iff_ne.mpr hL₂₃
      rw [if_pos h_bne₂₃] at h₂
      by_cases hLt₂₃ : L₂.length < L₃.length
      · rw [if_pos hLt₂₃] at h₂; exact (h₂ rfl).elim
      · -- L₂ > L₃. So L₁ = L₂ > L₃, hence L₁ ≠ L₃, L₁ > L₃.
        have hGt : L₂.length > L₃.length := by omega
        have hL₁₃_ne : L₁.length ≠ L₃.length := by omega
        have hLt₁₃ : ¬ L₁.length < L₃.length := by omega
        have h_bne₁₃ : (L₁.length != L₃.length) = true := bne_iff_ne.mpr hL₁₃_ne
        rw [if_pos h_bne₁₃, if_neg hLt₁₃]
        intro h; exact Ordering.noConfusion h
  · -- L₁.length ≠ L₂.length: similar.
    have h_bne₁₂ : (L₁.length != L₂.length) = true := bne_iff_ne.mpr hL₁₂
    rw [if_pos h_bne₁₂] at h₁
    by_cases hLt₁₂ : L₁.length < L₂.length
    · rw [if_pos hLt₁₂] at h₁; exact (h₁ rfl).elim
    · -- L₁ > L₂.
      have hGt : L₁.length > L₂.length := lt_of_le_of_ne (Nat.le_of_not_lt hLt₁₂) (Ne.symm hL₁₂)
      by_cases hL₂₃ : L₂.length = L₃.length
      · -- L₁ > L₂ = L₃, so L₁ > L₃.
        have hL₁₃_ne : L₁.length ≠ L₃.length := by omega
        have hLt₁₃ : ¬ L₁.length < L₃.length := by omega
        have h_bne₁₃ : (L₁.length != L₃.length) = true := bne_iff_ne.mpr hL₁₃_ne
        rw [if_pos h_bne₁₃, if_neg hLt₁₃]
        intro h; exact Ordering.noConfusion h
      · -- Both length-mismatches. L₂ vs L₃ trichotomy.
        have h_bne₂₃ : (L₂.length != L₃.length) = true := bne_iff_ne.mpr hL₂₃
        rw [if_pos h_bne₂₃] at h₂
        by_cases hLt₂₃ : L₂.length < L₃.length
        · rw [if_pos hLt₂₃] at h₂; exact (h₂ rfl).elim
        · -- L₁ > L₂ > L₃, so L₁ > L₃.
          have hGt' : L₂.length > L₃.length := by omega
          have hL₁₃_ne : L₁.length ≠ L₃.length := by omega
          have hLt₁₃ : ¬ L₁.length < L₃.length := by omega
          have h_bne₁₃ : (L₁.length != L₃.length) = true := bne_iff_ne.mpr hL₁₃_ne
          rw [if_pos h_bne₁₃, if_neg hLt₁₃]
          intro h; exact Ordering.noConfusion h

/-- Foldl-zip-`.eq` extracts pointwise `cmp = .eq` at every position. The reverse
direction is also true (and would follow by induction) but isn't needed here. -/
private theorem foldl_zip_eq_implies_pairwise_eq {α : Type} (cmp : α → α → Ordering) :
    ∀ (L : List (α × α)),
      L.foldl (fun (currentOrder : Ordering) (x : α × α) =>
          if (currentOrder != Ordering.eq) = true then currentOrder
          else cmp x.1 x.2) Ordering.eq = Ordering.eq →
      ∀ i (h : i < L.length), cmp ((L[i]'h).1) ((L[i]'h).2) = Ordering.eq := by
  intro L
  induction L with
  | nil => intros _ i h_lt; exact absurd h_lt (Nat.not_lt_zero _)
  | cons y L ih =>
    intro h i h_lt
    rw [List.foldl_cons] at h
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    match h_y : cmp y.1 y.2 with
    | .eq =>
      rw [h_y] at h
      cases i with
      | zero => exact h_y
      | succ i' =>
        have h_lt' : i' < L.length := Nat.lt_of_succ_lt_succ h_lt
        show cmp ((L[i']'h_lt').1) ((L[i']'h_lt').2) = Ordering.eq
        exact ih h i' h_lt'
    | .lt =>
      rw [h_y] at h
      have h_pres := orderInsensitiveListCmp_foldl_init_preserved cmp Ordering.lt
                        (by intro hh; cases hh) L
      rw [h_pres] at h; exact Ordering.noConfusion h
    | .gt =>
      rw [h_y] at h
      have h_pres := orderInsensitiveListCmp_foldl_init_preserved cmp Ordering.gt
                        (by intro hh; cases hh) L
      rw [h_pres] at h; exact Ordering.noConfusion h

/-- Bilateral compat lift for `orderInsensitiveListCmp`: if two lists are class-equal
under the order-insensitive cmp, they compare the same against any third list, in either
argument position. The proof extracts pointwise class equality from the foldl-`.eq`
hypothesis and pushes it through `foldl_pointwise_eq` via `h_compat`. -/
theorem orderInsensitiveListCmp_equivCompat {α : Type} (cmp : α → α → Ordering)
    (h_compat : ∀ a b, cmp a b = Ordering.eq → ∀ c, cmp a c = cmp b c ∧ cmp c a = cmp c b)
    (L₁ L₂ : List α) (h : orderInsensitiveListCmp cmp L₁ L₂ = Ordering.eq) (L₃ : List α) :
    orderInsensitiveListCmp cmp L₁ L₃ = orderInsensitiveListCmp cmp L₂ L₃ ∧
    orderInsensitiveListCmp cmp L₃ L₁ = orderInsensitiveListCmp cmp L₃ L₂ := by
  -- Extract length equality from h.
  have hLen : L₁.length = L₂.length := by
    unfold orderInsensitiveListCmp at h
    by_contra hne
    have h_bne : (L₁.length != L₂.length) = true := bne_iff_ne.mpr hne
    rw [if_pos h_bne] at h
    by_cases h_lt : L₁.length < L₂.length
    · rw [if_pos h_lt] at h; exact Ordering.noConfusion h
    · rw [if_neg h_lt] at h; exact Ordering.noConfusion h
  -- Extract foldl-`.eq` from h.
  have hFoldl : ((sortBy cmp L₁).zip (sortBy cmp L₂)).foldl
      (fun (currentOrder : Ordering) (x : α × α) =>
        if (currentOrder != Ordering.eq) = true then currentOrder
        else cmp x.1 x.2) Ordering.eq = Ordering.eq := by
    unfold orderInsensitiveListCmp at h
    have h_bne : (L₁.length != L₂.length) = false := by
      rw [hLen]; exact bne_self_eq_false (a := L₂.length)
    simp only [h_bne, Bool.false_eq_true, ↓reduceIte] at h
    exact h
  -- Pointwise class equality on sorted lists.
  have h_class : ∀ i (h₁ : i < (sortBy cmp L₁).length) (h₂ : i < (sortBy cmp L₂).length),
      cmp ((sortBy cmp L₁)[i]'h₁) ((sortBy cmp L₂)[i]'h₂) = Ordering.eq := by
    intros i h₁ h₂
    have h_zip_lt : i < ((sortBy cmp L₁).zip (sortBy cmp L₂)).length := by
      rw [List.length_zip]; omega
    have hp := foldl_zip_eq_implies_pairwise_eq cmp _ hFoldl i h_zip_lt
    rw [List.getElem_zip] at hp
    exact hp
  refine ⟨?_, ?_⟩
  · -- orderInsensitiveListCmp L₁ L₃ = orderInsensitiveListCmp L₂ L₃
    unfold orderInsensitiveListCmp
    by_cases hLen₁₃ : L₁.length = L₃.length
    · have hLen₂₃ : L₂.length = L₃.length := hLen.symm.trans hLen₁₃
      have h_bne₁₃ : (L₁.length != L₃.length) = false := by
        rw [hLen₁₃]; exact bne_self_eq_false (a := L₃.length)
      have h_bne₂₃ : (L₂.length != L₃.length) = false := by
        rw [hLen₂₃]; exact bne_self_eq_false (a := L₃.length)
      simp only [h_bne₁₃, h_bne₂₃, Bool.false_eq_true, ↓reduceIte]
      have h_zip_lengths : ((sortBy cmp L₁).zip (sortBy cmp L₃)).length
                         = ((sortBy cmp L₂).zip (sortBy cmp L₃)).length := by
        rw [List.length_zip, List.length_zip,
            (sortBy_perm cmp L₁).length_eq, (sortBy_perm cmp L₂).length_eq, hLen]
      apply foldl_pointwise_eq _ _ _ _ h_zip_lengths
      intros acc i h_i₁ h_i₂
      have h_sort₁_lt : i < (sortBy cmp L₁).length := by
        rw [List.length_zip] at h_i₁; omega
      have h_sort₂_lt : i < (sortBy cmp L₂).length := by
        rw [List.length_zip] at h_i₂; omega
      have h_sort₃_lt : i < (sortBy cmp L₃).length := by
        rw [List.length_zip] at h_i₁; omega
      have h_class_at_i := h_class i h_sort₁_lt h_sort₂_lt
      have h_eq_cmp := (h_compat _ _ h_class_at_i ((sortBy cmp L₃)[i]'h_sort₃_lt)).1
      show (fun (currentOrder : Ordering) (x : α × α) =>
              if (currentOrder != Ordering.eq) = true then currentOrder
              else cmp x.1 x.2) acc
            ((sortBy cmp L₁).zip (sortBy cmp L₃))[i]
         = (fun (currentOrder : Ordering) (x : α × α) =>
              if (currentOrder != Ordering.eq) = true then currentOrder
              else cmp x.1 x.2) acc
            ((sortBy cmp L₂).zip (sortBy cmp L₃))[i]
      rw [List.getElem_zip, List.getElem_zip]
      simp [h_eq_cmp]
    · have hLen₂₃ : L₂.length ≠ L₃.length := fun h => hLen₁₃ (hLen.trans h)
      have h_bne₁₃ : (L₁.length != L₃.length) = true := bne_iff_ne.mpr hLen₁₃
      have h_bne₂₃ : (L₂.length != L₃.length) = true := bne_iff_ne.mpr hLen₂₃
      simp only [h_bne₁₃, h_bne₂₃, ↓reduceIte]
      rw [hLen]
  · -- orderInsensitiveListCmp L₃ L₁ = orderInsensitiveListCmp L₃ L₂
    unfold orderInsensitiveListCmp
    by_cases hLen₃₁ : L₃.length = L₁.length
    · have hLen₃₂ : L₃.length = L₂.length := hLen₃₁.trans hLen
      have h_bne₃₁ : (L₃.length != L₁.length) = false := by
        rw [hLen₃₁]; exact bne_self_eq_false (a := L₁.length)
      have h_bne₃₂ : (L₃.length != L₂.length) = false := by
        rw [hLen₃₂]; exact bne_self_eq_false (a := L₂.length)
      simp only [h_bne₃₁, h_bne₃₂, Bool.false_eq_true, ↓reduceIte]
      have h_zip_lengths : ((sortBy cmp L₃).zip (sortBy cmp L₁)).length
                         = ((sortBy cmp L₃).zip (sortBy cmp L₂)).length := by
        rw [List.length_zip, List.length_zip,
            (sortBy_perm cmp L₁).length_eq, (sortBy_perm cmp L₂).length_eq, hLen]
      apply foldl_pointwise_eq _ _ _ _ h_zip_lengths
      intros acc i h_i₁ h_i₂
      have h_sort₁_lt : i < (sortBy cmp L₁).length := by
        rw [List.length_zip] at h_i₁; omega
      have h_sort₂_lt : i < (sortBy cmp L₂).length := by
        rw [List.length_zip] at h_i₂; omega
      have h_sort₃_lt : i < (sortBy cmp L₃).length := by
        rw [List.length_zip] at h_i₁; omega
      have h_class_at_i := h_class i h_sort₁_lt h_sort₂_lt
      have h_eq_cmp := (h_compat _ _ h_class_at_i ((sortBy cmp L₃)[i]'h_sort₃_lt)).2
      show (fun (currentOrder : Ordering) (x : α × α) =>
              if (currentOrder != Ordering.eq) = true then currentOrder
              else cmp x.1 x.2) acc
            ((sortBy cmp L₃).zip (sortBy cmp L₁))[i]
         = (fun (currentOrder : Ordering) (x : α × α) =>
              if (currentOrder != Ordering.eq) = true then currentOrder
              else cmp x.1 x.2) acc
            ((sortBy cmp L₃).zip (sortBy cmp L₂))[i]
      rw [List.getElem_zip, List.getElem_zip]
      simp [h_eq_cmp]
    · have hLen₃₂ : L₃.length ≠ L₂.length := fun h => hLen₃₁ (h.trans hLen.symm)
      have h_bne₃₁ : (L₃.length != L₁.length) = true := bne_iff_ne.mpr hLen₃₁
      have h_bne₃₂ : (L₃.length != L₂.length) = true := bne_iff_ne.mpr hLen₃₂
      simp only [h_bne₃₁, h_bne₃₂, ↓reduceIte]
      rw [hLen]

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
  -- Pull out the four properties of the inner cmp = comparePathSegments.
  obtain ⟨h_seg_refl, h_seg_anti₁, h_seg_anti₂, h_seg_trans⟩ :=
    comparePathSegments_total_preorder (vc := vc) vts br
  -- And the bilateral compat lemma.
  have h_seg_compat := comparePathSegments_equivCompat (vc := vc) vts br
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Refl: comparePathsBetween a a = .eq.
    intro a
    show (let xEndType := vts.getD a.endVertexIndex.val 0
          let yEndType := vts.getD a.endVertexIndex.val 0
          if xEndType != yEndType then compare xEndType yEndType
          else orderInsensitiveListCmp (comparePathSegments vts br)
                 a.connectedSubPaths a.connectedSubPaths) = Ordering.eq
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact orderInsensitiveListCmp_refl _ _ (fun s _ => h_seg_refl s)
  · -- Antisym₁: .lt → .gt.
    intros a b h_lt
    -- Unfold both sides.
    show (let yEndType := vts.getD b.endVertexIndex.val 0
          let xEndType := vts.getD a.endVertexIndex.val 0
          if yEndType != xEndType then compare yEndType xEndType
          else orderInsensitiveListCmp (comparePathSegments vts br)
                 b.connectedSubPaths a.connectedSubPaths) = Ordering.gt
    have h_lt' : (let xEndType := vts.getD a.endVertexIndex.val 0
                  let yEndType := vts.getD b.endVertexIndex.val 0
                  if xEndType != yEndType then compare xEndType yEndType
                  else orderInsensitiveListCmp (comparePathSegments vts br)
                         a.connectedSubPaths b.connectedSubPaths) = Ordering.lt := h_lt
    by_cases h_eq : vts.getD a.endVertexIndex.val 0 = vts.getD b.endVertexIndex.val 0
    · have h_bne_xy : (vts.getD a.endVertexIndex.val 0 != vts.getD b.endVertexIndex.val 0) = false := by
        rw [h_eq]; exact bne_self_eq_false (a := vts.getD b.endVertexIndex.val 0)
      have h_bne_yx : (vts.getD b.endVertexIndex.val 0 != vts.getD a.endVertexIndex.val 0) = false := by
        rw [h_eq]; exact bne_self_eq_false (a := vts.getD b.endVertexIndex.val 0)
      simp only [h_bne_xy, Bool.false_eq_true, ↓reduceIte] at h_lt'
      simp only [h_bne_yx, Bool.false_eq_true, ↓reduceIte]
      exact orderInsensitiveListCmp_swap_lt _ h_seg_anti₁ h_seg_anti₂ _ _ h_lt'
    · have h_bne_xy : (vts.getD a.endVertexIndex.val 0 != vts.getD b.endVertexIndex.val 0) = true :=
        bne_iff_ne.mpr h_eq
      simp only [h_bne_xy, ↓reduceIte] at h_lt'
      have h_xy_lt : (vts.getD a.endVertexIndex.val 0 : Nat) < vts.getD b.endVertexIndex.val 0 :=
        Nat.compare_eq_lt.mp h_lt'
      have h_yx_ne : vts.getD b.endVertexIndex.val 0 ≠ vts.getD a.endVertexIndex.val 0 := Ne.symm h_eq
      have h_bne_yx : (vts.getD b.endVertexIndex.val 0 != vts.getD a.endVertexIndex.val 0) = true :=
        bne_iff_ne.mpr h_yx_ne
      simp only [h_bne_yx, ↓reduceIte]
      exact Nat.compare_eq_gt.mpr h_xy_lt
  · -- Antisym₂: .gt → .lt. Mirror of above.
    intros a b h_gt
    show (let yEndType := vts.getD b.endVertexIndex.val 0
          let xEndType := vts.getD a.endVertexIndex.val 0
          if yEndType != xEndType then compare yEndType xEndType
          else orderInsensitiveListCmp (comparePathSegments vts br)
                 b.connectedSubPaths a.connectedSubPaths) = Ordering.lt
    have h_gt' : (let xEndType := vts.getD a.endVertexIndex.val 0
                  let yEndType := vts.getD b.endVertexIndex.val 0
                  if xEndType != yEndType then compare xEndType yEndType
                  else orderInsensitiveListCmp (comparePathSegments vts br)
                         a.connectedSubPaths b.connectedSubPaths) = Ordering.gt := h_gt
    by_cases h_eq : vts.getD a.endVertexIndex.val 0 = vts.getD b.endVertexIndex.val 0
    · have h_bne_xy : (vts.getD a.endVertexIndex.val 0 != vts.getD b.endVertexIndex.val 0) = false := by
        rw [h_eq]; exact bne_self_eq_false (a := vts.getD b.endVertexIndex.val 0)
      have h_bne_yx : (vts.getD b.endVertexIndex.val 0 != vts.getD a.endVertexIndex.val 0) = false := by
        rw [h_eq]; exact bne_self_eq_false (a := vts.getD b.endVertexIndex.val 0)
      simp only [h_bne_xy, Bool.false_eq_true, ↓reduceIte] at h_gt'
      simp only [h_bne_yx, Bool.false_eq_true, ↓reduceIte]
      exact orderInsensitiveListCmp_swap_gt _ h_seg_anti₁ h_seg_anti₂ _ _ h_gt'
    · have h_bne_xy : (vts.getD a.endVertexIndex.val 0 != vts.getD b.endVertexIndex.val 0) = true :=
        bne_iff_ne.mpr h_eq
      simp only [h_bne_xy, ↓reduceIte] at h_gt'
      have h_xy_gt : (vts.getD a.endVertexIndex.val 0 : Nat) > vts.getD b.endVertexIndex.val 0 :=
        Nat.compare_eq_gt.mp h_gt'
      have h_yx_ne : vts.getD b.endVertexIndex.val 0 ≠ vts.getD a.endVertexIndex.val 0 := Ne.symm h_eq
      have h_bne_yx : (vts.getD b.endVertexIndex.val 0 != vts.getD a.endVertexIndex.val 0) = true :=
        bne_iff_ne.mpr h_yx_ne
      simp only [h_bne_yx, ↓reduceIte]
      exact Nat.compare_eq_lt.mpr h_xy_gt
  · -- ≤-trans.
    intros a b c hab hbc
    -- Unfold all three.
    show (let xEndType := vts.getD a.endVertexIndex.val 0
          let zEndType := vts.getD c.endVertexIndex.val 0
          if xEndType != zEndType then compare xEndType zEndType
          else orderInsensitiveListCmp (comparePathSegments vts br)
                 a.connectedSubPaths c.connectedSubPaths) ≠ Ordering.gt
    have hab' : (let xEndType := vts.getD a.endVertexIndex.val 0
                 let yEndType := vts.getD b.endVertexIndex.val 0
                 if xEndType != yEndType then compare xEndType yEndType
                 else orderInsensitiveListCmp (comparePathSegments vts br)
                        a.connectedSubPaths b.connectedSubPaths) ≠ Ordering.gt := hab
    have hbc' : (let yEndType := vts.getD b.endVertexIndex.val 0
                 let zEndType := vts.getD c.endVertexIndex.val 0
                 if yEndType != zEndType then compare yEndType zEndType
                 else orderInsensitiveListCmp (comparePathSegments vts br)
                        b.connectedSubPaths c.connectedSubPaths) ≠ Ordering.gt := hbc
    set xT := vts.getD a.endVertexIndex.val 0 with hxT
    set yT := vts.getD b.endVertexIndex.val 0 with hyT
    set zT := vts.getD c.endVertexIndex.val 0 with hzT
    -- From hab', xT ≤ yT (via Nat.compare_eq_gt + Nat order).
    have h_xy_le : (xT : Nat) ≤ yT := by
      by_contra h_gt
      have hgt : yT < xT := Nat.lt_of_not_le h_gt
      have h_ne : xT ≠ yT := fun h => Nat.lt_irrefl _ (h ▸ hgt)
      have h_bne : (xT != yT) = true := bne_iff_ne.mpr h_ne
      simp only [h_bne, ↓reduceIte] at hab'
      exact hab' (Nat.compare_eq_gt.mpr hgt)
    have h_yz_le : (yT : Nat) ≤ zT := by
      by_contra h_gt
      have hgt : zT < yT := Nat.lt_of_not_le h_gt
      have h_ne : yT ≠ zT := fun h => Nat.lt_irrefl _ (h ▸ hgt)
      have h_bne : (yT != zT) = true := bne_iff_ne.mpr h_ne
      simp only [h_bne, ↓reduceIte] at hbc'
      exact hbc' (Nat.compare_eq_gt.mpr hgt)
    -- xT ≤ zT.
    have h_xz_le : (xT : Nat) ≤ zT := Nat.le_trans h_xy_le h_yz_le
    by_cases h_xz_eq : xT = zT
    · -- xT = zT, so all three equal (sandwich). Use trans on the orderInsensitiveListCmp.
      have h_yx_le : (yT : Nat) ≤ xT := by rw [h_xz_eq]; exact h_yz_le
      have h_xy_eq : xT = yT := Nat.le_antisymm h_xy_le h_yx_le
      have h_yz_eq : yT = zT := h_xy_eq ▸ h_xz_eq
      have h_bne_xz : (xT != zT) = false := by
        rw [h_xz_eq]; exact bne_self_eq_false (a := zT)
      have h_bne_xy : (xT != yT) = false := by
        rw [h_xy_eq]; exact bne_self_eq_false (a := yT)
      have h_bne_yz : (yT != zT) = false := by
        rw [h_yz_eq]; exact bne_self_eq_false (a := zT)
      simp only [h_bne_xy, Bool.false_eq_true, ↓reduceIte] at hab'
      simp only [h_bne_yz, Bool.false_eq_true, ↓reduceIte] at hbc'
      simp only [h_bne_xz, Bool.false_eq_true, ↓reduceIte]
      exact orderInsensitiveListCmp_trans _ h_seg_anti₁ h_seg_trans h_seg_compat _ _ _ hab' hbc'
    · -- xT < zT, conclusion is .lt ≠ .gt.
      have h_xz_lt : (xT : Nat) < zT := lt_of_le_of_ne h_xz_le h_xz_eq
      have h_bne_xz : (xT != zT) = true := bne_iff_ne.mpr h_xz_eq
      simp only [h_bne_xz, ↓reduceIte]
      rw [Nat.compare_eq_lt.mpr h_xz_lt]
      intro h; exact Ordering.noConfusion h


end Graph
