import FullCorrectness.Equivariance.ConvergeLoopGeneral
import FullCorrectness.Equivariance.RunFromRelational

/-!
# Phase 6 orderVertices σ-equivariance general σ (P6.C)
  (`FullCorrectness.Equivariance.OrderVerticesGeneral`)

The `orderVertices` outer foldl iterates `convergeLoop ∘ breakTie` over `0..n-1`.
For Phase 6 (`run zeros G = run zeros (G.permute σ)` for σ ∉ Aut G), we need a
"two-graphs" version of Phase 5's `runFrom_VtsInvariant_eq_strong`: the outputs of
`runFrom s arr₁ G` and `runFrom s arr₂ (G.permute σ)` are equal whenever
`arr₁`, `arr₂` are σ-related (with `σ_chain = σ * τ` for `τ ∈ Aut G`, so
`G.permute σ_chain = G.permute σ`).

## Status

The strong theorem `runFrom_VtsInvariant_eq_strong_general` is fully closed modulo the
`OrbitCompleteAfterConv_general` hypothesis, mirroring Phase 5's
`OrbitCompleteAfterConv` orbit-completeness invariant.

The Phase 6 application (`orderVertices_σ_equivariant_general_zeros`) is then a direct
specialization at `s = 0`, `vts = zeros`, `τ = 1`. The orbit hypothesis is provided as
a hypothesis to be discharged at the call site.
-/

namespace Graph

open AdjMatrix

variable {n : Nat}

/-! ### Two-graphs orbit-completeness invariant -/

/-- Orbit-completeness adapted for the two-graphs case: vertices with equal values in
`convergeLoop(initializePaths (G.permute σ)) mid n` lie in the same `TypedAut`-orbit of
that converged array on `G.permute σ`. Discharged at the call site by canonizer-correctness
reasoning. -/
def OrbitCompleteAfterConv_general (G : AdjMatrix n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ (mid : Array VertexType), mid.size = n →
    ∀ v₁ v₂ : Fin n,
      (convergeLoop (initializePaths (G.permute σ)) mid n).getD v₁.val 0 =
      (convergeLoop (initializePaths (G.permute σ)) mid n).getD v₂.val 0 →
      ∃ τ_step ∈ (G.permute σ).TypedAut
                  (convergeLoop (initializePaths (G.permute σ)) mid n),
        τ_step v₁ = v₂

/-! ### Two-graphs convergeLoop step preservation -/

/-- Two-graphs analogue of `convergeLoop_step_τ_preserved`, chaining through an
intermediate τ-shifted typing on the same G. Uses Phase 5's σ ∈ Aut G version
(`convergeLoop_VtsInvariant_eq`) for the τ-step plus P6.B
(`convergeLoop_σ_equivariant_general`) for the σ-step.

Decomposition: with σ_chain = σ * τ (τ ∈ Aut G), `σ_chain⁻¹ = τ⁻¹ * σ⁻¹`. We chain
through `vts_mid` (the τ-shift of vts₁ on G) which is τ-related to vts₁ AND σ-related
to vts₂ (the σ_chain-shift of vts₁). -/
private theorem convergeLoop_step_σ_chain_preserved_general
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (σ_chain : Equiv.Perm (Fin n))
    (h_chain_form : ∃ τ : Equiv.Perm (Fin n), τ ∈ AdjMatrix.Aut G ∧ σ_chain = σ * τ)
    (vts₁ vts₂ : Array VertexType)
    (h_size₁ : vts₁.size = n) (h_size₂ : vts₂.size = n)
    (h_rel : ∀ w : Fin n, vts₂.getD w.val 0 = vts₁.getD (σ_chain⁻¹ w).val 0) :
    let converged₁ := convergeLoop (initializePaths G) vts₁ n
    let converged₂ := convergeLoop (initializePaths (G.permute σ)) vts₂ n
    converged₁.size = n ∧ converged₂.size = n ∧
    (∀ w : Fin n, converged₂.getD w.val 0 = converged₁.getD (σ_chain⁻¹ w).val 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [convergeLoop_size_preserving]; exact h_size₁
  · rw [convergeLoop_size_preserving]; exact h_size₂
  · obtain ⟨τ, hτ_Aut, hστ_eq⟩ := h_chain_form
    -- Introduce intermediate vts_mid: the τ-shift of vts₁ on G.
    classical
    let vts_mid : Array VertexType := (Array.range n).map (fun i =>
      vts₁.getD (permNat τ⁻¹ i) 0)
    have h_vts_mid_size : vts_mid.size = n := by simp [vts_mid]
    -- vts_mid[w] = vts₁[τ⁻¹ w].
    have h_vts_mid_eq : ∀ w : Fin n, vts_mid.getD w.val 0 = vts₁.getD (τ⁻¹ w).val 0 := by
      intro w
      show ((Array.range n).map (fun i => vts₁.getD (permNat τ⁻¹ i) 0)).getD w.val 0
         = vts₁.getD (τ⁻¹ w).val 0
      have hw_lt : w.val < ((Array.range n).map (fun i => vts₁.getD (permNat τ⁻¹ i) 0)).size := by
        simp [w.isLt]
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw_lt, Option.getD_some,
          Array.getElem_map, Array.getElem_range]
      rw [show permNat τ⁻¹ w.val = (τ⁻¹ w).val from permNat_fin τ⁻¹ w]
    -- Step 1: vts_mid is τ-shifted from vts₁ on G (Phase 5 / convergeLoop_VtsInvariant_eq).
    have h_τ_step : ∀ w : Fin n,
        (convergeLoop (initializePaths G) vts_mid n).getD w.val 0
        = (convergeLoop (initializePaths G) vts₁ n).getD (τ⁻¹ w).val 0 := by
      intro w
      exact convergeLoop_VtsInvariant_eq G τ hτ_Aut vts₁ vts_mid n
        h_size₁ h_vts_mid_size h_vts_mid_eq w
    -- Step 2: vts₂[w] = vts_mid[σ⁻¹ w] (σ-shift relation between vts_mid and vts₂).
    have h_vts₂_σ_eq : ∀ w : Fin n, vts₂.getD w.val 0 = vts_mid.getD (σ⁻¹ w).val 0 := by
      intro w
      rw [h_vts_mid_eq (σ⁻¹ w)]
      -- Goal: vts₂[w] = vts₁[τ⁻¹ (σ⁻¹ w)]. We have h_rel: vts₂[w] = vts₁[σ_chain⁻¹ w].
      -- σ_chain⁻¹ = (σ * τ)⁻¹ = τ⁻¹ * σ⁻¹.
      have h_σ_chain_inv : σ_chain⁻¹ w = τ⁻¹ (σ⁻¹ w) := by
        rw [hστ_eq]
        show (σ * τ)⁻¹ w = τ⁻¹ (σ⁻¹ w)
        simp [mul_inv_rev]
      rw [h_rel w, h_σ_chain_inv]
    -- Step 3: convergeLoop on (G.permute σ, vts₂) is σ-shifted from
    -- convergeLoop on (G, vts_mid). Use P6.B.
    have h_σ_step : ∀ w : Fin n,
        (convergeLoop (initializePaths (G.permute σ)) vts₂ n).getD w.val 0
        = (convergeLoop (initializePaths G) vts_mid n).getD (σ⁻¹ w).val 0 := by
      intro w
      exact convergeLoop_σ_equivariant_general G σ vts_mid vts₂ n
        h_vts_mid_size h_size₂ h_vts₂_σ_eq w
    -- Step 4: chain Steps 1 and 2.
    intro w
    rw [h_σ_step w, h_τ_step (σ⁻¹ w)]
    -- Goal: conv on (G, vts₁) at (τ⁻¹ (σ⁻¹ w)) = conv on (G, vts₁) at σ_chain⁻¹ w.
    have h_σ_chain_inv_w : σ_chain⁻¹ w = τ⁻¹ (σ⁻¹ w) := by
      rw [hστ_eq]
      show (σ * τ)⁻¹ w = τ⁻¹ (σ⁻¹ w)
      simp [mul_inv_rev]
    rw [h_σ_chain_inv_w]

/-! ### Strong theorem for orderVertices outer loop on two graphs

This is the structural analog of Phase 5's `runFrom_VtsInvariant_eq_strong`, but
where the two sides use different graphs (`G` and `G.permute σ`) and a chained σ_chain
permutation. The chain form `σ_chain = σ * τ` (τ ∈ Aut G) ensures
`G.permute σ_chain = G.permute σ`, so the labelEdges base case applies.
-/

/-- **P6.C strong theorem — two-graphs orderVertices σ-equivariance**.

Mirrors `runFrom_VtsInvariant_eq_strong` but tracks the two-graphs σ-chain. -/
theorem runFrom_VtsInvariant_eq_strong_general
    (G : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (s : Nat) (σ_chain : Equiv.Perm (Fin n))
    (h_chain_form : ∃ τ : Equiv.Perm (Fin n), τ ∈ AdjMatrix.Aut G ∧ σ_chain = σ * τ)
    (arr₁ arr₂ : Array VertexType)
    (h_size₁ : arr₁.size = n) (h_size₂ : arr₂.size = n)
    (h_rel : ∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (σ_chain⁻¹ w).val 0)
    (h_prefix : @IsPrefixTyping n arr₁)
    (h_unique : @UniquelyHeldBelow n arr₁ s)
    (hs : s ≤ n)
    (hOrbit : OrbitCompleteAfterConv_general (n := n) G σ) :
    runFrom s arr₁ G = runFrom s arr₂ (G.permute σ) := by
  -- Induct on m := n - s, generalizing over s, σ_chain, arr₁, arr₂.
  suffices h : ∀ (m s : Nat) (σ_chain' : Equiv.Perm (Fin n))
      (h_chain_form' : ∃ τ' : Equiv.Perm (Fin n), τ' ∈ AdjMatrix.Aut G ∧ σ_chain' = σ * τ')
      (arr₁ arr₂ : Array VertexType),
      n - s = m →
      arr₁.size = n → arr₂.size = n →
      (∀ w : Fin n, arr₂.getD w.val 0 = arr₁.getD (σ_chain'⁻¹ w).val 0) →
      @IsPrefixTyping n arr₁ →
      @UniquelyHeldBelow n arr₁ s →
      s ≤ n →
      runFrom s arr₁ G = runFrom s arr₂ (G.permute σ) by
    exact h (n - s) s σ_chain h_chain_form arr₁ arr₂ rfl h_size₁ h_size₂ h_rel h_prefix h_unique hs
  clear h_size₁ h_size₂ h_rel h_prefix h_unique hs arr₁ arr₂ s σ_chain h_chain_form
  intro m
  induction m with
  | zero =>
    intro s σ_chain' h_chain_form' arr₁ arr₂ h_m_def h_size₁ h_size₂ h_rel h_prefix h_unique hs
    -- Base: n - s = 0 ⟹ s = n.
    have hsn : s = n := by omega
    have h_unique_n : @UniquelyHeldBelow n arr₁ n := hsn ▸ h_unique
    have h_tf₁ : TieFree arr₁ n :=
      UniquelyHeldBelow_n_implies_TieFree arr₁ h_size₁ h_unique_n
    have h_unique₂ : @UniquelyHeldBelow n arr₂ n :=
      UniquelyHeldBelow_τ_transfer σ_chain' arr₁ arr₂ h_rel n h_unique_n
    have h_tf₂ : TieFree arr₂ n :=
      UniquelyHeldBelow_n_implies_TieFree arr₂ h_size₂ h_unique₂
    -- Apply runFrom_at_n on both sides.
    rw [hsn]
    have h_lhs : runFrom n arr₁ G = labelEdgesAccordingToRankings arr₁ G :=
      runFrom_at_n G arr₁
    have h_rhs : runFrom n arr₂ (G.permute σ)
               = labelEdgesAccordingToRankings arr₂ (G.permute σ) :=
      runFrom_at_n (G.permute σ) arr₂
    rw [h_lhs, h_rhs]
    -- labelEdges_two_graphs_σ_related applies with σ replaced by σ_chain'.
    -- Since G.permute σ_chain' = G.permute σ (via h_chain_form'), the conclusion matches.
    obtain ⟨τ', hτ'_Aut, hστ'_eq⟩ := h_chain_form'
    have h_G_permute_σ_chain' : G.permute σ_chain' = G.permute σ := by
      rw [hστ'_eq, AdjMatrix.permute_mul σ τ' G]
      show (G.permute τ').permute σ = G.permute σ
      rw [show G.permute τ' = G from hτ'_Aut]
    rw [show G.permute σ = G.permute σ_chain' from h_G_permute_σ_chain'.symm]
    exact (labelEdges_two_graphs_σ_related G σ_chain' arr₁ arr₂
            h_size₁ h_size₂ h_tf₁ h_tf₂ h_rel).symm
  | succ m ih =>
    intro s σ_chain' h_chain_form' arr₁ arr₂ h_m_def h_size₁ h_size₂ h_rel h_prefix h_unique hs
    have hs_lt : s < n := by omega
    rw [runFrom_succ G arr₁ s hs_lt]
    -- For runFrom on G.permute σ, we need a runFrom_succ analog. Use the same lemma
    -- since runFrom is defined parametrically over G.
    rw [show runFrom s arr₂ (G.permute σ)
          = runFrom (s + 1)
              ((breakTie (convergeLoop (initializePaths (G.permute σ)) arr₂ n) s).1)
              (G.permute σ) from runFrom_succ (G.permute σ) arr₂ s hs_lt]
    set conv₁ := convergeLoop (initializePaths G) arr₁ n with h_conv₁_def
    set conv₂ := convergeLoop (initializePaths (G.permute σ)) arr₂ n with h_conv₂_def
    set arr₁' := (breakTie conv₁ s).1 with h_arr₁'_def
    set arr₂' := (breakTie conv₂ s).1 with h_arr₂'_def
    -- Get convergeLoop step preservation via the σ_chain version.
    have ⟨h_conv₁_size, h_conv₂_size, h_conv_rel⟩ :=
      convergeLoop_step_σ_chain_preserved_general G σ σ_chain' h_chain_form'
        arr₁ arr₂ h_size₁ h_size₂ h_rel
    have h_conv₁_prefix : @IsPrefixTyping n conv₁ :=
      convergeLoop_preserves_prefix G arr₁ n h_size₁ h_prefix
    have h_conv₁_both : @IsPrefixTyping n conv₁ ∧ @UniquelyHeldBelow n conv₁ s :=
      convergeLoop_preserves_lower_uniqueness G arr₁ s (Nat.le_of_lt hs_lt) n h_size₁ h_prefix h_unique
    have h_conv₁_unique : @UniquelyHeldBelow n conv₁ s := h_conv₁_both.2
    have ⟨h_arr₁'_prefix, h_arr₁'_unique⟩ :=
      breakTie_step_preserves_uniqueness conv₁ s hs_lt h_conv₁_size h_conv₁_prefix h_conv₁_unique
    have h_arr₁'_size : arr₁'.size = n := by
      rw [h_arr₁'_def, breakTie_size]; exact h_conv₁_size
    have h_arr₂'_size : arr₂'.size = n := by
      rw [h_arr₂'_def, breakTie_size]; exact h_conv₂_size
    have hs1 : s + 1 ≤ n := hs_lt
    have h_m_def' : n - (s + 1) = m := by omega
    have h_count_eq : breakTieCount conv₁ s = breakTieCount conv₂ s :=
      breakTieCount_τ_invariant σ_chain' conv₁ conv₂ h_conv₁_size h_conv₂_size h_conv_rel s
    by_cases hcount : breakTieCount conv₁ s < 2
    · -- Case 1 (no fire): arr_i' = conv_i. σ_chain'-related; apply IH at s+1 with same σ_chain'.
      have hcount₂ : breakTieCount conv₂ s < 2 := h_count_eq ▸ hcount
      have h_arr₁'_eq : arr₁' = conv₁ := by
        rw [h_arr₁'_def, breakTie_noop conv₁ s hcount]
      have h_arr₂'_eq : arr₂' = conv₂ := by
        rw [h_arr₂'_def, breakTie_noop conv₂ s hcount₂]
      rw [h_arr₁'_eq, h_arr₂'_eq]
      have h_conv₁_unique_succ : @UniquelyHeldBelow n conv₁ (s + 1) := h_arr₁'_eq ▸ h_arr₁'_unique
      exact ih (s + 1) σ_chain' h_chain_form' conv₁ conv₂ h_m_def' h_conv₁_size h_conv₂_size
        h_conv_rel h_conv₁_prefix h_conv₁_unique_succ hs1
    · -- Case 2 (fire): orbit-bridging.
      have hcount2 : 2 ≤ breakTieCount conv₁ s := by omega
      have hcount2_b : 2 ≤ breakTieCount conv₂ s := h_count_eq ▸ hcount2
      obtain ⟨v₁, hv₁_val, hv₁_min⟩ :=
        breakTie_min_witness conv₁ h_conv₁_size s hcount2
      obtain ⟨v₂, hv₂_val, hv₂_min⟩ :=
        breakTie_min_witness conv₂ h_conv₂_size s hcount2_b
      -- σ_chain' v₁ ∈ typeClass conv₂ s.
      have hσv₁_in : conv₂.getD (σ_chain' v₁).val 0 = s := by
        have := typeClass_τ_image_eq σ_chain' conv₁ conv₂ h_conv_rel s
        have h_in : σ_chain' v₁ ∈ @typeClass n conv₂ s := by
          rw [this]; exact ⟨v₁, hv₁_val, rfl⟩
        exact h_in
      -- Orbit hypothesis: ∃ τ_step ∈ TypedAut(conv₂) (on G.permute σ) with τ_step (σ_chain' v₁) = v₂.
      have hσv₁_v₂_same : conv₂.getD (σ_chain' v₁).val 0 = conv₂.getD v₂.val 0 := by
        rw [hσv₁_in, hv₂_val]
      obtain ⟨τ_step, hτ_step_TypedAut, hτ_step_apply⟩ :=
        hOrbit arr₂ h_size₂ (σ_chain' v₁) v₂ hσv₁_v₂_same
      -- τ_step ∈ Aut(G.permute σ).
      have hτ_step_Aut : τ_step ∈ AdjMatrix.Aut (G.permute σ) :=
        AdjMatrix.TypedAut_le_Aut (G.permute σ) conv₂ hτ_step_TypedAut
      have hτ_step_INV : VtsInvariant τ_step conv₂ := hτ_step_TypedAut.2
      -- New chained σ_chain'' = τ_step * σ_chain'.
      let σ_chain'' := τ_step * σ_chain'
      -- σ_chain'' has the chain form σ * (Aut G) (via conjugation).
      -- τ_step ∈ Aut(G.permute σ) ⟺ σ⁻¹ * τ_step * σ ∈ Aut G.
      have h_chain_form'' : ∃ τ'' : Equiv.Perm (Fin n), τ'' ∈ AdjMatrix.Aut G ∧
          σ_chain'' = σ * τ'' := by
        obtain ⟨τ', hτ'_Aut, hστ'_eq⟩ := h_chain_form'
        let τ'' := σ⁻¹ * τ_step * σ * τ'
        refine ⟨τ'', ?_, ?_⟩
        · -- τ'' ∈ Aut G: τ' ∈ Aut G and σ⁻¹ * τ_step * σ ∈ Aut G.
          have h_conj : σ⁻¹ * τ_step * σ ∈ AdjMatrix.Aut G := by
            -- τ_step ∈ Aut(G.permute σ): (G.permute σ).permute τ_step = G.permute σ.
            -- We want σ⁻¹ * τ_step * σ ∈ Aut G: G.permute (σ⁻¹ * τ_step * σ) = G.
            have h1 : (G.permute σ).permute τ_step = G.permute σ := hτ_step_Aut
            -- (G.permute σ).permute τ_step = G.permute (τ_step * σ).
            rw [show (G.permute σ).permute τ_step = G.permute (τ_step * σ)
                  from (AdjMatrix.permute_mul τ_step σ G).symm] at h1
            show G.permute (σ⁻¹ * τ_step * σ) = G
            have h2 : G.permute (τ_step * σ) = G.permute σ := h1
            have h3 : (G.permute (τ_step * σ)).permute σ⁻¹ = (G.permute σ).permute σ⁻¹ := by
              rw [h2]
            rw [show (G.permute (τ_step * σ)).permute σ⁻¹ = G.permute (σ⁻¹ * (τ_step * σ))
                  from (AdjMatrix.permute_mul σ⁻¹ (τ_step * σ) G).symm] at h3
            rw [show (G.permute σ).permute σ⁻¹ = G.permute (σ⁻¹ * σ)
                  from (AdjMatrix.permute_mul σ⁻¹ σ G).symm] at h3
            simp at h3
            rw [show σ⁻¹ * τ_step * σ = σ⁻¹ * (τ_step * σ) from mul_assoc _ _ _]
            exact h3
          exact Subgroup.mul_mem _ h_conj hτ'_Aut
        · -- σ_chain'' = σ * τ''.
          show τ_step * σ_chain' = σ * (σ⁻¹ * τ_step * σ * τ')
          rw [hστ'_eq]
          -- Goal: τ_step * (σ * τ') = σ * (σ⁻¹ * τ_step * σ * τ').
          -- Both equal τ_step * σ * τ'.
          rw [show σ * (σ⁻¹ * τ_step * σ * τ') = (σ * σ⁻¹) * τ_step * σ * τ' from by
                simp [mul_assoc]]
          rw [mul_inv_cancel, one_mul, mul_assoc]
      -- Now show arr₁', arr₂' are σ_chain''-related.
      have h_στ_rel : ∀ w : Fin n, arr₂'.getD w.val 0 = arr₁'.getD (σ_chain''⁻¹ w).val 0 := by
        intro w
        have h_inv_apply : σ_chain''⁻¹ w = σ_chain'⁻¹ (τ_step⁻¹ w) := by
          show (τ_step * σ_chain')⁻¹ w = σ_chain'⁻¹ (τ_step⁻¹ w)
          simp [mul_inv_rev]
        rw [h_inv_apply]
        set u := τ_step⁻¹ w with h_u_def
        have h_w_eq_τu : w = τ_step u := by simp [h_u_def]
        have h_conv₂_w_eq_u : conv₂.getD w.val 0 = conv₂.getD u.val 0 := by
          have := hτ_step_INV u
          rw [show τ_step u = w from h_w_eq_τu.symm] at this
          exact this
        have h_conv_link : conv₁.getD (σ_chain'⁻¹ u).val 0 = conv₂.getD u.val 0 := by
          rw [h_conv_rel u]
        rcases lt_trichotomy (conv₂.getD w.val 0) s with h_lt | h_eq | h_gt
        · -- conv₂[w] < s: both arr_i' = conv_i (below).
          rw [breakTie_getD_below conv₂ s h_lt]
          have h_below₁ : conv₁.getD (σ_chain'⁻¹ u).val 0 < s := by
            rw [h_conv_link, ← h_conv₂_w_eq_u]; exact h_lt
          rw [breakTie_getD_below conv₁ s h_below₁]
          rw [h_conv_link, ← h_conv₂_w_eq_u]
        · -- conv₂[w] = s: both in typeClass; differ by min-keep.
          have h_w_in : conv₂.getD w.val 0 = s := h_eq
          have h_u_in : conv₂.getD u.val 0 = s := h_conv₂_w_eq_u ▸ h_eq
          have h_τinv_u_in : conv₁.getD (σ_chain'⁻¹ u).val 0 = s := h_conv_link.trans h_u_in
          -- τ_step (σ_chain' v₁) = v₂; w = τ_step u; so w = v₂ ⟺ σ_chain'⁻¹ u = v₁.
          have h_iff : w = v₂ ↔ σ_chain'⁻¹ u = v₁ := by
            constructor
            · intro hw
              have : τ_step u = τ_step (σ_chain' v₁) := by
                rw [← h_w_eq_τu, hw, ← hτ_step_apply]
              have hu_eq : u = σ_chain' v₁ := τ_step.injective this
              have : σ_chain'⁻¹ u = σ_chain'⁻¹ (σ_chain' v₁) := by rw [hu_eq]
              simpa using this
            · intro h_inv_eq
              have hu_eq : u = σ_chain' v₁ := by
                have : σ_chain' (σ_chain'⁻¹ u) = σ_chain' v₁ := by rw [h_inv_eq]
                simpa using this
              rw [h_w_eq_τu, hu_eq, hτ_step_apply]
          have hv₂_size : v₂.val < conv₂.size := h_conv₂_size.symm ▸ v₂.isLt
          have hv₁_size : v₁.val < conv₁.size := h_conv₁_size.symm ▸ v₁.isLt
          have hv₁_min_idx : ∀ i, i < v₁.val → conv₁.getD i 0 ≠ s := by
            intro i hi h_i_eq
            have hi_lt_n : i < n := by
              have hv₁_lt_n : v₁.val < n := v₁.isLt
              omega
            exact hv₁_min ⟨i, hi_lt_n⟩ hi h_i_eq
          have hv₂_min_idx : ∀ i, i < v₂.val → conv₂.getD i 0 ≠ s := by
            intro i hi h_i_eq
            have hi_lt_n : i < n := by
              have hv₂_lt_n : v₂.val < n := v₂.isLt
              omega
            exact hv₂_min ⟨i, hi_lt_n⟩ hi h_i_eq
          by_cases hw_v₂ : w = v₂
          · have h_arr₂'_v₂ : arr₂'.getD v₂.val 0 = s := by
              show (breakTie conv₂ s).1.getD v₂.val 0 = s
              exact breakTie_getD_at_min conv₂ s hv₂_size hv₂_val hv₂_min_idx
            have h_τinv_u_v₁ : σ_chain'⁻¹ u = v₁ := h_iff.mp hw_v₂
            have h_arr₁'_v₁ : arr₁'.getD (σ_chain'⁻¹ u).val 0 = s := by
              rw [h_τinv_u_v₁]
              show (breakTie conv₁ s).1.getD v₁.val 0 = s
              exact breakTie_getD_at_min conv₁ s hv₁_size hv₁_val hv₁_min_idx
            rw [hw_v₂, h_arr₂'_v₂, h_arr₁'_v₁]
          · have hw_size : w.val < conv₂.size := h_conv₂_size.symm ▸ w.isLt
            have h_arr₂'_w : arr₂'.getD w.val 0 = s + 1 := by
              show (breakTie conv₂ s).1.getD w.val 0 = s + 1
              exact breakTie_getD_at_other conv₂ s hv₂_size hv₂_val hv₂_min_idx
                hw_size h_w_in (fun heq => hw_v₂ (Fin.ext heq))
            have h_τinv_u_ne_v₁ : σ_chain'⁻¹ u ≠ v₁ := fun heq => hw_v₂ (h_iff.mpr heq)
            have h_τinv_u_size : (σ_chain'⁻¹ u).val < conv₁.size :=
              h_conv₁_size.symm ▸ (σ_chain'⁻¹ u).isLt
            have h_arr₁'_τinv_u : arr₁'.getD (σ_chain'⁻¹ u).val 0 = s + 1 := by
              show (breakTie conv₁ s).1.getD (σ_chain'⁻¹ u).val 0 = s + 1
              exact breakTie_getD_at_other conv₁ s hv₁_size hv₁_val hv₁_min_idx
                h_τinv_u_size h_τinv_u_in (fun heq => h_τinv_u_ne_v₁ (Fin.ext heq))
            rw [h_arr₂'_w, h_arr₁'_τinv_u]
        · -- conv₂[w] > s: both arr_i' = conv_i + 1 (above).
          rw [breakTie_getD_above conv₂ s hcount2_b h_gt]
          have h_above₁ : conv₁.getD (σ_chain'⁻¹ u).val 0 > s := by
            rw [h_conv_link, ← h_conv₂_w_eq_u]; exact h_gt
          rw [breakTie_getD_above conv₁ s hcount2 h_above₁]
          rw [h_conv_link, ← h_conv₂_w_eq_u]
      exact ih (s + 1) σ_chain'' h_chain_form'' arr₁' arr₂' h_m_def'
        h_arr₁'_size h_arr₂'_size h_στ_rel h_arr₁'_prefix h_arr₁'_unique hs1

/-! ## Note on `orderVertices_σ_equivariant_general`

The orderVertices-only σ-equivariance specialization (without the labelEdges step)
is not needed for the Phase 6 / Main.lean closure: `run_swap_invariant_fwd` applies
the strong theorem (`runFrom_VtsInvariant_eq_strong_general`) directly to compare
the full `runFrom 0 zeros · ` outputs (which include labelEdges).

If a downstream consumer needs the orderVertices-only σ-equivariance, it can be
derived from the strong theorem by stripping the final labelEdges step (using the
fact that labelEdges is determined by the rankings). Not provided here. -/

end Graph
