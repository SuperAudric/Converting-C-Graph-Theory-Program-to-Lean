import FullCorrectness.Equivariance.CompareEquivariant

/-!
# Structural facts about `pathsAtDepth` from `initializePaths G` (`FullCorrectness.Equivariance.PathsAtDepthStructure`)

Mirrors `initializePaths_pathsAtDepth_startVertices_eq_range` from `Invariants.lean`,
but provided here so the σ-invariance proofs in `PathEquivariance.lean`
(which precede `Invariants.lean` in the import order) can use them.

Exposes:
- `initializePaths_pathsOfLength_get_eq` (private) — explicit constructor form of
  the depth-`d` slice.
- `initializePaths_pathsAtDepth_structure` (private) — outer length, start-vertex
  enumeration, and inner-length conditions for a single depth.
- `initializePaths_pathsAtDepth_inner_structure` (private) — inner per-`PathsFrom`
  structural facts (constant `startVertexIndex`, `endVertexIndex` enumeration).
- `initializePaths_allBetween_pairs_facts` (private) — Nodup of `(start, end)` pairs
  and completeness over `Fin n × Fin n` for the flattened `allBetween` list.
-/

namespace Graph

variable {n : Nat}

/-- The depth-`d` slice of `(initializePaths G).pathsOfLength` has the explicit
constructor form. Used to extract structural facts (lengths, start vertices, etc.). -/
private theorem initializePaths_pathsOfLength_get_eq
    (G : AdjMatrix n) {d : Nat} (hd : d < n)
    (h_in : d < (initializePaths G).pathsOfLength.size) :
    (initializePaths G).pathsOfLength[d]'h_in
      = (List.finRange n).toArray.map fun startFin : Fin n =>
          ({ depth := d, startVertexIndex := startFin,
             pathsToVertex := (List.finRange n).map fun endFin : Fin n =>
               { depth := d, startVertexIndex := startFin, endVertexIndex := endFin,
                 connectedSubPaths :=
                   if d = 0 then
                     (if startFin = endFin then [PathSegment.bottom startFin] else []
                      : List (PathSegment n))
                   else
                     (List.finRange n).map fun midFin : Fin n =>
                       PathSegment.inner (G.adj midFin endFin) (d - 1) startFin midFin } }
              : PathsFrom n) := by
  show ((List.finRange n).toArray.map _)[d]'_ = _
  rw [Array.getElem_map]
  simp [List.getElem_finRange]

/-- The structural facts about `pathsAtDepth` from `initializePaths G`: outer length,
start-vertex enumeration, and inner length conditions. -/
theorem initializePaths_pathsAtDepth_structure
    (G : AdjMatrix n) {d : Nat} (hd : d < n) :
    let pathsAtDepth := ((initializePaths G).pathsOfLength.getD d #[]).toList
    pathsAtDepth.length = n ∧
    pathsAtDepth.map (·.startVertexIndex.val) = List.range n ∧
    (∀ p ∈ pathsAtDepth, p.pathsToVertex.length = n) ∧
    (∀ p ∈ pathsAtDepth, ∀ q ∈ p.pathsToVertex,
        q.depth > 0 → q.connectedSubPaths.length = n) := by
  intro pathsAtDepth
  have h_in : d < (initializePaths G).pathsOfLength.size := by
    rw [initializePaths_pathsOfLength_size]; exact hd
  have h_pathsAtDepth_eq : pathsAtDepth = ((initializePaths G).pathsOfLength[d]'h_in).toList := by
    show ((initializePaths G).pathsOfLength.getD d #[]).toList = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h_in, Option.getD_some]
  have h_slice := initializePaths_pathsOfLength_get_eq G hd h_in
  -- Compute pathsAtDepth in the explicit form.
  have h_pathsAtDepth :
      pathsAtDepth = (List.finRange n).map fun startFin : Fin n =>
          ({ depth := d, startVertexIndex := startFin,
             pathsToVertex := (List.finRange n).map fun endFin : Fin n =>
               { depth := d, startVertexIndex := startFin, endVertexIndex := endFin,
                 connectedSubPaths :=
                   if d = 0 then
                     (if startFin = endFin then [PathSegment.bottom startFin] else []
                      : List (PathSegment n))
                   else
                     (List.finRange n).map fun midFin : Fin n =>
                       PathSegment.inner (G.adj midFin endFin) (d - 1) startFin midFin } }
              : PathsFrom n) := by
    rw [h_pathsAtDepth_eq, h_slice, Array.toList_map, List.toList_toArray]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- pathsAtDepth.length = n
    rw [h_pathsAtDepth, List.length_map, List.length_finRange]
  · -- pathsAtDepth.map (·.startVertexIndex.val) = List.range n
    rw [h_pathsAtDepth, List.map_map]
    show (List.finRange n).map (fun startFin : Fin n => startFin.val) = List.range n
    exact List.map_coe_finRange_eq_range
  · -- ∀ p ∈ pathsAtDepth, p.pathsToVertex.length = n
    intros p h_p_in
    rw [h_pathsAtDepth] at h_p_in
    obtain ⟨startFin, _, h_p_eq⟩ := List.mem_map.mp h_p_in
    subst h_p_eq
    show ((List.finRange n).map _).length = n
    rw [List.length_map, List.length_finRange]
  · -- ∀ p ∈ pathsAtDepth, ∀ q ∈ p.pathsToVertex, q.depth > 0 → q.connectedSubPaths.length = n
    intros p h_p_in q h_q_in h_q_depth
    rw [h_pathsAtDepth] at h_p_in
    obtain ⟨startFin, _, h_p_eq⟩ := List.mem_map.mp h_p_in
    subst h_p_eq
    -- q ∈ (List.finRange n).map (...).
    obtain ⟨endFin, _, h_q_eq⟩ := List.mem_map.mp h_q_in
    subst h_q_eq
    -- q.depth = d. By h_q_depth, d > 0 so d ≠ 0.
    have h_d_ne : d ≠ 0 := by
      intro h_d; rw [h_d] at h_q_depth; exact absurd h_q_depth (Nat.lt_irrefl 0)
    simp only [if_neg h_d_ne, List.length_map, List.length_finRange]

/-- Inner structural facts about `pathsAtDepth` from `initializePaths G`: every entry of
`pf.pathsToVertex` has its `startVertexIndex` equal to `pf.startVertexIndex`, and the
`endVertexIndex.val`s of `pf.pathsToVertex` enumerate `List.range n`. -/
private theorem initializePaths_pathsAtDepth_inner_structure
    (G : AdjMatrix n) {d : Nat} (hd : d < n) :
    let pathsAtDepth := ((initializePaths G).pathsOfLength.getD d #[]).toList
    (∀ pf ∈ pathsAtDepth, ∀ q ∈ pf.pathsToVertex,
        q.startVertexIndex = pf.startVertexIndex) ∧
    (∀ pf ∈ pathsAtDepth,
        pf.pathsToVertex.map (·.endVertexIndex.val) = List.range n) := by
  intro pathsAtDepth
  have h_in : d < (initializePaths G).pathsOfLength.size := by
    rw [initializePaths_pathsOfLength_size]; exact hd
  have h_pathsAtDepth_eq : pathsAtDepth = ((initializePaths G).pathsOfLength[d]'h_in).toList := by
    show ((initializePaths G).pathsOfLength.getD d #[]).toList = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h_in, Option.getD_some]
  have h_slice := initializePaths_pathsOfLength_get_eq G hd h_in
  have h_pathsAtDepth :
      pathsAtDepth = (List.finRange n).map fun startFin : Fin n =>
          ({ depth := d, startVertexIndex := startFin,
             pathsToVertex := (List.finRange n).map fun endFin : Fin n =>
               { depth := d, startVertexIndex := startFin, endVertexIndex := endFin,
                 connectedSubPaths :=
                   if d = 0 then
                     (if startFin = endFin then [PathSegment.bottom startFin] else []
                      : List (PathSegment n))
                   else
                     (List.finRange n).map fun midFin : Fin n =>
                       PathSegment.inner (G.adj midFin endFin) (d - 1) startFin midFin } }
              : PathsFrom n) := by
    rw [h_pathsAtDepth_eq, h_slice, Array.toList_map, List.toList_toArray]
  refine ⟨?_, ?_⟩
  · -- ∀ pf ∈ pathsAtDepth, ∀ q ∈ pf.pathsToVertex, q.startVertexIndex = pf.startVertexIndex
    intros pf h_pf_in q h_q_in
    rw [h_pathsAtDepth] at h_pf_in
    obtain ⟨startFin, _, h_pf_eq⟩ := List.mem_map.mp h_pf_in
    subst h_pf_eq
    obtain ⟨endFin, _, h_q_eq⟩ := List.mem_map.mp h_q_in
    subst h_q_eq
    rfl
  · -- ∀ pf ∈ pathsAtDepth, pf.pathsToVertex.map (·.endVertexIndex.val) = List.range n
    intros pf h_pf_in
    rw [h_pathsAtDepth] at h_pf_in
    obtain ⟨startFin, _, h_pf_eq⟩ := List.mem_map.mp h_pf_in
    subst h_pf_eq
    show ((List.finRange n).map _).map _ = _
    rw [List.map_map]
    show (List.finRange n).map (fun endFin : Fin n => endFin.val) = List.range n
    exact List.map_coe_finRange_eq_range

/-- The (start, end) pairs of `allBetween` are unique (Nodup) and complete (every
`(s, e) : Fin n × Fin n` appears as some entry's pair). -/
theorem initializePaths_allBetween_pairs_facts
    (G : AdjMatrix n) {d : Nat} (hd : d < n) :
    let pathsAtDepth := ((initializePaths G).pathsOfLength.getD d #[]).toList
    let allBetween := pathsAtDepth.foldl
      (fun acc pf => acc ++ pf.pathsToVertex) []
    (allBetween.map (fun q => (q.startVertexIndex.val, q.endVertexIndex.val))).Nodup ∧
    (∀ s e : Fin n, ∃ q ∈ allBetween,
        q.startVertexIndex.val = s.val ∧ q.endVertexIndex.val = e.val) := by
  intro pathsAtDepth allBetween
  have h_allBetween_eq : allBetween = pathsAtDepth.flatMap (·.pathsToVertex) := by
    show pathsAtDepth.foldl (fun acc pf => acc ++ pf.pathsToVertex) [] = _
    rw [List.flatMap_eq_foldl]
  obtain ⟨_, h_starts_eq, _, _⟩ :=
    initializePaths_pathsAtDepth_structure G hd
  obtain ⟨h_inner_start_eq, h_inner_ends_eq⟩ :=
    initializePaths_pathsAtDepth_inner_structure G hd
  refine ⟨?_, ?_⟩
  · -- Nodup of (start, end) pairs.
    rw [h_allBetween_eq, List.map_flatMap]
    rw [List.nodup_flatMap]
    refine ⟨?_, ?_⟩
    · -- Each pf.pathsToVertex.map (s,e) is Nodup.
      intros pf h_pf_in
      -- Use Nodup of ends → Nodup of pairs via Pairwise.imp.
      have h_ends_nodup : (pf.pathsToVertex.map (·.endVertexIndex.val)).Nodup := by
        rw [h_inner_ends_eq pf h_pf_in]; exact List.nodup_range
      show (pf.pathsToVertex.map (fun q => (q.startVertexIndex.val, q.endVertexIndex.val))).Nodup
      rw [List.Nodup, List.pairwise_map]
      rw [List.Nodup, List.pairwise_map] at h_ends_nodup
      apply h_ends_nodup.imp
      intros q q' h_ends_ne h_pairs_eq
      apply h_ends_ne
      exact ((Prod.mk.injEq _ _ _ _).mp h_pairs_eq).2
    · -- Pairwise (Disjoint on f) pathsAtDepth where f = ·.pathsToVertex.map ...
      have h_starts_nodup : (pathsAtDepth.map (·.startVertexIndex.val)).Nodup := by
        rw [h_starts_eq]; exact List.nodup_range
      rw [List.Nodup, List.pairwise_map] at h_starts_nodup
      apply h_starts_nodup.imp_of_mem
      intros pf₁ pf₂ h_pf₁_in h_pf₂_in h_starts_ne
      show List.Disjoint (pf₁.pathsToVertex.map _) (pf₂.pathsToVertex.map _)
      intros pair h_pair_in₁ h_pair_in₂
      obtain ⟨q₁, h_q₁_in, h_q₁_eq⟩ := List.mem_map.mp h_pair_in₁
      obtain ⟨q₂, h_q₂_in, h_q₂_eq⟩ := List.mem_map.mp h_pair_in₂
      apply h_starts_ne
      have h_q₁_start : q₁.startVertexIndex = pf₁.startVertexIndex :=
        h_inner_start_eq pf₁ h_pf₁_in q₁ h_q₁_in
      have h_q₂_start : q₂.startVertexIndex = pf₂.startVertexIndex :=
        h_inner_start_eq pf₂ h_pf₂_in q₂ h_q₂_in
      have h_pair_eq : (q₁.startVertexIndex.val, q₁.endVertexIndex.val)
                     = (q₂.startVertexIndex.val, q₂.endVertexIndex.val) :=
        h_q₁_eq.trans h_q₂_eq.symm
      have h_starts_eq_q : q₁.startVertexIndex.val = q₂.startVertexIndex.val :=
        ((Prod.mk.injEq _ _ _ _).mp h_pair_eq).1
      rw [h_q₁_start, h_q₂_start] at h_starts_eq_q
      exact h_starts_eq_q
  · -- Completeness.
    intros s e
    -- Find a pf with start = s.
    have h_s_in_starts : s.val ∈ pathsAtDepth.map (·.startVertexIndex.val) := by
      rw [h_starts_eq]; exact List.mem_range.mpr s.isLt
    obtain ⟨pf, h_pf_in, h_pf_start⟩ := List.mem_map.mp h_s_in_starts
    -- Find a q with end = e in pf.pathsToVertex.
    have h_e_in_ends : e.val ∈ pf.pathsToVertex.map (·.endVertexIndex.val) := by
      rw [h_inner_ends_eq pf h_pf_in]; exact List.mem_range.mpr e.isLt
    obtain ⟨q, h_q_in, h_q_end⟩ := List.mem_map.mp h_e_in_ends
    have h_q_start : q.startVertexIndex = pf.startVertexIndex :=
      h_inner_start_eq pf h_pf_in q h_q_in
    refine ⟨q, ?_, ?_, h_q_end⟩
    · rw [h_allBetween_eq]
      exact List.mem_flatMap.mpr ⟨pf, h_pf_in, h_q_in⟩
    · rw [h_q_start]; exact h_pf_start


end Graph
