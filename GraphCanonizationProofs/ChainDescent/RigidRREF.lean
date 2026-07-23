import ChainDescent.KernelGauss

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

end RigidRREF
end ChainDescent
