import ChainDescent.DeepenLocated

/-!
# Workstream A — `orbKey`: the equivariant key force hooks to

**What force needs.** `Force.Key n := AdjMatrix n → Colouring n → Fin n → CostM (List Nat)`, and the
*only* `①` obligation on a force resolver is `Force.KeyEquivariant` — the key's **value** commutes with
relabelling. Everything else force offers (`force_canonizer`, `forceBy_narrows_of_key_ne`,
`forceBy_singleton_of_separating`, the whole `Composite`) then applies with no further hypothesis.

**What `DeepenLocated` delivered.** `not_amenable_deepest`: a consume failure hands us a *reachable*
node `ψ` that is simultaneously `Amenable` and carries a `RigidObstructionAt` at its branch cell. To
turn that into "force fires at `ψ`" we need a key that is (i) equivariant and (ii) non-constant on a
cell carrying ≥ 2 orbits. This file builds (i); (ii) is workstream B.

**The key.** `deepen`'s own greedy descent from `v`, run to its leaf, read off invariantly:

```
orbKey adj χ v := if AmenablePath adj χ n (step adj χ v)
                  then readKey adj (indivOne χ v) (leafOf adj n (step adj χ v)).col
                  else []            -- defer
```

**Why the guard, and why it is not a cheat.** The greedy descent breaks ties by *vertex index*
(`w :: _`), which does **not** commute with relabelling — this is the obstruction the whole `C3b`
track keeps meeting (`DeepenSupply`'s `G8` falsifier). `AmenablePath` is exactly the repair: it says
every level's chosen cell is a single stabiliser orbit, so a stabiliser element absorbs the pick
mismatch and the two runs stay related by an accumulating isomorphism. The guard is therefore
*necessary*, and it is **invariant** (`amenablePath_transport`, landed), so the `if` splits the
vertices into two relabelling-stable classes and `KeyEquivariant` survives it.

**§3 is the technical core** (`leafOf_transport_of_amenablePath`, plan item A2): a strengthening of the
landed `amenablePath_transport`, which already builds the accumulated relating isomorphism `τ * σ`
level by level but discards it. Here it is threaded into the conclusion, together with a `Refines`
invariant that lets the *parent* colouring travel along with the leaf — the extra component workstream
B needs to pin the individualized vertex (a leaf-adjacency read alone proves only that the two
*uncoloured* individualized graphs are isomorphic, which is not enough to conclude "same orbit").

**⚠ Non-vacuity.** The guard is not almost-always-false: measured (`scratchpad/probe_orbit_oracle.py`)
`Amenable` holds at **1197 of 1361** swept descent nodes over ten families, and **100** of those nodes
carry ≥ 2 orbits in the branch cell — i.e. are exactly the nodes where this key is both defined and
required to fire. See scoping doc §13.3/§15.1.

**⚠ Cost.** `orbKey` is `noncomputable` (the guard is a `Prop`; `Amenable` *is* decidable — `IsColAut`
has a `Decidable` instance — but the search is exponential, so making it computable would be honest,
not cheap). Per the plan (§14.5 E1/E2) that is a `②` question: `①` closes here regardless, and the
billed `keyCost` is where the guard's price belongs.
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (IsColAut)
open ChainDescent.Descend (transportColouring)

variable {n : Nat}

/-! ## 1. `Refines` — a colouring at least as fine as another

Needed because the relating isomorphism the induction accumulates is an automorphism of a *deep*
colouring, while the key also reads the *parent*. A permutation fixing a fine colouring fixes every
coarser one, which is what lets the parent component travel. -/

/-- `ψ` refines `φ`: same `ψ`-colour ⟹ same `φ`-colour. -/
def Refines (ψ φ : Colouring n) : Prop := ∀ x y : Fin n, ψ x = ψ y → φ x = φ y

theorem Refines.trans {ψ φ ω : Colouring n} (h₁ : Refines ψ φ) (h₂ : Refines φ ω) :
    Refines ψ ω := fun x y h => h₂ x y (h₁ x y h)

/-- The warm-refined individualization refines the colouring it was applied to. Direct from
`Refine.refineSplits_encodeFreeFast` (a refiner never *merges* classes). -/
theorem step_col_eq (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    (step adj χ v).col = Refine.warmRefineR adj (Descend.indivOne χ v) := by
  show (Refine.warmRefineVec adj (Descend.indivOne χ v)).col = _
  exact Refine.warmRefineVec_col_eq _ _

theorem refines_step (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    Refines (step adj χ v).col (Descend.indivOne χ v) := by
  intro x y h
  refine Refine.refineSplits_encodeFreeFast adj (Descend.indivOne χ v) x y ?_
  rw [Refine.refineV_encodeFreeFast, ← step_col_eq]
  exact h

/-- Individualization refines the colouring it splits. -/
theorem refines_indivOne (χ : Colouring n) (v : Fin n) :
    Refines (Descend.indivOne χ v) χ := by
  intro x y h
  unfold Descend.indivOne at h
  by_cases hx : x = v <;> by_cases hy : y = v
  · rw [hx, hy]
  · rw [if_pos hx, if_neg hy] at h; omega
  · rw [if_neg hx, if_pos hy] at h; omega
  · rw [if_neg hx, if_neg hy] at h; omega

/-- `Refines` transports. -/
theorem refines_transport (σ : Equiv.Perm (Fin n)) {ψ φ : Colouring n} (h : Refines ψ φ) :
    Refines (transportColouring σ ψ) (transportColouring σ φ) := by
  intro x y hxy
  exact h _ _ hxy

/-- **A colour-automorphism of a FINE colouring fixes every COARSER one.** This is what carries the
parent colouring through the accumulated isomorphism. -/
theorem transport_eq_of_isColAut_refines {adj : AdjMatrix n} {ψ φ : Colouring n}
    {τ : Equiv.Perm (Fin n)} (hτ : IsColAut adj ψ τ) (href : Refines ψ φ) :
    transportColouring τ φ = φ := by
  funext u
  show φ (τ.symm u) = φ u
  have h : φ (τ (τ.symm u)) = φ (τ.symm u) := href _ _ (hτ.2 (τ.symm u))
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-! ## 2. `leafOf` — the greedy descent's leaf

Mirrors `AmenablePath`'s recursion **exactly** (same `chooseIdK`, same `w :: _` pick), so the two line
up level for level in §3. Total (returns the current state when the fuel runs out or the descent
stops), which is all §3 needs; discreteness at fuel `n` is a workstream-B concern. -/

/-- The state deepen's greedy path reaches from `cur` in at most `fuel` levels. -/
def leafOf (adj : AdjMatrix n) : Nat → Refine.ColData n → Refine.ColData n
  | 0, cur => cur
  | fuel + 1, cur =>
      match chooseIdK (List.finRange n) cur.col with
        | none => cur
        | some cid =>
            match (List.finRange n).filter (fun v => cur.col v == cid) with
            | [] => cur
            | w :: _ => leafOf adj fuel (step adj cur.col w)

/-! ### Equation lemmas

⚠ Reduce `leafOf` **only** through these. Unfolding in place and then `cases`-ing on `chooseIdK`
descends into its internal `foldl` and exposes spurious goals — the recorded `deepen` match-reduction
trap (deepen doc §11). -/

theorem leafOf_zero (adj : AdjMatrix n) (cur : Refine.ColData n) : leafOf adj 0 cur = cur := rfl

theorem leafOf_succ_none (adj : AdjMatrix n) (fuel : Nat) (cur : Refine.ColData n)
    (h : chooseIdK (List.finRange n) cur.col = none) : leafOf adj (fuel + 1) cur = cur := by
  simp only [leafOf, h]

theorem leafOf_succ_nil (adj : AdjMatrix n) (fuel : Nat) (cur : Refine.ColData n) {cid : Nat}
    (h : chooseIdK (List.finRange n) cur.col = some cid)
    (hf : (List.finRange n).filter (fun v => cur.col v == cid) = []) :
    leafOf adj (fuel + 1) cur = cur := by
  simp only [leafOf, h, hf]

theorem leafOf_succ_cons (adj : AdjMatrix n) (fuel : Nat) (cur : Refine.ColData n)
    {cid : Nat} {w : Fin n} {rest : List (Fin n)}
    (h : chooseIdK (List.finRange n) cur.col = some cid)
    (hf : (List.finRange n).filter (fun v => cur.col v == cid) = w :: rest) :
    leafOf adj (fuel + 1) cur = leafOf adj fuel (step adj cur.col w) := by
  simp only [leafOf, h, hf]

/-! ## 3. ★★ A2 — THE LEAF TRANSPORTS ALONG AN `AmenablePath`

`amenablePath_transport` (landed) proves the *predicate* transports, and inside its proof it builds the
relating isomorphism `τ * σ` one level at a time — then throws it away. This is the same induction with
that accumulator kept, plus the `Refines`-carried parent component. -/

/-- **★★ THE CORE.** If the `a`-side descent is `AmenablePath` and the two states are related by `σ`,
then their **leaves** are related by an accumulated isomorphism `ρ` of the same graph — and `ρ` acts on
any colouring `φ` that the state refines exactly as `σ` does. -/
theorem leafOf_transport_of_amenablePath (adj : AdjMatrix n) (χp : Colouring n) :
    ∀ (fuel : Nat) (cur_a cur_b : Refine.ColData n) (σ : Equiv.Perm (Fin n)) (φ : Colouring n),
      cur_b.col = transportColouring σ cur_a.col →
      Refines cur_a.col φ →
      AmenablePath adj χp fuel cur_a →
      ∃ ρ : Equiv.Perm (Fin n),
        relabelAdj ρ adj = relabelAdj σ adj ∧
        transportColouring ρ φ = transportColouring σ φ ∧
        (leafOf (relabelAdj σ adj) fuel cur_b).col
          = transportColouring ρ (leafOf adj fuel cur_a).col := by
  intro fuel
  induction fuel with
  | zero =>
      intro cur_a cur_b σ φ hrel _ _
      exact ⟨σ, rfl, rfl, hrel⟩
  | succ fuel ih =>
      intro cur_a cur_b σ φ hrel href hA
      unfold AmenablePath at hA
      dsimp only at hA
      cases hco : chooseIdK (List.finRange n) cur_a.col with
      | none =>
          have hb : chooseIdK (List.finRange n) cur_b.col = none := by
            rw [hrel, chooseIdK_finRange_transport]; exact hco
          rw [leafOf_succ_none adj fuel cur_a hco, leafOf_succ_none _ fuel cur_b hb]
          exact ⟨σ, rfl, rfl, hrel⟩
      | some cid =>
          have hb : chooseIdK (List.finRange n) cur_b.col = some cid := by
            rw [hrel, chooseIdK_finRange_transport]; exact hco
          rw [hco] at hA
          dsimp only at hA
          obtain ⟨hcell_a, hArec⟩ := hA
          have hcell_b : CellSingleOrbit (relabelAdj σ adj) cur_b.col cid := by
            rw [hrel]; exact cellSingleOrbit_transport_iso σ hcell_a
          have hlen_a : 2 ≤ (cidCell cur_a.col cid).length := chooseIdK_mem _ _ hco
          have hlen_b : 2 ≤ (cidCell cur_b.col cid).length := by
            rw [hrel, cidCell_length_transport]; exact hlen_a
          cases hfl : (List.finRange n).filter (fun v => cur_a.col v == cid) with
          | nil =>
              exfalso
              have hnil : cidCell cur_a.col cid = [] := hfl
              rw [hnil] at hlen_a; simp at hlen_a
          | cons w_a rest_a =>
              rw [hfl] at hArec
              dsimp only at hArec
              cases hfb : (List.finRange n).filter (fun v => cur_b.col v == cid) with
              | nil =>
                  exfalso
                  have hnil : cidCell cur_b.col cid = [] := hfb
                  rw [hnil] at hlen_b; simp at hlen_b
              | cons w_b rest_b =>
                  -- the stabilizer element absorbing the index-pick mismatch (as in `joint`)
                  have hwa_mem : w_a ∈ cidCell cur_a.col cid := by
                    show w_a ∈ (List.finRange n).filter (fun v => cur_a.col v == cid)
                    rw [hfl]; exact List.mem_cons_self ..
                  have hwb_mem : w_b ∈ cidCell cur_b.col cid := by
                    show w_b ∈ (List.finRange n).filter (fun v => cur_b.col v == cid)
                    rw [hfb]; exact List.mem_cons_self ..
                  have hσwa : cur_b.col (σ w_a) = cid := by
                    have hm : σ w_a ∈ cidCell cur_b.col cid := by
                      rw [hrel]; exact mem_cidCell_transport_apply σ cur_a.col cid w_a hwa_mem
                    exact (mem_cidCell_iff _ _ _).mp hm
                  have hwbcid : cur_b.col w_b = cid := (mem_cidCell_iff _ _ _).mp hwb_mem
                  obtain ⟨τ, hτ, hτeq⟩ := hcell_b (σ w_a) w_b hσwa hwbcid
                  have hadj' : relabelAdj (τ * σ) adj = relabelAdj σ adj := by
                    rw [relabelAdj_mul]; exact hτ.relabel
                  have hcolb : transportColouring (τ * σ) cur_a.col = cur_b.col := by
                    rw [← transportColouring_comp, ← hrel]; exact hτ.transport
                  have hwab : (τ * σ) w_a = w_b := by
                    show τ (σ w_a) = w_b; exact hτeq
                  have hrel' : (step (relabelAdj σ adj) cur_b.col w_b).col
                      = transportColouring (τ * σ) ((step adj cur_a.col w_a).col) := by
                    have hst := step_transport (τ * σ) adj cur_a.col w_a
                    rw [hadj', hcolb, hwab] at hst
                    exact hst
                  -- the parent component: `τ` fixes `transportColouring σ φ`, which `cur_b.col` refines
                  have hrefb : Refines cur_b.col (transportColouring σ φ) := by
                    rw [hrel]; exact refines_transport σ href
                  have hτφ : transportColouring (τ * σ) φ = transportColouring σ φ := by
                    rw [← transportColouring_comp]
                    exact transport_eq_of_isColAut_refines hτ hrefb
                  -- the descent's own state still refines `φ`
                  have href' : Refines (step adj cur_a.col w_a).col φ :=
                    Refines.trans (Refines.trans (refines_step adj cur_a.col w_a)
                      (refines_indivOne cur_a.col w_a)) href
                  obtain ⟨ρ, hρadj, hρφ, hρleaf⟩ :=
                    ih (step adj cur_a.col w_a) (step (relabelAdj σ adj) cur_b.col w_b) (τ * σ) φ
                      hrel' href' hArec
                  rw [leafOf_succ_cons adj fuel cur_a hco hfl,
                      leafOf_succ_cons _ fuel cur_b hb hfb]
                  refine ⟨ρ, ?_, ?_, ?_⟩
                  · rw [hρadj]; exact hadj'
                  · rw [hρφ]; exact hτφ
                  · rw [hadj'] at hρleaf; exact hρleaf

/-! ## 4. The invariant read

An iso-invariant, complete-when-discrete encoding of a coloured graph: the adjacency summed over each
ordered pair of colour classes, plus the parent colouring summed over each class. Both are sums over
`σ`-images of the same finite sets, so both transport by `Finset.sum_map`. -/

/-- Colour classes transport by `σ`. -/
theorem filter_col_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (c : Nat) :
    Finset.univ.filter (fun u => transportColouring σ χ u = c)
      = (Finset.univ.filter (fun u => χ u = c)).map σ.toEmbedding := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.coe_toEmbedding]
  constructor
  · intro h
    exact ⟨σ.symm x, h, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    show χ (σ.symm (σ y)) = c
    simpa using hy

/-- Total adjacency between the `c`-class and the `d`-class. -/
def readAt (adj : AdjMatrix n) (χ : Colouring n) (c d : Nat) : Nat :=
  ∑ u ∈ Finset.univ.filter (fun u => χ u = c),
    ∑ w ∈ Finset.univ.filter (fun w => χ w = d), adj.adj u w

/-- Total parent colour over the `c`-class. -/
def readColAt (φ χ : Colouring n) (c : Nat) : Nat :=
  ∑ u ∈ Finset.univ.filter (fun u => χ u = c), φ u

theorem readAt_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (c d : Nat) :
    readAt (relabelAdj σ adj) (transportColouring σ χ) c d = readAt adj χ c d := by
  unfold readAt
  rw [filter_col_transport, filter_col_transport, Finset.sum_map]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  show adj.adj (σ.symm (σ u)) (σ.symm (σ w)) = adj.adj u w
  simp

theorem readColAt_transport (σ : Equiv.Perm (Fin n)) (φ χ : Colouring n) (c : Nat) :
    readColAt (transportColouring σ φ) (transportColouring σ χ) c = readColAt φ χ c := by
  unfold readColAt
  rw [filter_col_transport, Finset.sum_map]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  show φ (σ.symm (σ u)) = φ u
  simp

/-- **The read.** Adjacency between every ordered pair of colour classes, then the parent colour of
every class. When `χ` is discrete each class is a singleton, so this is the full relabelled adjacency
together with the relabelled parent colouring — the object the probe calls `cert`. -/
def readKey (adj : AdjMatrix n) (φ χ : Colouring n) : List Nat :=
  (List.range n).flatMap (fun c => (List.range n).map (fun d => readAt adj χ c d))
    ++ (List.range n).map (fun c => readColAt φ χ c)

theorem readKey_transport (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (φ χ : Colouring n) :
    readKey (relabelAdj σ adj) (transportColouring σ φ) (transportColouring σ χ)
      = readKey adj φ χ := by
  unfold readKey
  congr 1
  · refine List.flatMap_congr (fun c _ => ?_)
    refine List.map_congr_left (fun d _ => ?_)
    exact readAt_transport σ adj χ c d
  · refine List.map_congr_left (fun c _ => ?_)
    exact readColAt_transport σ φ χ c

/-! ## 5. The guard transports -/

/-- **The guard is relabelling-invariant, both directions.** Forward is `amenablePath_transport` at
`σ`; backward is the same at `σ⁻¹`, using `relabelAdj_one` / `transportColouring_one`. -/
theorem amenablePath_step_transport_iff (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n)
    (χ : Colouring n) (v : Fin n) :
    AmenablePath (relabelAdj σ adj) (transportColouring σ χ) n
        (step (relabelAdj σ adj) (transportColouring σ χ) (σ v))
      ↔ AmenablePath adj χ n (step adj χ v) := by
  constructor
  · intro h
    have hinv := amenablePath_transport (relabelAdj σ adj) (transportColouring σ χ) χ n
      (step (relabelAdj σ adj) (transportColouring σ χ) (σ v)) (step adj χ v) σ⁻¹ ?_ h
    · rwa [← relabelAdj_mul, inv_mul_cancel, relabelAdj_one] at hinv
    · rw [step_transport σ adj χ v, transportColouring_comp, inv_mul_cancel,
          transportColouring_one]
  · intro h
    exact amenablePath_transport adj χ (transportColouring σ χ) n (step adj χ v)
      (step (relabelAdj σ adj) (transportColouring σ χ) (σ v)) σ (step_transport σ adj χ v) h

/-! ## 6. `orbKey` and `①` -/

/-- The guard is a `Prop` about the *true* automorphism group. It IS decidable (`IsColAut` has a
`Decidable` instance and `Equiv.Perm (Fin n)` is a `Fintype`), but the honest instance is an `n!`
search, so the key is declared `noncomputable` here and the executable guard is left to `②` (plan
§14.5 E1/E2). Registering one instance keeps `orbKey` and `keyV_orbKey` on the *same* instance term,
which is what makes the projection lemma `rfl`. -/
noncomputable instance instDecidableAmenablePath (adj : AdjMatrix n) (χp : Colouring n)
    (fuel : Nat) (cur : Refine.ColData n) : Decidable (AmenablePath adj χp fuel cur) :=
  Classical.dec _

/-- **★★★ THE KEY.** Run `deepen`'s greedy descent from `v` to its leaf and read it invariantly —
guarded by `AmenablePath`, which is exactly the condition making that (index-picked!) descent
labelling-independent. Off the guard the key is constant, so force simply does not act there.

The cost is billed at `n⁴`: `≤ n` levels, each a warm refinement (`≤ n³`). -/
noncomputable def orbKey : Force.Key n := fun adj χ v =>
  (if AmenablePath adj χ n (step adj χ v)
     then readKey adj (Descend.indivOne χ v) (leafOf adj n (step adj χ v)).col
     else [],
   n * n * n * n)

@[simp] theorem keyV_orbKey (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    Force.keyV orbKey adj χ v =
      if AmenablePath adj χ n (step adj χ v)
        then readKey adj (Descend.indivOne χ v) (leafOf adj n (step adj χ v)).col
        else [] := rfl

/-- **★★★ `①` FOR THE FORCE ROUTE — `orbKey` IS EQUIVARIANT, with no hypothesis.**

Both halves of the `if` transport: the guard by `amenablePath_step_transport_iff`, and the value by
`leafOf_transport_of_amenablePath` — which supplies an isomorphism `ρ` relating the two leaves *and*
acting on the parent colouring exactly as `σ` does, so `readKey_transport` closes it at `ρ`.

Consequence: `Force.force_canonizer` and `Composite.composite_canonizer` apply to `forceBy orbKey`
with nothing further to discharge. -/
theorem keyEquivariant_orbKey : Force.KeyEquivariant (orbKey (n := n)) := by
  intro σ adj χ v
  rw [keyV_orbKey, keyV_orbKey]
  by_cases hA : AmenablePath adj χ n (step adj χ v)
  · rw [if_pos ((amenablePath_step_transport_iff σ adj χ v).mpr hA), if_pos hA]
    obtain ⟨ρ, hρadj, hρφ, hρleaf⟩ :=
      leafOf_transport_of_amenablePath adj χ n (step adj χ v)
        (step (relabelAdj σ adj) (transportColouring σ χ) (σ v)) σ (Descend.indivOne χ v)
        (step_transport σ adj χ v) (refines_step adj χ v) hA
    rw [hρleaf, ← hρadj, Descend.indivOne_transport, ← hρφ, readKey_transport]
  · rw [if_neg (fun h => hA ((amenablePath_step_transport_iff σ adj χ v).mp h)), if_neg hA]

end Deepen
end ChainDescent
