import ChainDescent.Select
import ChainDescent.SupplyTransport
import ChainDescent.OrbitPrune
import ChainDescent.PrunedSupply
import ChainDescent.HandledBridge
import ChainDescent.SupplyCost

/-!
# `SelectNode` — the FUSED selector instance `selNode` (increment 3 of the sel rewrite)

## What this is

The concrete resolver-aware node resolver (handoff §6.1 build-state block): at each non-discrete node it probes
**every** non-singleton cell with the mixed per-cell narrowing (force's `keepMin`, then consume's orbit
representatives from the node's ONE shared `verified` list), and commits to the **least colour whose cell narrows
to `≤ 1`**. `[]` — the flag — fires exactly at the **true mutual stall**: *no* cell is resolvable. This is the
flag semantics `Publication.lean` §1 names, replacing the guarded blind object's "the LEAST cell stalled".

## The three acceptance criteria (bound in this file)

1. **No strength increase** — proved, not measured: `descendS_selNode_val_of_guard` (the DOMINANCE theorem). If
   the least cell resolves, it is the least *resolvable* cell, so `selNode` reproduces the guarded blind object's
   step exactly — the fused object answers (with the same value) wherever the blind object answers.
2. **Exposure dependency** — behavioural witness in `Regression.lean` §8 (blind flags, fused answers): the force
   half already reaches non-least cells, no all-cells supply needed for the witness.
3. **No exponential** — `selNode_children_length_le_one`: fan-out `≤ 1` **by construction** (a cell is committed
   to only after it narrowed to `≤ 1`), so the descent is a single path of `≤ n + 1` nodes exactly as the guarded
   object's; the probe is billed additively per node in `selProbeCost` (all cells billed, cells partition `V`).

## The transport story (`①` for the fused object)

`NodeTransport` is discharged by the covering argument mirroring `Residue.coveringOfAt_guarded`, per cell:
- the **chosen colour transports as a value** (`selColour_transport`, mirror of `targetColour_transport`): colour
  values are canonical, and per-cell resolvability is a length that counts orbits meeting the per-cell forced set
  (`cellNarrow_length_transport`, mirror of `SupplyTransport.stallEquivariant_forceThenConsume`);
- within the chosen cell, the kept representative covers the per-cell forced set (`rep_mem_keepMin_cell`, mirror
  of `Composite.rep_mem_forcedSet`) and discards are value-equal via verified automorphisms
  (`branchValS_eq_of_isColAut`, the `descendS` mirror of `Consume.branchVal_eq_of_isColAut`).

Hypotheses: exactly the guarded object's — `KeyEquivariant key` + `SupplyEquivariant S` (NO new hypothesis
class), plus the ambient `RefineEquivariant`. The `SameOrbits` reduction transfers the capstone to pruned
supplies with no equivariance proof (`selNode_canonizer_of_sameOrbits`), keeping the canonizer-of-record path
(`prunedSupply d`) open.

⚠ **Runtime (trap #1):** every colouring this file stores is `(rf adj …).1` for the ambient refiner; at
`rf = Refine.encodeFreeFast` that is `(warmRefineVec …).col` — a closure over an already-forced `ColData`, the
same per-child shape `descend` has today. No `… → Colouring n` definition is introduced.
-/

namespace ChainDescent
namespace Select

open ChainDescent.CanonSpec (Labelled)
open ChainDescent.CostModel (CostM)
open ChainDescent.Descend
open ChainDescent.Force (Key keyV keyCost KeyEquivariant keepMin)
open ChainDescent.Consume (Supply verified rep gens supplyCost IsColAut)
open ChainDescent.SupplyTransport (SupplyEquivariant)
open ChainDescent.OrbitPrune (SameOrbits)

variable {n : Nat}

/-! ## 1. Cells, by colour — `branches` generalized from the least cell to any cell -/

/-- The cell of colour `c`, as a list (index order — same construction as `branches`' `some` case, so the two
coincide at the target colour: `branches_eq_cellList`). -/
def cellList (χ : Colouring n) (c : Nat) : List (Fin n) :=
  (List.finRange n).filter (fun v => χ v = c)

theorem mem_cellList_iff {χ : Colouring n} {c : Nat} (v : Fin n) :
    v ∈ cellList χ c ↔ χ v = c := by
  unfold cellList
  simp [List.mem_filter]

/-- At the target colour, the cell IS the branch list — the definitional bridge to the blind object. -/
theorem branches_eq_cellList {χ : Colouring n} {c : Nat} (h : targetColour χ = some c) :
    branches χ = cellList χ c := by
  unfold branches
  rw [h]
  rfl

theorem cellList_nodup (χ : Colouring n) (c : Nat) : (cellList χ c).Nodup :=
  (List.nodup_finRange n).filter _

/-- A non-singleton colour's cell is nonempty. -/
theorem cellList_ne_nil {χ : Colouring n} {c : Nat} (hc : c ∈ nonSingletonColours χ) :
    cellList χ c ≠ [] := by
  have hcard : 1 < (cellOf χ c).card := (Finset.mem_filter.mp hc).2
  have hpos : 0 < (cellOf χ c).card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  have hχv : χ v = c := (Finset.mem_filter.mp hv).2
  intro hnil
  have : v ∈ cellList χ c := (mem_cellList_iff v).mpr hχv
  rw [hnil] at this
  exact absurd this (List.not_mem_nil)

/-- Every member of a non-singleton cell has a same-coloured partner (mirror of
`exists_partner_of_mem_branches`, for an arbitrary non-singleton colour). -/
theorem exists_partner_of_mem_cellList {χ : Colouring n} {c : Nat}
    (hc : c ∈ nonSingletonColours χ) {v : Fin n} (hv : v ∈ cellList χ c) :
    ∃ u, u ≠ v ∧ χ u = χ v := by
  have hχv : χ v = c := (mem_cellList_iff v).mp hv
  have hcard : 1 < (cellOf χ c).card := (Finset.mem_filter.mp hc).2
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  have hχa : χ a = c := (Finset.mem_filter.mp ha).2
  have hχb : χ b = c := (Finset.mem_filter.mp hb).2
  by_cases hav : a = v
  · exact ⟨b, by rw [← hav]; exact fun hc' => hab hc'.symm, by rw [hχb, hχv]⟩
  · exact ⟨a, hav, by rw [hχa, hχv]⟩

/-- The cell of a fixed colour transports up to permutation (mirror of `branches_transport_perm` — colour VALUES
are canonical, so no colour translation appears). -/
theorem cellList_transport_perm (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (c : Nat) :
    (cellList (transportColouring σ χ) c).Perm ((cellList χ c).map σ) := by
  unfold cellList
  refine List.perm_of_nodup_nodup_toFinset_eq
    ((List.nodup_finRange n).filter _) (((List.nodup_finRange n).filter _).map σ.injective) ?_
  ext u
  simp only [List.mem_toFinset, List.mem_filter, List.mem_map, List.mem_finRange,
    transportColouring, true_and, decide_eq_true_eq]
  constructor
  · intro hu; exact ⟨σ.symm u, hu, by simp⟩
  · rintro ⟨v, hv, rfl⟩; simpa using hv

/-- The non-singleton colour set is literally invariant (the first half of `targetColour_transport`, exposed —
the fused selector filters this set, so it needs the set itself, not only its min). -/
theorem nonSingletonColours_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) :
    nonSingletonColours (transportColouring σ χ) = nonSingletonColours χ := by
  unfold nonSingletonColours
  rw [image_transport σ χ]
  apply Finset.filter_congr
  intro c _
  rw [cellOf_card_transport σ χ c]

/-! ## 2. Generic `keepMin` facts (the branches-specialized ones, re-proved at an arbitrary cell) -/

theorem keepMin_subset {key : Key n} {adj : AdjMatrix n} {χ : Colouring n} {B : List (Fin n)}
    {v : Fin n} (hv : v ∈ keepMin key adj χ B) : v ∈ B :=
  ((Force.mem_keepMin_iff v).mp hv).1

theorem keepMin_ne_nil {key : Key n} {adj : AdjMatrix n} {χ : Colouring n} {B : List (Fin n)}
    (hB : B ≠ []) : keepMin key adj χ B ≠ [] := by
  cases hk : Force.kmin? (B.map (keyV key adj χ)) with
  | none => rw [Force.keepMin_none hk]; exact hB
  | some m =>
      rw [Force.keepMin_some hk]
      obtain ⟨v, hv, hvm⟩ := List.mem_map.mp (Force.kmin?_mem _ hk)
      intro hnil
      have hmem : v ∈ B.filter (fun v => decide (keyV key adj χ v = m)) :=
        List.mem_filter.mpr ⟨hv, by simp [hvm]⟩
      rw [hnil] at hmem
      exact absurd hmem (List.not_mem_nil)

theorem keepMin_nodup_of_nodup {key : Key n} {adj : AdjMatrix n} {χ : Colouring n}
    {B : List (Fin n)} (hB : B.Nodup) : (keepMin key adj χ B).Nodup := by
  cases hk : Force.kmin? (B.map (keyV key adj χ)) with
  | none => rw [Force.keepMin_none hk]; exact hB
  | some m => rw [Force.keepMin_some hk]; exact hB.filter _

/-- `mem_keepMin_of_aut`, at an arbitrary base list: a colour-automorphism image of a kept vertex is kept,
provided it is in the base list at all. -/
theorem mem_keepMin_of_aut' {key : Key n} (hk : KeyEquivariant key) {adj : AdjMatrix n}
    {χ : Colouring n} {α : Equiv.Perm (Fin n)} (hadj : relabelAdj α adj = adj)
    (hχ : transportColouring α χ = χ) {B : List (Fin n)} {v : Fin n}
    (hv : v ∈ keepMin key adj χ B) (hαv : α v ∈ B) : α v ∈ keepMin key adj χ B := by
  obtain ⟨_, hmin⟩ := (Force.mem_keepMin_iff v).mp hv
  refine (Force.mem_keepMin_iff _).mpr ⟨hαv, fun w hw => ?_⟩
  rw [Force.keyV_aut_invariant hk hadj hχ v]
  exact hmin w hw

/-- `keepMin` transports over any permutation-related pair of base lists (the generic-`B` core of
`Force.narrowEquivariant_forceBy`, which is this lemma at `B = branches χ`). -/
theorem keepMin_transport_perm {key : Key n} (hk : KeyEquivariant key) (σ : Equiv.Perm (Fin n))
    (adj : AdjMatrix n) (χ : Colouring n) {B' B : List (Fin n)} (hbr : B'.Perm (B.map σ)) :
    (keepMin key (relabelAdj σ adj) (transportColouring σ χ) B').Perm
      ((keepMin key adj χ B).map σ) := by
  have hkeys : ∀ v : Fin n,
      keyV key (relabelAdj σ adj) (transportColouring σ χ) (σ v) = keyV key adj χ v := hk σ adj χ
  have hmap : (B'.map (keyV key (relabelAdj σ adj) (transportColouring σ χ))).Perm
      (B.map (keyV key adj χ)) := by
    refine (hbr.map _).trans ?_
    rw [List.map_map]
    exact List.Perm.of_eq (List.map_congr_left (fun v _ => hkeys v))
  have hmin : Force.kmin? (B'.map (keyV key (relabelAdj σ adj) (transportColouring σ χ)))
      = Force.kmin? (B.map (keyV key adj χ)) :=
    Force.kmin?_congr_mem (fun x => hmap.mem_iff)
  cases hk0 : Force.kmin? (B.map (keyV key adj χ)) with
  | none =>
      rw [Force.keepMin_none (hmin.trans hk0), Force.keepMin_none hk0]
      exact hbr
  | some m =>
      rw [Force.keepMin_some (hmin.trans hk0), Force.keepMin_some hk0]
      refine (hbr.filter _).trans ?_
      rw [Force.filter_map_comm]
      refine List.Perm.of_eq (congrArg (List.map σ) ?_)
      apply List.filter_congr
      intro v _
      simp only [hkeys v]

/-! ## 3. The per-cell mixed narrowing -/

/-- The per-cell mixed narrowing against an ALREADY-COMPUTED verified list `V` — the form the runnable resolver
shares across the per-node probe (⚠ trap #2: phrasing this on `S` directly re-evaluates the supply once per
probed cell — measured ~10× per node at `n = 14`). -/
def cellNarrowV (key : Key n) (V : List (Equiv.Perm (Fin n))) (adj : AdjMatrix n) (χ : Colouring n)
    (c : Nat) : List (Fin n) :=
  ((keepMin key adj χ (cellList χ c)).map (rep V)).dedup

/-- **The mixed narrowing of the cell of colour `c`**: force's argmin over the cell, then one orbit
representative per verified-automorphism orbit. At `c = targetColour χ` this IS `narrow (forceThenConsume key S)`
(`cellNarrow_targetColour`). Note the `verified` list is per-NODE, not per-cell — the fused resolver computes it
once and probes every cell against it (`cellNarrowV`). -/
def cellNarrow (key : Key n) (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) :
    List (Fin n) :=
  cellNarrowV key (verified S adj χ) adj χ c

/-- At the target colour, the per-cell narrowing is the blind mixed resolver's narrowing. -/
theorem cellNarrow_targetColour {key : Key n} {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {c : Nat} (h : targetColour χ = some c) :
    cellNarrow key S adj χ c = narrow (Composite.forceThenConsume key S) adj χ := by
  rw [Composite.narrow_forceThenConsume]
  unfold cellNarrow cellNarrowV Composite.forcedSet
  rw [branches_eq_cellList h]

/-- An orbit representative stays in its vertex's cell (verified automorphisms preserve colour). -/
theorem rep_mem_cellList {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n} {c : Nat} {b : Fin n}
    (hb : b ∈ cellList χ c) : rep (verified S adj χ) b ∈ cellList χ c := by
  have hreach := Consume.reach_rep (G := verified S adj χ)
    (fun _ hg => Consume.isColAut_of_mem_verified hg) b
  rw [mem_cellList_iff] at hb ⊢
  rw [hreach.colour, hb]

/-- **The per-cell forced set is a union of orbits** (mirror of `Composite.rep_mem_forcedSet`): an orbit
representative of a kept vertex is itself kept, so consume-inside-the-cell never escapes the per-cell argmin. -/
theorem rep_mem_keepMin_cell {key : Key n} (hk : KeyEquivariant key) (S : Supply n)
    (adj : AdjMatrix n) (χ : Colouring n) {c : Nat} {b : Fin n}
    (hb : b ∈ keepMin key adj χ (cellList χ c)) :
    rep (verified S adj χ) b ∈ keepMin key adj χ (cellList χ c) := by
  obtain ⟨α, hα, hαb⟩ := Consume.reach_rep (adj := adj) (χ := χ)
    (fun _ hg => Consume.isColAut_of_mem_verified hg) b
  have hrepB : rep (verified S adj χ) b ∈ cellList χ c := rep_mem_cellList (keepMin_subset hb)
  have := mem_keepMin_of_aut' hk hα.relabel hα.transport hb (by rw [hαb]; exact hrepB)
  rwa [hαb] at this

theorem cellNarrow_subset {key : Key n} {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {c : Nat} {v : Fin n} (hv : v ∈ cellNarrow key S adj χ c) : v ∈ cellList χ c := by
  obtain ⟨b, hb, hbv⟩ := List.mem_map.mp (List.mem_dedup.mp hv)
  exact hbv ▸ rep_mem_cellList (keepMin_subset hb)

/-- A non-singleton cell's narrowing is nonempty — so "narrowed to `≤ 1`" means "narrowed to exactly one", and a
committed cell always yields a child. -/
theorem cellNarrow_ne_nil {key : Key n} {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {c : Nat} (hc : c ∈ nonSingletonColours χ) : cellNarrow key S adj χ c ≠ [] := by
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _
    (keepMin_ne_nil (key := key) (adj := adj) (cellList_ne_nil hc))
  intro hnil
  have : rep (verified S adj χ) b ∈ cellNarrow key S adj χ c :=
    List.mem_dedup.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)
  rw [hnil] at this
  exact absurd this (List.not_mem_nil)

/-! ## 4. The selector and the fused node resolver -/

/-- The selector against an already-computed verified list (the shared-probe form). -/
def selColourV (key : Key n) (V : List (Equiv.Perm (Fin n))) (adj : AdjMatrix n) (χ : Colouring n) :
    Option Nat :=
  ((nonSingletonColours χ).filter
    (fun c => (cellNarrowV key V adj χ c).length ≤ 1)).min

/-- **The selected colour: least colour whose cell the mixed narrowing collapses to `≤ 1`.** `none` = the TRUE
MUTUAL STALL — no cell is resolvable by either move. (Design pin: "makes progress" = narrows to `≤ 1`, NOT
"narrows strictly" — a cell cut 5→2 still stalls, keeping poly AND flag.) -/
def selColour (key : Key n) (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) : Option Nat :=
  selColourV key (verified S adj χ) adj χ

/-- The reasoning-side unfolding (definitionally true — the `V`-sharing is runtime-only). -/
theorem selColour_def (key : Key n) (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) :
    selColour key S adj χ
      = ((nonSingletonColours χ).filter
          (fun c => (cellNarrow key S adj χ c).length ≤ 1)).min := rfl

theorem selColour_spec {key : Key n} {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (h : selColour key S adj χ = some c) :
    c ∈ nonSingletonColours χ ∧ (cellNarrow key S adj χ c).length ≤ 1 := by
  rw [selColour_def] at h
  have hmem := Finset.mem_of_min h
  have := Finset.mem_filter.mp hmem
  exact ⟨this.1, by simpa using this.2⟩

/-- The flag fires only at a true mutual stall: NO non-singleton cell narrows to `≤ 1`. -/
theorem selColour_none {key : Key n} {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    (h : selColour key S adj χ = none) :
    ∀ c ∈ nonSingletonColours χ, ¬ (cellNarrow key S adj χ c).length ≤ 1 := by
  intro c hc hlen
  have hmem : c ∈ (nonSingletonColours χ).filter
      (fun c => (cellNarrow key S adj χ c).length ≤ 1) :=
    Finset.mem_filter.mpr ⟨hc, by simpa using hlen⟩
  rw [selColour_def] at h
  have hemp : (nonSingletonColours χ).filter
      (fun c => (cellNarrow key S adj χ c).length ≤ 1) = ∅ := Finset.min_eq_top.mp h
  rw [hemp] at hmem
  exact absurd hmem (Finset.notMem_empty c)

/-- **★ THE DOMINANCE HOOK — if the least cell resolves, it is the selected cell.** The selected colour is the
min over a SUBSET of the non-singleton colours; when that subset contains the overall min (`targetColour`), the
two mins coincide. This is what makes "no strength increase" a theorem: at the same resolver strength, "some cell
narrows to ≤ 1" is implied by "the least cell narrows to ≤ 1", never the reverse. -/
theorem selColour_of_target_resolvable {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    {χ : Colouring n} {c : Nat} (h : targetColour χ = some c)
    (hres : (cellNarrow key S adj χ c).length ≤ 1) : selColour key S adj χ = some c := by
  have hcmem : c ∈ nonSingletonColours χ := Finset.mem_of_min h
  have hcfil : c ∈ (nonSingletonColours χ).filter
      (fun c => (cellNarrow key S adj χ c).length ≤ 1) :=
    Finset.mem_filter.mpr ⟨hcmem, by simpa using hres⟩
  -- the filtered min is ≤ c (c is a member) and ≥ c (every member is in the full set, whose min is c)
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty ⟨c, hcfil⟩
  have hmc : m ≤ c := Finset.min_le_of_eq hcfil hm
  have hcm : c ≤ m := by
    have hmmem : m ∈ nonSingletonColours χ := (Finset.mem_filter.mp (Finset.mem_of_min hm)).1
    exact Finset.min_le_of_eq hmmem h
  rw [selColour_def, hm, Nat.le_antisymm hmc hcm]
  rfl

/-- The non-singleton colours as a **computable** list (`Finset.toList` is noncomputable; the probe's cost
expression must run under `#eval`). Same membership as `nonSingletonColours` (`mem_nsColours_iff`). -/
def nsColours (χ : Colouring n) : List Nat :=
  (((List.finRange n).map χ).dedup).filter (fun c => 1 < (cellList χ c).length)

/-- A cell's list length is its `Finset` card — the bridge between the computable per-cell objects and the
`nonSingletonColours` predicate. -/
theorem cellList_length_eq_card (χ : Colouring n) (c : Nat) :
    (cellList χ c).length = (cellOf χ c).card := by
  rw [← List.toFinset_card_of_nodup (cellList_nodup χ c)]
  congr 1
  ext v
  simp [mem_cellList_iff, cellOf]

theorem mem_nsColours_iff (χ : Colouring n) (c : Nat) :
    c ∈ nsColours χ ↔ c ∈ nonSingletonColours χ := by
  unfold nsColours nonSingletonColours
  simp only [List.mem_filter, List.mem_dedup, List.mem_map, List.mem_finRange, true_and,
    Finset.mem_filter, Finset.mem_image, Finset.mem_univ, decide_eq_true_eq,
    cellList_length_eq_card]

/-- The probe's bill: the supply once per node, one verification per candidate, then per cell one key evaluation
per member plus the scan plus the orbit BFS per member. Cells partition the vertex set, so the per-cell sums total
what ONE cell of size `n` would cost — the same shape `consume`/`forceBy` already bill (`SupplyCost` bounds it). -/
def selProbeCost (key : Key n) (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) : Nat :=
  supplyCost S adj χ + (gens S adj χ).length * (n * n)
    + ((nsColours χ).map (fun c =>
        ((cellList χ c).map (keyCost key adj χ)).sum + n * n
          + (cellList χ c).length * ((verified S adj χ).length * (n * n) + n * n))).sum

/-- The node step against an already-computed verified list and probe bill (the shared core). -/
def selNodeCore (rf : Refiner n) (key : Key n) (V : List (Equiv.Perm (Fin n))) (pc : Nat)
    (adj : AdjMatrix n) (χ : Colouring n) : CostM (List (Fin n × Colouring n)) :=
  match selColourV key V adj χ with
  | none => ([], pc)
  | some c =>
      let kept := cellNarrowV key V adj χ c
      (kept.map (fun v => (v, refineV rf adj (indivOne χ v))),
       pc + (kept.map (fun v => (rf adj (indivOne χ v)).2)).sum)

/-- **★ THE FUSED NODE RESOLVER.** Probe all cells, commit to the least resolvable one, hand each kept child its
refined colouring (the §6.4 hand-forward — the probe's refinement work IS the children's). `[] = flag` = the true
mutual stall.

⚠ Runtime shape (trap #2): the supply is evaluated **once** per node (`sv`), the verified list once, and every
per-cell probe reads the shared `V` — phrasing the probe on `S` directly re-evaluates the supply per cell
(measured ~10× per node at `n = 14`). The reasoning-side form is `selNode_eq`. -/
def selNode (rf : Refiner n) (key : Key n) (S : Supply n) : NodeRes n := fun adj χ =>
  let sv := S adj χ
  let V := sv.1.filter (fun g => decide (Consume.IsColAut adj χ g))
  selNodeCore rf key V
    (sv.2 + sv.1.length * (n * n)
      + ((nsColours χ).map (fun c =>
          ((cellList χ c).map (keyCost key adj χ)).sum + n * n
            + (cellList χ c).length * (V.length * (n * n) + n * n))).sum) adj χ

/-- The reasoning-side unfolding (definitionally true — the sharing is runtime-only). -/
theorem selNode_eq (rf : Refiner n) (key : Key n) (S : Supply n) (adj : AdjMatrix n)
    (χ : Colouring n) :
    selNode rf key S adj χ
      = selNodeCore rf key (verified S adj χ) (selProbeCost key S adj χ) adj χ := rfl

/-- **The RUNNABLE fused resolver** (trap #1, measured in the wild): definitionally equal to
`selNode (Refine.encodeFreeFast)` (`selNodeFast_eq` is `rfl`), but the children's colourings are built through
`Refine.ColData`, so each child's refinement is FORCED ONCE. The generic `refineV rf …` in `selNode` compiles as
a partial application whose body re-runs the refinement on EVERY colour lookup — measured ≈ 30 ms per lookup at
`n = 14`, which made the fused descent's probe (≈ `n²` lookups per node) hang while the blind object (few lookups)
merely crawled. Same cure as `encodeFreeFast` vs `encodeFree`: the expensive computation sits in a strict
ARGUMENT (`warmRefineVec`, forced once), never in a re-run closure body. -/
def selNodeFast (key : Key n) (S : Supply n) : NodeRes n := fun adj χ =>
  let sv := S adj χ
  let V := sv.1.filter (fun g => decide (Consume.IsColAut adj χ g))
  match selColourV key V adj χ with
  | none =>
      ([], sv.2 + sv.1.length * (n * n)
        + ((nsColours χ).map (fun c =>
            ((cellList χ c).map (keyCost key adj χ)).sum + n * n
              + (cellList χ c).length * (V.length * (n * n) + n * n))).sum)
  | some c =>
      let kept := cellNarrowV key V adj χ c
      (kept.map (fun v => (v, (Refine.warmRefineVec adj (indivOne χ v)).col)),
       (sv.2 + sv.1.length * (n * n)
         + ((nsColours χ).map (fun c =>
             ((cellList χ c).map (keyCost key adj χ)).sum + n * n
               + (cellList χ c).length * (V.length * (n * n) + n * n))).sum)
         + (kept.map (fun _ => CostModel.WarmRefine.warmRefineCost n)).sum)

/-- The runnable resolver IS the reasoned-about fused resolver at the runnable refiner — definitionally. -/
theorem selNodeFast_eq (key : Key n) (S : Supply n) :
    selNodeFast key S = selNode (Refine.encodeFreeFast (n := n)) key S := rfl

/-- The runnable top-level object (root colouring materialised once too). -/
def canonFormFastS? (key : Key n) (S : Supply n) (adj : AdjMatrix n) : Option (Labelled n) :=
  (descendS (selNodeFast key S) adj n ((Refine.warmRefineVec adj (fun _ => 0)).col)).1

/-- The runnable top-level object IS the reasoned-about one — definitionally, so every capstone
(`selNode_canonizer` etc.) speaks about it verbatim. -/
theorem canonFormFastS?_eq (key : Key n) (S : Supply n) :
    canonFormFastS? key S
      = canonFormS? (Refine.encodeFreeFast (n := n))
          (selNode (Refine.encodeFreeFast (n := n)) key S) := rfl

theorem selNode_children_none {rf : Refiner n} {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    {χ : Colouring n} (h : selColour key S adj χ = none) : (selNode rf key S adj χ).1 = [] := by
  rw [selNode_eq]
  unfold selNodeCore
  unfold selColour at h
  rw [h]

theorem selNode_children_some {rf : Refiner n} {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    {χ : Colouring n} {c : Nat} (h : selColour key S adj χ = some c) :
    (selNode rf key S adj χ).1
      = (cellNarrow key S adj χ c).map (fun v => (v, refineV rf adj (indivOne χ v))) := by
  rw [selNode_eq]
  unfold selNodeCore
  unfold selColour at h
  rw [h]
  rfl

/-! ## 5. The two structural obligations: fan-out ≤ 1, and properness -/

/-- **★ NO EXPONENTIAL, BY CONSTRUCTION** (acceptance criterion 3): the fused resolver emits at most ONE child —
it commits only to a cell already narrowed to `≤ 1`. The descent under `selNode` is a single path, unconditionally
— `Stall.guard`'s job is absorbed into the instance. -/
theorem selNode_children_length_le_one (rf : Refiner n) (key : Key n) (S : Supply n)
    (adj : AdjMatrix n) (χ : Colouring n) : (selNode rf key S adj χ).1.length ≤ 1 := by
  cases h : selColour key S adj χ with
  | none => rw [selNode_children_none h]; simp
  | some c =>
      rw [selNode_children_some h, List.length_map]
      exact (selColour_spec h).2

/-- The committed cell yields exactly one child (nonempty + `≤ 1`). -/
theorem selNode_children_length_one {rf : Refiner n} {key : Key n} {S : Supply n}
    {adj : AdjMatrix n} {χ : Colouring n} {c : Nat} (h : selColour key S adj χ = some c) :
    (selNode rf key S adj χ).1.length = 1 := by
  rw [selNode_children_some h, List.length_map]
  have h1 := (selColour_spec h).2
  have h0 : cellNarrow key S adj χ c ≠ [] := cellNarrow_ne_nil (selColour_spec h).1
  have := List.length_pos_of_ne_nil h0
  omega

/-- **`NodeProper`, discharged for the fused instance**: every child individualizes a vertex with a same-coloured
partner (the committed colour is non-singleton) and is handed exactly its refined colouring (definitionally). -/
theorem nodeProper_selNode (rf : Refiner n) (key : Key n) (S : Supply n) :
    NodeProper rf (selNode rf key S) := by
  intro adj χ vc hvc
  cases h : selColour key S adj χ with
  | none => rw [selNode_children_none h] at hvc; exact absurd hvc (List.not_mem_nil)
  | some c =>
      rw [selNode_children_some h] at hvc
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hvc
      exact ⟨exists_partner_of_mem_cellList (selColour_spec h).1 (cellNarrow_subset hv), rfl⟩

/-! ## 6. Transport — `NodeTransport` for the fused instance (the covering mirror)

The proof never transports `rep` (it cannot — the representative pick is deliberately non-equivariant). Per cell
it counts orbits (`cellNarrow_length_transport`), so resolvability — and hence the CHOSEN COLOUR — transports as
a value; within the chosen cell the covering argument of `Residue.coveringOfAt_guarded` applies verbatim, one
cell over. -/

/-- **Per-cell mirror of `SupplyTransport.stallEquivariant_forceThenConsume`**: the per-cell narrowing's length
counts orbits meeting the per-cell forced set, and both the orbit partition and the forced set transport. -/
theorem cellNarrow_length_transport {key : Key n} (hk : KeyEquivariant key) {S : Supply n}
    (hS : SupplyEquivariant S) (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (c : Nat) :
    (cellNarrow key S (relabelAdj σ adj) (transportColouring σ χ) c).length
      = (cellNarrow key S adj χ c).length := by
  unfold cellNarrow cellNarrowV
  have hmemG' : ∀ g, g ∈ verified S (relabelAdj σ adj) (transportColouring σ χ) ↔
      ∃ h ∈ verified S adj χ, g = σ * h * σ⁻¹ := fun g => hS σ adj χ g
  have hperm : (keepMin key (relabelAdj σ adj) (transportColouring σ χ)
      (cellList (transportColouring σ χ) c)).Perm
      ((keepMin key adj χ (cellList χ c)).map σ) :=
    keepMin_transport_perm hk σ adj χ (cellList_transport_perm σ χ c)
  have hFin : (keepMin key (relabelAdj σ adj) (transportColouring σ χ)
      (cellList (transportColouring σ χ) c)).toFinset
      = (keepMin key adj χ (cellList χ c)).toFinset.image σ := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_image]
    rw [hperm.mem_iff]
    simp [List.mem_map]
  rw [SupplyTransport.dedup_map_length_eq_card_image,
    SupplyTransport.dedup_map_length_eq_card_image, hFin, Finset.image_image]
  refine SupplyTransport.card_image_congr_of_iff ?_
  intro a _ b _
  show rep (verified S (relabelAdj σ adj) (transportColouring σ χ)) (σ a)
      = rep (verified S (relabelAdj σ adj) (transportColouring σ χ)) (σ b)
    ↔ rep (verified S adj χ) a = rep (verified S adj χ) b
  rw [Consume.rep_eq_iff_wordReach, Consume.rep_eq_iff_wordReach]
  exact SupplyTransport.wordReach_conj_iff hmemG'

/-- **★ THE CHOSEN COLOUR TRANSPORTS AS A VALUE** (mirror of `targetColour_transport`, with the resolvability
conjunct riding on `cellNarrow_length_transport`). This is why choosing a CELL is canonical while choosing a
within-cell vertex is not: colour values are invariant, the vertex indices are not. -/
theorem selColour_transport {key : Key n} (hk : KeyEquivariant key) {S : Supply n}
    (hS : SupplyEquivariant S) (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) :
    selColour key S (relabelAdj σ adj) (transportColouring σ χ) = selColour key S adj χ := by
  rw [selColour_def, selColour_def]
  rw [nonSingletonColours_transport σ χ]
  congr 1
  apply Finset.filter_congr
  intro c _
  rw [cellNarrow_length_transport hk hS σ adj χ c]

/-- Per-branch value transport for the generalized descent (mirror of `Descend.branchVal_transport`). -/
theorem branchValS_transport {rf : Refiner n} {N : NodeRes n} (hre : RefineEquivariant rf)
    {fuel : Nat} (ih : NodeTransportAt N fuel) (adj : AdjMatrix n) (σ : Equiv.Perm (Fin n))
    (χ : Colouring n) (v : Fin n) :
    (descendS N (relabelAdj σ adj) fuel
        (refineV rf (relabelAdj σ adj) (indivOne (transportColouring σ χ) (σ v)))).1
      = (descendS N adj fuel (refineV rf adj (indivOne χ v))).1 := by
  rw [indivOne_transport σ χ v, hre σ adj (indivOne χ v)]
  exact ih adj σ (refineV rf adj (indivOne χ v))

/-- **The covering witness at the `descendS` level** (mirror of `Consume.branchVal_eq_of_isColAut`): a verified
automorphism makes two branches value-equal — `branchValS_transport` at `σ = α` degenerates to an equality on the
same graph. -/
theorem branchValS_eq_of_isColAut {rf : Refiner n} {N : NodeRes n} (hre : RefineEquivariant rf)
    {fuel : Nat} (ih : NodeTransportAt N fuel) (adj : AdjMatrix n) (χ : Colouring n)
    {α : Equiv.Perm (Fin n)} (hα : IsColAut adj χ α) (v : Fin n) :
    (descendS N adj fuel (refineV rf adj (indivOne χ (α v)))).1
      = (descendS N adj fuel (refineV rf adj (indivOne χ v))).1 := by
  have h := branchValS_transport hre ih adj α χ v
  rw [hα.relabel, hα.transport] at h
  exact h

/-- **The per-cell covering step** (mirror of the un-stalled branch of `Residue.coveringOfAt_guarded`): for any
value function constant along verified-automorphism moves, the aggregate over the kept representatives equals the
aggregate over the per-cell forced set — consume's discards inside the cell are redundant. -/
theorem aggregate_cellNarrow_eq {key : Key n} (hk : KeyEquivariant key) (S : Supply n)
    (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) {f : Fin n → Option (Labelled n)}
    (hval : ∀ b : Fin n, f (rep (verified S adj χ) b) = f b) :
    aggregate ((cellNarrow key S adj χ c).map f)
      = aggregate ((keepMin key adj χ (cellList χ c)).map f) := by
  refine aggregate_congr_mem ?_
  intro x
  unfold cellNarrow cellNarrowV
  constructor
  · intro hx
    obtain ⟨v, hv, hvx⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, hbv⟩ := List.mem_map.mp (List.mem_dedup.mp hv)
    exact List.mem_map.mpr ⟨v, hbv ▸ rep_mem_keepMin_cell hk S adj χ hb, hvx⟩
  · intro hx
    obtain ⟨b, hb, hbx⟩ := List.mem_map.mp hx
    refine List.mem_map.mpr ⟨rep (verified S adj χ) b, ?_, ?_⟩
    · exact List.mem_dedup.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)
    · rw [hval b]; exact hbx

/-- **★★★ THE FUSED INSTANCE MEETS THE NODE CONTRACT** — from exactly the guarded blind object's hypotheses
(`KeyEquivariant` + `SupplyEquivariant`; NO new hypothesis class). Chosen colour transports
(`selColour_transport`); within the chosen cell, covering on each side down to the per-cell forced set, which
transports as a permutation with value-equal entries. -/
theorem nodeTransport_selNode {rf : Refiner n} (hre : RefineEquivariant rf) {key : Key n}
    (hk : KeyEquivariant key) {S : Supply n} (hS : SupplyEquivariant S) :
    NodeTransport (selNode rf key S) := by
  intro fuel ih adj σ χ _hd
  cases hsel : selColour key S adj χ with
  | none =>
      rw [selNode_children_none hsel,
        selNode_children_none (by rw [selColour_transport hk hS σ adj χ]; exact hsel)]
      rfl
  | some c =>
      have hsel' : selColour key S (relabelAdj σ adj) (transportColouring σ χ) = some c := by
        rw [selColour_transport hk hS σ adj χ]; exact hsel
      rw [selNode_children_some hsel, selNode_children_some hsel', List.map_map, List.map_map]
      simp only [Function.comp_def]
      have hval : ∀ b : Fin n,
          (descendS (selNode rf key S) adj fuel
              (refineV rf adj (indivOne χ (rep (verified S adj χ) b)))).1
            = (descendS (selNode rf key S) adj fuel (refineV rf adj (indivOne χ b))).1 := by
        intro b
        obtain ⟨α, hα, hαb⟩ := Consume.reach_rep (G := verified S adj χ)
          (fun _ hg => Consume.isColAut_of_mem_verified hg) b
        rw [← hαb]
        exact branchValS_eq_of_isColAut hre ih adj χ hα b
      have hval' : ∀ b : Fin n,
          (descendS (selNode rf key S) (relabelAdj σ adj) fuel
              (refineV rf (relabelAdj σ adj) (indivOne (transportColouring σ χ)
                (rep (verified S (relabelAdj σ adj) (transportColouring σ χ)) b)))).1
            = (descendS (selNode rf key S) (relabelAdj σ adj) fuel
              (refineV rf (relabelAdj σ adj) (indivOne (transportColouring σ χ) b))).1 := by
        intro b
        obtain ⟨α, hα, hαb⟩ := Consume.reach_rep
          (G := verified S (relabelAdj σ adj) (transportColouring σ χ))
          (fun _ hg => Consume.isColAut_of_mem_verified hg) b
        rw [← hαb]
        exact branchValS_eq_of_isColAut hre ih (relabelAdj σ adj) (transportColouring σ χ) hα b
      refine (aggregate_cellNarrow_eq hk S (relabelAdj σ adj) (transportColouring σ χ) c
          (f := fun v => (descendS (selNode rf key S) (relabelAdj σ adj) fuel
            (refineV rf (relabelAdj σ adj) (indivOne (transportColouring σ χ) v))).1)
          hval').trans
        (Eq.trans ?_ (aggregate_cellNarrow_eq hk S adj χ c
          (f := fun v => (descendS (selNode rf key S) adj fuel
            (refineV rf adj (indivOne χ v))).1) hval).symm)
      refine aggregate_perm
        (((keepMin_transport_perm hk σ adj χ (cellList_transport_perm σ χ c)).map _).trans ?_)
      rw [List.map_map]
      exact List.Perm.of_eq
        (List.map_congr_left (fun v _ => branchValS_transport hre ih adj σ χ v))

/-! ## 7. The capstone, the `SameOrbits` transfer, and the DOMINANCE theorem -/

/-- **★★★ THE FUSED CANONIZER** — `①a`/`①b`/`①c` for the resolver-aware selector object, from exactly the
hypotheses the guarded blind object carries. The flag this object emits is the TRUE MUTUAL STALL
(`selNode_stall_iff`) — the flag semantics `Publication.lean` §1 names. -/
theorem selNode_canonizer {key : Key n} (hk : KeyEquivariant key) {S : Supply n}
    (hS : SupplyEquivariant S) :
    CanonSpec.IsCanonicalFormOpt
      (canonFormS? (Refine.encodeFreeFast (n := n))
        (selNode (Refine.encodeFreeFast (n := n)) key S)) :=
  isCanonicalFormOptS_canonFormS? Refine.refineEquivariant_encodeFreeFast
    (nodeTransport_selNode Refine.refineEquivariant_encodeFreeFast hk hS)

/-- The first CONCRETE fused canonizer — every parameter a named, built object; no hypothesis carried. -/
theorem selNode_match_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (canonFormS? (Refine.encodeFreeFast (n := n))
        (selNode (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (Consume.matchSupply (n := n)))) :=
  selNode_canonizer Force.keyEquivariant_lookahead SupplyTransport.supplyEquivariant_matchSupply

/-! ### The `SameOrbits` transfer — the fused object reads the supply only through its orbit relation -/

theorem cellNarrow_congr {key : Key n} {S₁ S₂ : Supply n} (h : SameOrbits S₁ S₂)
    (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) :
    cellNarrow key S₂ adj χ c = cellNarrow key S₁ adj χ c := by
  unfold cellNarrow cellNarrowV
  have hrep : rep (verified S₂ adj χ) = rep (verified S₁ adj χ) :=
    funext (OrbitPrune.rep_congr (fun u w => (h adj χ u w).symm))
  rw [hrep]

theorem selColour_congr {key : Key n} {S₁ S₂ : Supply n} (h : SameOrbits S₁ S₂)
    (adj : AdjMatrix n) (χ : Colouring n) :
    selColour key S₂ adj χ = selColour key S₁ adj χ := by
  rw [selColour_def, selColour_def]
  congr 1
  apply Finset.filter_congr
  intro c _
  rw [cellNarrow_congr h adj χ c]

theorem selNode_children_congr {rf : Refiner n} {key : Key n} {S₁ S₂ : Supply n}
    (h : SameOrbits S₁ S₂) (adj : AdjMatrix n) (χ : Colouring n) :
    (selNode rf key S₂ adj χ).1 = (selNode rf key S₁ adj χ).1 := by
  cases hsel : selColour key S₁ adj χ with
  | none =>
      rw [selNode_children_none hsel,
        selNode_children_none (by rw [selColour_congr h adj χ]; exact hsel)]
  | some c =>
      rw [selNode_children_some hsel,
        selNode_children_some (by rw [selColour_congr h adj χ]; exact hsel),
        cellNarrow_congr h adj χ c]

theorem descendS_selNode_val_congr {rf : Refiner n} {key : Key n} {S₁ S₂ : Supply n}
    (h : SameOrbits S₁ S₂) (adj : AdjMatrix n) :
    ∀ (fuel : Nat) (χ : Colouring n),
      (descendS (selNode rf key S₂) adj fuel χ).1
        = (descendS (selNode rf key S₁) adj fuel χ).1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro χ
      by_cases hd : Discrete χ
      · rw [descendS_val_leaf _ adj hd 0, descendS_val_leaf _ adj hd 0]
      · rw [descendS_val_zero _ adj hd, descendS_val_zero _ adj hd]
  | succ fuel ih =>
      intro χ
      by_cases hd : Discrete χ
      · rw [descendS_val_leaf _ adj hd (fuel + 1), descendS_val_leaf _ adj hd (fuel + 1)]
      · rw [descendS_val_succ _ adj hd fuel, descendS_val_succ _ adj hd fuel,
          selNode_children_congr h adj χ]
        exact congrArg aggregate (List.map_congr_left (fun vc _ => ih vc.2))

theorem canonFormS?_selNode_congr {rf : Refiner n} {key : Key n} {S₁ S₂ : Supply n}
    (h : SameOrbits S₁ S₂) (adj : AdjMatrix n) :
    canonFormS? rf (selNode rf key S₂) adj = canonFormS? rf (selNode rf key S₁) adj :=
  descendS_selNode_val_congr h adj n _

/-- **★★ THE REDUCTION, FUSED** (mirror of `OrbitPrune.guarded_mixed_canonizer_of_sameOrbits`): a pruned supply
inherits the fused capstone from any orbit-equal equivariant reference supply, with NO equivariance proof of its
own — the canonizer-of-record path (`prunedSupply d`) stays open under the sel rewrite. -/
theorem selNode_canonizer_of_sameOrbits {key : Key n} (hk : KeyEquivariant key)
    {S₁ S₂ : Supply n} (h1 : SupplyEquivariant S₁) (hso : SameOrbits S₁ S₂) :
    CanonSpec.IsCanonicalFormOpt
      (canonFormS? (Refine.encodeFreeFast (n := n))
        (selNode (Refine.encodeFreeFast (n := n)) key S₂)) := by
  obtain ⟨hsound, hiso⟩ := selNode_canonizer hk h1
  refine ⟨soundOptS_canonFormS? _ _, fun σ adj => ?_⟩
  rw [canonFormS?_selNode_congr hso (relabelAdj σ adj), canonFormS?_selNode_congr hso adj]
  exact hiso σ adj

/-- The fused canonizer at the canonizer-of-record supply (`prunedSupply d`), for every depth. -/
theorem selNode_pruned_canonizer (d : Nat) :
    CanonSpec.IsCanonicalFormOpt
      (canonFormS? (Refine.encodeFreeFast (n := n))
        (selNode (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (PrunedSupply.prunedSupply (n := n) d))) :=
  selNode_canonizer_of_sameOrbits Force.keyEquivariant_lookahead
    (DeepMatch.supplyEquivariant_deepMatchSupply d) (PrunedSupply.sameOrbits_deepMatchSupply d)

/-! ### ★ THE DOMINANCE THEOREM (acceptance criterion 1 — no strength increase, as a theorem)

If the guarded blind object answers, the fused object answers **with the same value**: at every node the blind
object survives, its least cell narrowed to `≤ 1`, so the least cell is resolvable, so it is the least
*resolvable* cell — `selNode` makes the identical step. "Some cell narrows to `≤ 1`" is strictly weaker per node
than "the least cell narrows to `≤ 1`" at the SAME resolver strength; the residue can only shrink. -/

theorem exists_targetColour_of_not_discrete {χ : Colouring n} (hd : ¬ Discrete χ) :
    ∃ c, targetColour χ = some c := by
  cases hc : targetColour χ with
  | some c => exact ⟨c, rfl⟩
  | none =>
      exfalso
      apply branches_ne_nil hd
      unfold branches
      rw [hc]

theorem aggregate_singleton (x : Option (Labelled n)) : aggregate [x] = x := by
  cases x with
  | none => rfl
  | some c => rfl

theorem descendS_selNode_val_of_guard {rf : Refiner n} {key : Key n} {S : Supply n}
    (adj : AdjMatrix n) :
    ∀ (fuel : Nat) (χ : Colouring n) (c : Labelled n),
      (descend rf (Stall.guard (Composite.forceThenConsume key S)) adj fuel χ).1 = some c →
      (descendS (selNode rf key S) adj fuel χ).1 = some c := by
  intro fuel
  induction fuel with
  | zero =>
      intro χ c h
      by_cases hd : Discrete χ
      · rw [descend_val_leaf _ _ adj hd 0] at h
        rw [descendS_val_leaf _ adj hd 0]
        exact h
      · rw [descend_val_zero _ _ adj hd] at h
        exact absurd h (by simp)
  | succ fuel ih =>
      intro χ c h
      by_cases hd : Discrete χ
      · rw [descend_val_leaf _ _ adj hd (fuel + 1)] at h
        rw [descendS_val_leaf _ adj hd (fuel + 1)]
        exact h
      · rw [descend_val_succ _ _ adj hd fuel] at h
        by_cases hst : Stall.stalled (Composite.forceThenConsume key S) adj χ
        · rw [Stall.narrow_guard, if_pos hst, List.map_nil] at h
          have hcontra : (none : Option (Labelled n)) = some c := h
          exact absurd hcontra (by simp)
        · rw [Stall.narrow_guard, if_neg hst] at h
          have hle : (narrow (Composite.forceThenConsume key S) adj χ).length ≤ 1 :=
            Nat.not_lt.mp hst
          have hne := (Composite.narrowProper_forceThenConsume (key := key) S).1 adj χ hd
          obtain ⟨v, hv⟩ : ∃ v, narrow (Composite.forceThenConsume key S) adj χ = [v] := by
            rcases hnar : narrow (Composite.forceThenConsume key S) adj χ with _ | ⟨v, t⟩
            · exact absurd hnar hne
            · rw [hnar] at hle
              simp only [List.length_cons] at hle
              have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
              exact ⟨v, by rw [ht]⟩
          obtain ⟨c₀, hc₀⟩ := exists_targetColour_of_not_discrete hd
          have hres : (cellNarrow key S adj χ c₀).length ≤ 1 := by
            rw [cellNarrow_targetColour hc₀, hv]
            simp
          have hsel : selColour key S adj χ = some c₀ :=
            selColour_of_target_resolvable hc₀ hres
          rw [hv, List.map_cons, List.map_nil, aggregate_singleton] at h
          rw [descendS_val_succ _ adj hd fuel, selNode_children_some hsel,
            cellNarrow_targetColour hc₀, hv, List.map_cons, List.map_nil, List.map_cons,
            List.map_nil, aggregate_singleton]
          exact ih (refineV rf adj (indivOne χ v)) c h

/-- **★★ THE FUSED OBJECT DOMINATES THE GUARDED BLIND OBJECT** — same refiner, same key, same supply: wherever
the guarded object answers, the fused object answers with the SAME canonical form. Every `Handled` graph of the
blind stack is handled by the fused stack; the exposure-dependency witness (`Regression.lean`) shows the
containment is strict. -/
theorem canonFormS?_selNode_dominates {rf : Refiner n} {key : Key n} {S : Supply n}
    (adj : AdjMatrix n) {c : Labelled n}
    (h : canonForm? rf (Stall.guard (Composite.forceThenConsume key S)) adj = some c) :
    canonFormS? rf (selNode rf key S) adj = some c :=
  descendS_selNode_val_of_guard adj n _ c h

/-! ## 8. The flag is the TRUE MUTUAL STALL -/

/-- **★ THE FLAG SEMANTICS** `Publication.lean` §1 names, as a characterization: the fused resolver emits no
child **iff** NO non-singleton cell narrows to `≤ 1` — neither move applies anywhere on the node. (Contrast
`Stall.stalled`, which reads only the least cell.) -/
theorem selNode_stall_iff {rf : Refiner n} {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    {χ : Colouring n} :
    (selNode rf key S adj χ).1 = []
      ↔ ∀ c ∈ nonSingletonColours χ, 1 < (cellNarrow key S adj χ c).length := by
  constructor
  · intro h c hc
    cases hsel : selColour key S adj χ with
    | none => exact Nat.not_le.mp (selColour_none hsel c hc)
    | some c' =>
        rw [selNode_children_some hsel] at h
        have := List.map_eq_nil_iff.mp h
        exact absurd this (cellNarrow_ne_nil (selColour_spec hsel).1)
  · intro hall
    cases hsel : selColour key S adj χ with
    | none => exact selNode_children_none hsel
    | some c' =>
        have h1 := (selColour_spec hsel).2
        have h2 := hall c' (selColour_spec hsel).1
        omega

/-! ## 9. The sel-aware residue — `NodeResolved` / `HandledS` (the residue DEFLATES; increment 5)

`Cost.CellResolved` demands the LEAST cell resolve; `NodeResolved` demands SOME cell resolve — strictly weaker
per node at the same key/supply strength, over the (widened) same `Reaches` set. So `Handled ⟹ HandledS`
(`handledS_of_handled`): every graph the blind stack handles, the fused stack handles — and the exposure
witness (`Regression.lean`) shows the containment is strict. This is the point of the sel rewrite. -/

/-- The fused resolver can act: SOME non-singleton cell narrows to `≤ 1`. -/
def NodeResolved (key : Key n) (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∃ c ∈ nonSingletonColours χ, (cellNarrow key S adj χ c).length ≤ 1

/-- The sel-aware capability predicate: every reached non-discrete node has some resolvable cell. -/
def HandledS (key : Key n) (S : Supply n) (adj : AdjMatrix n) : Prop :=
  ∀ χ : Colouring n, Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ → ¬ Discrete χ →
    NodeResolved key S adj χ

/-- The blind payload implies the fused one, node by node: a resolved least cell IS a resolvable cell. -/
theorem nodeResolved_of_cellResolved {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    {χ : Colouring n} (hd : ¬ Discrete χ) (h : Cost.CellResolved key S adj χ) :
    NodeResolved key S adj χ := by
  obtain ⟨c₀, hc₀⟩ := exists_targetColour_of_not_discrete hd
  refine ⟨c₀, Finset.mem_of_min hc₀, ?_⟩
  rw [cellNarrow_targetColour hc₀]
  rcases h with horb | hsep
  · exact le_of_eq (Composite.forceThenConsume_singleton_of_cellIsOrbit hd horb)
  · exact le_of_eq (Composite.forceThenConsume_singleton_of_separating hd hsep)

/-- **★ THE RESIDUE DEFLATES**: `Handled ⟹ HandledS`, same key, same supply. -/
theorem handledS_of_handled {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    (h : Residue.Handled key S adj) : HandledS key S adj :=
  fun χ hr hd => nodeResolved_of_cellResolved hd (h χ hr hd)

/-- Contrapositive: the sel-aware residue is CONTAINED in the blind residue. -/
theorem residue_of_not_handledS {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    (h : ¬ HandledS key S adj) : Residue.Residue key S adj :=
  fun hh => h (handledS_of_handled hh)

/-- `HandledS` transfers along `SameOrbits` (the fused object reads the supply only through its orbits). -/
theorem handledS_of_sameOrbits {key : Key n} {S₁ S₂ : Supply n} (hso : SameOrbits S₁ S₂)
    {adj : AdjMatrix n} (h : HandledS key S₁ adj) : HandledS key S₂ adj := by
  intro χ hr hd
  obtain ⟨c, hc, hres⟩ := h χ hr hd
  refine ⟨c, hc, ?_⟩
  rw [cellNarrow_congr hso adj χ c]
  exact hres

/-- **The seal populates the SEL-AWARE predicate too** — depth + localisation give `HandledS` for the deep
oracle, through the (widened) `HandledBridge.handled_of_seal`; the `∀ T CellsAreOrbits` hook absorbs the
`Reaches`/`ValidPath` widening with no change. -/
theorem handledS_of_seal {adj : AdjMatrix n} {k : Nat} (key : Key n)
    (hdepth : CascadesAt adj (Refine.constP n) k)
    (hloc : ∀ T : Finset (Fin n), CellsAreOrbits adj (Refine.constP n) T) :
    HandledS key (DeepMatch.deepMatchSupply (n := n) k) adj :=
  handledS_of_handled (HandledBridge.handled_of_seal key hdepth hloc)

/-! ## 10. Totality and the answers theorem — `HandledS` graphs are CANONIZED by the fused object -/

/-- **Totality for the generalized descent** (mirror of `descend_ne_none_reaches`): under a `NodeProper` node
resolver that emits a child at every reached non-discrete node, the descent reaches a leaf within the fuel —
`NodeProper`'s partner component is exactly the widened `Reaches.step`, and the hand-forward equation re-bases
each child onto `refineV` so the colour count strictly climbs. -/
theorem descendS_ne_none_reaches {rf : Refiner n} {N : NodeRes n} (hs : RefineSplits rf)
    (hproper : NodeProper rf N) {adj : AdjMatrix n}
    (hne : ∀ χ : Colouring n, Reaches rf adj χ → ¬ Discrete χ → (N adj χ).1 ≠ []) :
    ∀ (fuel : Nat) (χ : Colouring n), Reaches rf adj χ → n ≤ ncol χ + fuel →
      (descendS N adj fuel χ).1 ≠ none := by
  intro fuel
  induction fuel with
  | zero =>
      intro χ _ hb
      have hd : Discrete χ := discrete_of_ncol_eq (le_antisymm (ncol_le χ) (by omega))
      rw [descendS_val_leaf N adj hd 0]
      exact fun hc => by simp at hc
  | succ fuel ih =>
      intro χ hr hb
      by_cases hd : Discrete χ
      · rw [descendS_val_leaf N adj hd (fuel + 1)]
        exact fun hc => by simp at hc
      · rw [descendS_val_succ N adj hd fuel]
        refine aggregate_ne_none ?_ ?_
        · exact fun hc => (hne χ hr hd) (List.map_eq_nil_iff.mp hc)
        · intro x hx
          obtain ⟨vc, hvc, rfl⟩ := List.mem_map.mp hx
          obtain ⟨hpart, heq⟩ := hproper adj χ vc hvc
          rw [heq]
          refine ih (refineV rf adj (indivOne χ vc.1)) (hr.step hd hpart) ?_
          have h1 : ncol χ < ncol (indivOne χ vc.1) := ncol_lt_indivOne_of_partner hpart
          have h2 : ncol (indivOne χ vc.1) ≤ ncol (refineV rf adj (indivOne χ vc.1)) :=
            ncol_le_refine hs adj (indivOne χ vc.1)
          omega

/-- A `NodeResolved` node is never a stall for the fused resolver. -/
theorem selNode_ne_nil_of_nodeResolved {rf : Refiner n} {key : Key n} {S : Supply n}
    {adj : AdjMatrix n} {χ : Colouring n} (h : NodeResolved key S adj χ) :
    (selNode rf key S adj χ).1 ≠ [] := by
  obtain ⟨c, hc, hres⟩ := h
  intro hnil
  have := selNode_stall_iff.mp hnil c hc
  omega

/-- **★★ THE ANSWERS THEOREM** (mirror of `Residue.answers_of_handled`): the fused canonizer ANSWERS on every
`HandledS` graph — no flag. With `handledS_of_handled` this recovers every blind answers-instance; with the
exposure witness it answers strictly more. -/
theorem answersS_of_handledS {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    (h : HandledS key S adj) :
    canonFormS? (Refine.encodeFreeFast (n := n))
      (selNode (Refine.encodeFreeFast (n := n)) key S) adj ≠ none := by
  unfold canonFormS?
  refine descendS_ne_none_reaches Refine.refineSplits_encodeFreeFast
    (nodeProper_selNode _ _ _)
    (fun χ hr hd => selNode_ne_nil_of_nodeResolved (h χ hr hd)) n _ Descend.Reaches.root ?_
  have := Nat.zero_le (ncol (refineV (Refine.encodeFreeFast (n := n)) adj (fun _ => 0)))
  omega

/-- **`③a` for the fused object** (mirror of `Residue.residue_if_flag`): the flag names the sel-aware residue —
which sits INSIDE the blind residue (`residue_of_not_handledS`). -/
theorem not_handledS_if_flagS {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    (hflag : canonFormS? (Refine.encodeFreeFast (n := n))
      (selNode (Refine.encodeFreeFast (n := n)) key S) adj = none) :
    ¬ HandledS key S adj :=
  fun h => answersS_of_handledS h hflag

/-! ## 11. `②` for the fused object — single path unconditionally, probe billed per node -/

theorem descendS_cost_leaf (N : NodeRes n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : Discrete χ) : ∀ fuel, (descendS N adj fuel χ).2 = 1
  | 0 => by rw [descendS, dif_pos h]
  | _ + 1 => by rw [descendS, dif_pos h]

theorem descendS_cost_zero (N : NodeRes n) (adj : AdjMatrix n) {χ : Colouring n}
    (h : ¬ Discrete χ) : (descendS N adj 0 χ).2 = 1 := by
  rw [descendS, dif_neg h]

/-- **The single-path cost bound for the generalized descent** (mirror of `Cost.descend_cost_le_of_resolved`,
with the fan-out hypothesis `≤ 1` — which `selNode` meets BY CONSTRUCTION, no firing hypothesis at all). The
node resolver's bill `cN` includes the children's refinements (the §6.4 hand-forward: they are the same work). -/
theorem descendS_cost_le_of_le_one {N : NodeRes n} {adj : AdjMatrix n}
    (hone : ∀ χ : Colouring n, ¬ Discrete χ → (N adj χ).1.length ≤ 1)
    {cN : Nat} (hN : ∀ χ : Colouring n, (N adj χ).2 ≤ cN) :
    ∀ (fuel : Nat) (χ : Colouring n), (descendS N adj fuel χ).2 ≤ (fuel + 1) * (1 + cN) := by
  intro fuel
  induction fuel with
  | zero =>
      intro χ
      have hone' : (descendS N adj 0 χ).2 = 1 := by
        by_cases hd : Discrete χ
        · exact descendS_cost_leaf N adj hd 0
        · exact descendS_cost_zero N adj hd
      rw [hone', Nat.one_mul]
      omega
  | succ fuel ih =>
      intro χ
      set K := 1 + cN with hK
      have hKle : K ≤ (fuel + 1 + 1) * K := Nat.le_mul_of_pos_left K (by omega)
      have hexp : (fuel + 1 + 1) * K = K + (fuel + 1) * K := by ring
      by_cases hd : Discrete χ
      · rw [descendS_cost_leaf N adj hd (fuel + 1)]; omega
      · rw [descendS_cost_succ N adj hd fuel]
        have hNc : (N adj χ).2 ≤ cN := hN χ
        have hcase : (N adj χ).1 = [] ∨ ∃ vc, (N adj χ).1 = [vc] := by
          have hlen := hone χ hd
          rcases hnar : (N adj χ).1 with _ | ⟨vc, t⟩
          · exact Or.inl rfl
          · rw [hnar] at hlen
            simp only [List.length_cons] at hlen
            have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
            exact Or.inr ⟨vc, by rw [ht]⟩
        rcases hcase with h0 | ⟨vc, h0⟩
        · rw [h0]; simp only [List.map_nil, List.sum_nil]; omega
        · rw [h0]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
          have h2 : (descendS N adj fuel vc.2).2 ≤ (fuel + 1) * K := ih _
          omega

/-- The top-level `②` shape for the generalized object. -/
theorem descentCostS_le_of_le_one {rf : Refiner n} {N : NodeRes n} {adj : AdjMatrix n}
    (hone : ∀ χ : Colouring n, ¬ Discrete χ → (N adj χ).1.length ≤ 1)
    {c₁ cN : Nat} (hrf : ∀ χ : Colouring n, (rf adj χ).2 ≤ c₁)
    (hN : ∀ χ : Colouring n, (N adj χ).2 ≤ cN) :
    descentCostS rf N adj ≤ c₁ + (n + 1) * (1 + cN) := by
  unfold descentCostS
  have h1 : (rf adj (fun _ => 0)).2 ≤ c₁ := hrf _
  have h2 := descendS_cost_le_of_le_one hone hN n (refineV rf adj (fun _ => 0))
  omega

theorem selNode_cost_none {rf : Refiner n} {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    {χ : Colouring n} (h : selColour key S adj χ = none) :
    (selNode rf key S adj χ).2 = selProbeCost key S adj χ := by
  rw [selNode_eq]
  unfold selNodeCore
  unfold selColour at h
  rw [h]

theorem selNode_cost_some {rf : Refiner n} {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    {χ : Colouring n} {c : Nat} (h : selColour key S adj χ = some c) :
    (selNode rf key S adj χ).2
      = selProbeCost key S adj χ
        + ((cellNarrow key S adj χ c).map (fun v => (rf adj (indivOne χ v)).2)).sum := by
  rw [selNode_eq]
  unfold selNodeCore
  unfold selColour at h
  rw [h]
  rfl

/-- The fused resolver's per-node bill: the probe, plus at most ONE child refinement. -/
theorem selNode_cost_le {rf : Refiner n} {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    {χ : Colouring n} {cP cr : Nat} (hp : selProbeCost key S adj χ ≤ cP)
    (hr : ∀ χ' : Colouring n, (rf adj χ').2 ≤ cr) :
    (selNode rf key S adj χ).2 ≤ cP + cr := by
  cases hsel : selColour key S adj χ with
  | none => rw [selNode_cost_none hsel]; omega
  | some c =>
      rw [selNode_cost_some hsel]
      have hlen := (selColour_spec hsel).2
      rcases hk : cellNarrow key S adj χ c with _ | ⟨v, t⟩
      · simp only [List.map_nil, List.sum_nil]; omega
      · rw [hk] at hlen
        simp only [List.length_cons] at hlen
        have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst ht
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        have := hr (indivOne χ v)
        omega

theorem cellList_length_le (χ : Colouring n) (c : Nat) : (cellList χ c).length ≤ n := by
  unfold cellList
  refine le_trans (List.length_filter_le _ _) ?_
  rw [List.length_finRange]

theorem nsColours_length_le (χ : Colouring n) : (nsColours χ).length ≤ n := by
  unfold nsColours
  refine le_trans (List.length_filter_le _ _) ?_
  refine le_trans (List.dedup_sublist _).length_le ?_
  rw [List.length_map, List.length_finRange]

/-- The probe's budget, coarsely: `≤ n` cells, each cell `≤ n` members, each member one key evaluation and one
orbit BFS against `≤ gB` verified generators. -/
def selProbeBound (n sB gB kc : Nat) : Nat :=
  sB + gB * (n * n) + n * (n * kc + n * n + n * (gB * (n * n) + n * n))

theorem selProbeCost_le {key : Key n} {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n}
    {sB gB kc : Nat} (hs : supplyCost S adj χ ≤ sB) (hg : (gens S adj χ).length ≤ gB)
    (hk : ∀ v : Fin n, keyCost key adj χ v ≤ kc) :
    selProbeCost key S adj χ ≤ selProbeBound n sB gB kc := by
  unfold selProbeCost selProbeBound
  have hver : (verified S adj χ).length ≤ gB := le_trans (List.length_filter_le _ _) hg
  have hterm : ∀ x ∈ (nsColours χ).map (fun c =>
      ((cellList χ c).map (keyCost key adj χ)).sum + n * n
        + (cellList χ c).length * ((verified S adj χ).length * (n * n) + n * n)),
      x ≤ n * kc + n * n + n * (gB * (n * n) + n * n) := by
    intro x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    have h1 : ((cellList χ c).map (keyCost key adj χ)).sum ≤ n * kc := by
      refine le_trans (List.sum_le_card_nsmul _ kc ?_) ?_
      · intro y hy
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
        exact hk v
      · rw [List.length_map, smul_eq_mul]
        exact Nat.mul_le_mul_right kc (cellList_length_le χ c)
    have h2 : (cellList χ c).length * ((verified S adj χ).length * (n * n) + n * n)
        ≤ n * (gB * (n * n) + n * n) :=
      Nat.mul_le_mul (cellList_length_le χ c)
        (Nat.add_le_add (Nat.mul_le_mul_right (n * n) hver) le_rfl)
    omega
  have hsum := List.sum_le_card_nsmul _ _ hterm
  rw [List.length_map, smul_eq_mul] at hsum
  have hsum' : ((nsColours χ).map (fun c =>
      ((cellList χ c).map (keyCost key adj χ)).sum + n * n
        + (cellList χ c).length * ((verified S adj χ).length * (n * n) + n * n))).sum
      ≤ n * (n * kc + n * n + n * (gB * (n * n) + n * n)) :=
    le_trans hsum (Nat.mul_le_mul_right _ (nsColours_length_le χ))
  have hg2 : (gens S adj χ).length * (n * n) ≤ gB * (n * n) :=
    Nat.mul_le_mul_right (n * n) hg
  omega

/-- **★★ `②` END-TO-END FOR THE FUSED CANONIZER OF RECORD** (mirror of
`SupplyCost.descentCost_pruned_lookahead_le`): the fused object over `lookaheadKey` + `prunedSupply d` has an
explicit polynomial `descentCost` — on EVERY input, answer or flag alike, per fixed `d`. Fan-out `≤ 1` needs no
firing hypothesis (it holds by construction), so unlike the guarded bound this one carries no `ResolvedAll`. -/
theorem descentCostS_selNode_pruned_lookahead_le (d : Nat) (adj : AdjMatrix n) :
    descentCostS (Refine.encodeFreeFast (n := n))
        (selNode (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (PrunedSupply.prunedSupply (n := n) d)) adj
      ≤ n * n * n + (n + 1)
          * (1 + (selProbeBound n (SupplyCost.refSupplyBound n d) (SupplyCost.tableBound n d)
              (n * n * n + n * n) + n * n * n)) := by
  refine descentCostS_le_of_le_one
    (fun χ _ => selNode_children_length_le_one _ _ _ adj χ)
    (fun χ => le_of_eq (Cost.refiner_cost adj χ)) (fun χ => ?_)
  refine selNode_cost_le (selProbeCost_le (SupplyCost.supplyCost_prunedSupply_le d adj χ)
    (SupplyCost.gens_prunedSupply_length_le d adj χ)
    (fun v => SupplyCost.keyCost_lookaheadKey_le adj χ v)) ?_
  exact fun χ' => le_of_eq (Cost.refiner_cost adj χ')

/-- The same, for the one-step oracle (`d = 0` shape): explicit polynomial, no hypotheses. -/
theorem descentCostS_selNode_match_lookahead_le (adj : AdjMatrix n) :
    descentCostS (Refine.encodeFreeFast (n := n))
        (selNode (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (Consume.matchSupply (n := n))) adj
      ≤ n * n * n + (n + 1)
          * (1 + (selProbeBound n (SupplyCost.matchSupplyBound n) (n * n)
              (n * n * n + n * n) + n * n * n)) := by
  refine descentCostS_le_of_le_one
    (fun χ _ => selNode_children_length_le_one _ _ _ adj χ)
    (fun χ => le_of_eq (Cost.refiner_cost adj χ)) (fun χ => ?_)
  refine selNode_cost_le (selProbeCost_le (SupplyCost.supplyCost_matchSupply_le adj χ)
    (SupplyCost.gens_matchSupply_length_le adj χ)
    (fun v => SupplyCost.keyCost_lookaheadKey_le adj χ v)) ?_
  exact fun χ' => le_of_eq (Cost.refiner_cost adj χ')

/-- **★★★ THE FUSED CAPSTONE OF RECORD, ①+②+③a IN ONE PLACE**: for every graph, the fused pruned-lookahead
canonizer is sound/complete/flag-iso-invariant (`selNode_pruned_canonizer`), runs within an explicit polynomial
budget unconditionally (`descentCostS_selNode_pruned_lookahead_le`), and its flag names the sel-aware residue
(`not_handledS_if_flagS`), which sits inside the blind residue. -/
theorem selNode_pruned_record (d : Nat) (adj : AdjMatrix n) :
    CanonSpec.IsCanonicalFormOpt
      (canonFormS? (Refine.encodeFreeFast (n := n))
        (selNode (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (PrunedSupply.prunedSupply (n := n) d)))
    ∧ descentCostS (Refine.encodeFreeFast (n := n))
        (selNode (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (PrunedSupply.prunedSupply (n := n) d)) adj
      ≤ n * n * n + (n + 1)
          * (1 + (selProbeBound n (SupplyCost.refSupplyBound n d) (SupplyCost.tableBound n d)
              (n * n * n + n * n) + n * n * n)) :=
  ⟨selNode_pruned_canonizer d, descentCostS_selNode_pruned_lookahead_le d adj⟩

/-! ## 12. The ALL-CELLS harvest — `allCellsMatchSupply` (increment 3 item (i))

Every built supply harvests candidates from `branches χ` (the least cell) only — so the fused resolver's CONSUME
half can act on a non-least cell only when a least-rooted candidate happens to move it. The all-cells harvest
widens candidate GENERATION to every non-singleton cell: same construct-and-check candidates, the same
`matchSupplyBound`-shape cost (`|nsList| ≤ n` exactly as `|branches| ≤ n`), and `GensEquivariant` by the same
conjugation argument (`nsList` transports because per-colour cell sizes are invariant).

**Why it is load-bearing (2026-07-17 witness analysis, recorded in the handoff):** for a graph whose least cell's
pins do NOT discretize (e.g. a `Z₄`-symmetric graph whose least cell is the 2-orbit — pinning it leaves `γ²`
alive), the least-rooted harvest is empty, so the fused object could not consume-fire on the 4-orbit cell whose
pins DO discretize. With the all-cells harvest those pins are harvested, `γ` is reconstructed and verified, and
the 4-orbit collapses — the exposure-dependency witness (`Regression.lean` §8). -/

/-- The vertices of the non-singleton cells — the all-cells harvest roots, computably. -/
def nsList (χ : Colouring n) : List (Fin n) :=
  (List.finRange n).filter (fun v => decide (1 < (cellList χ (χ v)).length))

theorem nsList_length_le (χ : Colouring n) : (nsList χ).length ≤ n := by
  unfold nsList
  refine le_trans (List.length_filter_le _ _) ?_
  rw [List.length_finRange]

/-- **★ THE ALL-CELLS COLOUR-MATCH SUPPLY** — `matchSupply` with the harvest widened from `branches χ` to the
vertices of every non-singleton cell. Untrusted as always (`verified` filters); cross-cell candidate pairs are
junk the filter discards. Refinements materialised once, before pairing (the measured `|cell|²`-refinements
trap). -/
def allCellsMatchSupply : Supply n := fun adj χ =>
  let data : List (Fin n × Refine.ColData n) :=
    (nsList χ).map (fun v => (v, Consume.lookData adj χ v))
  (data.flatMap (fun p => data.filterMap (fun q => Consume.matchFrom p.2 q.2)),
   (nsList χ).length * CostModel.WarmRefine.warmRefineCost n
     + (nsList χ).length * (nsList χ).length * (n * n))

theorem mem_gens_allCellsMatchSupply_iff {adj : AdjMatrix n} {χ : Colouring n}
    {g : Equiv.Perm (Fin n)} :
    g ∈ gens (allCellsMatchSupply (n := n)) adj χ ↔
      ∃ v ∈ nsList χ, ∃ w ∈ nsList χ, Consume.matchCandidate adj χ v w = some g := by
  constructor
  · intro hg
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hg
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    obtain ⟨q, hq2, hmf⟩ := List.mem_filterMap.mp hq
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq2
    exact ⟨v, hv, w, hw, hmf⟩
  · rintro ⟨v, hv, w, hw, h⟩
    refine List.mem_flatMap.mpr ⟨(v, Consume.lookData adj χ v), List.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
    exact List.mem_filterMap.mpr ⟨(w, Consume.lookData adj χ w), List.mem_map.mpr ⟨w, hw, rfl⟩, h⟩

/-- The per-colour cell size is transport-invariant (list form of `cellOf_card_transport`). -/
theorem cellList_length_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) (c : Nat) :
    (cellList (transportColouring σ χ) c).length = (cellList χ c).length := by
  rw [cellList_length_eq_card, cellList_length_eq_card, cellOf_card_transport]

/-- The all-cells harvest roots transport up to permutation (mirror of `branches_transport_perm`). -/
theorem nsList_transport_perm (σ : Equiv.Perm (Fin n)) (χ : Colouring n) :
    (nsList (transportColouring σ χ)).Perm ((nsList χ).map σ) := by
  unfold nsList
  refine List.perm_of_nodup_nodup_toFinset_eq
    ((List.nodup_finRange n).filter _) (((List.nodup_finRange n).filter _).map σ.injective) ?_
  ext u
  simp only [List.mem_toFinset, List.mem_filter, List.mem_map, List.mem_finRange, true_and,
    decide_eq_true_eq]
  constructor
  · intro hu
    refine ⟨σ.symm u, ?_, by simp⟩
    have : transportColouring σ χ u = χ (σ.symm u) := rfl
    rwa [this, cellList_length_transport σ χ (χ (σ.symm u))] at hu
  · rintro ⟨v, hv, rfl⟩
    have : transportColouring σ χ (σ v) = χ v := by
      show χ (σ.symm (σ v)) = χ v
      rw [Equiv.symm_apply_apply]
    rw [this, cellList_length_transport σ χ (χ v)]
    exact hv

/-- **★★ The all-cells supply is EQUIVARIANT** (mirror of `gensEquivariant_matchSupply`): the candidates
conjugate, and the harvest roots transport. So the fused capstone instantiates on it with no new hypothesis. -/
theorem gensEquivariant_allCellsMatchSupply :
    SupplyTransport.GensEquivariant (allCellsMatchSupply (n := n)) := by
  intro σ adj χ g
  have hbr : ∀ x : Fin n, x ∈ nsList (transportColouring σ χ) ↔ ∃ y ∈ nsList χ, σ y = x := by
    intro x
    rw [(nsList_transport_perm σ χ).mem_iff, List.mem_map]
  simp only [mem_gens_allCellsMatchSupply_iff]
  constructor
  · rintro ⟨v, hv, w, hw, hmc⟩
    obtain ⟨v₀, hv₀, rfl⟩ := (hbr v).mp hv
    obtain ⟨w₀, hw₀, rfl⟩ := (hbr w).mp hw
    rw [Consume.matchCandidate_conj] at hmc
    rcases hcase : Consume.matchCandidate adj χ v₀ w₀ with _ | t
    · rw [hcase] at hmc; simp at hmc
    · rw [hcase] at hmc
      simp only [Option.map_some, Option.some.injEq] at hmc
      exact ⟨t, ⟨v₀, hv₀, w₀, hw₀, hcase⟩, hmc.symm⟩
  · rintro ⟨h, ⟨v, hv, w, hw, hmc⟩, rfl⟩
    refine ⟨σ v, (hbr _).mpr ⟨v, hv, rfl⟩, σ w, (hbr _).mpr ⟨w, hw, rfl⟩, ?_⟩
    rw [Consume.matchCandidate_conj, hmc]
    rfl

theorem supplyEquivariant_allCellsMatchSupply :
    SupplyEquivariant (allCellsMatchSupply (n := n)) :=
  SupplyTransport.supplyEquivariant_of_gensEquivariant gensEquivariant_allCellsMatchSupply

/-- **The fused canonizer over the all-cells harvest** — concrete, no hypotheses. This is the instance the
exposure witness runs. -/
theorem selNode_allCellsMatch_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (canonFormS? (Refine.encodeFreeFast (n := n))
        (selNode (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (allCellsMatchSupply (n := n)))) :=
  selNode_canonizer Force.keyEquivariant_lookahead supplyEquivariant_allCellsMatchSupply

/-- The all-cells harvest prices exactly like `matchSupply` (`|nsList| ≤ n` replaces `|branches| ≤ n`). -/
theorem supplyCost_allCellsMatchSupply_le (adj : AdjMatrix n) (χ : Colouring n) :
    supplyCost (allCellsMatchSupply (n := n)) adj χ ≤ SupplyCost.matchSupplyBound n := by
  show (nsList χ).length * CostModel.WarmRefine.warmRefineCost n
      + (nsList χ).length * (nsList χ).length * (n * n) ≤ _
  unfold SupplyCost.matchSupplyBound
  exact Nat.add_le_add
    (Nat.mul_le_mul (nsList_length_le χ) (CostModel.WarmRefine.warmRefineCost_le n))
    (Nat.mul_le_mul (Nat.mul_le_mul (nsList_length_le χ) (nsList_length_le χ)) le_rfl)

theorem gens_allCellsMatchSupply_length_le (adj : AdjMatrix n) (χ : Colouring n) :
    (gens (allCellsMatchSupply (n := n)) adj χ).length ≤ n * n := by
  have h := SupplyCost.length_pairTable_le ((nsList χ).map fun v => (v, Consume.lookData adj χ v))
    (fun p q => Consume.matchFrom p.2 q.2)
  rw [List.length_map] at h
  exact le_trans h (Nat.mul_le_mul (nsList_length_le χ) (nsList_length_le χ))

/-- `②` for the fused all-cells object: explicit polynomial on every input. -/
theorem descentCostS_selNode_allCells_le (adj : AdjMatrix n) :
    descentCostS (Refine.encodeFreeFast (n := n))
        (selNode (Refine.encodeFreeFast (n := n)) (Force.lookaheadKey (n := n))
          (allCellsMatchSupply (n := n))) adj
      ≤ n * n * n + (n + 1)
          * (1 + (selProbeBound n (SupplyCost.matchSupplyBound n) (n * n)
              (n * n * n + n * n) + n * n * n)) := by
  refine descentCostS_le_of_le_one
    (fun χ _ => selNode_children_length_le_one _ _ _ adj χ)
    (fun χ => le_of_eq (Cost.refiner_cost adj χ)) (fun χ => ?_)
  refine selNode_cost_le (selProbeCost_le (supplyCost_allCellsMatchSupply_le adj χ)
    (gens_allCellsMatchSupply_length_le adj χ)
    (fun v => SupplyCost.keyCost_lookaheadKey_le adj χ v)) ?_
  exact fun χ' => le_of_eq (Cost.refiner_cost adj χ')

/-- `nsList` extends `branches`: every branch vertex is an all-cells harvest root — so the all-cells verified
list contains everything `matchSupply` verifies (the harvest only widens). -/
theorem branches_subset_nsList {χ : Colouring n} {v : Fin n} (hv : v ∈ branches χ) :
    v ∈ nsList χ := by
  obtain ⟨u, hu, huv⟩ := exists_partner_of_mem_branches hv
  unfold nsList
  refine List.mem_filter.mpr ⟨List.mem_finRange v, ?_⟩
  simp only [decide_eq_true_eq]
  have h2 : u ∈ cellList χ (χ v) := (mem_cellList_iff u).mpr huv
  have h1 : v ∈ cellList χ (χ v) := (mem_cellList_iff v).mpr rfl
  rcases hc : cellList χ (χ v) with _ | ⟨x, t⟩
  · rw [hc] at h1; exact absurd h1 (List.not_mem_nil)
  · rcases ht : t with _ | _
    · rw [hc, ht] at h1 h2
      rw [List.mem_singleton.mp h1, List.mem_singleton.mp h2] at hu
      exact absurd rfl hu
    · simp

end Select
end ChainDescent
