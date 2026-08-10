import ChainDescent.SelectNode

/-!
# ★★★ THE CELL-INDEXED FUSED RESOLVER — design `B`, step 2

`SelectNode.cellNarrow` reads **one node-global** `verified S adj χ` list and probes every cell
against it. For a *cell-agnostic* supply (`foldSupply` / `deckSupply` / `deck2Supply` /
`kernelSupply`, all of which harvest from the whole graph) that is the right object. For a
**pair-anchored** supply it is not: `deepenSupply`'s generators come from deepening pairs of the
*branch* cell, and judging some other cell by them is measured **not relabelling-invariant**
(`scratchpad/probe_offbranch2.py`, CFI m = 8/10 at depth 1, `(1,1)` vs `(2,)`, with the guard OPEN on
both sides — `probe_offbranch3.py`).

This file gives each cell its own generator list. Everything is **additive**: `SelectNode` is not
touched, every theorem stated at `selNode` keeps its proof, and the two agree on values at
`ofSupply`.

## Why this costs almost nothing to build

Two structural facts do the work.

1. **`Select.lean`'s spine is resolver-generic.** `selNodeC` is just another `NodeRes n`, so
   `descendS` / `canonFormS?` / `isCanonicalFormOptS_canonFormS?` / `descentCostS` apply verbatim.
   The only thing that has to be re-proved is `NodeTransport`.
2. **`cellNarrowC key S adj χ c` is *definitionally* `cellNarrow key (S c) adj χ c`.** So every
   per-cell lemma already in `SelectNode` — `cellNarrow_ne_nil`, `cellNarrow_subset`,
   `rep_mem_keepMin_cell`, `aggregate_cellNarrow_eq` — applies unchanged at `S c`. The *one* lemma
   that does not carry over is `cellNarrow_length_transport`, because it is the only one that
   consumes `SupplyEquivariant`. §2 replaces exactly that hypothesis.

## ★ What replaces `SupplyEquivariant`, and why it is weaker

Tracing `nodeTransport_selNode`: after a colour is committed, `aggregate_cellNarrow_eq` rewrites both
sides down to `keepMin key adj χ (cellList χ c)`, which does **not mention the supply**, and they are
matched by `KeyEquivariant` alone. So the supply enters `①` through exactly one channel —
`selColour_transport`, and there only through the per-cell **orbit count**.

`CellOrbitTransport` (§2) is precisely that: *the emitted orbit relation transports, at pairs inside
each cell*. It is implied by `SupplyEquivariant` at a cell-agnostic supply
(`cellOrbitTransport_ofSupply`, so nothing regresses), and — this is the point — it is **also**
delivered by a guarded cell-anchored supply with no equivariance anywhere
(`Deepen.cellOrbit_transport_deepenCellSupply`), because a shut guard emits `[]` on both sides and an
open guard makes the relation equal the intrinsic `IsColAut`-orbit relation.

Quality bar: axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no fresh `axiom`,
`native_decide` banned.
-/

namespace ChainDescent
namespace Select

open ChainDescent.Descend
open ChainDescent.Consume (Supply gens verified rep IsColAut WordReach)
open ChainDescent.Force (Key KeyEquivariant keyCost keepMin)
open ChainDescent.SupplyTransport (SupplyEquivariant)

variable {n : Nat}

/-! ## 1. The cell-indexed supply and resolver -/

/-- **A cell-indexed supply**: one supply per cell colour. A `Nat`-indexed family rather than a new
structure, so every existing supply lifts by `ofSupply` and every existing lemma applies at `S c`. -/
abbrev CellSupply (n : Nat) := Nat → Supply n

/-- Every cell-agnostic supply lifts, ignoring the cell. `selNode`'s object is this special case. -/
def ofSupply (S : Supply n) : CellSupply n := fun _ => S

/-- **The per-cell narrowing against the cell's OWN generators.** Definitionally
`cellNarrow key (S c) adj χ c`, so all of `SelectNode`'s per-cell lemmas apply verbatim. -/
def cellNarrowC (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) :
    List (Fin n) :=
  cellNarrow key (S c) adj χ c

theorem cellNarrowC_eq (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n)
    (c : Nat) : cellNarrowC key S adj χ c = cellNarrow key (S c) adj χ c := rfl

theorem cellNarrowC_ofSupply (key : Key n) (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n)
    (c : Nat) : cellNarrowC key (ofSupply S) adj χ c = cellNarrow key S adj χ c := rfl

/-- **The selected colour** — unchanged in shape from `selColour`: the least non-singleton colour
whose cell narrows to `≤ 1`. Only the evidence each cell is judged on has changed. -/
def selColourC (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) : Option Nat :=
  ((nonSingletonColours χ).filter (fun c => (cellNarrowC key S adj χ c).length ≤ 1)).min

theorem selColourC_ofSupply (key : Key n) (S : Supply n) (adj : AdjMatrix n) (χ : Colouring n) :
    selColourC key (ofSupply S) adj χ = selColour key S adj χ := rfl

theorem selColourC_spec {key : Key n} {S : CellSupply n} {adj : AdjMatrix n} {χ : Colouring n}
    {c : Nat} (h : selColourC key S adj χ = some c) :
    c ∈ nonSingletonColours χ ∧ (cellNarrowC key S adj χ c).length ≤ 1 := by
  unfold selColourC at h
  have := Finset.mem_filter.mp (Finset.mem_of_min h)
  exact ⟨this.1, by simpa using this.2⟩

/-- The per-cell probe bill: each cell now pays for its own supply evaluation and its own orbit BFS.
Cells partition the vertex set, so `Σ_c m_c² ≤ n²` and the family together still fits the flat charge
a single node-global harvest already bills. -/
def selProbeCostC (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) : Nat :=
  ((nsColours χ).map (fun c =>
    Consume.supplyCost (S c) adj χ + (gens (S c) adj χ).length * (n * n)
      + ((cellList χ c).map (keyCost key adj χ)).sum + n * n
      + (cellList χ c).length * ((verified (S c) adj χ).length * (n * n) + n * n))).sum

/-- **★ THE CELL-INDEXED FUSED NODE RESOLVER.** Same decision procedure as `selNode` — probe the
non-singleton cells, commit to the least that narrows to `≤ 1`, `[]` = the true mutual stall — with
each cell judged by its own generators. -/
def selNodeC (rf : Refiner n) (key : Key n) (S : CellSupply n) : NodeRes n := fun adj χ =>
  match selColourC key S adj χ with
  | none => ([], selProbeCostC key S adj χ)
  | some c =>
      let kept := cellNarrowC key S adj χ c
      (kept.map (fun v => (v, refineV rf adj (indivOne χ v))),
       selProbeCostC key S adj χ + (kept.map (fun v => (rf adj (indivOne χ v)).2)).sum)

theorem selNodeC_children_none {rf : Refiner n} {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} (h : selColourC key S adj χ = none) : (selNodeC rf key S adj χ).1 = [] := by
  unfold selNodeC; rw [h]

theorem selNodeC_children_some {rf : Refiner n} {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} {c : Nat} (h : selColourC key S adj χ = some c) :
    (selNodeC rf key S adj χ).1
      = (cellNarrowC key S adj χ c).map (fun v => (v, refineV rf adj (indivOne χ v))) := by
  unfold selNodeC; rw [h]

/-- **`NodeProper`, for the cell-indexed instance**: every child individualizes a vertex with a
same-coloured partner. The committed colour is non-singleton and `cellNarrowC` stays inside its
cell — both facts inherited from `SelectNode` at `S c`. -/
theorem nodeProper_selNodeC (rf : Refiner n) (key : Key n) (S : CellSupply n) :
    NodeProper rf (selNodeC rf key S) := by
  intro adj χ vc hvc
  cases h : selColourC key S adj χ with
  | none => rw [selNodeC_children_none h] at hvc; exact absurd hvc (List.not_mem_nil)
  | some c =>
      rw [selNodeC_children_some h] at hvc
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hvc
      exact ⟨exists_partner_of_mem_cellList (selColourC_spec h).1 (cellNarrow_subset hv), rfl⟩

/-! ## 2. ★★★ THE HYPOTHESIS THAT REPLACES `SupplyEquivariant`

The *only* thing `①` reads from the supply is the number of orbits meeting each cell. So the only
thing that has to transport is the orbit relation, **at pairs inside a cell**. -/

/-- **Per-cell orbit transport.** Strictly weaker than `SupplyEquivariant`: it says nothing about
*which* generators are emitted, only that the relation they induce **inside each cell** is a
relabelling invariant. A guarded cell-anchored supply satisfies it with no equivariance at all. -/
def CellOrbitTransport (S : CellSupply n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) {a b : Fin n},
    a ∈ cellList χ c → b ∈ cellList χ c →
      (WordReach (verified (S c) (relabelAdj σ adj) (transportColouring σ χ)) (σ a) (σ b)
        ↔ WordReach (verified (S c) adj χ) a b)

/-- **Nothing regresses**: a cell-agnostic equivariant supply satisfies the new hypothesis, by the
same conjugation argument `cellNarrow_length_transport` already ran. -/
theorem cellOrbitTransport_ofSupply {S : Supply n} (hS : SupplyEquivariant S) :
    CellOrbitTransport (ofSupply S) := by
  intro σ adj χ _c _a _b _ha _hb
  exact SupplyTransport.wordReach_conj_iff (fun g => hS σ adj χ g)

/-- **The `SameOrbits` route to a transporting relation** — the shape
`Deepen.cellOrbitTransport_append` asks of its left factor, and the only route open to a supply that
is not `GensEquivariant`. `kernelSupply` (hence the whole record supply) enters here: its Gaussian
basis is pivot-order dependent, but its *orbits* match an equivariant set-level reference
(`Kernel.sameOrbits_recordSupply`), and the relation is all `①` reads. -/
theorem wordReach_transport_of_sameOrbits {Sref S : Supply n}
    (hso : OrbitPrune.SameOrbits Sref S) (hE : SupplyEquivariant Sref)
    (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (a b : Fin n) :
    WordReach (verified S (relabelAdj σ adj) (transportColouring σ χ)) (σ a) (σ b)
      ↔ WordReach (verified S adj χ) a b := by
  rw [← hso _ _ _ _, ← hso _ _ _ _]
  exact SupplyTransport.wordReach_conj_iff (fun g => hE σ adj χ g)

/-- The cell-agnostic instance, for symmetry with `cellOrbitTransport_ofSupply`. -/
theorem cellOrbitTransport_ofSupply_of_sameOrbits {Sref S : Supply n}
    (hso : OrbitPrune.SameOrbits Sref S) (hE : SupplyEquivariant Sref) :
    CellOrbitTransport (ofSupply S) :=
  fun σ adj χ _c _a _b _ha _hb => wordReach_transport_of_sameOrbits hso hE σ adj χ _a _b

/-- **★★ THE PER-CELL ORBIT COUNT TRANSPORTS** — `cellNarrow_length_transport` with
`SupplyEquivariant` replaced by `CellOrbitTransport`. The proof is the original's; the hypothesis is
consumed at exactly the same place, and the `keepMin` members it is applied to are inside the cell
(`keepMin_subset`), which is why the weaker per-cell form suffices. -/
theorem cellNarrowC_length_transport {key : Key n} (hk : KeyEquivariant key) {S : CellSupply n}
    (hS : CellOrbitTransport S) (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n)
    (c : Nat) :
    (cellNarrowC key S (relabelAdj σ adj) (transportColouring σ χ) c).length
      = (cellNarrowC key S adj χ c).length := by
  unfold cellNarrowC cellNarrow cellNarrowV
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
  intro a ha b hb
  have ha' : a ∈ cellList χ c := keepMin_subset (List.mem_toFinset.mp ha)
  have hb' : b ∈ cellList χ c := keepMin_subset (List.mem_toFinset.mp hb)
  show rep (verified (S c) (relabelAdj σ adj) (transportColouring σ χ)) (σ a)
      = rep (verified (S c) (relabelAdj σ adj) (transportColouring σ χ)) (σ b)
    ↔ rep (verified (S c) adj χ) a = rep (verified (S c) adj χ) b
  rw [Consume.rep_eq_iff_wordReach, Consume.rep_eq_iff_wordReach]
  exact hS σ adj χ c ha' hb'

/-- **★ THE CHOSEN COLOUR TRANSPORTS AS A VALUE.** The cell *order* is invariant because colour
values are (`nonSingletonColours_transport`), and each cell's verdict is invariant by §2 — which is
exactly the architecture's own reading: run the resolver on a cell, move to the next if it does not
fire, and both the sequence and each verdict are labelling-independent. -/
theorem selColourC_transport {key : Key n} (hk : KeyEquivariant key) {S : CellSupply n}
    (hS : CellOrbitTransport S) (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) :
    selColourC key S (relabelAdj σ adj) (transportColouring σ χ) = selColourC key S adj χ := by
  unfold selColourC
  rw [nonSingletonColours_transport σ χ]
  congr 1
  apply Finset.filter_congr
  intro c _
  rw [cellNarrowC_length_transport hk hS σ adj χ c]

/-! ## 3. ★★★ THE NODE CONTRACT, AND THE CANONIZER

`nodeTransport_selNode`'s proof, with `selColour_transport` replaced by §2's version. Everything
after the colour is committed is supply-free — `aggregate_cellNarrow_eq` at `S c` reduces both sides
to `keepMin key adj χ (cellList χ c)`, matched by `KeyEquivariant` alone. -/

theorem nodeTransport_selNodeC {rf : Refiner n} (hre : RefineEquivariant rf) {key : Key n}
    (hk : KeyEquivariant key) {S : CellSupply n} (hS : CellOrbitTransport S) :
    NodeTransport (selNodeC rf key S) := by
  intro fuel ih adj σ χ _hd
  cases hsel : selColourC key S adj χ with
  | none =>
      rw [selNodeC_children_none hsel,
        selNodeC_children_none (by rw [selColourC_transport hk hS σ adj χ]; exact hsel)]
      rfl
  | some c =>
      have hsel' : selColourC key S (relabelAdj σ adj) (transportColouring σ χ) = some c := by
        rw [selColourC_transport hk hS σ adj χ]; exact hsel
      rw [selNodeC_children_some hsel, selNodeC_children_some hsel', List.map_map, List.map_map]
      simp only [Function.comp_def]
      have hval : ∀ b : Fin n,
          (descendS (selNodeC rf key S) adj fuel
              (refineV rf adj (indivOne χ (rep (verified (S c) adj χ) b)))).1
            = (descendS (selNodeC rf key S) adj fuel (refineV rf adj (indivOne χ b))).1 := by
        intro b
        obtain ⟨α, hα, hαb⟩ := Consume.reach_rep (G := verified (S c) adj χ)
          (fun _ hg => Consume.isColAut_of_mem_verified hg) b
        rw [← hαb]
        exact branchValS_eq_of_isColAut hre ih adj χ hα b
      have hval' : ∀ b : Fin n,
          (descendS (selNodeC rf key S) (relabelAdj σ adj) fuel
              (refineV rf (relabelAdj σ adj) (indivOne (transportColouring σ χ)
                (rep (verified (S c) (relabelAdj σ adj) (transportColouring σ χ)) b)))).1
            = (descendS (selNodeC rf key S) (relabelAdj σ adj) fuel
              (refineV rf (relabelAdj σ adj) (indivOne (transportColouring σ χ) b))).1 := by
        intro b
        obtain ⟨α, hα, hαb⟩ := Consume.reach_rep
          (G := verified (S c) (relabelAdj σ adj) (transportColouring σ χ))
          (fun _ hg => Consume.isColAut_of_mem_verified hg) b
        rw [← hαb]
        exact branchValS_eq_of_isColAut hre ih (relabelAdj σ adj) (transportColouring σ χ) hα b
      refine (aggregate_cellNarrow_eq hk (S c) (relabelAdj σ adj) (transportColouring σ χ) c
          (f := fun v => (descendS (selNodeC rf key S) (relabelAdj σ adj) fuel
            (refineV rf (relabelAdj σ adj) (indivOne (transportColouring σ χ) v))).1)
          hval').trans
        (Eq.trans ?_ (aggregate_cellNarrow_eq hk (S c) adj χ c
          (f := fun v => (descendS (selNodeC rf key S) adj fuel
            (refineV rf adj (indivOne χ v))).1) hval).symm)
      refine aggregate_perm
        (((keepMin_transport_perm hk σ adj χ (cellList_transport_perm σ χ c)).map _).trans ?_)
      rw [List.map_map]
      exact List.Perm.of_eq
        (List.map_congr_left (fun v _ => branchValS_transport hre ih adj σ χ v))

/-- **★★★ THE CELL-INDEXED FUSED CANONIZER** — `①a`/`①b`/`①c`, from `KeyEquivariant` plus per-cell
orbit transport. **No `SupplyEquivariant` anywhere**, which is what lets a pair-anchored supply enter
the fused object at all. -/
theorem selNodeC_canonizer {key : Key n} (hk : KeyEquivariant key) {S : CellSupply n}
    (hS : CellOrbitTransport S) :
    CanonSpec.IsCanonicalFormOpt
      (canonFormS? (Refine.encodeFreeFast (n := n))
        (selNodeC (Refine.encodeFreeFast (n := n)) key S)) :=
  isCanonicalFormOptS_canonFormS? Refine.refineEquivariant_encodeFreeFast
    (nodeTransport_selNodeC Refine.refineEquivariant_encodeFreeFast hk hS)

/-- Sanity: at a cell-agnostic equivariant supply the new capstone reproduces the old one, so the
generalization is conservative. -/
theorem selNodeC_canonizer_ofSupply {key : Key n} (hk : KeyEquivariant key) {S : Supply n}
    (hS : SupplyEquivariant S) :
    CanonSpec.IsCanonicalFormOpt
      (canonFormS? (Refine.encodeFreeFast (n := n))
        (selNodeC (Refine.encodeFreeFast (n := n)) key (ofSupply S))) :=
  selNodeC_canonizer hk (cellOrbitTransport_ofSupply hS)

/-! ## 4. ★★ THE STALL, THE RESIDUE, AND TOTALITY — `SelectNode` §9–§10 at the cell-indexed object

⚠ **These are NOT inherited.** `Select.lean`'s spine is resolver-generic, so `descendS` /
`canonFormS?` / `isCanonicalFormOptS_canonFormS?` / `descentCostS_le_of_le_one` /
`descendS_ne_none_reaches` apply to `selNodeC` verbatim — but `HandledS`, `answersS_of_handledS`
and `not_handledS_if_flagS` are stated at **`selNode`**, so `③` does not transfer by rewriting. This
section is the mirror; every proof is `SelectNode`'s with `cellNarrow key S` read as
`cellNarrowC key S` (definitionally `cellNarrow key (S c)`, so the per-cell lemmas apply as they
stand).

★ The one genuinely new thing is what `NodeResolvedC` *means*: "some cell narrows to `≤ 1` **on its
own evidence**". At `ofSupply` it is `NodeResolved`; at a cell-anchored supply it is strictly the
per-cell claim, which is the whole point of design `B`. -/

/-- The flag fires only at a true mutual stall: NO non-singleton cell narrows to `≤ 1` on its own
generators. -/
theorem selColourC_none {key : Key n} {S : CellSupply n} {adj : AdjMatrix n} {χ : Colouring n}
    (h : selColourC key S adj χ = none) :
    ∀ c ∈ nonSingletonColours χ, ¬ (cellNarrowC key S adj χ c).length ≤ 1 := by
  intro c hc hlen
  have hmem : c ∈ (nonSingletonColours χ).filter
      (fun c => (cellNarrowC key S adj χ c).length ≤ 1) :=
    Finset.mem_filter.mpr ⟨hc, by simpa using hlen⟩
  unfold selColourC at h
  have hemp : (nonSingletonColours χ).filter
      (fun c => (cellNarrowC key S adj χ c).length ≤ 1) = ∅ := Finset.min_eq_top.mp h
  rw [hemp] at hmem
  exact absurd hmem (Finset.notMem_empty c)

/-- **Fan-out `≤ 1` by construction** — a cell is committed to only after it narrowed to `≤ 1`. This
is what makes the descent a single path of `≤ n + 1` nodes, and it carries no hypothesis. -/
theorem selNodeC_children_length_le_one (rf : Refiner n) (key : Key n) (S : CellSupply n)
    (adj : AdjMatrix n) (χ : Colouring n) : (selNodeC rf key S adj χ).1.length ≤ 1 := by
  cases h : selColourC key S adj χ with
  | none => rw [selNodeC_children_none h]; simp
  | some c =>
      rw [selNodeC_children_some h, List.length_map]
      exact (selColourC_spec h).2

/-- **★ THE FLAG SEMANTICS**, as a characterization: the cell-indexed resolver emits no child **iff**
no non-singleton cell narrows to `≤ 1` against its own generators. -/
theorem selNodeC_stall_iff {rf : Refiner n} {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} :
    (selNodeC rf key S adj χ).1 = []
      ↔ ∀ c ∈ nonSingletonColours χ, 1 < (cellNarrowC key S adj χ c).length := by
  constructor
  · intro h c hc
    cases hsel : selColourC key S adj χ with
    | none => exact Nat.not_le.mp (selColourC_none hsel c hc)
    | some c' =>
        rw [selNodeC_children_some hsel] at h
        exact absurd (List.map_eq_nil_iff.mp h) (cellNarrow_ne_nil (selColourC_spec hsel).1)
  · intro hall
    cases hsel : selColourC key S adj χ with
    | none => exact selNodeC_children_none hsel
    | some c' =>
        have h1 := (selColourC_spec hsel).2
        have h2 := hall c' (selColourC_spec hsel).1
        omega

/-- **The cell-indexed capability predicate, per node**: SOME non-singleton cell narrows to `≤ 1`
**on the evidence of descents anchored in that cell**. -/
def NodeResolvedC (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∃ c ∈ nonSingletonColours χ, (cellNarrowC key S adj χ c).length ≤ 1

/-- The cell-indexed capability predicate: every reached non-discrete node has a resolvable cell. -/
def HandledSC (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) : Prop :=
  ∀ χ : Colouring n, Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ → ¬ Discrete χ →
    NodeResolvedC key S adj χ

theorem nodeResolvedC_ofSupply {key : Key n} {S : Supply n} {adj : AdjMatrix n} {χ : Colouring n} :
    NodeResolvedC key (ofSupply S) adj χ ↔ NodeResolved key S adj χ := Iff.rfl

theorem handledSC_ofSupply {key : Key n} {S : Supply n} {adj : AdjMatrix n} :
    HandledSC key (ofSupply S) adj ↔ HandledS key S adj := Iff.rfl

/-- A `NodeResolvedC` node is never a stall. -/
theorem selNodeC_ne_nil_of_nodeResolvedC {rf : Refiner n} {key : Key n} {S : CellSupply n}
    {adj : AdjMatrix n} {χ : Colouring n} (h : NodeResolvedC key S adj χ) :
    (selNodeC rf key S adj χ).1 ≠ [] := by
  obtain ⟨c, hc, hres⟩ := h
  intro hnil
  have := selNodeC_stall_iff.mp hnil c hc
  omega

/-- **★★ THE ANSWERS THEOREM** for the cell-indexed object — no flag on a `HandledSC` graph.
`descendS_ne_none_reaches` is resolver-generic and `nodeProper_selNodeC` was proved in §1, so the
only new ingredient is the stall characterization above. -/
theorem answersSC_of_handledSC {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    (h : HandledSC key S adj) :
    canonFormS? (Refine.encodeFreeFast (n := n))
      (selNodeC (Refine.encodeFreeFast (n := n)) key S) adj ≠ none := by
  unfold canonFormS?
  refine descendS_ne_none_reaches Refine.refineSplits_encodeFreeFast
    (nodeProper_selNodeC _ _ _)
    (fun χ hr hd => selNodeC_ne_nil_of_nodeResolvedC (h χ hr hd)) n _ Descend.Reaches.root ?_
  have := Nat.zero_le (ncol (refineV (Refine.encodeFreeFast (n := n)) adj (fun _ => 0)))
  omega

/-- **`③`'s SHAPE for the cell-indexed object**: the flag names the cell-indexed residue. -/
theorem not_handledSC_if_flagSC {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    (hflag : canonFormS? (Refine.encodeFreeFast (n := n))
      (selNodeC (Refine.encodeFreeFast (n := n)) key S) adj = none) :
    ¬ HandledSC key S adj :=
  fun h => answersSC_of_handledSC h hflag

/-! ## 5. `②` — the per-node bill at the cell-indexed object (plan `W-h`)

⚠ **Also NOT inherited.** `SelectNode` §11's chain is `selNode`-specific at every step except
`descentCostS_le_of_le_one`, which is generic and is reused verbatim below. This section mirrors
`selNode_cost_none/some/le` and `selProbeCost_le`.

★ **The one real difference is where the supply is billed.** `selProbeCost` evaluates one node-global
supply and charges `supplyCost S + |gens S| · n²` **once**; `selProbeCostC` charges each cell for its
own supply, so those two terms move *inside* the per-cell sum and pick up a factor `≤ n`:

```
selProbeBound  n sB gB kc = sB + gB·n² + n·(n·kc + n² + n·(gB·n² + n²))
selProbeBoundC n sB gB kc = n·(sB + gB·n² +  n·kc + n² + n·(gB·n² + n²))
```

That is an honest extra factor of `n` on the supply terms, not an artefact — cell `c` really does
evaluate `S c`. ⚠ It is also why the runnable twin (plan `W-i`) matters: the *proof* is fine either
way, but the object as written re-harvests per probed cell. -/

theorem selNodeC_cost_none {rf : Refiner n} {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} (h : selColourC key S adj χ = none) :
    (selNodeC rf key S adj χ).2 = selProbeCostC key S adj χ := by
  unfold selNodeC; rw [h]

theorem selNodeC_cost_some {rf : Refiner n} {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} {c : Nat} (h : selColourC key S adj χ = some c) :
    (selNodeC rf key S adj χ).2
      = selProbeCostC key S adj χ
        + ((cellNarrowC key S adj χ c).map (fun v => (rf adj (indivOne χ v)).2)).sum := by
  unfold selNodeC; rw [h]

/-- The per-node bill: the probe, plus at most ONE child refinement (the committed cell narrowed to
`≤ 1`, so there is at most one child to refine). -/
theorem selNodeC_cost_le {rf : Refiner n} {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} {cP cr : Nat} (hp : selProbeCostC key S adj χ ≤ cP)
    (hr : ∀ χ' : Colouring n, (rf adj χ').2 ≤ cr) :
    (selNodeC rf key S adj χ).2 ≤ cP + cr := by
  cases hsel : selColourC key S adj χ with
  | none => rw [selNodeC_cost_none hsel]; omega
  | some c =>
      rw [selNodeC_cost_some hsel]
      have hlen := (selColourC_spec hsel).2
      rcases hk : cellNarrowC key S adj χ c with _ | ⟨v, t⟩
      · simp only [List.map_nil, List.sum_nil]; omega
      · rw [hk] at hlen
        simp only [List.length_cons] at hlen
        have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst ht
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        have := hr (indivOne χ v)
        omega

/-- The cell-indexed probe budget: `≤ n` cells, each paying for **its own** supply evaluation
(`sB`), its own candidate filter (`gB · n²`), one key evaluation per member and one orbit BFS per
member. -/
def selProbeBoundC (n sB gB kc : Nat) : Nat :=
  n * (sB + gB * (n * n) + (n * kc + n * n + n * (gB * (n * n) + n * n)))

theorem selProbeCostC_le {key : Key n} {S : CellSupply n} {adj : AdjMatrix n} {χ : Colouring n}
    {sB gB kc : Nat} (hs : ∀ c : Nat, Consume.supplyCost (S c) adj χ ≤ sB)
    (hg : ∀ c : Nat, (gens (S c) adj χ).length ≤ gB)
    (hk : ∀ v : Fin n, keyCost key adj χ v ≤ kc) :
    selProbeCostC key S adj χ ≤ selProbeBoundC n sB gB kc := by
  unfold selProbeCostC selProbeBoundC
  have hterm : ∀ x ∈ (nsColours χ).map (fun c =>
      Consume.supplyCost (S c) adj χ + (gens (S c) adj χ).length * (n * n)
        + ((cellList χ c).map (keyCost key adj χ)).sum + n * n
        + (cellList χ c).length * ((verified (S c) adj χ).length * (n * n) + n * n)),
      x ≤ sB + gB * (n * n) + (n * kc + n * n + n * (gB * (n * n) + n * n)) := by
    intro x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    have hver : (verified (S c) adj χ).length ≤ gB :=
      le_trans (List.length_filter_le _ _) (hg c)
    have h0 : Consume.supplyCost (S c) adj χ ≤ sB := hs c
    have hg2 : (gens (S c) adj χ).length * (n * n) ≤ gB * (n * n) :=
      Nat.mul_le_mul_right (n * n) (hg c)
    have h1 : ((cellList χ c).map (keyCost key adj χ)).sum ≤ n * kc := by
      refine le_trans (List.sum_le_card_nsmul _ kc ?_) ?_
      · intro y hy
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
        exact hk v
      · rw [List.length_map, smul_eq_mul]
        exact Nat.mul_le_mul_right kc (cellList_length_le χ c)
    have h2 : (cellList χ c).length * ((verified (S c) adj χ).length * (n * n) + n * n)
        ≤ n * (gB * (n * n) + n * n) :=
      Nat.mul_le_mul (cellList_length_le χ c)
        (Nat.add_le_add (Nat.mul_le_mul_right (n * n) hver) le_rfl)
    omega
  have hsum := List.sum_le_card_nsmul _ _ hterm
  rw [List.length_map, smul_eq_mul] at hsum
  exact le_trans hsum (Nat.mul_le_mul_right _ (nsColours_length_le χ))

/-- **★★ `②`, PARAMETRIC, AT THE CELL-INDEXED OBJECT.** Fan-out `≤ 1` holds by construction
(`selNodeC_children_length_le_one`), so — exactly as at `selNode` — this carries **no firing
hypothesis**: it bounds answer and flag alike. -/
theorem descentCostS_selNodeC_le {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {sB gB kc : Nat} (hs : ∀ (c : Nat) (χ : Colouring n), Consume.supplyCost (S c) adj χ ≤ sB)
    (hg : ∀ (c : Nat) (χ : Colouring n), (gens (S c) adj χ).length ≤ gB)
    (hk : ∀ (χ : Colouring n) (v : Fin n), keyCost key adj χ v ≤ kc) :
    descentCostS (Refine.encodeFreeFast (n := n))
        (selNodeC (Refine.encodeFreeFast (n := n)) key S) adj
      ≤ n * n * n + (n + 1) * (1 + (selProbeBoundC n sB gB kc + n * n * n)) := by
  refine descentCostS_le_of_le_one
    (fun χ _ => selNodeC_children_length_le_one _ _ _ adj χ)
    (fun χ => le_of_eq (Cost.refiner_cost adj χ)) (fun χ => ?_)
  refine selNodeC_cost_le
    (selProbeCostC_le (fun c => hs c χ) (fun c => hg c χ) (fun v => hk χ v)) ?_
  exact fun χ' => le_of_eq (Cost.refiner_cost adj χ')

/-! ## 6. `W-i` — THE RUNNABLE TWIN

`selNodeC` is the **slow** shape, and both standing traps are live in it:

* **trap #1** — it stores a generic `refineV rf adj (indivOne χ v)`, which compiles as a partial
  application whose body re-runs the refinement on *every* colour lookup (≈ 30 ms at `n = 14`;
  `SelectNode` §5's note on `selNodeFast` records this hanging the fused descent);
* **trap #2** — it evaluates `S c adj χ` **three** times per cell: once inside `selProbeCostC`, once
  inside `selColourC`'s filter, and once more for the committed cell.

`selNodeFast` cures both for the node-global object by binding `sv := S adj χ` once and inlining the
probe bill. The cell-indexed analogue needs a **table** rather than a single binding, which is the
one place where the twin is *not* `rfl`: `verOf` agrees with `verified (S ·)` only on
`nsColours χ`, so `selNodeFastC_eq` is a proved equation instead of a definitional one. Every
capstone transfers by rewriting with it, exactly as `selNodeFast_eq` is used.

★ After this the twin re-computes only what `selNodeFast` also re-computes (`cellNarrowV` for the
committed cell) — i.e. it is at parity with the node-global runnable object, per cell. -/

/-- One cell's probe data: `(colour, gens, verified gens, supply cost)`. -/
abbrev CellProbe (n : Nat) :=
  Nat × List (Equiv.Perm (Fin n)) × List (Equiv.Perm (Fin n)) × Nat

/-- **The shared per-cell table** — every cell's supply evaluated **once** per node. This is the
cell-indexed analogue of `selNodeFast`'s `let sv := S adj χ`. -/
def cellData (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) : List (CellProbe n) :=
  (nsColours χ).map (fun c =>
    let sv := S c adj χ
    (c, sv.1, sv.1.filter (fun g => decide (Consume.IsColAut adj χ g)), sv.2))

/-- Read a cell's verified list off the table. Direct recursion rather than `List.find?` so the
agreement lemma is a three-line induction. -/
def verOf : List (CellProbe n) → Nat → List (Equiv.Perm (Fin n))
  | [], _ => []
  | d :: t, c => if d.1 = c then d.2.2.1 else verOf t c

private theorem verOf_map (f : Nat → CellProbe n) (hf : ∀ c, (f c).1 = c) :
    ∀ (l : List Nat) {c : Nat}, c ∈ l → verOf (l.map f) c = (f c).2.2.1 := by
  intro l
  induction l with
  | nil => intro c hc; exact absurd hc (List.not_mem_nil)
  | cons x xs ih =>
      intro c hc
      by_cases hx : x = c
      · subst hx; simp [verOf, hf]
      · rw [List.map_cons, verOf, if_neg (by rw [hf]; exact hx)]
        exact ih (by rcases List.mem_cons.mp hc with h | h; exacts [absurd h.symm hx, h])

/-- **The table agrees with the supply, on every cell the object ever probes.** ⚠ Off `nsColours χ`
it returns `[]`, which is why the twin is a proved equation and not `rfl`. -/
theorem verOf_cellData {S : CellSupply n} {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (hc : c ∈ nsColours χ) : verOf (cellData S adj χ) c = verified (S c) adj χ :=
  verOf_map _ (fun _ => rfl) (nsColours χ) hc

/-- The selector against the shared table. -/
def selColourT (key : Key n) (t : List (CellProbe n)) (adj : AdjMatrix n) (χ : Colouring n) :
    Option Nat :=
  ((nonSingletonColours χ).filter (fun c => (cellNarrowV key (verOf t c) adj χ c).length ≤ 1)).min

theorem selColourT_cellData (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) :
    selColourT key (cellData S adj χ) adj χ = selColourC key S adj χ := by
  unfold selColourT selColourC
  congr 1
  refine Finset.filter_congr (fun c hc => ?_)
  rw [verOf_cellData ((mem_nsColours_iff χ c).mpr hc)]
  rfl

/-- **★★ THE RUNNABLE CELL-INDEXED RESOLVER.** Each cell's supply is evaluated **once** (`cellData`),
the probe bill is read off the same table, and the children's colourings are built through
`Refine.ColData` so each refinement is forced exactly once. -/
def selNodeFastC (key : Key n) (S : CellSupply n) : NodeRes n := fun adj χ =>
  let t := cellData S adj χ
  let pc := (t.map (fun d =>
    d.2.2.2 + d.2.1.length * (n * n)
      + ((cellList χ d.1).map (keyCost key adj χ)).sum + n * n
      + (cellList χ d.1).length * (d.2.2.1.length * (n * n) + n * n))).sum
  match selColourT key t adj χ with
  | none => ([], pc)
  | some c =>
      let kept := cellNarrowV key (verOf t c) adj χ c
      (kept.map (fun v => (v, (Refine.warmRefineVec adj (indivOne χ v)).col)),
       pc + (kept.map (fun _ => CostModel.WarmRefine.warmRefineCost n)).sum)

/-- The shared table reproduces the probe bill exactly — `cellData` is a `map` over the same
`nsColours χ`, and each summand is the `selProbeCostC` summand definitionally. -/
theorem cellData_probeCost (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) :
    ((cellData S adj χ).map (fun d =>
      d.2.2.2 + d.2.1.length * (n * n)
        + ((cellList χ d.1).map (keyCost key adj χ)).sum + n * n
        + (cellList χ d.1).length * (d.2.2.1.length * (n * n) + n * n))).sum
      = selProbeCostC key S adj χ := by
  unfold cellData selProbeCostC
  rw [List.map_map]
  rfl

/-- **★★★ THE RUNNABLE RESOLVER *IS* THE REASONED-ABOUT ONE.** ⚠ A theorem, not `rfl` — see §6's
note. Rewriting with it carries `selNodeC_canonizer`, `descentCostS_selNodeC_le`,
`answersSC_of_handledSC` and `not_handledSC_if_flagSC` onto the runnable object verbatim. -/
theorem selNodeFastC_eq (key : Key n) (S : CellSupply n) :
    selNodeFastC key S = selNodeC (Refine.encodeFreeFast (n := n)) key S := by
  funext adj χ
  show (match selColourT key (cellData S adj χ) adj χ with
        | none => ([], _)
        | some c => _) = _
  rw [selColourT_cellData key S adj χ]
  unfold selNodeC
  cases hsel : selColourC key S adj χ with
  | none => simpa using cellData_probeCost key S adj χ
  | some c =>
      have hver : verOf (cellData S adj χ) c = verified (S c) adj χ :=
        verOf_cellData ((mem_nsColours_iff χ c).mpr (selColourC_spec hsel).1)
      have hkept : cellNarrowV key (verOf (cellData S adj χ) c) adj χ c
          = cellNarrowC key S adj χ c := by rw [hver]; rfl
      simp only [hkept, cellData_probeCost key S adj χ]
      rfl

/-- **The runnable top-level object** (root colouring materialised once too). -/
def canonFormFastSC? (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) :
    Option (CanonSpec.Labelled n) :=
  (descendS (selNodeFastC key S) adj n ((Refine.warmRefineVec adj (fun _ => 0)).col)).1

theorem canonFormFastSC?_eq (key : Key n) (S : CellSupply n) :
    canonFormFastSC? key S
      = canonFormS? (Refine.encodeFreeFast (n := n))
          (selNodeC (Refine.encodeFreeFast (n := n)) key S) := by
  funext adj
  unfold canonFormFastSC?
  rw [selNodeFastC_eq]
  rfl

/-- …and its cost, likewise. -/
theorem descentCostSC_fast_eq (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) :
    descentCostS (Refine.encodeFreeFast (n := n)) (selNodeFastC key S) adj
      = descentCostS (Refine.encodeFreeFast (n := n))
          (selNodeC (Refine.encodeFreeFast (n := n)) key S) adj := by
  rw [selNodeFastC_eq]

/-! ## 7. `W-e` — LAZY BILLING

⛔ **A lazy *selector* buys nothing, and that is why this section exists.** `selProbeCostC` sums over
**all** of `nsColours χ`, and `selNodeFastC` builds the whole `cellData` table and its bill *before*
`selColourT` runs — so the returned **cost** already forces every cell's supply, and short-circuiting
the choice afterwards saves zero. Laziness has to reach the billing.

`probeWalk` walks the cells in increasing colour order, evaluating each cell's supply **on demand**,
accumulating that cell's bill, and stopping at the first cell that narrows to `≤ 1`. It therefore
returns a **smaller** cost than `selProbeCostC` and the **same** children.

★ That split is exactly what makes it cheap to justify: `NodeTransport`/`NodeTransportAt` are stated
purely on `.1` (`Select.lean` §3), so `descendS_val_congr` carries `①` across unchanged, and `②`
rides `probeWalk_snd_le` into the *existing* `selProbeCostC_le` — **no new numerals**.

⚠ Iteration order must be by **colour value**, because `selColourC` takes the `Finset.min`.
`nsColours χ` is `((List.finRange n).map χ).dedup.filter …` — first-occurrence order, **not sorted** —
so walking it would return the first *encountered* firing colour, not the least. We walk
`Finset.sort (· ≤ ·) (nonSingletonColours χ)` instead, which brings `Finset.pairwise_sort`,
`Finset.sort_nodup` and `Finset.mem_sort` with it. -/

/-- One cell's probe bill, named so the walk and `selProbeCostC` share a single expression. -/
def cellBill (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) :
    Nat :=
  Consume.supplyCost (S c) adj χ + (gens (S c) adj χ).length * (n * n)
    + ((cellList χ c).map (keyCost key adj χ)).sum + n * n
    + (cellList χ c).length * ((verified (S c) adj χ).length * (n * n) + n * n)

theorem selProbeCostC_eq_sum (key : Key n) (S : CellSupply n) (adj : AdjMatrix n)
    (χ : Colouring n) :
    selProbeCostC key S adj χ = ((nsColours χ).map (cellBill key S adj χ)).sum := rfl

/-- The per-cell firing test, as a `Bool` so `List.find?` can consume it. -/
def firesAt (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) :
    Bool :=
  decide ((cellNarrowC key S adj χ c).length ≤ 1)

/-- **★★ THE LAZY PROBE.** Walk the cells in increasing colour order; evaluate each cell's supply
once, on demand; bill it; stop at the first that narrows to `≤ 1`, returning that cell **and its
narrowing** so the committed cell is never re-probed. -/
def probeWalk (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) :
    List Nat → Option (Nat × List (Fin n)) × Nat
  | [] => (none, 0)
  | c :: cs =>
      let sv := S c adj χ
      let V := sv.1.filter (fun g => decide (Consume.IsColAut adj χ g))
      let kept := cellNarrowV key V adj χ c
      let bill := sv.2 + sv.1.length * (n * n)
        + ((cellList χ c).map (keyCost key adj χ)).sum + n * n
        + (cellList χ c).length * (V.length * (n * n) + n * n)
      if kept.length ≤ 1 then (some (c, kept), bill)
      else
        let r := probeWalk key S adj χ cs
        (r.1, bill + r.2)

/-- The walk finds exactly what `List.find?` would, and carries the committed cell's narrowing. -/
theorem probeWalk_fst (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) :
    ∀ l : List Nat, (probeWalk key S adj χ l).1
      = (l.find? (firesAt key S adj χ)).map (fun c => (c, cellNarrowC key S adj χ c)) := by
  intro l
  induction l with
  | nil => rfl
  | cons c cs ih =>
      simp only [probeWalk]
      split
      · rename_i h
        have hc : (cellNarrowC key S adj χ c).length ≤ 1 := h
        rw [List.find?_cons_of_pos (by simp [firesAt, hc])]
        rfl
      · rename_i h
        have hc : ¬ (cellNarrowC key S adj χ c).length ≤ 1 := h
        rw [List.find?_cons_of_neg (by simp [firesAt, hc])]
        exact ih

/-- The walk bills a **sub-sum**: only the cells it actually probed. -/
theorem probeWalk_snd_le (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) :
    ∀ l : List Nat, (probeWalk key S adj χ l).2 ≤ (l.map (cellBill key S adj χ)).sum := by
  intro l
  induction l with
  | nil => exact le_rfl
  | cons c cs ih =>
      rw [List.map_cons, List.sum_cons]
      simp only [probeWalk]
      split
      · exact Nat.le_add_right _ _
      · exact Nat.add_le_add_left ih _

/-! ### 7a. The two bridges: the walk's choice is `selColourC`, its bill is `≤ selProbeCostC` -/

/-- **★★ LEMMA A** — over a **sorted** list of a finset's elements, `List.find?` *is* `Finset.min` of
the filter. This is what licenses stopping at the first firing colour. -/
theorem find?_sort_eq_min (s : Finset Nat) (p : Nat → Bool) :
    (s.sort (· ≤ ·)).find? p = (s.filter (fun c => p c = true)).min := by
  cases h : (s.sort (· ≤ ·)).find? p with
  | none =>
      have hE : s.filter (fun c => p c = true) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro a ha
        exact List.find?_eq_none.mp h a ((Finset.mem_sort _).mpr ha)
      rw [hE]; rfl
  | some c =>
      obtain ⟨hpc, as, bs, hsplit, hbefore⟩ := List.find?_eq_some_iff_append.mp h
      have hcs : c ∈ s := (Finset.mem_sort (· ≤ ·)).mp (by rw [hsplit]; simp)
      have hcf : c ∈ s.filter (fun x => p x = true) := Finset.mem_filter.mpr ⟨hcs, hpc⟩
      have hpair : (as ++ c :: bs).Pairwise (· ≤ ·) := by
        rw [← hsplit]; exact Finset.pairwise_sort s _
      have htail : ∀ b ∈ bs, c ≤ b :=
        (List.pairwise_cons.mp (List.pairwise_append.mp hpair).2.1).1
      have hle : ∀ b ∈ s.filter (fun x => p x = true), (↑c : WithTop Nat) ≤ ↑b := by
        intro b hb
        refine (WithTop.coe_le_coe).mpr ?_
        obtain ⟨hbs, hpb⟩ := Finset.mem_filter.mp hb
        have hbl : b ∈ as ++ c :: bs := by
          rw [← hsplit]; exact (Finset.mem_sort _).mpr hbs
        rcases List.mem_append.mp hbl with hb1 | hb2
        · have hb' := hbefore b hb1
          simp only [Bool.not_eq_true'] at hb'
          rw [hb'] at hpb; exact absurd hpb (by simp)
        · rcases List.mem_cons.mp hb2 with rfl | hb3
          · exact le_rfl
          · exact htail b hb3
      show (↑c : WithTop Nat) = (s.filter (fun x => p x = true)).min
      exact le_antisymm (Finset.le_min hle) (Finset.min_le hcf)

/-- The sorted colour list is a permutation of `nsColours χ` — same members, both nodup. -/
theorem sort_nonSingletonColours_perm (χ : Colouring n) :
    ((nonSingletonColours χ).sort (· ≤ ·)).Perm (nsColours χ) := by
  refine List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup _ _) ?_ ?_
  · exact List.Nodup.filter _ (List.nodup_dedup _)
  · ext c
    simp only [List.mem_toFinset, Finset.mem_sort, mem_nsColours_iff]

theorem probeWalk_choice (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) :
    ((nonSingletonColours χ).sort (· ≤ ·)).find? (firesAt key S adj χ)
      = selColourC key S adj χ := by
  rw [find?_sort_eq_min]
  unfold selColourC
  congr 1
  refine Finset.filter_congr (fun c _ => ?_)
  simp [firesAt]

theorem probeWalk_bill_le (key : Key n) (S : CellSupply n) (adj : AdjMatrix n)
    (χ : Colouring n) :
    (probeWalk key S adj χ ((nonSingletonColours χ).sort (· ≤ ·))).2
      ≤ selProbeCostC key S adj χ := by
  refine le_trans (probeWalk_snd_le key S adj χ _) ?_
  rw [selProbeCostC_eq_sum]
  exact le_of_eq ((sort_nonSingletonColours_perm χ).map (cellBill key S adj χ)).sum_eq

/-! ### 7b. The lazy resolver -/

/-- **★★★ THE LAZY CELL-INDEXED RESOLVER.** Same children as `selNodeC`, strictly smaller bill: only
the cells actually probed are evaluated and charged. -/
def selNodeLazyC (key : Key n) (S : CellSupply n) : NodeRes n := fun adj χ =>
  match probeWalk key S adj χ ((nonSingletonColours χ).sort (· ≤ ·)) with
  | (none, pc) => ([], pc)
  | (some (_, kept), pc) =>
      (kept.map (fun v => (v, (Refine.warmRefineVec adj (indivOne χ v)).col)),
       pc + (kept.map (fun _ => CostModel.WarmRefine.warmRefineCost n)).sum)

/-- **★★ THE CHILDREN ARE UNCHANGED** — which, with `descendS_val_congr`, is all `①` needs. -/
theorem selNodeLazyC_children (key : Key n) (S : CellSupply n) (adj : AdjMatrix n)
    (χ : Colouring n) :
    (selNodeLazyC key S adj χ).1
      = (selNodeC (Refine.encodeFreeFast (n := n)) key S adj χ).1 := by
  unfold selNodeLazyC
  rw [show probeWalk key S adj χ ((nonSingletonColours χ).sort (· ≤ ·))
        = ((probeWalk key S adj χ ((nonSingletonColours χ).sort (· ≤ ·))).1,
           (probeWalk key S adj χ ((nonSingletonColours χ).sort (· ≤ ·))).2) from rfl,
    probeWalk_fst, probeWalk_choice]
  cases hsel : selColourC key S adj χ with
  | none => rw [selNodeC_children_none hsel]; rfl
  | some c => rw [selNodeC_children_some hsel]; rfl

/-- The lazy resolver's per-node bill: the probed cells, plus at most one child refinement. -/
theorem selNodeLazyC_cost_le {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} {cP cr : Nat} (hp : selProbeCostC key S adj χ ≤ cP)
    (hr : ∀ χ' : Colouring n, (Refine.encodeFreeFast (n := n) adj χ').2 ≤ cr) :
    (selNodeLazyC key S adj χ).2 ≤ cP + cr := by
  have hw : (probeWalk key S adj χ ((nonSingletonColours χ).sort (· ≤ ·))).2 ≤ cP :=
    le_trans (probeWalk_bill_le key S adj χ) hp
  have hlen : (selNodeLazyC key S adj χ).1.length ≤ 1 := by
    rw [selNodeLazyC_children]
    exact selNodeC_children_length_le_one _ _ _ adj χ
  unfold selNodeLazyC at hlen ⊢
  rcases hpw : probeWalk key S adj χ ((nonSingletonColours χ).sort (· ≤ ·)) with ⟨w1, pc⟩
  rw [hpw] at hw
  cases w1 with
  | none => simpa using le_trans hw (Nat.le_add_right _ _)
  | some ck =>
      obtain ⟨c, kept⟩ := ck
      rw [hpw] at hlen
      simp only [List.length_map] at hlen
      rcases hk : kept with _ | ⟨v, t⟩
      · simp
        omega
      · subst hk
        simp only [List.length_cons] at hlen
        have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst ht
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        have := hr (indivOne χ v)
        show pc + CostModel.WarmRefine.warmRefineCost n ≤ cP + cr
        have hwr : CostModel.WarmRefine.warmRefineCost n
            = (Refine.encodeFreeFast (n := n) adj (indivOne χ v)).2 := rfl
        omega

/-! ### 7c. `①` and `②` for the lazy resolver

**★★ LEMMA B is what makes `①` free.** `descendS`'s *value* projection reads the resolver only
through its children (`descendS_val_succ`), and `NodeTransport`/`NodeTransportAt` are stated purely
on that projection. So a resolver with the same `.1` and a smaller `.2` inherits the entire `①`
capstone by rewriting — no transport argument is re-run. -/

/-- **★★ LEMMA B** — `descendS`'s value depends on the resolver **only through its children**. -/
theorem descendS_val_congr {N₁ N₂ : NodeRes n} (h : ∀ adj χ, (N₁ adj χ).1 = (N₂ adj χ).1)
    (adj : AdjMatrix n) :
    ∀ (fuel : Nat) (χ : Colouring n),
      (descendS N₁ adj fuel χ).1 = (descendS N₂ adj fuel χ).1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro χ
      by_cases hd : Discrete χ
      · rw [descendS_val_leaf N₁ adj hd 0, descendS_val_leaf N₂ adj hd 0]
      · rw [descendS_val_zero N₁ adj hd, descendS_val_zero N₂ adj hd]
  | succ fuel ih =>
      intro χ
      by_cases hd : Discrete χ
      · rw [descendS_val_leaf N₁ adj hd (fuel + 1), descendS_val_leaf N₂ adj hd (fuel + 1)]
      · rw [descendS_val_succ N₁ adj hd fuel, descendS_val_succ N₂ adj hd fuel, h adj χ]
        congr 1
        exact List.map_congr_left (fun vc _ => ih vc.2)

theorem canonFormS?_congr {rf : Refiner n} {N₁ N₂ : NodeRes n}
    (h : ∀ adj χ, (N₁ adj χ).1 = (N₂ adj χ).1) : canonFormS? rf N₁ = canonFormS? rf N₂ := by
  funext adj
  exact descendS_val_congr h adj n _

/-- The lazy object computes the **same canonical form** as the eager one — so `①` and the flag
semantics carry across verbatim. -/
theorem canonFormS?_selNodeLazyC_eq (key : Key n) (S : CellSupply n) :
    canonFormS? (Refine.encodeFreeFast (n := n)) (selNodeLazyC key S)
      = canonFormS? (Refine.encodeFreeFast (n := n))
          (selNodeC (Refine.encodeFreeFast (n := n)) key S) :=
  canonFormS?_congr (fun adj χ => selNodeLazyC_children key S adj χ)

/-- **★★★ `①` FOR THE LAZY RESOLVER** — free from `selNodeC_canonizer`, via lemma B. -/
theorem selNodeLazyC_canonizer {key : Key n} (hk : KeyEquivariant key) {S : CellSupply n}
    (hS : CellOrbitTransport S) :
    CanonSpec.IsCanonicalFormOpt
      (canonFormS? (Refine.encodeFreeFast (n := n)) (selNodeLazyC key S)) := by
  rw [canonFormS?_selNodeLazyC_eq]
  exact selNodeC_canonizer hk hS

/-- **★★ `②` FOR THE LAZY RESOLVER** — the *same* bound as the eager one, reached through
`probeWalk_bill_le`, so there are **no new numerals**. The true cost is of course smaller; the point
is that the proved ceiling does not move. -/
theorem descentCostS_selNodeLazyC_le {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {sB gB kc : Nat} (hs : ∀ (c : Nat) (χ : Colouring n), Consume.supplyCost (S c) adj χ ≤ sB)
    (hg : ∀ (c : Nat) (χ : Colouring n), (gens (S c) adj χ).length ≤ gB)
    (hk : ∀ (χ : Colouring n) (v : Fin n), keyCost key adj χ v ≤ kc) :
    descentCostS (Refine.encodeFreeFast (n := n)) (selNodeLazyC key S) adj
      ≤ n * n * n + (n + 1) * (1 + (selProbeBoundC n sB gB kc + n * n * n)) := by
  refine descentCostS_le_of_le_one
    (fun χ _ => by
      rw [selNodeLazyC_children]; exact selNodeC_children_length_le_one _ _ _ adj χ)
    (fun χ => le_of_eq (Cost.refiner_cost adj χ)) (fun χ => ?_)
  exact selNodeLazyC_cost_le
    (selProbeCostC_le (fun c => hs c χ) (fun c => hg c χ) (fun v => hk χ v))
    (fun χ' => le_of_eq (Cost.refiner_cost adj χ'))

/-- **The runnable top-level lazy object** (root colouring materialised once too, as in
`canonFormFastSC?`). -/
def canonFormLazySC? (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) :
    Option (CanonSpec.Labelled n) :=
  (descendS (selNodeLazyC key S) adj n ((Refine.warmRefineVec adj (fun _ => 0)).col)).1

theorem canonFormLazySC?_eq (key : Key n) (S : CellSupply n) :
    canonFormLazySC? key S
      = canonFormS? (Refine.encodeFreeFast (n := n)) (selNodeLazyC key S) := rfl

/-- …and the residue statement, likewise unchanged. -/
theorem not_handledSC_if_flag_lazy {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    (hflag : canonFormS? (Refine.encodeFreeFast (n := n)) (selNodeLazyC key S) adj = none) :
    ¬ HandledSC key S adj := by
  rw [canonFormS?_selNodeLazyC_eq] at hflag
  exact not_handledSC_if_flagSC hflag

/-! ## 8. `W-j` — SHARE THE KEY, HOIST THE NODE-LEVEL SUPPLY FACTOR

⚠ **`W-e` reduced *how many* cells are probed; it did not touch what each probed cell costs.** Two
recomputations survive inside `probeWalk`, both instances of standing trap #2, and both measured:

1. **The key is evaluated three times per vertex.** The bill maps `keyCost key adj χ` over
   `cellList χ c`, and `cellNarrowV → Force.keepMin` evaluates `Force.keyV` twice more (`kmin?` over
   `B.map keyV`, then `B.filter (keyV · = m)`). `keyCost` and `keyV` are `.2` and `.1` of the **same
   strict pair**, so each of the three is a full key computation and nothing is shared.
2. **A node-level supply factor is re-harvested per probed cell.** The endgame supply is
   `fun c => recordSupplyFast ++ deepenCellSupply c`; only the right factor depends on `c`, yet
   `S c adj χ` evaluates both, and the `IsColAut` filter re-runs over the left factor's generators
   as well.

★ Neither is specific to the cell-indexed design — `selNode`/`selNodeFast` do (1) over **every**
cell. This section fixes both **without changing the bill**, so `②` is not an inequality but an
equation: `probeWalkH_eq` says the hoisted walk *is* `probeWalk` at the composed supply.

★★ Consequently every capstone transfers by `rw`, exactly as with `selNodeFastC_eq` — `①` through
`canonFormS?_selNodeLazyC_eq`, `②` through `descentCostS_selNodeLazyC_le`, `③` through
`not_handledSC_if_flagSC`. **No new numerals; `costConst`/`costDeg` do not move.**

**Measured** (`scratchpad/ProbeShareWalk.lean`, `ProbeShareWalk6.lean`, identical billed cost):
`C₅` 27.6 s → **20.7 s** (1.34×), `K₁,₂,₃` 74.4 s → **50.2 s** (1.48×). At one cell the win is
entirely (1); (2) starts paying from two cells and scales with the number of cells *probed*. -/

/-- **The key evaluated ONCE per vertex** — value and cost kept together, so the bill and the argmin
read the same computation instead of re-running it. -/
def keyTable (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) (B : List (Fin n)) :
    List (Fin n × List Nat × Nat) :=
  B.map (fun v => (v, key adj χ v))

/-- `Force.keepMin` read off the table: no further key evaluation. -/
def keepMinT (t : List (Fin n × List Nat × Nat)) : List (Fin n) :=
  match Force.kmin? (t.map (fun p => p.2.1)) with
  | none => t.map (fun p => p.1)
  | some m => (t.filter (fun p => decide (p.2.1 = m))).map (fun p => p.1)

/-- Filtering a table of `(v, f v)` pairs on the second component and projecting back is filtering
the original list — the one induction this section needs. -/
private theorem map_fst_pair {α : Type} (f : Fin n → α) :
    ∀ B : List (Fin n), (B.map (fun v => (v, f v))).map (fun q => q.1) = B := by
  intro B; induction B with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, ih]

private theorem map_filter_pair {α : Type} (f : Fin n → α) (p : α → Bool) :
    ∀ B : List (Fin n),
      ((B.map (fun v => (v, f v))).filter (fun q => p q.2)).map (fun q => q.1)
        = B.filter (fun v => p (f v)) := by
  intro B
  induction B with
  | nil => rfl
  | cons a t ih => by_cases h : p (f a) = true <;> simp [h, ih]

/-- **The table computes `keepMin`.** -/
theorem keepMinT_keyTable (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) (B : List (Fin n)) :
    keepMinT (keyTable key adj χ B) = keepMin key adj χ B := by
  have hmap : (keyTable key adj χ B).map (fun p => p.2.1) = B.map (Force.keyV key adj χ) := by
    simp only [keyTable, List.map_map]; rfl
  unfold keepMinT keepMin
  rw [hmap]
  cases Force.kmin? (B.map (Force.keyV key adj χ)) with
  | none =>
      show (keyTable key adj χ B).map (fun p => p.1) = B
      exact map_fst_pair (fun v => key adj χ v) B
  | some m =>
      show ((keyTable key adj χ B).filter (fun p => decide (p.2.1 = m))).map (fun p => p.1) = _
      exact map_filter_pair (fun v => key adj χ v) (fun a => decide (a.1 = m)) B

/-- …and the table's cost column is the bill's key term. -/
theorem keyTable_cost (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) (B : List (Fin n)) :
    ((keyTable key adj χ B).map (fun p => p.2.2)).sum = (B.map (keyCost key adj χ)).sum := by
  simp only [keyTable, List.map_map]; rfl

/-- **The supply splits into a node-level factor and a cell-level one.** Stated as a property rather
than as `Deck.appendSupply` so this file needs no new import; the endgame instance is `rfl`. -/
def SplitSupply (S : CellSupply n) (L : Supply n) (T : CellSupply n) : Prop :=
  ∀ (c : Nat) (adj : AdjMatrix n) (χ : Colouring n),
    S c adj χ = ((L adj χ).1 ++ (T c adj χ).1, (L adj χ).2 + (T c adj χ).2)

/-- **★★ THE HOISTED LAZY PROBE.** `Lc`/`Lgn`/`VL` are the node-level factor's cost, candidate count
and **verified** list, evaluated once per node by `selNodeLazyHC` and reused by every probed cell;
`keyTable` evaluates the key once per vertex. Same walk, same stopping rule, same bill. -/
def probeWalkH (key : Key n) (Lc Lgn : Nat) (VL : List (Equiv.Perm (Fin n)))
    (T : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) :
    List Nat → Option (Nat × List (Fin n)) × Nat
  | [] => (none, 0)
  | c :: cs =>
      let tv := T c adj χ
      let V := VL ++ tv.1.filter (fun g => decide (Consume.IsColAut adj χ g))
      let kt := keyTable key adj χ (cellList χ c)
      let kept := ((keepMinT kt).map (rep V)).dedup
      let bill := (Lc + tv.2) + (Lgn + tv.1.length) * (n * n)
        + (kt.map (fun p => p.2.2)).sum + n * n
        + (cellList χ c).length * (V.length * (n * n) + n * n)
      if kept.length ≤ 1 then (some (c, kept), bill)
      else
        let r := probeWalkH key Lc Lgn VL T adj χ cs
        (r.1, bill + r.2)

/-- **★★★ THE HOISTED WALK *IS* THE WALK** — both components, at the composed supply. Everything in
§7 therefore transfers by rewriting, with no inequality anywhere. -/
theorem probeWalkH_eq {S : CellSupply n} {L : Supply n} {T : CellSupply n} (hS : SplitSupply S L T)
    (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) :
    ∀ l : List Nat,
      probeWalkH key (Consume.supplyCost L adj χ) (gens L adj χ).length (verified L adj χ)
          T adj χ l
        = probeWalk key S adj χ l := by
  intro l
  induction l with
  | nil => rfl
  | cons c cs ih =>
      have hV : verified L adj χ ++ (T c adj χ).1.filter (fun g => decide (Consume.IsColAut adj χ g))
          = (S c adj χ).1.filter (fun g => decide (Consume.IsColAut adj χ g)) := by
        rw [hS c adj χ]
        exact (List.filter_append _ _).symm
      have hlen : (gens L adj χ).length + (T c adj χ).1.length = (S c adj χ).1.length := by
        rw [hS c adj χ]; exact List.length_append.symm
      have hcost : Consume.supplyCost L adj χ + (T c adj χ).2 = (S c adj χ).2 := by
        rw [hS c adj χ]; rfl
      simp only [probeWalkH, probeWalk, cellNarrowV, keepMinT_keyTable, keyTable_cost,
        hV, hlen, hcost, ih]

/-- **★★ THE HOISTED LAZY RESOLVER.** The node-level supply factor is harvested and verified **once
per node**; each probed cell adds only its own generators and one key pass. -/
def selNodeLazyHC (key : Key n) (L : Supply n) (T : CellSupply n) : NodeRes n := fun adj χ =>
  let lv := L adj χ
  let VL := lv.1.filter (fun g => decide (Consume.IsColAut adj χ g))
  match probeWalkH key lv.2 lv.1.length VL T adj χ ((nonSingletonColours χ).sort (· ≤ ·)) with
  | (none, pc) => ([], pc)
  | (some (_, kept), pc) =>
      (kept.map (fun v => (v, (Refine.warmRefineVec adj (indivOne χ v)).col)),
       pc + (kept.map (fun _ => CostModel.WarmRefine.warmRefineCost n)).sum)

theorem selNodeLazyHC_eq {S : CellSupply n} {L : Supply n} {T : CellSupply n}
    (hS : SplitSupply S L T) (key : Key n) : selNodeLazyHC key L T = selNodeLazyC key S := by
  funext adj χ
  show (match probeWalkH key (Consume.supplyCost L adj χ) (gens L adj χ).length
          (verified L adj χ) T adj χ ((nonSingletonColours χ).sort (· ≤ ·)) with
        | (none, pc) => ([], pc)
        | (some (_, kept), pc) => _) = _
  rw [probeWalkH_eq hS key adj χ]
  rfl

/-- **The runnable top-level hoisted object.** -/
def canonFormLazyHSC? (key : Key n) (L : Supply n) (T : CellSupply n) (adj : AdjMatrix n) :
    Option (CanonSpec.Labelled n) :=
  (descendS (selNodeLazyHC key L T) adj n ((Refine.warmRefineVec adj (fun _ => 0)).col)).1

theorem canonFormLazyHSC?_eq {S : CellSupply n} {L : Supply n} {T : CellSupply n}
    (hS : SplitSupply S L T) (key : Key n) :
    canonFormLazyHSC? key L T = canonFormLazySC? key S := by
  funext adj
  unfold canonFormLazyHSC? canonFormLazySC?
  rw [selNodeLazyHC_eq hS key]

/-- …and the cost, likewise an equation: `②`'s numerals do not move. -/
theorem descentCostS_selNodeLazyHC_eq {S : CellSupply n} {L : Supply n} {T : CellSupply n}
    (hS : SplitSupply S L T) (key : Key n) (adj : AdjMatrix n) :
    descentCostS (Refine.encodeFreeFast (n := n)) (selNodeLazyHC key L T) adj
      = descentCostS (Refine.encodeFreeFast (n := n)) (selNodeLazyC key S) adj := by
  rw [selNodeLazyHC_eq hS key]

/-! ## 9. `W2` STAGE 1 — THE SOCKET: `HandledSC` FROM **ONE** CELL PER NODE

The `③` population on record (`RecordDeepenCell.handledSC_of_tinhoferGraph`) reaches
`NodeResolvedC` through the **target** cell: `Select.cellNarrow_targetColour` rewrites the per-cell
narrowing into `Composite.narrow (forceThenConsume …)`, and `Consume.CellIsOrbit` is itself stated at
`Descend.branches χ`. That route is what `TinhoferGraph` can feed, because `SchurianAt` says *every*
cell is an orbit — so the target cell in particular.

**A CFI residue cannot feed it.** `probe_offbranch5` measures the per-cell guard open on
26/28, 26/28, 18/24, 22/26, 14/14, 10/10, 14/14 cells at depth-1 CFI nodes — most cells, not all, and
nothing pins the *target* cell to the open set. But `NodeResolvedC` only ever asked for **some**
non-singleton cell, and `selColourC` already takes the minimum over whichever cells fire. This
section removes the target-cell restriction from the sufficient condition, so a wider class can be
supplied without re-proving anything below.

★ **Widening the handled region is now: exhibit one cell per reached node.** That is the `SelectCell`
analogue of `TwinFamily.handledS_of_noRigidObstruction`, and it is deliberately CFI-free — no graph
family appears here.

⚠ It is a *sufficient* condition, not a characterization: a cell can also fire because the **key**
separates it, which `cellNarrowC` applies first. `SomeCellOrbit` is the supply-side half only. -/

/-- **The per-cell orbit condition, at an ARBITRARY cell.** `Consume.CellIsOrbit` is this statement
at `Descend.branches χ` (the target cell) against a node-global supply; here `c` is any cell and the
generators are the ones anchored **in `c`**. -/
def CellOrbitAt (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) : Prop :=
  ∀ u ∈ cellList χ c, ∀ w ∈ cellList χ c, WordReach (verified (S c) adj χ) u w

/-- A nodup list whose elements are all equal to one value has length `≤ 1`. -/
private theorem length_le_one_of_nodup_const {α : Type} {l : List α} {a : α} (hnd : l.Nodup)
    (h : ∀ x ∈ l, x = a) : l.length ≤ 1 := by
  match l with
  | [] => simp
  | [_] => simp
  | x :: y :: t =>
      exact absurd (by
        have hx : x = a := h x (by simp)
        have hy : y = a := h y (by simp)
        exact List.mem_cons.mpr (Or.inl (hx.trans hy.symm)))
        (List.nodup_cons.mp hnd).1

/-! ### 9a. ★★★ THE DISJUNCTIVE FORM — the condition is on the KEY'S SURVIVORS, not on the cell

`CellOrbitAt` asks the **whole cell** to be one orbit. That is a *consume-only* hypothesis, and on a
**rigid** cell it is not merely hard but **unsatisfiable** (`Deepen.CellSingleOrbit` quantifies over
the true `IsColAut`), so no socket stated at it can ever express what the architecture actually does:

> **consume** clears cells that *are* orbits; **force** *splits mixed-orbit cells* so that such a
> node is reached (`Force.forceBy_no_narrowing_on_orbit`, `Descend.narrow_eq_branches_of_orbit` —
> complementary, non-overlapping firing domains).

★ But `cellNarrowC` maps `rep` over `keepMin key …`, **not** over `cellList χ c`. So the length bound
only ever needed the **survivors** to be one orbit — and the original proof already only applied its
hypothesis there. Weakening the quantifier is therefore the *same proof*, and it admits three routes
where there was one:

* **consume** — the whole cell is one orbit (`cellResolvedAt_of_cellOrbitAt`); nothing regresses;
* **force** — the key is injective on the cell, so there is one survivor and nothing left to certify
  (`cellResolvedAt_of_cellSeparatedAt`). **No supply appears**, which is the only way a *rigid* cell
  can ever be reached;
* **mixed** — the key cuts *between* orbits and the supply certifies the survivor. This is the case a
  CFI gadget cell needs, and it is unreachable from either hypothesis alone. -/

/-- **The per-cell condition, relative to the key's survivors.** -/
def CellResolvedAt (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) :
    Prop :=
  ∀ u ∈ keepMin key adj χ (cellList χ c), ∀ w ∈ keepMin key adj χ (cellList χ c),
    WordReach (verified (S c) adj χ) u w

/-- **★★ THE SURVIVORS BEING ONE ORBIT MAKES THE CELL FIRE** — at **any** cell, with no reference to
`targetColour`. `Consume.rep_eq_of_wordReach` carries no hypothesis on the supply, so this holds for
every `S`. -/
theorem cellNarrowC_length_le_one_of_cellResolvedAt {key : Key n} {S : CellSupply n}
    {adj : AdjMatrix n} {χ : Colouring n} {c : Nat} (h : CellResolvedAt key S adj χ c) :
    (cellNarrowC key S adj χ c).length ≤ 1 := by
  rcases hk : keepMin key adj χ (cellList χ c) with _ | ⟨b, t⟩
  · show (((keepMin key adj χ (cellList χ c)).map _).dedup).length ≤ 1
    rw [hk]; simp
  · have hb : b ∈ keepMin key adj χ (cellList χ c) := by rw [hk]; exact List.mem_cons_self
    refine length_le_one_of_nodup_const (a := rep (verified (S c) adj χ) b)
      (List.nodup_dedup _) ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hx)
    exact Consume.rep_eq_of_wordReach (h y hy b hb)

/-- **Route 1 — consume.** The whole cell being one orbit is the special case. -/
theorem cellResolvedAt_of_cellOrbitAt {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} {c : Nat} (h : CellOrbitAt S adj χ c) : CellResolvedAt key S adj χ c :=
  fun u hu w hw => h u (keepMin_subset hu) w (keepMin_subset hw)

/-- **★★ ONE CELL BEING A SINGLE ORBIT OF ITS OWN GENERATORS MAKES THAT CELL FIRE** — the original
statement, now a corollary of the key-relative one. -/
theorem cellNarrowC_length_le_one_of_cellOrbitAt {key : Key n} {S : CellSupply n}
    {adj : AdjMatrix n} {χ : Colouring n} {c : Nat} (h : CellOrbitAt S adj χ c) :
    (cellNarrowC key S adj χ c).length ≤ 1 :=
  cellNarrowC_length_le_one_of_cellResolvedAt (cellResolvedAt_of_cellOrbitAt h)

/-- Elements of a list of length `≤ 1` are all equal. -/
private theorem eq_of_mem_of_length_le_one {α : Type} {l : List α} (h : l.length ≤ 1) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  cases l with
  | nil => simp at ha
  | cons x t =>
    cases t with
    | nil => rw [List.mem_singleton] at ha hb; rw [ha, hb]
    | cons y s => simp only [List.length_cons] at h; omega

/-- **Route 2 — force, in its raw form.** At most one survivor ⟹ nothing to certify. **The supply is
unconstrained**, so this is the branch that can reach a cell with no symmetry at all. -/
theorem cellResolvedAt_of_keepMin_le_one {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} {c : Nat} (h : (keepMin key adj χ (cellList χ c)).length ≤ 1) :
    CellResolvedAt key S adj χ c := by
  intro u hu w hw
  rw [eq_of_mem_of_length_le_one h hu hw]
  exact Consume.WordReach.refl w

/-- **The force route's hypothesis**: the key is injective on the cell — the per-cell analogue of
`Force.forceBy_singleton_of_separating`'s hypothesis (which is stated at `branches χ`), and of
`KeyComplete.KeySeparatesAt` with the automorphism escape removed. -/
def CellSeparatedAt (key : Key n) (adj : AdjMatrix n) (χ : Colouring n) (c : Nat) : Prop :=
  ∀ u ∈ cellList χ c, ∀ w ∈ cellList χ c,
    Force.keyV key adj χ u = Force.keyV key adj χ w → u = w

private theorem keepMin_nodup {key : Key n} {adj : AdjMatrix n} {χ : Colouring n}
    {B : List (Fin n)} (hB : B.Nodup) : (keepMin key adj χ B).Nodup := by
  cases hk : Force.kmin? (B.map (Force.keyV key adj χ)) with
  | none => rw [Force.keepMin_none hk]; exact hB
  | some m => rw [Force.keepMin_some hk]; exact hB.filter _

/-- A separating key leaves at most one survivor: every survivor attains the same (minimal) key
value, and injectivity turns that into equality. -/
theorem keepMin_length_le_one_of_cellSeparatedAt {key : Key n} {adj : AdjMatrix n}
    {χ : Colouring n} {c : Nat} (h : CellSeparatedAt key adj χ c) :
    (keepMin key adj χ (cellList χ c)).length ≤ 1 := by
  rcases hk : keepMin key adj χ (cellList χ c) with _ | ⟨b, t⟩
  · simp
  · refine length_le_one_of_nodup_const (a := b) (hk ▸ keepMin_nodup (cellList_nodup χ c)) ?_
    intro x hx
    have hxk : x ∈ keepMin key adj χ (cellList χ c) := by rw [hk]; exact hx
    have hbk : b ∈ keepMin key adj χ (cellList χ c) := by rw [hk]; exact List.mem_cons_self
    have hx' := (Force.mem_keepMin_iff x).mp hxk
    have hb' := (Force.mem_keepMin_iff b).mp hbk
    exact h x hx'.1 b hb'.1
      (Descend.lexLeList_antisymm _ _ (hx'.2 b hb'.1) (hb'.2 x hx'.1))

/-- **Route 2 — force.** A key that separates the cell resolves it, with no supply. -/
theorem cellResolvedAt_of_cellSeparatedAt {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} {c : Nat} (h : CellSeparatedAt key adj χ c) : CellResolvedAt key S adj χ c :=
  cellResolvedAt_of_keepMin_le_one (keepMin_length_le_one_of_cellSeparatedAt h)

/-- **The socket's hypothesis at one node**: some non-singleton cell is a single orbit of the
generators anchored in it. ⚠ **Consume-only** — `SomeCellResolved` is the disjunctive form. -/
def SomeCellOrbit (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∃ c ∈ nonSingletonColours χ, CellOrbitAt S adj χ c

/-- **★★★ THE DISJUNCTIVE SOCKET'S HYPOTHESIS AT ONE NODE.** Some non-singleton cell has its key
survivors inside one orbit of the generators anchored in it — reachable by consume, by force, or by
the two together. -/
def SomeCellResolved (key : Key n) (S : CellSupply n) (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∃ c ∈ nonSingletonColours χ, CellResolvedAt key S adj χ c

theorem nodeResolvedC_of_someCellResolved {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} (h : SomeCellResolved key S adj χ) : NodeResolvedC key S adj χ := by
  obtain ⟨c, hc, hres⟩ := h
  exact ⟨c, hc, cellNarrowC_length_le_one_of_cellResolvedAt hres⟩

theorem someCellResolved_of_someCellOrbit {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} (h : SomeCellOrbit S adj χ) : SomeCellResolved key S adj χ := by
  obtain ⟨c, hc, horb⟩ := h
  exact ⟨c, hc, cellResolvedAt_of_cellOrbitAt horb⟩

/-- **The force-only instance** — some non-singleton cell is separated by the key. No supply. -/
theorem someCellResolved_of_cellSeparatedAt {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} {c : Nat} (hc : c ∈ nonSingletonColours χ)
    (h : CellSeparatedAt key adj χ c) : SomeCellResolved key S adj χ :=
  ⟨c, hc, cellResolvedAt_of_cellSeparatedAt h⟩

theorem nodeResolvedC_of_someCellOrbit {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} (h : SomeCellOrbit S adj χ) : NodeResolvedC key S adj χ :=
  nodeResolvedC_of_someCellResolved (someCellResolved_of_someCellOrbit (key := key) h)

/-- **★★★ THE SOCKET.** *One resolvable cell at every reached non-discrete node ⟹ `HandledSC`* —
hence (with `answersSC_of_handledSC`) the object never flags, and (contrapositive) the flag names a
node where **no** cell is a single orbit of its own generators.

▶ **To widen the handled region, supply a wider hypothesis here; nothing below re-proves.** The
existing `TinhoferGraph` population is the instance that takes `c` to be the target colour
(`RecordDeepenCell.handledSC_of_tinhoferGraph`, re-derived through this socket). -/
theorem handledSC_of_someCellOrbit {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    (h : ∀ χ : Colouring n, Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ → ¬ Discrete χ →
      SomeCellOrbit S adj χ) :
    HandledSC key S adj :=
  fun χ hr hd => nodeResolvedC_of_someCellOrbit (h χ hr hd)

/-- **★★★ THE DISJUNCTIVE SOCKET.** The same statement at `SomeCellResolved`, which is strictly
weaker: it is satisfiable on a **rigid** node (where `SomeCellOrbit` is not), and it is the form a
force-splits-then-consume-clears argument lands in.

▶ **This is the socket a CFI *layer* theorem must be stated against.** `handledSC_of_someCellOrbit`
is its consume-only specialisation and keeps every existing population unchanged. -/
theorem handledSC_of_someCellResolved {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    (h : ∀ χ : Colouring n, Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ → ¬ Discrete χ →
      SomeCellResolved key S adj χ) :
    HandledSC key S adj :=
  fun χ hr hd => nodeResolvedC_of_someCellResolved (h χ hr hd)

/-! ### 9b. THE FORCE ROUTE'S ENTRY POINT — separation on `branches χ` lands in the socket

The rigid stack's firing lemmas (`RigidSeal.nodeResolved_compKey_of_rigid`,
`RigidGen.nodeResolved_compKey_genOfRef`) conclude at **`Select.NodeResolved`** — the `selNode` layer
— and by the three-layer inheritance rule that does **not** transfer to the cell-indexed object.

★ But look at what their proofs actually establish: both end in
`Select.nodeResolved_of_cellResolved hnd (Or.inr …)`, whose right disjunct is precisely *"the key is
injective on `branches χ`"*. And `branches χ` **is** `cellList χ c` at the target colour
(`branches_eq_cellList`). So the rigid conclusion lands in `CellSeparatedAt` — hence in
`SomeCellResolved` — by plumbing alone.

⚠ Stated **generically**, with no rigid-stack import: this file is upstream of the published object,
and pulling `Rigid*` into its dependency graph would change the deliverable's imports for no proof
benefit. Instantiating these at `compKey` is a one-liner wherever the solver key is eventually
wired. -/

/-- Separation on the branch cell **is** separation on the target cell. -/
theorem cellSeparatedAt_of_branchSeparation {key : Key n} {adj : AdjMatrix n} {χ : Colouring n}
    {c : Nat} (htc : Descend.targetColour χ = some c)
    (hsep : ∀ u ∈ Descend.branches χ, ∀ w ∈ Descend.branches χ,
      Force.keyV key adj χ u = Force.keyV key adj χ w → u = w) :
    CellSeparatedAt key adj χ c := by
  intro u hu w hw h
  rw [← branches_eq_cellList htc] at hu hw
  exact hsep u hu w hw h

/-- **★★★ THE FORCE ROUTE, AT THE CELL-INDEXED LAYER.** A key that separates the branch cell resolves
the node — **with no condition on the supply**, which is what lets it reach a cell carrying no
symmetry. The force-side analogue of `handledSC_of_someCellOrbit`'s consume-side entry. -/
theorem someCellResolved_of_branchSeparation {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} (hnd : ¬ Discrete χ)
    (hsep : ∀ u ∈ Descend.branches χ, ∀ w ∈ Descend.branches χ,
      Force.keyV key adj χ u = Force.keyV key adj χ w → u = w) :
    SomeCellResolved key S adj χ := by
  obtain ⟨c, hc⟩ := exists_targetColour_of_not_discrete hnd
  exact someCellResolved_of_cellSeparatedAt (Finset.mem_of_min hc)
    (cellSeparatedAt_of_branchSeparation hc hsep)

theorem nodeResolvedC_of_branchSeparation {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} (hnd : ¬ Discrete χ)
    (hsep : ∀ u ∈ Descend.branches χ, ∀ w ∈ Descend.branches χ,
      Force.keyV key adj χ u = Force.keyV key adj χ w → u = w) :
    NodeResolvedC key S adj χ :=
  nodeResolvedC_of_someCellResolved (someCellResolved_of_branchSeparation hnd hsep)

/-- **The socket, force side**: a key separating the branch cell at every reached non-discrete node
makes the cell-indexed object `HandledSC`, for **every** supply. -/
theorem handledSC_of_branchSeparation {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    (h : ∀ χ : Colouring n, Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ → ¬ Discrete χ →
      ∀ u ∈ Descend.branches χ, ∀ w ∈ Descend.branches χ,
        Force.keyV key adj χ u = Force.keyV key adj χ w → u = w) :
    HandledSC key S adj :=
  handledSC_of_someCellResolved (fun χ hr hd => someCellResolved_of_branchSeparation hd (h χ hr hd))

/-- The target cell is the special case the `Tinhofer` population uses: `Descend.branches χ` **is**
`cellList χ c` there (`branches_eq_cellList`), so `Consume.CellIsOrbit` at the cell's own supply is
literally `CellOrbitAt` at that colour. -/
theorem someCellOrbit_of_targetCellIsOrbit {S : CellSupply n} {adj : AdjMatrix n} {χ : Colouring n}
    {c : Nat} (htc : Descend.targetColour χ = some c)
    (h : Consume.CellIsOrbit (S c) adj χ) : SomeCellOrbit S adj χ := by
  refine ⟨c, Finset.mem_of_min htc, ?_⟩
  intro u hu w hw
  rw [← branches_eq_cellList htc] at hu hw
  exact h u hu w hw

/-! ### 9c. THE INSTANCE KIT — a transitive verified subgroup lands in the socket

§9a/§9b give the socket; this gives the **only** way a *family* ever discharges its consume half, so
that no future family has to re-derive it. The pattern is always the same: exhibit a list `V` of
permutations that (1) the supply for that cell actually **emits**, (2) are **colour-automorphisms**,
and (3) act **transitively** on the cell. Then the cell is a single orbit of the *verified* list and
the node resolves. `verified` is `gens.filter IsColAut`, so (1)+(2) put `V` inside it and (3)
transports through `WordReach`'s monotonicity.

▶ **This is the shape the CFI layer theorem lands in** (`docs/chain-descent-wind-down.md` §2 W2,
item 3b). Take `V` = the F₂ gauge flips of the cycle space: (2) is `CFI.cfiFlipAut`, (3) is measured
exact at **every reached node** whenever the base is resolved (`scratchpad/probe_w2_asymbase.out` —
1-WL-discrete base ⟹ every non-singleton cell is a *single* gauge-orbit, 21/21 and 26/26 at the root
and at all four levels of the descent walk), and (1) — *`Kernel.kernelSupply`'s harvest emits them* —
is the one carried, algorithmic obligation. ⚠ `KernelSupply.lean` is a **definition module with no
theorems**, so (1) is not a small proof; carry it as a hypothesis, as `ForcingModel.bridge` is. -/

/-- `WordReach` only grows when the generator list does. -/
theorem wordReach_mono {V V' : List (Equiv.Perm (Fin n))} (hsub : ∀ g ∈ V, g ∈ V')
    {u w : Fin n} (h : Consume.WordReach V u w) : Consume.WordReach V' u w := by
  induction h with
  | refl => exact Consume.WordReach.refl _
  | step _ hg ih => exact Consume.WordReach.step ih (hsub _ hg)

/-- **★★★ THE INSTANCE KIT.** A list of emitted, colour-automorphic permutations that is transitive
on cell `c` discharges `CellOrbitAt` there — hence `SomeCellResolved`, hence (at every reached node)
`HandledSC`. The three hypotheses are exactly *emitted* / *sound* / *transitive*. -/
theorem cellOrbitAt_of_transitiveGens {S : CellSupply n} {adj : AdjMatrix n} {χ : Colouring n}
    {c : Nat} (V : List (Equiv.Perm (Fin n)))
    (hemit : ∀ g ∈ V, g ∈ Consume.gens (S c) adj χ)
    (haut : ∀ g ∈ V, Consume.IsColAut adj χ g)
    (htrans : ∀ u ∈ cellList χ c, ∀ w ∈ cellList χ c, Consume.WordReach V u w) :
    CellOrbitAt S adj χ c := by
  have hsub : ∀ g ∈ V, g ∈ Consume.verified (S c) adj χ := by
    intro g hg
    exact List.mem_filter.mpr ⟨hemit g hg, decide_eq_true (haut g hg)⟩
  intro u hu w hw
  exact wordReach_mono hsub (htrans u hu w hw)

/-- The same kit delivered straight to the disjunctive socket's hypothesis at one node. -/
theorem someCellResolved_of_transitiveGens {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    {χ : Colouring n} {c : Nat} (hc : c ∈ nonSingletonColours χ)
    (V : List (Equiv.Perm (Fin n)))
    (hemit : ∀ g ∈ V, g ∈ Consume.gens (S c) adj χ)
    (haut : ∀ g ∈ V, Consume.IsColAut adj χ g)
    (htrans : ∀ u ∈ cellList χ c, ∀ w ∈ cellList χ c, Consume.WordReach V u w) :
    SomeCellResolved key S adj χ :=
  someCellResolved_of_someCellOrbit ⟨c, hc, cellOrbitAt_of_transitiveGens V hemit haut htrans⟩

/-- **★★★ THE LAYER SOCKET.** *If at every reached non-discrete node some cell carries an emitted,
sound, transitive generator list, the object is `HandledSC`* — the consume-side layer statement in
the form a family instantiates. `key` is arbitrary: **no key work is required**, which is precisely
what the CFI measurement says about a resolved base. -/
theorem handledSC_of_transitiveGens {key : Key n} {S : CellSupply n} {adj : AdjMatrix n}
    (h : ∀ χ : Colouring n, Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ → ¬ Discrete χ →
      ∃ c ∈ nonSingletonColours χ, ∃ V : List (Equiv.Perm (Fin n)),
        (∀ g ∈ V, g ∈ Consume.gens (S c) adj χ) ∧ (∀ g ∈ V, Consume.IsColAut adj χ g) ∧
        (∀ u ∈ cellList χ c, ∀ w ∈ cellList χ c, Consume.WordReach V u w)) :
    HandledSC key S adj := by
  refine handledSC_of_someCellResolved (fun χ hr hd => ?_)
  obtain ⟨c, hc, V, hemit, haut, htrans⟩ := h χ hr hd
  exact someCellResolved_of_transitiveGens hc V hemit haut htrans

end Select
end ChainDescent
