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

end Select
end ChainDescent
