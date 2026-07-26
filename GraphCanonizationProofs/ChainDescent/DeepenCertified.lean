import ChainDescent.DeepenAmenable

/-!
# `Amenable` as a RUN-TIME CERTIFICATE, not an assumption

**What this file is for.** `DeepenAmenable`'s capstone `deepenSupply_guarded_canonizer_direct` carries
`hAmen : ∀ adj χ, Amenable adj χ` — a hypothesis that is **false on rigid graphs**, which is why that
capstone is a conditional scaffold rather than an applicable theorem. `Amenable` is a statement about
the *true* automorphism group (`CellSingleOrbit` quantifies over all of `IsColAut`), so it cannot be
observed by the algorithm.

**The observation this file makes.** `CellSingleOrbit` does not have to be *assumed*; it can be
**witnessed from below by deepen's own harvest**. Every twist deepen emits is a *verified*
`IsColAut` (`twistOf_isColAut` / `deepenGens_isColAut`), and `IsColAut` is closed under composition
(`IsColAut.comp`), so:

> **the harvested twists acting transitively on a cell IS a proof that the cell is a single orbit.**

That is `cellSingleOrbit_of_certifiedOrbit` below, and it is one line given `wordReach_imp_isColAut`.
Lifting it along `AmenablePath`'s recursion gives `amenable_of_certified`: the whole `Amenable`
hypothesis is discharged by a predicate the algorithm can *check*, level by level, in polynomial time
(one deepen harvest per level).

**The three further results.**

* **§4 — a consume failure is a decision AT THIS CELL.** `not_amenablePath_imp_rigidObstruction` only
  gives `∃ χc cid, RigidObstructionAt adj χc cid` — an obstruction *somewhere*, possibly far below.
  At a certified node the failure is *located*: `consume_fail_gives_real_decision` names two branch
  vertices linked by **no** colour-automorphism, and `rigidObstructionAt_branch_of_certified` states
  it as a `RigidObstructionAt` at **this** colouring and **this** branch cell. Force is handed a node
  it can act on, not an existence statement.
* **§5 — `Amenable` TRANSPORTS.** `AmenablePath`'s per-level pick is by vertex index and so does not
  commute with a relabelling — the obstruction this whole track keeps meeting. It is absorbable
  exactly as in `joint`: the level's cell *is* a single orbit (that is what `AmenablePath` says), so a
  stabilizer element carries `σ wₐ` to `w_b` and the relating isomorphism accumulates
  (`amenablePath_transport`, `amenable_transport`).
* **§6 — `①c` WITH NO HYPOTHESIS.** Given §5, a supply that simply *defers* where `Amenable` fails is
  equivariant unconditionally (good side: §5 transports; bad side: both emit nothing). So
  `deepenSupplyGuarded_canonizer` carries **no** hypothesis at all, where
  `deepenSupply_guarded_canonizer_direct` carried a globally-false one. Soundness no longer rests on
  anything; only *firing* is reduced, and the guard is exactly where the rigid side takes over.

⚠ **What is still open.** The guard is a `Prop` test, so `deepenSupplyGuarded` is `noncomputable`.
Which *poly, relabelling-invariant* check to use in the executable is open: `Certified` (§2) is poly
and sound, but its own invariance is not established, because `deepenGens` is index-dependent.

**Non-vacuity (§3, proved here).** `chooseIdK (List.finRange n) χ = Descend.targetColour χ` — deepen's
per-level cell selector and the canonizer's branch cell are the *same object*. So the harvest
`deepenGens adj χ`, which runs on `Descend.branches χ`, is in fact a harvest on the very cell
`AmenablePath` asks about, and the consume-side `Consume.CellIsOrbit` discharges each level's
certificate (`certifiedOrbit_of_cellIsOrbit_chooseIdK`). Without this the certificate would be sound
but not obviously *achievable*.
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (IsColAut)
open ChainDescent.Descend (transportColouring)

variable {n : Nat}

/-! ## 1. The certificate -/

/-- **The run-time certificate that a cell is a single orbit.** deepen's own verified twists act
transitively on the `cid`-colour class. Every ingredient is *observable*: `deepenSupply`'s generators
are computed by the harvest, `Consume.verified` re-checks each one, and `WordReach` is the orbit BFS
the algorithm already runs. Contrast `CellSingleOrbit`, which quantifies over the true `IsColAut`
group and is therefore not observable. -/
def CertifiedOrbit (adj : AdjMatrix n) (χ : Colouring n) (cid : Nat) : Prop :=
  ∀ u w : Fin n, χ u = cid → χ w = cid →
    Consume.WordReach (Consume.verified deepenSupply adj χ) u w

/-- **★ THE CERTIFICATE IS SOUND — a checked transitivity IS `CellSingleOrbit`.** Each harvested twist
is a verified `IsColAut` and `IsColAut` is closed under composition, so a `WordReach` word furnishes
the automorphism `CellSingleOrbit` asks for. This is the step that lets an *observable* predicate
discharge an *unobservable* one. -/
theorem cellSingleOrbit_of_certifiedOrbit {adj : AdjMatrix n} {χ : Colouring n} {cid : Nat}
    (h : CertifiedOrbit adj χ cid) : CellSingleOrbit adj χ cid :=
  fun u w hu hw => wordReach_imp_isColAut (h u w hu hw)

/-- The certificate at the **branch cell** is exactly `Consume.CellIsOrbit` for `deepenSupply` — the
predicate the consume side already speaks in. (Stated for the branch cell's own colour; the bridge to
`AmenablePath`'s `chooseIdK`-supplied `cid` is the selector-identity noted at the file end.) -/
theorem certifiedOrbit_of_cellIsOrbit {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (hc : Descend.targetColour χ = some c) (h : Consume.CellIsOrbit deepenSupply adj χ) :
    CertifiedOrbit adj χ c := by
  intro u w hu hw
  exact h u ((Descend.mem_branches_iff hc u).mpr hu) w ((Descend.mem_branches_iff hc w).mpr hw)

/-! ## 2. Lifting the certificate along the deepening path -/

/-- **`CertifiedPath`** — the observable mirror of `AmenablePath`: at every level that individualizes a
cell, that cell's single-orbit-ness is *witnessed* by the harvest rather than assumed. The recursion is
`AmenablePath`'s, verbatim, with `CertifiedOrbit` in place of `CellSingleOrbit`. -/
def CertifiedPath (adj : AdjMatrix n) (χp : Colouring n) :
    Nat → Refine.ColData n → Prop
  | 0, _ => True
  | fuel + 1, cur =>
      let χc := cur.col
      match chooseIdK (List.finRange n) χc with
        | none => True
        | some cid =>
            CertifiedOrbit adj χc cid ∧
            (match (List.finRange n).filter (fun v => χc v == cid) with
             | [] => True
             | w :: _ => CertifiedPath adj χp fuel (step adj χc w))

/-- **★★ THE LIFT — a certified path IS an amenable path.** Level-by-level induction: each level's
certificate discharges that level's `CellSingleOrbit` via `cellSingleOrbit_of_certifiedOrbit`, and the
tails match because the two recursions are the same recursion. -/
theorem amenablePath_of_certifiedPath (adj : AdjMatrix n) (χp : Colouring n) :
    ∀ (fuel : Nat) (cur : Refine.ColData n),
      CertifiedPath adj χp fuel cur → AmenablePath adj χp fuel cur := by
  intro fuel
  induction fuel with
  | zero => intro cur _; trivial
  | succ fuel ih =>
      intro cur h
      unfold CertifiedPath at h
      unfold AmenablePath
      dsimp only at h ⊢
      -- `cases hco :` already substitutes in the GOAL; only `h` still mentions `chooseIdK`.
      cases hco : chooseIdK (List.finRange n) cur.col with
      | none => trivial
      | some cid =>
          rw [hco] at h
          dsimp only at h
          refine ⟨cellSingleOrbit_of_certifiedOrbit h.1, ?_⟩
          have htail := h.2
          cases hfl : (List.finRange n).filter (fun v => cur.col v == cid) with
          | nil => trivial
          | cons w rest =>
              rw [hfl] at htail
              exact ih _ htail

/-- **`Certified`** — the observable mirror of `Amenable`: every anchor's deepening path is certified. -/
def Certified (adj : AdjMatrix n) (χ : Colouring n) : Prop :=
  ∀ r ∈ Descend.branches χ, CertifiedPath adj χ n (step adj χ r)

/-- **★★★ `Certified ⟹ Amenable`.** The domain hypothesis the whole `C3b` track carries is discharged
by a predicate the algorithm computes. -/
theorem amenable_of_certified {adj : AdjMatrix n} {χ : Colouring n}
    (h : Certified adj χ) : Amenable adj χ :=
  fun r hr => amenablePath_of_certifiedPath adj χ n (step adj χ r) (h r hr)

/-- The `①c` capstone restated over the observable hypothesis. ⚠ **This is not yet the unconditional
theorem** — `Certified` is *stronger* than `Amenable`, so as a GLOBAL hypothesis this is strictly worse.
Its value is that `Certified` is *checkable*: the next block replaces the global quantifier by a
per-node run-time guard, which is what actually removes the hypothesis. -/
theorem deepenSupply_guarded_canonizer_of_certified
    (hCert : ∀ (adj : AdjMatrix n) (χ : Colouring n), Certified adj χ) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (Force.lookaheadKey (n := n))
          (deepenSupply (n := n))))) :=
  deepenSupply_guarded_canonizer_direct (fun adj χ => amenable_of_certified (hCert adj χ))

/-! ## 3. Non-vacuity — deepen's cell selector IS the canonizer's branch cell

`CertifiedOrbit adj χ cid` is sound for any `cid` (§1), but for it to be *achievable* the harvest has
to run on the very cell `AmenablePath` asks about. `deepenGens adj χ` harvests on `Descend.branches χ`
(selected by `Descend.targetColour`), while `AmenablePath` names its cell by `chooseIdK (List.finRange
n)`. This section proves those two selectors are **the same object**, which is what lets
`certifiedOrbit_of_cellIsOrbit` fire at every level rather than only at the branch cell.

Both are the minimum of the same set of colours: `chooseIdK` folds a minimum over
`{χ v | 2 ≤ (classOf χ v).length}` and `targetColour` is `Finset.min` of
`(univ.image χ).filter (1 < (cellOf χ ·).card)`. -/

/-- `classOf` at `v` is the `cid`-cell at `v`'s own colour — the same filter, definitionally. -/
theorem classOf_eq_cidCell (χ : Colouring n) (v : Fin n) : classOf χ v = cidCell χ (χ v) := rfl

/-- The list-side cell and the `Finset`-side cell have the same size (`cidCell` is `Nodup`). -/
theorem cidCell_length_eq_cellOf_card (χ : Colouring n) (c : Nat) :
    (cidCell χ c).length = (Descend.cellOf χ c).card := by
  have hset : (cidCell χ c).toFinset = Descend.cellOf χ c := by
    ext u
    simp [List.mem_toFinset, mem_cidCell_iff, Descend.cellOf, Finset.mem_filter]
  rw [← hset, List.toFinset_card_of_nodup (cidCell_nodup χ c)]

section FoldMin

variable (χ : Colouring n)

/-- The fold never exceeds its seed. -/
private theorem foldMin_le_acc :
    ∀ (L : List (Fin n)) (m cid : Nat), L.foldl (fun acc v => match acc with
        | none => some (χ v) | some m => some (min m (χ v))) (some m) = some cid → cid ≤ m := by
  intro L
  induction L with
  | nil => intro m cid h; simp only [List.foldl_nil, Option.some.injEq] at h; omega
  | cons a t ih =>
      intro m cid h
      simp only [List.foldl_cons] at h
      exact le_trans (ih (min m (χ a)) cid h) (min_le_left _ _)

/-- The fold is a lower bound for every element it saw. -/
private theorem foldMin_le :
    ∀ (L : List (Fin n)) (acc : Option Nat) (cid : Nat), L.foldl (fun acc v => match acc with
        | none => some (χ v) | some m => some (min m (χ v))) acc = some cid →
      ∀ v ∈ L, cid ≤ χ v := by
  intro L
  induction L with
  | nil => intro _ _ _ v hv; exact absurd hv List.not_mem_nil
  | cons a t ih =>
      intro acc cid h v hv
      simp only [List.foldl_cons] at h
      rcases List.mem_cons.mp hv with rfl | hvt
      · cases acc with
        | none => exact foldMin_le_acc χ t (χ v) cid h
        | some m => exact le_trans (foldMin_le_acc χ t (min m (χ v)) cid h) (min_le_right _ _)
      · exact ih _ cid h v hvt

/-- A `none` result means nothing was folded. (Same technique as `discrete_of_chooseIdK_none`,
reusing the landed `foldl_min_isSome`.) -/
private theorem foldMin_nil_of_none {L : List (Fin n)}
    (h : L.foldl (fun acc v => match acc with
        | none => some (χ v) | some m => some (min m (χ v))) none = none) : L = [] := by
  by_contra hne
  obtain ⟨a, t, hfl⟩ := List.exists_cons_of_ne_nil hne
  rw [hfl] at h
  simp only [List.foldl_cons] at h
  exact absurd h (Option.isSome_iff_ne_none.mp (foldl_min_isSome χ t (χ a)))

end FoldMin

/-- The two descriptions of "this colour's cell is non-singleton" agree. -/
theorem mem_nonSingletonColours_iff (χ : Colouring n) (c : Nat) :
    c ∈ Descend.nonSingletonColours χ ↔ ∃ v : Fin n, 2 ≤ (classOf χ v).length ∧ χ v = c := by
  constructor
  · intro hc
    obtain ⟨-, hcard⟩ := Finset.mem_filter.mp hc
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (Descend.cellOf χ c).card)
    have hχv : χ v = c := (Finset.mem_filter.mp hv).2
    refine ⟨v, ?_, hχv⟩
    rw [classOf_eq_cidCell, hχv, cidCell_length_eq_cellOf_card]
    omega
  · rintro ⟨v, hlen, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [classOf_eq_cidCell, cidCell_length_eq_cellOf_card] at hlen
    omega

/-- **★★ THE SELECTOR IDENTITY.** deepen's per-level cell selector and the canonizer's branch-cell
selector are the *same object*. Hence `deepenGens adj χ` — which harvests on `Descend.branches χ` — is
a harvest on exactly the cell `AmenablePath` names, so `Consume.CellIsOrbit deepenSupply adj χ`
discharges that level's `CertifiedOrbit` (`certifiedOrbit_of_cellIsOrbit`). This is what makes the
certificate of §1–§2 *achievable* rather than merely sound. -/
theorem chooseIdK_eq_targetColour (χ : Colouring n) :
    chooseIdK (List.finRange n) χ = Descend.targetColour χ := by
  have hmemL : ∀ v : Fin n,
      v ∈ (List.finRange n).filter (fun v => decide ((classOf χ v).length ≥ 2)) ↔
        2 ≤ (classOf χ v).length := by
    intro v; rw [List.mem_filter]; simp [List.mem_finRange]
  cases hck : chooseIdK (List.finRange n) χ with
  | none =>
      -- nothing was folded, so no colour is non-singleton, so `targetColour` is `none` too
      have hnil := foldMin_nil_of_none χ (by unfold chooseIdK at hck; exact hck)
      cases hT : Descend.targetColour χ with
      | none => rfl
      | some c =>
          exfalso
          obtain ⟨v, hlen, -⟩ :=
            (mem_nonSingletonColours_iff χ c).mp (Finset.mem_of_min (by
              unfold Descend.targetColour at hT; exact hT))
          have : v ∈ (List.finRange n).filter (fun v => decide ((classOf χ v).length ≥ 2)) :=
            (hmemL v).mpr hlen
          rw [hnil] at this; exact absurd this List.not_mem_nil
  | some cid =>
      -- `cid` is attained and is a lower bound, so it IS the `Finset.min`
      have hck' : ((List.finRange n).filter (fun v => decide ((classOf χ v).length ≥ 2))).foldl
          (fun acc v => match acc with
            | none => some (χ v) | some m => some (min m (χ v))) none = some cid := by
        unfold chooseIdK at hck; exact hck
      have hattain : ∃ v ∈ (List.finRange n).filter (fun v => decide ((classOf χ v).length ≥ 2)),
          χ v = cid := by
        rcases foldl_min_mem χ _ none hck' with h | h
        · exact absurd h (by simp)
        · exact h
      obtain ⟨v0, hv0mem, hv0⟩ := hattain
      have hcidmem : cid ∈ Descend.nonSingletonColours χ :=
        (mem_nonSingletonColours_iff χ cid).mpr ⟨v0, (hmemL v0).mp hv0mem, hv0⟩
      have hlb : ∀ c ∈ Descend.nonSingletonColours χ, cid ≤ c := by
        intro c hc
        obtain ⟨v, hlen, rfl⟩ := (mem_nonSingletonColours_iff χ c).mp hc
        exact foldMin_le χ _ none cid hck' v ((hmemL v).mpr hlen)
      obtain ⟨m, hm⟩ := Finset.min_of_nonempty ⟨cid, hcidmem⟩
      have hmmem : m ∈ Descend.nonSingletonColours χ := Finset.mem_of_min hm
      have h1 : cid ≤ m := hlb m hmmem
      have h2 : m ≤ cid := by
        have hle := Finset.min_le hcidmem
        rw [hm] at hle
        exact_mod_cast hle
      -- goal (after `cases hck`) is `some cid = Descend.targetColour χ`
      have hcm : cid = m := le_antisymm h1 h2
      subst hcm
      unfold Descend.targetColour
      exact hm.symm

/-- **★★★ THE PER-LEVEL BRIDGE, ASSEMBLED.** At *any* level of a deepening path, the consume-side
predicate `Consume.CellIsOrbit deepenSupply adj χ` discharges that level's `CertifiedOrbit` for the
very `cid` that `AmenablePath` names — because the two selectors are the same object (§3). Composed
with §1–§2 this is the whole soundness route: a consume-side orbit check, level by level, discharges
`Amenable`. -/
theorem certifiedOrbit_of_cellIsOrbit_chooseIdK {adj : AdjMatrix n} {χ : Colouring n} {cid : Nat}
    (hcid : chooseIdK (List.finRange n) χ = some cid)
    (h : Consume.CellIsOrbit deepenSupply adj χ) : CertifiedOrbit adj χ cid :=
  certifiedOrbit_of_cellIsOrbit (by rw [← chooseIdK_eq_targetColour]; exact hcid) h

/-! ## 4. The forcible node — a consume failure is a decision AT THIS CELL

`not_amenablePath_imp_rigidObstruction` says a path failure exposes a `RigidObstructionAt` *somewhere*:
`∃ χc cid, RigidObstructionAt adj χc cid`, with no control over which colouring or cell. That is the
"exposed rigid obstruction". This section upgrades it: at a **certified** node, a consume failure
names a non-automorphic pair **in the branch cell of the node you are standing on**. -/

/-- **Exactness at a certified node.** deepen's emitted branch-orbit relation *is* the `IsColAut`-orbit
relation. `⊆` is soundness (`wordReach_imp_isColAut`); `⊇` is `exec_recovers_refgen_on_cell` through
`Amenable`, which the certificate supplies. -/
theorem branchOrbit_iff_aut_of_certified (adj : AdjMatrix n) (χ : Colouring n)
    (hCert : Certified adj χ) {u : Fin n} (hu : u ∈ Descend.branches χ) {w : Fin n} :
    Consume.WordReach (Consume.verified deepenSupply adj χ) u w
      ↔ ∃ β : Equiv.Perm (Fin n), IsColAut adj χ β ∧ β u = w :=
  deepen_branch_orbit_iff_aut adj χ (amenable_of_certified hCert) hu

/-- **★★★ A CONSUME FAILURE AT A CERTIFIED NODE IS A REAL DECISION IN THIS CELL.** If the certificate
held at every level and consume still could not make the branch cell one orbit, then two *named*
branch vertices are provably linked by **no** colour-automorphism. Not "an obstruction exists
somewhere below" — a decision, here, on the cell the resolver is currently looking at. -/
theorem consume_fail_gives_real_decision {adj : AdjMatrix n} {χ : Colouring n}
    (hCert : Certified adj χ) (hfail : ¬ Consume.CellIsOrbit deepenSupply adj χ) :
    ∃ u ∈ Descend.branches χ, ∃ w ∈ Descend.branches χ,
      ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w := by
  by_contra hcon
  push Not at hcon
  refine hfail (fun u hu w hw => ?_)
  obtain ⟨σ, hσ, hσu⟩ := hcon u hu w hw
  exact (branchOrbit_iff_aut_of_certified adj χ hCert hu).mpr ⟨σ, hσ, hσu⟩

/-- **★★★ THE SAME FACT IN THE PROJECT'S VOCABULARY — a LOCATED `RigidObstructionAt`.** Compare
`not_amenablePath_imp_rigidObstruction`, which yields `∃ χc cid, RigidObstructionAt adj χc cid` with no
control over `χc` or `cid`. Here the obstruction is at **this** colouring and **this** branch cell, so
the force side is handed a node it can act on rather than an existence statement. -/
theorem rigidObstructionAt_branch_of_certified {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (hc : Descend.targetColour χ = some c)
    (hCert : Certified adj χ) (hfail : ¬ Consume.CellIsOrbit deepenSupply adj χ) :
    RigidObstructionAt adj χ c := by
  obtain ⟨u, hu, w, hw, hrig⟩ := consume_fail_gives_real_decision hCert hfail
  exact ⟨u, w, (Descend.mem_branches_iff hc u).mp hu, (Descend.mem_branches_iff hc w).mp hw, hrig⟩

/-! ## 5. `Amenable` TRANSPORTS — removing the GLOBAL quantifier

`deepen_branchOrbit_transport` carries `hAmen : ∀ adj χ, Amenable adj χ` — globally quantified purely
because the transport argument needs `Amenable` on the *relabelled* graph too, and `AmenablePath`'s
per-level pick is by vertex index, which does not commute with a relabelling. That index pick is the
same obstruction the whole track keeps meeting.

It is removable. The pick mismatch is absorbed exactly as in `joint`: the chosen cell is a single
orbit (that is what `AmenablePath` *says*), so a stabilizer element carries `σ w_a` to `w_b`, and the
relating isomorphism accumulates. The result is that `Amenable` is transport-stable, so the global
`∀ adj χ` collapses to the single graph in hand. -/

/-- Relabelling composes. -/
theorem relabelAdj_mul (τ σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) :
    relabelAdj (τ * σ) adj = relabelAdj τ (relabelAdj σ adj) := rfl

/-- `CellSingleOrbit` transports across an **isomorphism** (not just an automorphism): conjugating the
witnessing stabilizer element by `σ` lands it in the relabelled graph's stabilizer
(`Consume.isColAut_conj_iff`, which is already stated cross-graph). -/
theorem cellSingleOrbit_transport_iso {adj : AdjMatrix n} {χc : Colouring n}
    (σ : Equiv.Perm (Fin n)) {cid : Nat} (h : CellSingleOrbit adj χc cid) :
    CellSingleOrbit (relabelAdj σ adj) (transportColouring σ χc) cid := by
  intro u' w' hu' hw'
  have hu : χc (σ.symm u') = cid := hu'
  have hw : χc (σ.symm w') = cid := hw'
  obtain ⟨ρ, hρ, hρuw⟩ := h (σ.symm u') (σ.symm w') hu hw
  refine ⟨σ * ρ * σ⁻¹, (Consume.isColAut_conj_iff σ).mpr hρ, ?_⟩
  show σ (ρ (σ.symm u')) = w'
  rw [hρuw]; exact Equiv.apply_symm_apply σ w'

/-- deepen's whole-graph cell selector is relabelling-invariant. Immediate from the §3 selector
identity plus the landed `Descend.targetColour_transport` — the `List.map σ` mismatch in
`chooseIdK_transport` never has to be dealt with. -/
theorem chooseIdK_finRange_transport (σ : Equiv.Perm (Fin n)) (χ : Colouring n) :
    chooseIdK (List.finRange n) (transportColouring σ χ) = chooseIdK (List.finRange n) χ := by
  rw [chooseIdK_eq_targetColour, chooseIdK_eq_targetColour, Descend.targetColour_transport]

/-- **★★ `AmenablePath` TRANSPORTS.** The relating isomorphism accumulates a stabilizer element per
level, exactly as in `joint`: `AmenablePath` asserts the level's cell is a single orbit, which is
precisely what supplies the `τ` absorbing the index-pick mismatch `σ w_a ↦ w_b`. -/
theorem amenablePath_transport (adj : AdjMatrix n) (χp χq : Colouring n) :
    ∀ (fuel : Nat) (cur_a cur_b : Refine.ColData n) (σ : Equiv.Perm (Fin n)),
      cur_b.col = transportColouring σ cur_a.col →
      AmenablePath adj χp fuel cur_a →
      AmenablePath (relabelAdj σ adj) χq fuel cur_b := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _; trivial
  | succ fuel ih =>
      intro cur_a cur_b σ hrel hA
      unfold AmenablePath at hA
      unfold AmenablePath
      dsimp only at hA ⊢
      cases hco : chooseIdK (List.finRange n) cur_a.col with
      | none =>
          have hb : chooseIdK (List.finRange n) cur_b.col = none := by
            rw [hrel, chooseIdK_finRange_transport]; exact hco
          rw [hb]; trivial
      | some cid =>
          have hb : chooseIdK (List.finRange n) cur_b.col = some cid := by
            rw [hrel, chooseIdK_finRange_transport]; exact hco
          rw [hco] at hA
          rw [hb]
          dsimp only at hA ⊢
          obtain ⟨hcell_a, hArec⟩ := hA
          have hcell_b : CellSingleOrbit (relabelAdj σ adj) cur_b.col cid := by
            rw [hrel]; exact cellSingleOrbit_transport_iso σ hcell_a
          refine ⟨hcell_b, ?_⟩
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
                  -- the accumulated relating isomorphism `τ * σ`
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
                  have := ih (step adj cur_a.col w_a) (step (relabelAdj σ adj) cur_b.col w_b)
                    (τ * σ) hrel' hArec
                  rwa [hadj'] at this

/-- **★★★ `Amenable` TRANSPORTS.** Hence the global `∀ adj χ, Amenable adj χ` that
`deepen_branchOrbit_transport` carries is equivalent to the *local* fact on the graph in hand: it was
globally quantified only to cover the relabelled graph, which this now supplies. -/
theorem amenable_transport {adj : AdjMatrix n} {χ : Colouring n} (σ : Equiv.Perm (Fin n))
    (h : Amenable adj χ) : Amenable (relabelAdj σ adj) (transportColouring σ χ) := by
  intro r hr
  have hbr : ∃ y ∈ Descend.branches χ, σ y = r := by
    rw [(Descend.branches_transport_perm σ χ).mem_iff, List.mem_map] at hr
    exact hr
  obtain ⟨y, hy, rfl⟩ := hbr
  have hstep : (step (relabelAdj σ adj) (transportColouring σ χ) (σ y)).col
      = transportColouring σ ((step adj χ y).col) := step_transport σ adj χ y
  exact amenablePath_transport adj χ (transportColouring σ χ) n
    (step adj χ y) (step (relabelAdj σ adj) (transportColouring σ χ) (σ y)) σ hstep (h y hy)

/-! ## 6. The GUARDED supply — `①c` with NO hypothesis at all

With `Amenable` known relabelling-invariant (§5), a supply that simply *defers* where `Amenable` fails
is equivariant unconditionally: on the good side both graphs take the deepen branch and §5 transports
the orbit relation; on the bad side both emit nothing and the relation is trivial. So the flag is never
a soundness artefact — the `∀ adj χ, Amenable adj χ` scaffold disappears. -/

theorem relabelAdj_one (adj : AdjMatrix n) : relabelAdj 1 adj = adj := rfl

theorem transportColouring_one (χ : Colouring n) :
    transportColouring (1 : Equiv.Perm (Fin n)) χ = χ := rfl

/-- `Amenable` is relabelling-INVARIANT, both directions. -/
theorem amenable_transport_iff {adj : AdjMatrix n} {χ : Colouring n} (σ : Equiv.Perm (Fin n)) :
    Amenable (relabelAdj σ adj) (transportColouring σ χ) ↔ Amenable adj χ := by
  refine ⟨fun h => ?_, amenable_transport σ⟩
  have h' := amenable_transport σ⁻¹ h
  rwa [← relabelAdj_mul, transportColouring_comp, inv_mul_cancel, relabelAdj_one,
       transportColouring_one] at h'

/-- Reaching nothing: with no generators, `WordReach` is equality. -/
theorem wordReach_nil_iff {u w : Fin n} : Consume.WordReach [] u w ↔ u = w := by
  refine ⟨fun h => ?_, fun h => h ▸ Consume.WordReach.refl _⟩
  by_contra hne
  exact Residue.not_wordReach_nil hne h

open Classical in
/-- **★ THE GUARDED DEEPEN SUPPLY.** Emit deepen's generators only where `Amenable` actually holds;
defer (emit nothing) otherwise. ⚠ **Proof-side object** — the guard is a `Prop` test, so this is
`noncomputable`. What poly, relabelling-invariant check to use in the *executable* is a separate,
open question (`Certified` of §2 is poly and sound but its own invariance is not established, since
`deepenGens` is index-dependent). Nothing below depends on the guard being computable. -/
noncomputable def deepenSupplyGuarded : Consume.Supply n := fun adj χ =>
  if Amenable adj χ then deepenSupply adj χ else ([], n * n * n * n * n * n)

theorem verified_guarded_of_amenable {adj : AdjMatrix n} {χ : Colouring n} (h : Amenable adj χ) :
    Consume.verified deepenSupplyGuarded adj χ = Consume.verified deepenSupply adj χ := by
  unfold Consume.verified Consume.gens deepenSupplyGuarded
  rw [if_pos h]

theorem verified_guarded_of_not {adj : AdjMatrix n} {χ : Colouring n} (h : ¬ Amenable adj χ) :
    Consume.verified deepenSupplyGuarded adj χ = [] := by
  unfold Consume.verified Consume.gens deepenSupplyGuarded
  rw [if_neg h]; rfl

/-- **★★ THE GUARDED BRANCH-ORBIT RELATION TRANSPORTS — UNCONDITIONALLY.** Compare
`deepen_branchOrbit_transport`, which carries `∀ adj χ, Amenable adj χ`. Here the good case is handled
by §5's `amenable_transport` and the bad case by the guard itself. -/
theorem deepen_branchOrbit_transport_guarded
    (σ : Equiv.Perm (Fin n)) (adj : AdjMatrix n) (χ : Colouring n) (a b : Fin n)
    (ha : a ∈ Descend.branches χ) (_hb : b ∈ Descend.branches χ) :
    Consume.WordReach
        (Consume.verified deepenSupplyGuarded (relabelAdj σ adj) (transportColouring σ χ)) (σ a) (σ b)
      ↔ Consume.WordReach (Consume.verified deepenSupplyGuarded adj χ) a b := by
  by_cases hA : Amenable adj χ
  · have hA' : Amenable (relabelAdj σ adj) (transportColouring σ χ) := amenable_transport σ hA
    rw [verified_guarded_of_amenable hA', verified_guarded_of_amenable hA]
    have hσa : σ a ∈ Descend.branches (transportColouring σ χ) :=
      (Descend.branches_transport_perm σ χ).mem_iff.mpr (List.mem_map_of_mem ha)
    rw [deepen_branch_orbit_iff_aut _ _ hA' hσa, deepen_branch_orbit_iff_aut _ _ hA ha]
    constructor
    · rintro ⟨β, hβ, hβa⟩
      refine ⟨σ⁻¹ * β * σ, ?_, ?_⟩
      · have hc := (Consume.isColAut_conj_iff σ (adj := adj) (χ := χ) (α := σ⁻¹ * β * σ)).mp
        rw [show σ * (σ⁻¹ * β * σ) * σ⁻¹ = β by group] at hc
        exact hc hβ
      · simp [Equiv.Perm.mul_apply, hβa]
    · rintro ⟨β, hβ, hβa⟩
      refine ⟨σ * β * σ⁻¹, (Consume.isColAut_conj_iff σ).mpr hβ, ?_⟩
      simp [Equiv.Perm.mul_apply, hβa]
  · have hA' : ¬ Amenable (relabelAdj σ adj) (transportColouring σ χ) :=
      fun h => hA ((amenable_transport_iff σ).mp h)
    rw [verified_guarded_of_not hA', verified_guarded_of_not hA, wordReach_nil_iff,
        wordReach_nil_iff]
    exact ⟨fun h => σ.injective h, fun h => congrArg σ h⟩

/-- **★★★ `①c` FOR THE GUARDED DEEPEN SUPPLY — NO HYPOTHESIS.** The `∀ adj χ, Amenable adj χ` scaffold
of `deepenSupply_guarded_canonizer_direct` is gone: where `Amenable` fails the supply defers, and §5
says that failure is itself relabelling-invariant, so the canonizer stays iso-invariant on every input.
Firing (②) is of course reduced — the guard is where the rigid side takes over — but soundness no
longer rests on anything. -/
theorem deepenSupplyGuarded_canonizer :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n))
        (Stall.guard (Composite.forceThenConsume (Force.lookaheadKey (n := n))
          (deepenSupplyGuarded (n := n))))) :=
  Residue.guarded_mixed_canonizer Force.keyEquivariant_lookahead
    (SupplyTransport.stallEquivariant_forceThenConsume_of_branchOrbitTransport
      Force.keyEquivariant_lookahead deepen_branchOrbit_transport_guarded)

/-! ## 7. What this block leaves open

**The guarded supply.** Replace the global `hCert` by a supply that *tests* the certificate per level
and defers when it fails. `CertifiedOrbit` is checkable (finitely many verified generators, orbit BFS
— and by §3 the harvest is on the right cell), so the guard is implementable; the capstone then reads
"either the certificate held all the way down — and `①c` holds — or the check failed at a named level,
which is a `RigidObstructionAt` there (`rigidObstruction_of_not_cellSingleOrbit`) and is handed to
force". That is the theorem this track is aiming at.
-/

end Deepen
end ChainDescent
