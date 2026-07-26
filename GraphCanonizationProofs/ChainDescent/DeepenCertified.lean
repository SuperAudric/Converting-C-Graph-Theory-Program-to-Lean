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

**What this does and does not buy.** It converts `Amenable` from an unobservable domain hypothesis
into an observable one — the *soundness* half. It does **not** by itself make the capstone
unconditional: `Certified` is *stronger* than `Amenable` (a certificate implies single-orbit, not
conversely), so `∀ adj χ, Certified adj χ` is a strictly stronger global assumption than `hAmen`. The
payoff is only realised once the supply **branches on the certificate** rather than assuming it — a
guarded `deepenSupply` that defers when the check fails. That is the next block (see the file-end
note); this file is its soundness core.

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

/-! ## 4. What this block leaves open

**The guarded supply.** Replace the global `hCert` by a supply that *tests* the certificate per level
and defers when it fails. `CertifiedOrbit` is checkable (finitely many verified generators, orbit BFS
— and by §3 the harvest is on the right cell), so the guard is implementable; the capstone then reads
"either the certificate held all the way down — and `①c` holds — or the check failed at a named level,
which is a `RigidObstructionAt` there (`rigidObstruction_of_not_cellSingleOrbit`) and is handed to
force". That is the theorem this track is aiming at.
-/

end Deepen
end ChainDescent
