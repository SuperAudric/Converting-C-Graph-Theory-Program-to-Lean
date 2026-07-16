import ChainDescent.Stall

/-!
# `③` — the residue, as the COMPLEMENT of what the resolvers positively handle

## The framing (deliberate)

The residue is **not asserted**. It is *defined* as the complement of a **positive capability predicate**:

> **`Handled key S adj`** — at every **reachable** non-discrete colouring (`Descend.Reaches` — the descent's own
> node colourings, over-approximated resolver-independently), the branch cell is **either** connected by the
> supply's verified generators (**consume**'s domain) **or** separated by the key (**force**'s domain).

Everything is then proved *forwards* from `Handled`: the guarded descent **answers** (`answers_of_handled`) and is
**polynomial** (`Stall.descentCost_guard_le`, already unconditional). The residue is what is left over —

> **`Residue key S adj := ¬ Handled key S adj`** — and `residue_if_flag`: **the descent flags only on the residue.**

This matters methodologically. Asserting residue atoms up front is how the project has repeatedly manufactured
*vacuous* predicates (`hflag`, `SchemeReproduced`, `∃ gens, closure = group` were all uninhabited or trivially
true). A residue defined as the complement of a **positive, checkable, already-instantiated** capability cannot be
vacuous by accident: it is inhabited exactly when some cell defeats both resolvers, and it **shrinks** — with no
re-proof of anything — every time the oracle or the key gets stronger.

## What this discharges

`residue_if_flag` is the `Publication.residue_if_flag` obligation (`③`) for the real object, and
`Residue` is a **definition**, not an `opaque` atom — so `unhandledResidue_nonvacuous` becomes *provable in
principle*, which it was not before (the three `Publication` atoms are `opaque … : Prop` with no definition, hence
can be neither inhabited nor refuted).

## The remaining content, stated honestly

`Handled` is where **all** the open work now lives, and it is exactly the two halves:

* **consume's half** — a `Supply` and its firing (`CellIsOrbit`) on everything except the Cameron / node-4
  obstruction. Two structural supplies now exist — `MatchSupply.matchSupply` (fires at a `Discretizing` node,
  i.e. regular-action only) and `DeepMatchSupply.deepMatchSupply d` (fires under `SeparatesAt d` — the seal's
  bounded-depth ladder). The seal's depth vocabulary reaches `SeparatesAt` via `SealDepthBridge` (P2b/P2c), and
  **`HandledBridge.handled_of_seal` now discharges `Handled` itself** from the two structural seal hypotheses:
  depth (`CascadesAt`, which `theorem_1_HOR_*` / `viaSpielman` produce at bounded `k`) and localisation at every
  committed set (`∀ T, CellsAreOrbits` — the seal's own open per-family obligation, stated honestly as the
  hypothesis).
* **force's half** — a solve-derived `Key` and its separation theorem (`KeySeparates`), i.e. §11.12's P1/P3.
  *Nothing is wired in today* beyond `lookaheadKey`.

Both are **firing** obligations. Neither can break `①` (soundness is proved for *every* supply and *every*
equivariant key), and neither can break the single-path node bound (unconditional; the wall-clock cost is
polynomial iff the supply's per-call cost is). They only move the boundary of `Handled`.
-/

namespace ChainDescent
namespace Residue

open ChainDescent.CanonSpec (Labelled)
open ChainDescent.CostModel (CostM)
open ChainDescent.Descend
open ChainDescent.Force (Key keyV KeyEquivariant)
open ChainDescent.Consume (Supply)
open ChainDescent.Composite (forceThenConsume forcedSet)
open ChainDescent.Stall (guard stalled StallEquivariant)

variable {n : Nat}

/-! ## 1. `①` for the GUARDED composite

`Stall.narrowEquivariant_guard` covered the *force-only* route. The mixed resolver is not `NarrowEquivariant` (its
consume half picks a representative non-equivariantly), so the guarded composite needs the **general** contract
route: it covers the equivariant intermediate "**the forced set, or nothing if stalled**". -/

/-- The guarded composite's reference narrowing: the forced set, emptied when the node stalls. -/
def guardedRef (key : Key n) (S : Supply n) : NarrowFn n := fun adj χ =>
  if stalled (forceThenConsume key S) adj χ then [] else forcedSet key adj χ

/-- The reference transports — **given that the stall predicate does** (`StallEquivariant`, i.e. an equivariant
supply; see `Stall.StallEquivariant` for why the flag needs this and soundness does not). -/
theorem narrowFnEquivariant_guardedRef {key : Key n} (hk : KeyEquivariant key) {S : Supply n}
    (hse : StallEquivariant (forceThenConsume key S)) :
    NarrowFnEquivariant (guardedRef key S) := by
  intro σ adj χ
  unfold guardedRef stalled
  have hlen := hse σ adj χ
  by_cases h : 1 < (narrow (forceThenConsume key S) adj χ).length
  · rw [if_pos (by rw [hlen]; exact h), if_pos h]; simp
  · rw [if_neg (by rw [hlen]; exact h), if_neg h]
    exact Composite.narrowFnEquivariant_forcedSet hk σ adj χ

/-- **The guarded composite covers its reference.** When the node stalls both sides are empty; otherwise this is
exactly `Composite.coveringOfAt_forceThenConsume` (whose proof is generic in the descending resolver). -/
theorem coveringOfAt_guarded {rf : Refiner n} (hre : RefineEquivariant rf) {key : Key n}
    (hk : KeyEquivariant key) (S : Supply n) :
    CoveringOfAt rf (guard (forceThenConsume key S)) (guardedRef key S) := by
  intro fuel ih adj χ
  set C := forceThenConsume key S with hC
  set R := guard C with hR
  set f : Fin n → Option (Labelled n) :=
    fun v => (descend rf R adj fuel (refineV rf adj (indivOne χ v))).1 with hf
  rw [Stall.narrow_guard]
  unfold guardedRef
  by_cases hst : stalled C adj χ
  · rw [if_pos hst, if_pos hst]
  · rw [if_neg hst, if_neg hst]
    -- the un-stalled case is the composite's own covering argument, with `R = guard C` descending
    have hval : ∀ b : Fin n, f (Consume.rep (Consume.verified S adj χ) b) = f b := by
      intro b
      obtain ⟨α, hα, hαb⟩ := Consume.reach_rep (adj := adj) (χ := χ)
        (fun _ hg => Consume.isColAut_of_mem_verified hg) b
      rw [hf]; simp only; rw [← hαb]
      exact Consume.branchVal_eq_of_isColAut hre ih adj χ hα b
    refine aggregate_congr_mem ?_
    intro x
    rw [Composite.narrow_forceThenConsume]
    constructor
    · intro hx
      obtain ⟨v, hv, hvx⟩ := List.mem_map.mp hx
      obtain ⟨b, hb, hbv⟩ := List.mem_map.mp (List.mem_dedup.mp hv)
      exact List.mem_map.mpr ⟨v, hbv ▸ Composite.rep_mem_forcedSet hk S adj χ hb, hvx⟩
    · intro hx
      obtain ⟨b, hb, hbx⟩ := List.mem_map.mp hx
      refine List.mem_map.mpr ⟨Consume.rep (Consume.verified S adj χ) b, ?_, ?_⟩
      · exact List.mem_dedup.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)
      · rw [hval b]; exact hbx

/-- **★★ THE GUARDED MIXED RESOLVER MEETS THE CONTRACT** — modulo `KeyEquivariant` and `StallEquivariant`. -/
theorem narrowTransport_guarded {rf : Refiner n} (hre : RefineEquivariant rf) {key : Key n}
    (hk : KeyEquivariant key) {S : Supply n}
    (hse : StallEquivariant (forceThenConsume key S)) :
    NarrowTransport rf (guard (forceThenConsume key S)) :=
  narrowTransport_of_coveringOfAt hre (narrowFnEquivariant_guardedRef hk hse)
    (coveringOfAt_guarded hre hk S)

/-- **★★★ THE GUARDED MIXED CANONIZER** — sound, iso-invariant, complete, **and unconditionally polynomial**. -/
theorem guarded_mixed_canonizer {key : Key n} (hk : KeyEquivariant key) {S : Supply n}
    (hse : StallEquivariant (forceThenConsume key S)) :
    CanonSpec.IsCanonicalFormOpt
      (Descend.canonForm? (Refine.encodeFreeFast (n := n)) (guard (forceThenConsume key S))) :=
  Descend.isCanonicalFormOpt_canonForm? Refine.refineEquivariant_encodeFreeFast
    (narrowTransport_guarded Refine.refineEquivariant_encodeFreeFast hk hse)

/-! ## 2. ★ `Handled` — the POSITIVE capability predicate, on the REACHED nodes

**Why `Handled` quantifies over `Descend.Reaches`, not over all colourings (2026-07-16 correction).** The
original definition demanded `CellResolved` at **every** non-discrete colouring — including colourings the
descent never visits. That was undischargeable **in principle** for the intended import route: the seal corpus
produces its firing hypotheses (`CellsAreOrbits`, `CascadesAt`) only at *committed individualization paths*
(`SealBridge.pathCol`), and `CellsAreOrbits` genuinely **fails** at generic non-refinement-closed colourings —
so no sealed family could ever have populated the old predicate, and zero theorem instances of it existed. The
descent only visits `Reaches`-reachable colourings (an over-approximation closed under "individualize a branch
vertex, refine"), so that is the honest domain of the capability claim: `answers_of_handled` goes through
unchanged, and the seal imports can now discharge it (`HandledBridge.lean`). -/

/-- **★★ WHAT THE RESOLVERS HANDLE.** At every **reachable** non-discrete colouring, the branch cell is
**either** connected by the supply's verified generators (consume's domain) **or** separated by the key
(force's domain).

This is the *whole* remaining content of the project, and it is stated **positively**: every strengthening of the
oracle or the key enlarges it, with no re-proof of soundness or of the cost bound (both are unconditional). It is
the mixed-canonizer analogue of the seal's `reachesRigidOrCameron` boundary: an improvable proof target, extended
family-by-family (`HandledBridge.handled_of_seal`) or resolver-by-resolver (`OrbitPrune.handled_congr`), with the
residue always its exact complement. The reachability set is **resolver-independent** (any branch vertex), so a
`Handled` instance survives every future resolver strengthening. -/
def Handled (key : Key n) (S : Supply n) (adj : AdjMatrix n) : Prop :=
  ∀ χ : Colouring n, Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ → ¬ Discrete χ →
    Cost.CellResolved key S adj χ

/-- The old universally-quantified capability still lands (it is strictly stronger) — kept so a discharge that
happens to hold at every colouring plugs in unchanged. -/
theorem handled_of_forall {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    (h : ∀ χ : Colouring n, ¬ Discrete χ → Cost.CellResolved key S adj χ) :
    Handled key S adj :=
  fun χ _ hd => h χ hd

/-- **A 1-WL-rigid graph is handled by ANY resolvers.** If the refined root is already discrete, the root is the
only reachable node (the branch step needs a non-discrete parent), so the capability demand is vacuous. This is
the innermost ring of the boundary: plain refinement finishes, and neither resolver is ever consulted. -/
theorem handled_of_root_discrete (key : Key n) (S : Supply n) {adj : AdjMatrix n}
    (h : Discrete (Descend.refineV (Refine.encodeFreeFast (n := n)) adj (fun _ => 0))) :
    Handled key S adj := by
  have hall : ∀ χ : Colouring n,
      Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ → Discrete χ := by
    intro χ hr
    induction hr with
    | root => exact h
    | step _ hd _ ih => exact absurd ih hd
  exact fun χ hr hd => absurd (hall χ hr) hd

/-- On a handled graph no reachable node ever stalls, so the guarded narrowing is proper there. -/
theorem narrowProper_guard_of_handled {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    (h : Handled key S adj) :
    ∀ χ : Colouring n, Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ → ¬ Discrete χ →
      narrow (guard (forceThenConsume key S)) adj χ ≠ [] := by
  intro χ hr hd
  have hone : (narrow (forceThenConsume key S) adj χ).length = 1 := by
    rcases h χ hr hd with horb | hsep
    · exact Composite.forceThenConsume_singleton_of_cellIsOrbit hd horb
    · exact Composite.forceThenConsume_singleton_of_separating hd hsep
  have hns : ¬ stalled (forceThenConsume key S) adj χ := by
    unfold stalled; omega
  rw [Stall.narrow_guard, if_neg hns]
  intro hc
  rw [hc] at hone
  simp at hone

/-- **★★★ A HANDLED GRAPH ANSWERS.** The guarded descent never flags on it — and it was already unconditionally
polynomial (`Stall.descentCost_guard_le`). So on `Handled`: **sound, iso-invariant, complete, polynomial, and it
answers.** -/
theorem answers_of_handled {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    (h : Handled key S adj) :
    Descend.canonForm? (Refine.encodeFreeFast (n := n)) (guard (forceThenConsume key S)) adj
      ≠ none := by
  -- properness is needed only at `adj`, and only at the REACHED nodes — exactly what `Handled` gives.
  refine Descend.canonForm?_ne_none_reaches Refine.refineSplits_encodeFreeFast
    (fun χ hr hd => narrowProper_guard_of_handled h χ hr hd) ?_
  intro χ v hv
  rw [Stall.narrow_guard] at hv
  by_cases hst : stalled (forceThenConsume key S) adj χ
  · rw [if_pos hst] at hv; exact absurd hv (List.not_mem_nil)
  · rw [if_neg hst] at hv
    exact (Composite.narrowProper_forceThenConsume S).2 adj χ v hv

/-! ## 3. ★ The residue — the complement, and nothing more -/

/-- **THE UNHANDLED RESIDUE** — defined, not asserted: some cell defeats **both** resolvers. -/
def Residue (key : Key n) (S : Supply n) (adj : AdjMatrix n) : Prop :=
  ¬ Handled key S adj

/-- **★★★ `③` — THE DESCENT FLAGS ONLY ON THE RESIDUE.** (`Publication.residue_if_flag`, for the real object.) -/
theorem residue_if_flag {key : Key n} {S : Supply n} {adj : AdjMatrix n}
    (hflag : Descend.canonForm? (Refine.encodeFreeFast (n := n))
      (guard (forceThenConsume key S)) adj = none) :
    Residue key S adj :=
  fun h => answers_of_handled h hflag

/-- Unfolded: a residual graph has a **reachable** cell that is **neither** supply-connected **nor**
key-separated — which is exactly `Composite.forceThenConsume_stall`'s *attribution*. Each residual cell is
assignable to **one** side's weakness, and it is a cell the descent can actually be confronted with. -/
theorem residue_iff {key : Key n} {S : Supply n} {adj : AdjMatrix n} :
    Residue key S adj ↔ ∃ χ : Colouring n,
      Descend.Reaches (Refine.encodeFreeFast (n := n)) adj χ ∧ ¬ Discrete χ ∧
        ¬ Cost.CellResolved key S adj χ := by
  unfold Residue Handled
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h (fun χ hr hd => hc χ hr hd)
  · rintro ⟨χ, hr, hd, hnr⟩ h
    exact hnr (h χ hr hd)

/-! ## 4. Non-vacuity — the residue is INHABITED, and it SHRINKS

`unhandledResidue_nonvacuous` was **unprovable in principle** while the `Publication` residue atoms were `opaque …
: Prop` with no definition. With `Residue` a *definition*, it is provable — and here it is, on the weakest possible
resolvers (an empty supply and a constant key certify nothing, so any cell with two vertices defeats them).

That witness is deliberately degenerate: it shows the predicate is **inhabited**, not that the residue is *hard*.
The interesting content is that `Residue` **shrinks as the resolvers strengthen**, and both directions are already
*measured* in `PerformanceTest.lean`:

* `C₇` with the **rotation-only** supply — the cell `{1,6}` after individualizing `0` is an orbit under the
  **reflection**, which that supply lacks ⟹ neither route fires ⟹ **flags** (residual);
* `C₇` with the **full** `Aut(C₇) = D₇` supply ⟹ consume closes it ⟹ **answers** (no longer residual).

The residue was pure oracle incompleteness, and strengthening the oracle removed it — with **no re-proof of ①, of
the cost bound, or of anything else.** That is the architecture doing its job. -/

/-- The empty supply certifies nothing. -/
def emptySupply : Supply n := fun _ _ => ([], 0)

/-- A constant key separates nothing. -/
def constKey : Key n := fun _ _ _ => ([], 0)

theorem keyEquivariant_constKey : KeyEquivariant (constKey (n := n)) := fun _ _ _ _ => rfl

theorem not_wordReach_nil {u w : Fin n} (h : u ≠ w) :
    ¬ Consume.WordReach ([] : List (Equiv.Perm (Fin n))) u w := by
  intro hr
  cases hr with
  | refl => exact h rfl
  | step _ hg => exact absurd hg (List.not_mem_nil)

/-- The empty graph on two vertices — the smallest graph whose swap symmetry survives refinement, so its root
node is genuinely non-discrete and *reached*. (An arbitrary `AdjMatrix 2` would not do: a graph whose root
refines to discrete is handled by ANY resolvers — `handled_of_root_discrete` — hence not residual.) -/
def adjE2 : AdjMatrix 2 := ⟨fun _ _ => 0⟩

/-- **★★ `unhandledResidue_nonvacuous` — the residue is INHABITED.** With resolvers that certify nothing, the
empty two-vertex graph is residual: its refined **root** — a genuinely reached node — still has both vertices in
one cell (the swap is a symmetry of the graph and the refiner is equivariant, so no round can split them), the
empty supply cannot connect them and the constant key cannot separate them. -/
theorem residue_nonvacuous :
    Residue (constKey (n := 2)) (emptySupply (n := 2)) adjE2 := by
  rw [residue_iff]
  set χ₀ : Colouring 2 := Descend.refineV (Refine.encodeFreeFast (n := 2)) adjE2 (fun _ => 0)
    with hχ₀
  -- the swap is a symmetry of the empty graph and the refiner is equivariant ⟹ the root keeps `0 ∼ 1`
  have hswap : Descend.transportColouring (Equiv.swap 0 1) χ₀ = χ₀ :=
    (Refine.refineEquivariant_encodeFreeFast (n := 2) (Equiv.swap 0 1) adjE2 (fun _ => 0)).symm
  have h01 : χ₀ 0 = χ₀ 1 := by
    have h := congrFun hswap 1
    simpa [Descend.transportColouring, Equiv.symm_swap, Equiv.swap_apply_right] using h
  have hnd : ¬ Discrete χ₀ := fun hdisc => absurd (hdisc 0 1 h01) (by decide)
  refine ⟨χ₀, Descend.Reaches.root, hnd, ?_⟩
  -- the (reached) root cell defeats both resolvers
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ (branches_ne_nil hnd)
  obtain ⟨c, hc, hvc⟩ := Consume.exists_targetColour_of_mem hv
  have hvall : χ₀ 0 = χ₀ v ∧ χ₀ 1 = χ₀ v := by
    fin_cases v
    · exact ⟨rfl, h01.symm⟩
    · exact ⟨h01, rfl⟩
  have h0 : (0 : Fin 2) ∈ branches χ₀ := (mem_branches_iff hc 0).mpr (hvall.1.trans hvc)
  have h1 : (1 : Fin 2) ∈ branches χ₀ := (mem_branches_iff hc 1).mpr (hvall.2.trans hvc)
  rintro (horb | hsep)
  · -- consume: the empty supply gives no words
    have hne : (0 : Fin 2) ≠ 1 := by decide
    have := horb 0 h0 1 h1
    have hverif : Consume.verified (emptySupply (n := 2)) adjE2 χ₀ = [] := rfl
    rw [hverif] at this
    exact not_wordReach_nil hne this
  · -- force: the constant key cannot tell `0` from `1`
    have hne : (0 : Fin 2) ≠ 1 := by decide
    exact hne (hsep 0 h0 1 h1 rfl)

end Residue
end ChainDescent
