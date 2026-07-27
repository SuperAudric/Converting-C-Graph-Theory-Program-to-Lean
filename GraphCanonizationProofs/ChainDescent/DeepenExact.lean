import ChainDescent.DeepenKey

/-!
# Workstream B — `orbKey` is EXACT, so a consume failure makes FORCE FIRE

`DeepenKey` gave the `①` half: `orbKey` is `Force.KeyEquivariant`, unconditionally. That alone says
nothing about *firing* — the constant key is equivariant too. This file supplies the firing half and
closes the consume→force hook.

**The pivot is the direction that needs no hypothesis.** `keyEquivariant_orbKey` already gives
"same orbit ⟹ same key" (an automorphism is a relabelling that fixes the graph, so
`Force.keyV_aut_invariant` applies). What firing needs is the **converse**:

> `readKey` equal ⟹ the two branch vertices are in the same orbit.   (`isColAut_of_readKey_eq`)

and that is *unconditional* — no `Tinhofer`, no rigidity. It is pure completeness of the encoding:

* the greedy leaf at fuel `n` is **discrete** (§1, the `Descend.ncol` measure — the same one
  `deepen_succeeds` uses, with `ncol_lt_step_of_partner` already isolated in `DeepenLocated`), and its
  colours are `< n` (`Refine.refineRound_lt`), so each leaf colour class is a **singleton**;
* hence `readAt` at a leaf colour pair is a *single adjacency entry* and `readColAt` a *single parent
  colour* (§2), so equal keys give a permutation `ρ` matching the leaves colour-for-colour with
  `relabelAdj ρ adj = adj` and `indivOne χ u = indivOne χ w ∘ ρ`;
* and `indivOne χ u` takes an **odd** value exactly at `u` — so that last equation forces `ρ u = w`,
  while halving it gives `χ ∘ ρ = χ`. Together: `IsColAut adj χ ρ ∧ ρ u = w` (§4).

**The payoff (§5).** At a node that is `Tinhofer` (so both guards are open) with a `RigidObstructionAt`
in its branch cell, `orbKey` separates the obstructed pair, so `Force.forceBy_narrows_of_key_ne` fires.
Chaining with `DeepenLocated.consume_fail_locates`:

> **`consume_fail_force_fires`** — if `deepenSupply` fails to make the branch cell one orbit, then the
> descent reaches a colouring `ψ` at which `forceBy orbKey` **strictly narrows**.

That is the target this track has been aiming at, in the only form that can be true: §1.2 of the
scoping doc records the measured witness (CFI over a cubic base, `m = 8`) showing that force *cannot*
be made to fire at `χ` itself — there the branch cell is a single orbit and
`Force.forceBy_no_narrowing_on_orbit` forbids it. The reachable-node form is what survives.

**⚠ Measured, before the proof** (`scratchpad/probe_orbit_oracle.py`): at **147 of 147** hook nodes
across seven families `orbKey` fires *and* its fibres are exactly the true `Aut`-orbits, with every
leaf discrete. So neither `orbKey`'s definedness nor its exactness is vacuous. See scoping doc §2.5.
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (IsColAut)
open ChainDescent.Descend (transportColouring)

variable {n : Nat}

/-! ## 1. The greedy leaf is discrete, with colours `< n` -/

/-- Warm refinement produces **ranks**, so every colour is `< n`. -/
theorem warmRefineR_lt (adj : AdjMatrix n) (χ : Colouring n) (v : Fin n) :
    Refine.warmRefineR adj χ v < n := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show ((Refine.refineRound adj)^[m + 1] χ) v < m + 1
  rw [Function.iterate_succ_apply']
  exact Refine.refineRound_lt adj _ v

theorem step_col_lt (adj : AdjMatrix n) (χ : Colouring n) (v x : Fin n) :
    (step adj χ v).col x < n := by
  rw [step_col_eq]; exact warmRefineR_lt adj _ x

theorem leafOf_lt (adj : AdjMatrix n) :
    ∀ (fuel : Nat) (cur : Refine.ColData n), (∀ x, cur.col x < n) →
      ∀ x, (leafOf adj fuel cur).col x < n := by
  intro fuel
  induction fuel with
  | zero => intro cur h x; rw [leafOf_zero]; exact h x
  | succ fuel ih =>
      intro cur h x
      cases hco : chooseIdK (List.finRange n) cur.col with
      | none => rw [leafOf_succ_none adj fuel cur hco]; exact h x
      | some cid =>
          cases hcell : cidCell cur.col cid with
          | nil =>
              have hf : (List.finRange n).filter (fun v => cur.col v == cid) = [] := hcell
              rw [leafOf_succ_nil adj fuel cur hco hf]; exact h x
          | cons w rest =>
              have hf : (List.finRange n).filter (fun v => cur.col v == cid) = w :: rest := hcell
              rw [leafOf_succ_cons adj fuel cur hco hf]
              exact ih _ (fun y => step_col_lt adj cur.col w y) x

/-- **The greedy leaf is DISCRETE once the fuel covers the colour deficit.** Same measure as
`deepen_succeeds`: every level individualizes a cell with ≥ 2 members, so `Descend.ncol` strictly
rises; when it reaches `n` the colouring is injective. -/
theorem leafOf_discrete (adj : AdjMatrix n) :
    ∀ (fuel : Nat) (cur : Refine.ColData n), n ≤ fuel + Descend.ncol cur.col →
      Discrete (leafOf adj fuel cur).col := by
  intro fuel
  induction fuel with
  | zero =>
      intro cur h
      rw [leafOf_zero]
      exact Descend.discrete_of_ncol_eq
        (le_antisymm (Descend.ncol_le _) (by omega))
  | succ fuel ih =>
      intro cur h
      cases hco : chooseIdK (List.finRange n) cur.col with
      | none =>
          rw [leafOf_succ_none adj fuel cur hco]
          exact discrete_of_chooseIdK_none hco
      | some cid =>
          cases hcell : cidCell cur.col cid with
          | nil =>
              exfalso
              have hlen : 2 ≤ (cidCell cur.col cid).length := chooseIdK_mem _ _ hco
              rw [hcell] at hlen; simp at hlen
          | cons w rest =>
              have hf : (List.finRange n).filter (fun v => cur.col v == cid) = w :: rest := hcell
              rw [leafOf_succ_cons adj fuel cur hco hf]
              refine ih _ ?_
              have hlt := ncol_lt_step_of_partner adj (partner_of_chooseIdK hco hcell)
              omega

theorem leafOf_discrete_n (adj : AdjMatrix n) (cur : Refine.ColData n) :
    Discrete (leafOf adj n cur).col :=
  leafOf_discrete adj n cur (by omega)

/-! ## 2. Reading a DISCRETE colouring reads one entry -/

theorem filter_eq_singleton_of_discrete {χ : Colouring n} (hd : Discrete χ) {x : Fin n} {c : Nat}
    (hx : χ x = c) : Finset.univ.filter (fun u => χ u = c) = {x} := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hy; exact hd y x (by rw [hy, hx])
  · rintro rfl; exact hx

theorem readAt_discrete {adj : AdjMatrix n} {χ : Colouring n} (hd : Discrete χ) {x y : Fin n}
    {c d : Nat} (hx : χ x = c) (hy : χ y = d) : readAt adj χ c d = adj.adj x y := by
  unfold readAt
  rw [filter_eq_singleton_of_discrete hd hx, Finset.sum_singleton,
      filter_eq_singleton_of_discrete hd hy, Finset.sum_singleton]

theorem readColAt_discrete {φ χ : Colouring n} (hd : Discrete χ) {x : Fin n} {c : Nat}
    (hx : χ x = c) : readColAt φ χ c = φ x := by
  unfold readColAt
  rw [filter_eq_singleton_of_discrete hd hx, Finset.sum_singleton]

/-! ## 3. Components of a key equality -/

theorem readKey_components {adj : AdjMatrix n} {φa φb χa χb : Colouring n}
    (h : readKey adj φa χa = readKey adj φb χb) :
    (∀ k < n * n, readAtIdx adj χa k = readAtIdx adj χb k) ∧
      (∀ c < n, readColAt φa χa c = readColAt φb χb c) := by
  unfold readKey at h
  have hlen : ((List.range (n * n)).map (readAtIdx adj χa)).length
      = ((List.range (n * n)).map (readAtIdx adj χb)).length := by simp
  obtain ⟨h1, h2⟩ := List.append_inj h hlen
  exact ⟨fun k hk => List.map_inj_left.mp h1 k (List.mem_range.mpr hk),
         fun c hc => List.map_inj_left.mp h2 c (List.mem_range.mpr hc)⟩

/-! ## 4. ★★ B1 — EQUAL KEYS ⟹ SAME ORBIT (no hypothesis)

A discrete colouring with values `< n` is a bijection onto `Fin n` (injective on a `Fintype` of the
right card), so two of them can be matched colour-for-colour. The matching permutation is then read
off the key equality: the adjacency component makes it an automorphism, and the parent component —
whose **odd** values pin the individualized vertex — makes it carry `u` to `w`. -/

/-- A discrete colouring with colours `< n`, as a permutation. -/
noncomputable def colEquiv {χ : Colouring n} (hd : Discrete χ) (hl : ∀ x, χ x < n) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun x => (⟨χ x, hl x⟩ : Fin n))
    (Finite.injective_iff_bijective.mp
      (fun x y hxy => hd x y (congrArg Fin.val hxy)))

theorem colEquiv_val {χ : Colouring n} (hd : Discrete χ) (hl : ∀ x, χ x < n) (x : Fin n) :
    ((colEquiv hd hl) x : Fin n).val = χ x := rfl

/-- The permutation matching two discrete colourings colour-for-colour. -/
noncomputable def matchPerm {χa χb : Colouring n} (hda : Discrete χa) (hla : ∀ x, χa x < n)
    (hdb : Discrete χb) (hlb : ∀ x, χb x < n) : Equiv.Perm (Fin n) :=
  (colEquiv hda hla).trans (colEquiv hdb hlb).symm

theorem matchPerm_col {χa χb : Colouring n} (hda : Discrete χa) (hla : ∀ x, χa x < n)
    (hdb : Discrete χb) (hlb : ∀ x, χb x < n) (x : Fin n) :
    χb (matchPerm hda hla hdb hlb x) = χa x := by
  have h : (colEquiv hdb hlb) (matchPerm hda hla hdb hlb x) = (colEquiv hda hla) x := by
    show (colEquiv hdb hlb) ((colEquiv hdb hlb).symm ((colEquiv hda hla) x)) = _
    exact Equiv.apply_symm_apply _ _
  have := congrArg Fin.val h
  rwa [colEquiv_val, colEquiv_val] at this

/-- **★★ THE COMPLETENESS DIRECTION — UNCONDITIONAL.** Two discrete leaves with equal reads are
related by a colour-automorphism carrying `u` to `w`. No `Tinhofer`: this is completeness of the
encoding, not a property of the descent. -/
theorem isColAut_of_readKey_eq {adj : AdjMatrix n} {χ : Colouring n} {u w : Fin n}
    {χa χb : Colouring n} (hda : Discrete χa) (hla : ∀ x, χa x < n)
    (hdb : Discrete χb) (hlb : ∀ x, χb x < n)
    (hkey : readKey adj (Descend.indivOne χ u) χa = readKey adj (Descend.indivOne χ w) χb) :
    ∃ ρ : Equiv.Perm (Fin n), IsColAut adj χ ρ ∧ ρ u = w := by
  obtain ⟨hA, hC⟩ := readKey_components hkey
  set ρ := matchPerm hda hla hdb hlb with hρdef
  have hmatch : ∀ x, χb (ρ x) = χa x := matchPerm_col hda hla hdb hlb
  -- `n > 0`: there is a vertex.
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  -- (a) `ρ` preserves adjacency, from the flattened adjacency component.
  have hadj : ∀ i j : Fin n, adj.adj (ρ i) (ρ j) = adj.adj i j := by
    intro i j
    have hci : χa i < n := hla i
    have hcj : χa j < n := hla j
    have hk : χa j + n * χa i < n * n := by
      have h1 : n * χa i + n ≤ n * n := by
        have h2 : n * (χa i + 1) ≤ n * n := Nat.mul_le_mul_left n (by omega)
        simpa [Nat.mul_add] using h2
      omega
    have hdiv : (χa j + n * χa i) / n = χa i := by
      rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hcj]
      omega
    have hmod : (χa j + n * χa i) % n = χa j := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcj]
    have h := hA _ hk
    unfold readAtIdx at h
    rw [hdiv, hmod] at h
    rw [readAt_discrete (x := i) (y := j) hda rfl rfl,
        readAt_discrete (x := ρ i) (y := ρ j) hdb (hmatch i) (hmatch j)] at h
    exact h.symm
  -- (b) the parent component: `indivOne χ u = indivOne χ w ∘ ρ`
  have hind : ∀ x : Fin n, Descend.indivOne χ u x = Descend.indivOne χ w (ρ x) := by
    intro x
    have h := hC _ (hla x)
    rw [readColAt_discrete (x := x) hda rfl,
        readColAt_discrete (x := ρ x) hdb (hmatch x)] at h
    exact h
  -- the odd value of `indivOne χ u` sits exactly at `u`, which pins `ρ u = w`
  have hρu : ρ u = w := by
    have h := hind u
    unfold Descend.indivOne at h
    rw [if_pos rfl] at h
    by_cases hy : ρ u = w
    · exact hy
    · rw [if_neg hy] at h; omega
  have hcol : ∀ x : Fin n, χ (ρ x) = χ x := by
    intro x
    have h := hind x
    unfold Descend.indivOne at h
    by_cases hx : x = u
    · subst hx
      rw [if_pos rfl, if_pos hρu] at h
      omega
    · rw [if_neg hx] at h
      by_cases hy : ρ x = w
      · exfalso
        rw [if_pos hy] at h
        omega
      · rw [if_neg hy] at h; omega
  exact ⟨ρ, ⟨hadj, hcol⟩, hρu⟩

/-! ## 5. ★★★ FORCE FIRES

Assembling: at a node where both guards are open, `orbKey` separates any pair that no
colour-automorphism links. Combined with `DeepenLocated`'s localization, a consume failure makes force
fire at a reachable node. -/

/-- The guard is open at every branch rep of an `Tinhofer` node — that is what `Tinhofer` says. -/
theorem tinhoferPath_of_tinhofer {adj : AdjMatrix n} {χ : Colouring n} (hA : Tinhofer adj χ)
    {v : Fin n} (hv : v ∈ Descend.branches χ) : TinhoferPath adj χ n (step adj χ v) := hA v hv

/-- **★★ `orbKey` SEPARATES a non-automorphic pair.** The contrapositive of `isColAut_of_readKey_eq`,
with both guards open. -/
theorem orbKey_ne_of_no_aut {adj : AdjMatrix n} {χ : Colouring n} {u w : Fin n}
    (hAu : TinhoferPath adj χ n (step adj χ u)) (hAw : TinhoferPath adj χ n (step adj χ w))
    (hno : ∀ σ : Equiv.Perm (Fin n), IsColAut adj χ σ → σ u ≠ w) :
    Force.keyV orbKey adj χ u ≠ Force.keyV orbKey adj χ w := by
  rw [keyV_orbKey, keyV_orbKey, if_pos hAu, if_pos hAw]
  intro hkey
  obtain ⟨ρ, hρ, hρu⟩ :=
    isColAut_of_readKey_eq (χ := χ) (u := u) (w := w)
      (leafOf_discrete_n adj (step adj χ u))
      (leafOf_lt adj n (step adj χ u) (fun x => step_col_lt adj χ u x))
      (leafOf_discrete_n adj (step adj χ w))
      (leafOf_lt adj n (step adj χ w) (fun x => step_col_lt adj χ w x))
      hkey
  exact hno ρ hρ hρu

/-- **★★★ B3 — AT AN `Tinhofer` NODE WITH A RIGID OBSTRUCTION, FORCE STRICTLY NARROWS.**
The obstruction names a branch pair no colour-automorphism links; `orbKey` separates it
(`orbKey_ne_of_no_aut`); `Force.forceBy_narrows_of_key_ne` converts that into strictly fewer
branches. Note this does **not** contradict `Force.forceBy_no_narrowing_on_orbit`: the obstruction is
exactly the statement that the cell is *not* a single orbit. -/
theorem forceBy_orbKey_narrows {adj : AdjMatrix n} {χ : Colouring n} {c : Nat}
    (hc : Descend.targetColour χ = some c) (hA : Tinhofer adj χ)
    (hobs : RigidObstructionAt adj χ c) :
    (Descend.narrow (Force.forceBy orbKey) adj χ).length < (Descend.branches χ).length := by
  obtain ⟨u, w, hu, hw, hno⟩ := hobs
  have hub : u ∈ Descend.branches χ := (Descend.mem_branches_iff hc u).mpr hu
  have hwb : w ∈ Descend.branches χ := (Descend.mem_branches_iff hc w).mpr hw
  exact Force.forceBy_narrows_of_key_ne hub hwb
    (orbKey_ne_of_no_aut (tinhoferPath_of_tinhofer hA hub)
      (tinhoferPath_of_tinhofer hA hwb) hno)

/-- **★★★ B2 — AT AN `Tinhofer` NODE, `orbKey`'s FIBRES **ARE** THE ORBITS.** `⟸` is the ceiling
(`Force.keyV_aut_invariant`, free from `keyEquivariant_orbKey`); `⟹` is `isColAut_of_readKey_eq`.

This is also the **consistency check** against `Force.forceBy_no_narrowing_on_orbit`: the key is
constant on each orbit, so force can never cut *inside* one — it separates orbits and nothing finer.
Measured agreement: 147/147 hook nodes (scoping doc §2.5). -/
theorem orbKey_eq_iff_orbit {adj : AdjMatrix n} {χ : Colouring n} (hA : Tinhofer adj χ)
    {u w : Fin n} (hu : u ∈ Descend.branches χ) (hw : w ∈ Descend.branches χ) :
    Force.keyV orbKey adj χ u = Force.keyV orbKey adj χ w
      ↔ ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w := by
  constructor
  · intro hkey
    by_contra hno
    push Not at hno
    exact orbKey_ne_of_no_aut (tinhoferPath_of_tinhofer hA hu)
      (tinhoferPath_of_tinhofer hA hw) (fun σ hσ => hno σ hσ) hkey
  · rintro ⟨σ, hσ, rfl⟩
    exact (Force.keyV_aut_invariant keyEquivariant_orbKey hσ.relabel hσ.transport u).symm

/-- **★★★ D2 — FORCE NARROWS THE CELL TO A SINGLE ORBIT.** Any two survivors of `forceBy orbKey`
attain the same (minimal) key, hence by `orbKey_eq_iff_orbit` are automorphic. So at an `Tinhofer`
node force does not merely *shrink* the fan-out — it reduces it to one orbit, which is precisely the
input `Composite.forceThenConsume_singleton_of_cellIsOrbit` wants. -/
theorem forcedSet_single_orbit {adj : AdjMatrix n} {χ : Colouring n} (hA : Tinhofer adj χ)
    {u w : Fin n}
    (hu : u ∈ Force.keepMin orbKey adj χ (Descend.branches χ))
    (hw : w ∈ Force.keepMin orbKey adj χ (Descend.branches χ)) :
    ∃ σ : Equiv.Perm (Fin n), IsColAut adj χ σ ∧ σ u = w := by
  obtain ⟨hub, hminu⟩ := (Force.mem_keepMin_iff u).mp hu
  obtain ⟨hwb, hminw⟩ := (Force.mem_keepMin_iff w).mp hw
  exact (orbKey_eq_iff_orbit hA hub hwb).mp
    (Descend.lexLeList_antisymm _ _ (hminu w hwb) (hminw u hub))

/-- Every non-discrete colouring has a branch colour. -/
theorem exists_targetColour {χ : Colouring n} (hd : ¬ Discrete χ) :
    ∃ c, Descend.targetColour χ = some c := by
  cases hc : Descend.targetColour χ with
  | none =>
      exact absurd (by unfold Descend.branches; rw [hc]) (Descend.branches_ne_nil hd)
  | some c => exact ⟨c, rfl⟩

/-- **★★★ D1 — THE HOOK, CLOSED. A CONSUME FAILURE MAKES FORCE FIRE.**

If `deepenSupply` cannot make the branch cell a single orbit, then the descent reaches a colouring
`ψ` — the node itself when it is `Tinhofer`, otherwise the deeper one `not_tinhofer_deepest`
produces — at which `forceBy orbKey` **strictly narrows the branch cell**.

This is the strongest form available: §1.2 of the scoping doc records a measured witness (CFI over a
random cubic base, `m = 8`) where consume fails at a node whose branch cell is a *single orbit*, so
force provably cannot fire *there* (`Force.forceBy_no_narrowing_on_orbit`). Relocating to a reachable
node is not a weakening of the target — it is the target. -/
theorem consume_fail_force_fires (adj : AdjMatrix n) {χ : Colouring n}
    (hd : ¬ Discrete χ) (hfail : ¬ Consume.CellIsOrbit deepenSupply adj χ) :
    ∃ ψ : Colouring n, DescentReach adj χ ψ ∧
      (Descend.narrow (Force.forceBy orbKey) adj ψ).length < (Descend.branches ψ).length := by
  obtain ⟨c, hc⟩ := exists_targetColour hd
  by_cases hA : Tinhofer adj χ
  · exact ⟨χ, DescentReach.refl _,
      forceBy_orbKey_narrows hc hA (rigidObstructionAt_branch_of_tinhofer hc hA hfail)⟩
  · obtain ⟨ψ, hreach, hAψ, cid, hct, hobs⟩ := not_tinhofer_deepest adj hA
    exact ⟨ψ, hreach, forceBy_orbKey_narrows hct hAψ hobs⟩

end Deepen
end ChainDescent
