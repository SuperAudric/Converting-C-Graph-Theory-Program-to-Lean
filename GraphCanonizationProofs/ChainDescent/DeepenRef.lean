import ChainDescent.DeepenCrux
/-! ⚠⚠ SUPERSEDED & PARKED (2026-07-23, TRACK A) — NOT in `build.sh`, DOES NOT COMPILE against the current
`deepen`. This is the DISCARDED reference route (`deepenRefSupply`/`DeepenRefInExec`/R1/R2) for `deepenSupply`
's `①c`. It was made MOOT by the whole-graph-discretize redesign: `①c` now closes modulo `{Tinhofer}` alone
(`DeepenTinhofer.deepenSupply_guarded_canonizer_direct`), with `[DISC]`/gate/termination structural and
`AnchorFires` eliminated. Retained for provenance only — see `docs/chain-descent-deepen-supply.md` STATUS +
§8/§9 (provenance) and `docs/00-START-HERE.md` §2 C3b. Do NOT build on this. -/


/-!
# `C3b` tranche 2, part III — the all-paths reference and the easy inclusion

Part I (`DeepenTransport`) isolated the whole ①c residue to the per-level vertex pick `w :: _`.
Part II (`DeepenCrux`) named the residue and proved soundness (`deepenGens_isColAut`). This file
builds the object both remaining routes share and lands the direction that is unconditional.

## The reference (proof-side only — enumerated, never shipped)

`deepenRefGens` runs the *same* deepen/replay/twist pipeline as the executable, but branches over
**every** member of the chosen sub-cell at each level, on both the anchor descent (`deepenAll`) and
the replay (`replayAll`). It is exponential and never executed by the canonizer; it exists only so
①c can be discharged by the `OrbitPrune.SameOrbits` reduction against an equivariant reference — the
exact shape `kernelSupply` used (`KernelRef` / `KernelTransport`).

## The two routes to ①c, and where this file sits

Both discharge ①c through `SameOrbits deepenRefSupply deepenSupply` + reference equivariance:

* **Route (a) — "the pick is interchangeable."** Prove `SameOrbits` in FULL, including the hard
  direction (ref orbits ⊆ exec orbits): enumerating every pick reaches no orbit the single canonical
  pick misses. **Measured true on every partially-firing witness** (`ScratchPickTest`, 2026-07-20:
  `G8` exec 16 / ref 28 generators but BOTH orbit partition `[2,2,4]`; `t3` exec 6 / ref 96 but both
  `[3]`; `wcyc9` both `[3]`). The all-picks reference reaches the same orbits as the one pick — the
  surplus generators are already words in the executable's.
* **Route (b) — "target the reference, not truth" (fallback).** If the hard direction resists a
  clean proof, restate the crux (`DeepenForcedMatch`) against `deepenRefGens` instead of against
  `Aut`. This sidesteps the completeness-vs-truth question entirely (which is where the retracted
  GI∈P anxiety lived): the claim becomes procedure-internal path-independence, never "the executable
  recovers the true orbit". Strictly weaker, and enough — ①c needs an equivariant *reference*, not
  the true orbit relation.

**What this file proves (unconditional, both routes):** the single canonical pick is one of the
enumerated paths, so `deepenGens ⊆ deepenRefGens`, giving the easy `⊇` direction of `SameOrbits`
(exec orbits ⊆ ref orbits). What remains — the hard `⊆` direction and the reference's own transport
— is the residue, stated at the end as `SameOrbits_deepenRef` / `deepenRefSupply` equivariance,
tackled next (the `KernelTransport` analog).
-/

namespace ChainDescent
namespace Deepen

open ChainDescent.Consume (Supply gens verified IsColAut)
open ChainDescent.Deck2 (permOf)

variable {n : Nat}

/-! ## 1. All-picks deepen and replay -/

/-- All-picks deepening: at each level branch over EVERY member of the chosen sub-cell, not just the
head `w :: _`. The recorded id sequence is the same for every branch (`chooseIdK` is pick-invariant,
`DeepenTransport.chooseIdK_transport`); only the vertex chosen differs. -/
def deepenAll (adj : AdjMatrix n) (χp : Colouring n) :
    Nat → Refine.ColData n → List Nat → List (Refine.ColData n × List Nat)
  | 0, _, _ => []
  | fuel + 1, cur, seq =>
      let χc := cur.col
      let K := coupled χp χc
      if K.isEmpty then []
      else match chooseIdK K χc with
        | none => [(cur, seq.reverse)]
        | some cid =>
            let mem := (List.finRange n).filter (fun v => χc v == cid)
            mem.flatMap (fun w => deepenAll adj χp fuel (step adj χc w) (cid :: seq))

/-- All-picks replay: follow the id sequence, branching over every member at each level. -/
def replayAll (adj : AdjMatrix n) : List Nat → Refine.ColData n → List (Refine.ColData n)
  | [], cur => [cur]
  | cid :: rest, cur =>
      let χc := cur.col
      let mem := (List.finRange n).filter (fun v => χc v == cid)
      if mem.length < 2 then []
      else mem.flatMap (fun w => replayAll adj rest (step adj χc w))

/-! ## 2. The reference generator set and supply -/

/-- The all-anchors × ALL-PATHS reference generators, built through the SAME `twistOf` as the
executable. Exponential, proof-side only. -/
def deepenRefGens (adj : AdjMatrix n) (χ : Colouring n) : List (Equiv.Perm (Fin n)) :=
  let cell := Descend.branches χ
  let firsts : List (Fin n × Refine.ColData n) := cell.map (fun r => (r, step adj χ r))
  firsts.flatMap (fun p1 =>
    (deepenAll adj χ n p1.2 []).flatMap (fun ds =>
      let χ1 := ds.1.col
      let K := coupled χ χ1
      if K.isEmpty || !allSingletonsK K χ1 then []
      else firsts.flatMap (fun pj =>
        if pj.1 == p1.1 then []
        else (replayAll adj ds.2 pj.2).filterMap (fun dj => twistOf adj χ χ1 K dj.col))))

/-- The reference supply. Same cost slot as the executable (never billed — proof-side). -/
def deepenRefSupply : Supply n := fun adj χ => (deepenRefGens adj χ, n * n * n * n * n * n)

/-! ## 3. The single pick is one of the enumerated paths -/

/-- `deepen`'s canonical result is one of `deepenAll`'s leaves: the head `w :: _` is a member of
`mem`, so the single-pick recursion is the head branch of the all-picks `flatMap`. -/
theorem deepen_mem_deepenAll (adj : AdjMatrix n) (χp : Colouring n) :
    ∀ (fuel : Nat) (cur : Refine.ColData n) (seq : List Nat) (res : Refine.ColData n × List Nat),
      deepen adj χp fuel cur seq = some res → res ∈ deepenAll adj χp fuel cur seq := by
  intro fuel
  induction fuel with
  | zero => intro cur seq res h; simp [deepen] at h
  | succ fuel ih =>
      intro cur seq res h
      unfold deepen at h
      unfold deepenAll
      dsimp only at h ⊢
      split at h
      · simp at h
      · rename_i hK
        rw [if_neg hK]
        split at h
        · -- chooseIdK = none : h reduced to `some (cur, seq.reverse) = some res`
          rename_i hcid
          simp only [hcid, List.mem_singleton, Option.some.injEq] at h ⊢
          exact h.symm
        · -- chooseIdK = some cid
          rename_i cid hcid
          simp only [hcid]
          split at h
          · simp at h
          · rename_i w tail hfilter
            simp only [hfilter, List.mem_flatMap]
            exact ⟨w, List.mem_cons_self .., ih _ _ _ h⟩

/-- `replay`'s canonical result is one of `replayAll`'s leaves, by the same head-is-a-member argument. -/
theorem replay_mem_replayAll (adj : AdjMatrix n) :
    ∀ (seq : List Nat) (cur res : Refine.ColData n),
      replay adj seq cur = some res → res ∈ replayAll adj seq cur := by
  intro seq
  induction seq with
  | nil => intro cur res h; simp [replay] at h; simp [replayAll, h]
  | cons cid rest ih =>
      intro cur res h
      unfold replay at h
      unfold replayAll
      dsimp only at h ⊢
      split at h
      · simp at h
      · rename_i hlt
        rw [if_neg hlt]
        split at h
        · simp at h
        · rename_i w tail hfilter
          simp only [hfilter, List.mem_flatMap]
          exact ⟨w, List.mem_cons_self .., ih _ _ h⟩

/-! ## 4. The easy inclusion — `deepenGens ⊆ deepenRefGens` -/

/-- **Every executable generator is a reference generator.** The single canonical pick's anchor
result is a `deepenAll` leaf and its replay is a `replayAll` leaf, and both build the twist through
the same `twistOf`, so the emitted generator appears verbatim in the reference. -/
theorem deepenGens_subset_ref (adj : AdjMatrix n) (χ : Colouring n) :
    ∀ ρ ∈ deepenGens adj χ, ρ ∈ deepenRefGens adj χ := by
  intro ρ hρ
  unfold deepenGens at hρ
  unfold deepenRefGens
  rw [List.mem_flatMap] at hρ ⊢
  obtain ⟨p1, hp1, hρ⟩ := hρ
  refine ⟨p1, hp1, ?_⟩
  -- anchor deepen: split on the single-pick result
  cases hd : deepen adj χ n p1.2 [] with
  | none => rw [hd] at hρ; simp at hρ
  | some ds =>
      rw [hd] at hρ
      obtain ⟨d1, seq⟩ := ds
      dsimp only at hρ
      rw [List.mem_flatMap]
      -- (d1, seq) is one of the all-picks leaves
      refine ⟨(d1, seq), deepen_mem_deepenAll adj χ n p1.2 [] (d1, seq) hd, ?_⟩
      dsimp only
      split at hρ
      · simp at hρ                       -- gate failed: exec emitted nothing
      · rename_i hgate
        rw [if_neg hgate]
        -- exec: filterMap over `firsts`; ref: flatMap over `firsts` then filterMap over `replayAll`
        rw [List.mem_filterMap] at hρ
        rw [List.mem_flatMap]
        obtain ⟨pj, hpj, hρ⟩ := hρ
        refine ⟨pj, hpj, ?_⟩
        split at hρ
        · simp at hρ                     -- pj = p1 (self): exec skips it
        · rename_i hne
          rw [if_neg hne]
          rw [List.mem_filterMap]
          -- the single-pick replay result `dj`, lifted to a `replayAll` leaf
          split at hρ
          · simp at hρ                   -- replay failed
          · rename_i dj hr
            exact ⟨dj, replay_mem_replayAll adj seq pj.2 dj hr, hρ⟩

/-! ## 5. The easy `SameOrbits` direction — exec orbits ⊆ ref orbits -/

/-- Word-reachability is monotone in the generator set. -/
theorem wordReach_mono {G G' : List (Equiv.Perm (Fin n))} (hsub : ∀ g ∈ G, g ∈ G')
    {u w : Fin n} (h : Consume.WordReach G u w) : Consume.WordReach G' u w := by
  induction h with
  | refl => exact Consume.WordReach.refl _
  | step _ hg ih => exact ih.step (hsub _ hg)

/-- The executable's **verified** generators are among the reference's — `deepenGens_subset_ref`
survives the `IsColAut` filter unchanged (both sides filter by the same predicate). -/
theorem verified_deepen_subset_ref (adj : AdjMatrix n) (χ : Colouring n) :
    ∀ g ∈ Consume.verified deepenSupply adj χ, g ∈ Consume.verified deepenRefSupply adj χ := by
  intro g hg
  rw [Consume.verified, List.mem_filter] at hg ⊢
  exact ⟨deepenGens_subset_ref adj χ g hg.1, hg.2⟩

/-- **The easy half of `SameOrbits deepenRefSupply deepenSupply`.** Every orbit the executable proves,
the all-picks reference also proves — because the single canonical pick is one of the enumerated
paths. (The reverse — the reference proves NO orbit the executable misses — is the residual crux;
measured true on every partially-firing witness, see the header.) -/
theorem wordReach_ref_of_deepen (adj : AdjMatrix n) (χ : Colouring n) (u w : Fin n)
    (h : Consume.WordReach (Consume.verified deepenSupply adj χ) u w) :
    Consume.WordReach (Consume.verified deepenRefSupply adj χ) u w :=
  wordReach_mono (verified_deepen_subset_ref adj χ) h

/-! ## 6. ★ THE RESIDUAL — the two obligations that close ①c

`①c` for `deepenSupply` reduces (`OrbitPrune.SameOrbits` + the reference's equivariance) to:

**(R1) `SameOrbits deepenRefSupply deepenSupply` — the reverse direction.**
    `∀ adj χ u w, WordReach (verified deepenRefSupply adj χ) u w →
                  WordReach (verified deepenSupply adj χ) u w`
    i.e. the all-picks reference proves no orbit the single canonical pick misses. `wordReach_ref_of_deepen`
    is the ⊇ half; this is the ⊆ half — **route (a)'s "the pick is interchangeable".** MEASURED true on
    `G8` (exec 16 / ref 28 generators, both orbit partition `[2,2,4]`), `t3` (exec 6 / ref 96, both `[3]`),
    `wcyc9` (`ScratchPickTest`, 2026-07-20). The mechanism: an emitted reference generator carries `r₁ ↦ rⱼ`
    and is a genuine automorphism (`twistOf_isColAut`), so the canonical pick — whose gate also passes,
    all-singletons on the coupled component — recovers a verified generator with the same action, up to a
    word. Not yet proved.

**(R2) `deepenRefSupply` is equivariant** — its own transport, the `KernelTransport.gensEquivariant_kernelRefSupply`
    analog. The reference enumerates EVERY pick, so relabelling `σ` permutes the set of all pick-paths
    bijectively (part I, `DeepenTransport`, gives that every stage but the pick transports; quantifying over
    all picks absorbs the one non-transporting step), and the emitted verified-generator set transports up to
    conjugation. Route (b) — restating the crux against this reference rather than against `Aut` — needs only
    (R2) plus the gate-conditional match, never "the executable recovers the true orbit".

Until (R1)+(R2) land, `deepenSupply` stays out of `Publication.canonForm?` (exactly as `kernelSupply` was
staged behind `KernelRef`/`KernelTransport`).
-/

end Deepen
end ChainDescent
