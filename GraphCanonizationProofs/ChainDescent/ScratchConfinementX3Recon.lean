/-
# ScratchConfinementX3Recon.lean — W3: the reconciling automorphism (WIP, NOT in build.sh)

**Goal (W3).** Produce the reconciling `H`-automorphism `b` that `ScratchConfinementX3.ifCanon_iso_invariant_of_reconcile`
takes as `hrec : picksH = (picksG.map π).map b`. With the **equivariant** cell selector (`selCell`, W1) and confinement
now stated over the **descent's own colouring** (`SelectedCellIsOrbit`, colouring-generalized in W2), the two descents'
selected cells correspond cross-graph and only their within-cell reps differ — reconciled per level.

**The construction (verified on paper; the genuine remaining content).** For `H = π·G`, run both descents with the
`selCell`-driven single-vertex selector. Maintain the invariant
  `I(k) : b_k ∈ Aut(H) ∧ ∀ j < k, b_k (π (picksG_j)) = picksH_j`.
At level `k`, the transport invariant makes `H`'s selected cell the `(b_k∘π)`-image of `G`'s (via
`descentColouring_transport` (P4) + `selCell_transport` (W1)), so `(b_k∘π)(picksG_k)` and `picksH_k` lie in one cell
= one `Stab(oneStepD_H k)`-orbit (confinement `SelectedCellIsOrbit`). That orbit gives `a_k ∈ Stab(oneStepD_H k)` with
`a_k((b_k∘π)(picksG_k)) = picksH_k`; set `b_{k+1} = a_k ∘ b_k`. Since every later `a_j (j>k)` fixes `oneStepD_H j ∋
picksH_k`, the FINAL `b = b_K` satisfies `b(π(picksG_j)) = picksH_j` for ALL `j` — exactly `hrec`. (This is why a
single global `b` works, reviving the "same-order-only" `ifCanon_iso_invariant_of_reconcile`: the cells correspond by
construction, so the orders correspond and the per-level `a_k`'s compose into one `b`.)

**This file, step by step.**
  · **W3a (this commit): the `selCell`-driven pick list + its `descentColouring`.** `descentPicks` generates the
    single-vertex picks (min of `selCell` at each warm-refined level); `descentColouring_descentPicks_cons` shows it
    folds through `descentColouring` exactly, so the `ifCanon` machinery (stated on `descentColouring`) speaks about it.
  · W3b: the generated picks reach a discrete leaf in ≤ n steps (the direct termination for `selCell`, non-PI so not
    transferred via `eq_default`).
  · W3c: the reconciliation induction producing `b` + `hrec` (the algebraic core).

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementX3Sel
import ChainDescent.Confinement

namespace ChainDescent.ConfinementX3Recon

open ChainDescent
open ChainDescent.ConfinementX3
open ChainDescent.ConfinementX3Sel
open ChainDescent.CanonSound
open ChainDescent.NodeCountBridge

variable {n : Nat}

/-! ## W3a — the `selCell`-driven pick list

Each descent step warm-refines, then individualizes the minimum-index vertex of the minimum-value non-singleton cell
(`selCell`). `descentPicks adj P fuel χ` is the list of picks the descent makes from seed `χ` with `fuel` steps of
headroom; the descent stops early (empty tail) when the warm-refined colouring is discrete. The recursion mirrors
`descentColouring`'s fold exactly (`descentStep adj P r χ = indivStep1 r (warmRefine adj P χ)`). -/

/-- The `selCell`-driven pick list from seed `χ`, with `fuel` steps of headroom. -/
noncomputable def descentPicks (adj : AdjMatrix n) (P : PMatrix n) :
    Nat → Colouring n → List (Fin n)
  | 0, _ => []
  | fuel + 1, χ =>
    let π := warmRefine adj P χ
    if h : (selCell π).Nonempty then
      let r := (selCell π).min' h
      r :: descentPicks adj P fuel (indivStep1 r π)
    else []

@[simp] theorem descentPicks_zero (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) :
    descentPicks adj P 0 χ = [] := rfl

/-- One unfolding of `descentPicks` at a non-discrete step: the pick is `min (selCell (warmRefine … χ))`, and the tail
is the descent from the individualized colouring. -/
theorem descentPicks_succ_of_nonempty (adj : AdjMatrix n) (P : PMatrix n) (fuel : Nat) (χ : Colouring n)
    (h : (selCell (warmRefine adj P χ)).Nonempty) :
    descentPicks adj P (fuel + 1) χ
      = (selCell (warmRefine adj P χ)).min' h
        :: descentPicks adj P fuel (indivStep1 ((selCell (warmRefine adj P χ)).min' h) (warmRefine adj P χ)) := by
  simp only [descentPicks, dif_pos h]

/-- At a discrete step the descent stops (no further picks). -/
theorem descentPicks_succ_of_empty (adj : AdjMatrix n) (P : PMatrix n) (fuel : Nat) (χ : Colouring n)
    (h : ¬ (selCell (warmRefine adj P χ)).Nonempty) :
    descentPicks adj P (fuel + 1) χ = [] := by
  simp only [descentPicks, dif_neg h]

/-- **The generated picks fold through `descentColouring` exactly.** `descentColouring adj P χ (descentPicks … χ)` is
the colouring the `selCell`-descent reaches — so the `ifCanon` transport lemmas (stated on `descentColouring`) speak
about the actual `selCell`-driven descent. The `cons` step matches because `descentStep adj P r χ = indivStep1 r
(warmRefine adj P χ)`, exactly the `descentPicks` recursion body. -/
theorem descentColouring_descentPicks_succ (adj : AdjMatrix n) (P : PMatrix n) (fuel : Nat) (χ : Colouring n)
    (h : (selCell (warmRefine adj P χ)).Nonempty) :
    descentColouring adj P χ (descentPicks adj P (fuel + 1) χ)
      = descentColouring adj P (indivStep1 ((selCell (warmRefine adj P χ)).min' h) (warmRefine adj P χ))
          (descentPicks adj P fuel (indivStep1 ((selCell (warmRefine adj P χ)).min' h) (warmRefine adj P χ))) := by
  rw [descentPicks_succ_of_nonempty adj P fuel χ h]
  rfl

/-! ## W3c core — the single-step reconciliation extension (the algebraic crux)

The reconciliation carries `hrec : picksH = picksG.map (fun x => b (g x))` — a SINGLE global `b`. The dead-end record
declared this "same-order only": a fixed `b` cannot track cells consumed in different orders. The revival: with the
equivariant cell selector the cells DO correspond, and the per-level reconcilers compose into one `b` precisely because
each new reconciler `aₖ ∈ Stab(prefix)` **fixes every earlier pick**. This lemma is that step: extend a length-`k`
reconciliation by one level, composing `aₖ` on the left. The `psH.map aₖ = psH` step (from `aₖ` fixing `psH`
pointwise) is what makes the accumulation preserve all earlier correspondences — the crux the single-`b` shape needs. -/

/-- **★ W3c — single-step reconciliation extension.** Given a length-`k` reconciliation `psH = psG.map (bₖ∘g)`, a new
reconciler `aₖ` that fixes every earlier `H`-pick (`hfix`, delivered by `aₖ ∈ Stab(psH.toFinset)` = confinement's
orbit automorphism), and the level-`k` match `aₖ (bₖ (g rG)) = rH`, the composed `aₖ * bₖ` reconciles the extended
lists. Front-to-back accumulation of this lemma over the descent yields the global `b` for
`ifCanon_iso_invariant_of_reconcile`'s `hrec`. -/
theorem reconcile_extend {g bk ak : Equiv.Perm (Fin n)}
    {psG psH : List (Fin n)} {rG rH : Fin n}
    (hstep : psH = psG.map (fun x => bk (g x)))
    (hfix : ∀ p ∈ psH, ak p = p)
    (hrH : ak (bk (g rG)) = rH) :
    psH ++ [rH] = (psG ++ [rG]).map (fun x => (ak * bk) (g x)) := by
  rw [List.map_append]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · -- earlier picks: `aₖ` fixes each `bₖ (g x) ∈ psH`, so the map is unchanged.
    conv_lhs => rw [hstep]
    refine List.map_congr_left (fun x hx => ?_)
    have hmem : bk (g x) ∈ psH := by
      rw [hstep]; exact List.mem_map_of_mem hx
    simp only [Equiv.Perm.mul_apply]
    exact (hfix _ hmem).symm
  · -- the new level: `aₖ (bₖ (g rG)) = rH`.
    simp only [List.map_cons, List.map_nil, Equiv.Perm.mul_apply, hrH]

/-! ## W3b0 — an automorphism fixing the picks (+ seed) fixes the whole descent colouring

The genuine subtlety flagged for W3: the per-level reconciler `aₖ` is delivered by confinement's `OrbitPartition` as an
`H`-automorphism that fixes the *earlier picks pointwise* (`FixesPointwise aₖ S_H`) — NOT one that fixes the running
descent colouring globally. But the induction's transport step (`warmRefine H P χH (aₖ x) = warmRefine H P χH x`) needs
exactly the latter. This lemma bridges the two: since the level-`k` colouring `χH = descentColouring H P χι picksH_{<k}`
is built *only* from the picks in `S_H` (each `indivStep1` marks one pick), an automorphism fixing all of them pointwise
(and fixing the seed) fixes the whole colouring. `warmRefine_invariant_of_isAut` then upgrades that to the warm layer. -/

/-- One descent step is invariant under an `H`-automorphism that fixes the seed and fixes the committed vertex `r`. -/
theorem descentStep_fixed_of_aut {adj : AdjMatrix n} {P : PMatrix n} {a : Equiv.Perm (Fin n)}
    (ha : IsAut a adj) (haP : ∀ x u, P (a x) (a u) = P x u) {χ : Colouring n}
    (hχ : ∀ v, χ (a v) = χ v) {r : Fin n} (har : a r = r) :
    ∀ v, descentStep adj P r χ (a v) = descentStep adj P r χ v := by
  intro v
  unfold descentStep indivStep1
  have hW : ∀ x, warmRefine adj P χ (a x) = warmRefine adj P χ x :=
    fun x => warmRefine_invariant_of_isAut ha haP hχ x
  by_cases h : v = r
  · subst h; simp [har]
  · have h' : a v ≠ r := by rw [← har]; exact fun hh => h (a.injective hh)
    rw [if_neg h, if_neg h', hW v]

/-- **★ W3b0 — the descent colouring is fixed by an automorphism fixing its picks + seed.** For `a ∈ Aut(adj)`
`P`-preserving with `a`-invariant seed `χι`, if `a` fixes every pick of `picks` pointwise then it fixes the whole
descent colouring `descentColouring adj P χι picks`. Induction on `picks`, each step by `descentStep_fixed_of_aut`. This
discharges the `hχHaut` hypothesis of `reconcile_one_level` for the actual descent colourings. -/
theorem descentColouring_fixed_of_aut {adj : AdjMatrix n} {P : PMatrix n} {a : Equiv.Perm (Fin n)}
    (ha : IsAut a adj) (haP : ∀ x u, P (a x) (a u) = P x u) :
    ∀ (picks : List (Fin n)) {χι : Colouring n}, (∀ v, χι (a v) = χι v) →
      FixesPointwise a picks.toFinset →
      ∀ v, descentColouring adj P χι picks (a v) = descentColouring adj P χι picks v := by
  intro picks
  induction picks with
  | nil => intro χι hχι _ v; exact hχι v
  | cons r rs ih =>
    intro χι hχι hfix v
    have har : a r = r := hfix r (by simp)
    have hfixrs : FixesPointwise a rs.toFinset := by
      intro x hx; exact hfix x (by simp only [List.toFinset_cons, Finset.mem_insert]; exact Or.inr hx)
    have hstep : ∀ w, descentStep adj P r χι (a w) = descentStep adj P r χι w :=
      descentStep_fixed_of_aut ha haP hχι har
    simp only [descentColouring]
    exact ih hstep hfixrs v

/-! ## W3 list/fold helpers -/

/-- `descentColouring` folds through an append: process `as`, then `bs` from the resulting colouring. -/
theorem descentColouring_append (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) (as bs : List (Fin n)) :
    descentColouring adj P χ (as ++ bs)
      = descentColouring adj P (descentColouring adj P χ as) bs := by
  induction as generalizing χ with
  | nil => rfl
  | cons r rs ih => simp only [List.cons_append, descentColouring]; exact ih (descentStep adj P r χ)

/-- Snoc form: appending one pick `r` is one `descentStep` on the accumulated colouring. -/
theorem descentColouring_snoc (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n)
    (done : List (Fin n)) (r : Fin n) :
    descentColouring adj P χ (done ++ [r]) = descentStep adj P r (descentColouring adj P χ done) := by
  rw [descentColouring_append]; rfl

/-- Snoc in the `indivStep1`-of-`warmRefine` form — matches the tail seed `descentPicks` produces verbatim. -/
theorem descentColouring_snoc' (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n)
    (done : List (Fin n)) (r : Fin n) :
    descentColouring adj P χ (done ++ [r])
      = indivStep1 r (warmRefine adj P (descentColouring adj P χ done)) := by
  rw [descentColouring_snoc]; rfl

/-- Discreteness transports across a relabel (both directions): a `g`-relabel of a colouring is discrete iff the
colouring is. Used so the two descents hit their discrete leaves at the same level. -/
theorem discrete_transport_iff {g : Equiv.Perm (Fin n)} {χ₁ χ₂ : Colouring n}
    (hχ : ∀ v, χ₂ (g v) = χ₁ v) : Discrete χ₁ ↔ Discrete χ₂ := by
  constructor
  · intro hd i j hij
    have h : χ₁ (g.symm i) = χ₁ (g.symm j) := by
      rw [← hχ (g.symm i), ← hχ (g.symm j), Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hij
    exact g.symm.injective (hd _ _ h)
  · intro hd i j hij
    have h : χ₂ (g i) = χ₂ (g j) := by rw [hχ i, hχ j]; exact hij
    exact g.injective (hd _ _ h)

/-! ## W3c — the one-level reconciliation (the de-risked crux)

At level `k` we hold `bₖ` (an `H`-automorphism) with the *seed* transport `∀v, χH (bₖ (π v)) = χG v`. This lemma
performs one level: it produces the reconciler `aₖ` (confinement's orbit automorphism matching the two competing reps)
and re-establishes the seed transport at level `k+1` for the composed map `aₖ * bₖ`. Front-to-back accumulation of this
(with `reconcile_extend` doing the pick-list bookkeeping) yields the global `b`. The one genuine risk — that `aₖ`, which
only fixes the earlier picks, nonetheless fixes the descent colouring enough to carry the transport — is discharged by
the `hχHaut` hypothesis (supplied in the full induction by `descentColouring_fixed_of_aut`). -/

/-- **★ W3c — one level of reconciliation.** From the level-`k` seed transport `hST` and confinement's
`SelectedCellIsOrbit` on `H`'s selected cell, produce the reconciler `aₖ` (an `H`-automorphism fixing the earlier picks
`S_H`, mapping `bₖ`'s image of `G`'s rep to `H`'s rep) and re-establish the seed transport at level `k+1` for
`aₖ * bₖ`. `rG`/`rH` are the two descents' `selCellRep`-picks (the `min'` of each selected cell). -/
theorem reconcile_one_level
    {G H : AdjMatrix n} {P : PMatrix n} {π bk : Equiv.Perm (Fin n)}
    (hiso : ∀ v w, H.adj (π v) (π w) = G.adj v w) (hisoP : ∀ v u, P (π v) (π u) = P v u)
    (hbk : IsAut bk H) (hbkP : ∀ x u, P (bk x) (bk u) = P x u)
    {χG χH : Colouring n}
    (hST : ∀ v, χH (bk (π v)) = χG v)
    {S_H : Finset (Fin n)}
    (hχHaut : ∀ a : Equiv.Perm (Fin n), IsAut a H → (∀ x u, P (a x) (a u) = P x u) →
        FixesPointwise a S_H → ∀ x, warmRefine H P χH (a x) = warmRefine H P χH x)
    (hconf : SelectedCellIsOrbit H P selCell (warmRefine H P χH) S_H)
    (hcG : (selCell (warmRefine G P χG)).Nonempty) (hcH : (selCell (warmRefine H P χH)).Nonempty) :
    ∃ ak : Equiv.Perm (Fin n),
      IsAut ak H ∧ (∀ x u, P (ak x) (ak u) = P x u) ∧ FixesPointwise ak S_H ∧
      ak (bk (π ((selCell (warmRefine G P χG)).min' hcG)))
          = (selCell (warmRefine H P χH)).min' hcH ∧
      (∀ v, descentStep H P ((selCell (warmRefine H P χH)).min' hcH) χH ((ak * bk) (π v))
            = descentStep G P ((selCell (warmRefine G P χG)).min' hcG) χG v) := by
  -- `bk ∘ π` is a graph iso `G → H` preserving `P`.
  have hf : ∀ v w, H.adj (bk (π v)) (bk (π w)) = G.adj v w := fun v w => by
    rw [hbk (π v) (π w), hiso v w]
  have hPbkπ : ∀ v u, P (bk (π v)) (bk (π u)) = P v u := fun v u => by
    rw [hbkP (π v) (π u), hisoP v u]
  -- WT_k: the warm-refined colourings transport under `bk ∘ π`.
  have hWT : ∀ v, warmRefine H P χH (bk (π v)) = warmRefine G P χG v := by
    intro v
    have := warmRefine_transport_iso (g := bk * π) (adj₂ := H) (adj₁ := G) (P₂ := P) (P₁ := P)
      (χ₂ := χH) (χ₁ := χG)
      (fun v w => by simp only [Equiv.Perm.mul_apply]; exact hf v w)
      (fun v u => by simp only [Equiv.Perm.mul_apply]; exact hPbkπ v u)
      (fun v => by simp only [Equiv.Perm.mul_apply]; exact hST v) v
    simpa only [Equiv.Perm.mul_apply] using this
  set WG := warmRefine G P χG with hWGdef
  set WH := warmRefine H P χH with hWHdef
  set rG := (selCell WG).min' hcG with hrGdef
  set rH := (selCell WH).min' hcH with hrHdef
  -- both competing reps lie in `WH`'s selected cell.
  have hmemG : rG ∈ selCell WG := (selCell WG).min'_mem hcG
  have hmemH : rH ∈ selCell WH := (selCell WH).min'_mem hcH
  have hmemBkG : bk (π rG) ∈ selCell WH := by
    have := (selCell_transport (g := bk * π) (χ₂ := WH) (χ₁ := WG)
      (fun v => by simp only [Equiv.Perm.mul_apply]; exact hWT v) rG).mpr hmemG
    simpa only [Equiv.Perm.mul_apply] using this
  -- same colour (both carry `minNSVal WH`).
  have hcol : WH (bk (π rG)) = WH rH := by
    rw [selCell_colour hmemBkG, selCell_colour hmemH]
  -- confinement supplies the reconciler.
  obtain ⟨ak, hak, hakP, hakfix, hakmatch⟩ := hconf (bk (π rG)) rH hmemBkG hmemH hcol
  refine ⟨ak, hak, hakP, hakfix, hakmatch, ?_⟩
  -- re-establish the seed transport at level k+1 for `ak * bk`.
  intro v
  -- `ak` fixes `WH` (from `hχHaut` applied to `ak`).
  have hakWH : ∀ x, WH (ak x) = WH x := hχHaut ak hak hakP hakfix
  -- the pre-refinement transport for `(ak*bk) ∘ π`.
  have hχnext : ∀ w, WH (((ak * bk) * π) w) = WG w := by
    intro w
    simp only [Equiv.Perm.mul_apply]
    rw [hakWH (bk (π w)), hWT w]
  have hgrG : ((ak * bk) * π) rG = rH := by
    simp only [Equiv.Perm.mul_apply]; exact hakmatch
  have key := indivStep1_equivariant (ak * bk * π) rG hχnext v
  rw [hgrG] at key
  unfold descentStep
  simpa only [Equiv.Perm.mul_apply] using key

/-! ## W3 — the reconciliation induction (folds `reconcile_one_level` over the whole descent)

For `H = π·G`, run both `selCell`-descents from the constant seed `χι`. This induction (on `fuel`) produces the single
global `H`-automorphism `b` with `picksH = (picksG.map π).map b` — the `hrec` that
`ifCanon_iso_invariant_of_reconcile` (P6c) consumes. It threads two invariants across levels:
  · the **seed transport** `∀v, χHk (bk (π v)) = χGk v` (advanced by `reconcile_one_level`), and
  · the **prefix correspondence** `doneH = (doneG.map π).map bk` (advanced by `reconcile_extend`).
The confinement input is the list-indexed `SelectedCellIsOrbit … (warmRefine H P (descentColouring H P χι done)) …`
(= the W2 `χsel` instantiated at the descent's own colouring). `descentColouring_fixed_of_aut` discharges the
per-level `hχHaut`; `discrete_transport_iff` makes the two descents stop at the same level. -/

/-- **★ W3 — the reconciliation induction.** From a constant seed, an iso `π : G → H`, and confinement (list-indexed,
over the descent's own colouring), the two `selCell`-descents' pick-lists (continued from any matched prefix
`doneG`/`doneH`) are reconciled by a single `H`-automorphism `b`. The `∃ b` conclusion is exactly the input to
`ifCanon_iso_invariant_of_reconcile`. -/
theorem reconcile_descent
    {G H : AdjMatrix n} {P : PMatrix n} {π : Equiv.Perm (Fin n)}
    (hiso : ∀ v w, H.adj (π v) (π w) = G.adj v w) (hisoP : ∀ v u, P (π v) (π u) = P v u)
    {χι : Colouring n} (hχιconst : ∀ v w, χι v = χι w)
    (hconf : ∀ done : List (Fin n),
        SelectedCellIsOrbit H P selCell (warmRefine H P (descentColouring H P χι done)) done.toFinset) :
    ∀ (fuel : Nat) (doneG doneH : List (Fin n)) (bk : Equiv.Perm (Fin n)),
      IsAut bk H → (∀ x u, P (bk x) (bk u) = P x u) →
      (∀ v, descentColouring H P χι doneH (bk (π v)) = descentColouring G P χι doneG v) →
      doneH = (doneG.map π).map bk →
      ∃ b : Equiv.Perm (Fin n),
        IsAut b H ∧ (∀ x u, P (b x) (b u) = P x u) ∧
        doneH ++ descentPicks H P fuel (descentColouring H P χι doneH)
          = ((doneG ++ descentPicks G P fuel (descentColouring G P χι doneG)).map π).map b := by
  intro fuel
  induction fuel with
  | zero =>
    intro doneG doneH bk hbk hbkP _ hpre
    exact ⟨bk, hbk, hbkP, by simp only [descentPicks_zero, List.append_nil]; exact hpre⟩
  | succ fuel ih =>
    intro doneG doneH bk hbk hbkP hST hpre
    have hf : ∀ v w, H.adj (bk (π v)) (bk (π w)) = G.adj v w := fun v w => by
      rw [hbk (π v) (π w), hiso v w]
    have hPbkπ : ∀ v u, P (bk (π v)) (bk (π u)) = P v u := fun v u => by
      rw [hbkP (π v) (π u), hisoP v u]
    have hWT : ∀ v, warmRefine H P (descentColouring H P χι doneH) (bk (π v))
        = warmRefine G P (descentColouring G P χι doneG) v := by
      intro v
      have := warmRefine_transport_iso (g := bk * π) (adj₂ := H) (adj₁ := G) (P₂ := P) (P₁ := P)
        (χ₂ := descentColouring H P χι doneH) (χ₁ := descentColouring G P χι doneG)
        (fun v w => by simp only [Equiv.Perm.mul_apply]; exact hf v w)
        (fun v u => by simp only [Equiv.Perm.mul_apply]; exact hPbkπ v u)
        (fun v => by simp only [Equiv.Perm.mul_apply]; exact hST v) v
      simpa only [Equiv.Perm.mul_apply] using this
    have hne_iff : (selCell (warmRefine G P (descentColouring G P χι doneG))).Nonempty
        ↔ (selCell (warmRefine H P (descentColouring H P χι doneH))).Nonempty := by
      rw [selCell_nonempty_iff, selCell_nonempty_iff]
      exact not_congr (discrete_transport_iff (g := bk * π)
        (fun v => by simp only [Equiv.Perm.mul_apply]; exact hWT v))
    by_cases hcH : (selCell (warmRefine H P (descentColouring H P χι doneH))).Nonempty
    · have hcG : (selCell (warmRefine G P (descentColouring G P χι doneG))).Nonempty := hne_iff.mpr hcH
      have hχHaut : ∀ a : Equiv.Perm (Fin n), IsAut a H → (∀ x u, P (a x) (a u) = P x u) →
          FixesPointwise a doneH.toFinset →
          ∀ x, warmRefine H P (descentColouring H P χι doneH) (a x)
            = warmRefine H P (descentColouring H P χι doneH) x := by
        intro a ha haP hfix x
        exact warmRefine_invariant_of_isAut ha haP
          (descentColouring_fixed_of_aut ha haP doneH (fun v => hχιconst (a v) v) hfix) x
      obtain ⟨ak, hak, hakP, hakfix, hakmatch, hstept⟩ :=
        reconcile_one_level hiso hisoP hbk hbkP hST hχHaut (hconf doneH) hcG hcH
      -- pick names (explicit, to match `descentPicks`/`reconcile_one_level` output verbatim)
      set rG := (selCell (warmRefine G P (descentColouring G P χι doneG))).min' hcG with hrGdef
      set rH := (selCell (warmRefine H P (descentColouring H P χι doneH))).min' hcH with hrHdef
      have hbk' : IsAut (ak * bk) H := fun v w => by
        simp only [Equiv.Perm.mul_apply]; rw [hak (bk v) (bk w), hbk v w]
      have hbkP' : ∀ x u, P ((ak * bk) x) ((ak * bk) u) = P x u := fun x u => by
        simp only [Equiv.Perm.mul_apply]; rw [hakP (bk x) (bk u), hbkP x u]
      have hST' : ∀ v, descentColouring H P χι (doneH ++ [rH]) ((ak * bk) (π v))
          = descentColouring G P χι (doneG ++ [rG]) v := by
        intro v; rw [descentColouring_snoc, descentColouring_snoc]; exact hstept v
      have hpre' : doneH ++ [rH] = ((doneG ++ [rG]).map π).map (ak * bk) := by
        have hstep : doneH = doneG.map (fun x => bk (π x)) := by rw [hpre, List.map_map]; rfl
        have hfixl : ∀ p ∈ doneH, ak p = p := fun p hp => hakfix p (List.mem_toFinset.mpr hp)
        rw [reconcile_extend (g := π) hstep hfixl hakmatch]
        simp only [List.map_map, Function.comp_def]
      obtain ⟨b, hb, hbP, heq⟩ := ih (doneG ++ [rG]) (doneH ++ [rH]) (ak * bk) hbk' hbkP' hST' hpre'
      refine ⟨b, hb, hbP, ?_⟩
      have hlistH : doneH ++ descentPicks H P (fuel + 1) (descentColouring H P χι doneH)
          = (doneH ++ [rH]) ++ descentPicks H P fuel (descentColouring H P χι (doneH ++ [rH])) := by
        rw [descentPicks_succ_of_nonempty _ _ _ _ hcH, ← hrHdef, List.append_cons, descentColouring_snoc']
      have hlistG : doneG ++ descentPicks G P (fuel + 1) (descentColouring G P χι doneG)
          = (doneG ++ [rG]) ++ descentPicks G P fuel (descentColouring G P χι (doneG ++ [rG])) := by
        rw [descentPicks_succ_of_nonempty _ _ _ _ hcG, ← hrGdef, List.append_cons, descentColouring_snoc']
      rw [hlistH, hlistG]; exact heq
    · refine ⟨bk, hbk, hbkP, ?_⟩
      have hcG : ¬ (selCell (warmRefine G P (descentColouring G P χι doneG))).Nonempty :=
        fun h => hcH (hne_iff.mp h)
      rw [descentPicks_succ_of_empty _ _ _ _ hcH, descentPicks_succ_of_empty _ _ _ _ hcG]
      simp only [List.append_nil]; exact hpre

/-! ## W3b — termination: the `selCell`-descent reaches a discrete leaf within `n` levels

The `selCell` selector is value-based (not `PartitionInvariant`), so `oneStepSpineChain_reaches_leaf`'s transfer route
(via `SpineChain.eq_default`) does not apply; and `descentPicks` uses the index-free `indivStep1`, a *different*
colouring from the set-individualizing `defaultSpineChain`. So termination is a DIRECT growth argument: each nonempty
step individualizes one vertex `r` (previously in a non-singleton cell), and `r` — plus every prior singleton — is a
singleton of the next warm-refined colouring, so the non-singleton count strictly drops. Starting `≤ n`, the descent is
discrete within `n` levels. Supplies the `Discrete (warmRefine …)` leaf hypotheses `ifCanon_iso_invariant_of_reconcile`
(W4) consumes. -/

/-- `warmRefine` preserves singletons per-vertex: a colour unique in `χ` stays unique after refinement. -/
theorem warmRefine_preserves_singleton (adj : AdjMatrix n) (P : PMatrix n) {χ : Colouring n} {a : Fin n}
    (hsing : ∀ u, u ≠ a → χ u ≠ χ a) : ∀ u, u ≠ a → warmRefine adj P χ u ≠ warmRefine adj P χ a := by
  intro u hu; unfold warmRefine
  exact iterate_refineStep_preserves_singleton adj P a n χ hsing u hu

/-- `nonDiscreteSel χ = ∅ ⟹ χ discrete` (contrapositive of `nonDiscreteSel_nonempty`). -/
theorem discrete_of_nonDiscreteSel_empty {χ : Colouring n} (h : nonDiscreteSel χ = ∅) : Discrete χ := by
  by_contra hd; exact nonDiscreteSel_nonempty χ hd h

/-- **The strict-decrease step.** Individualizing the selected rep `r` makes it — and every prior singleton — a
singleton of the next warm-refined colouring, so the non-singleton count strictly drops. -/
theorem nonDiscreteSel_warmRefine_shrinks (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n)
    (h : (selCell (warmRefine adj P χ)).Nonempty) :
    (nonDiscreteSel (warmRefine adj P
        (indivStep1 ((selCell (warmRefine adj P χ)).min' h) (warmRefine adj P χ)))).card
      < (nonDiscreteSel (warmRefine adj P χ)).card := by
  set π := warmRefine adj P χ with hπ
  set r := (selCell π).min' h with hr
  set π' := warmRefine adj P (indivStep1 r π) with hπ'
  -- v singleton of π ⟹ v singleton of `indivStep1 r π`.
  have hkeep_indiv : ∀ v, (∀ u, u ≠ v → π u ≠ π v) →
      (∀ u, u ≠ v → indivStep1 r π u ≠ indivStep1 r π v) := by
    intro v hv u hu
    by_cases hvr : v = r
    · subst hvr
      have e1 : indivStep1 r π u = 2 * π u := by simp [indivStep1, hu]
      have e2 : indivStep1 r π r = 1 := by simp [indivStep1]
      rw [e1, e2]; omega
    · have ev : indivStep1 r π v = 2 * π v := by simp [indivStep1, hvr]
      by_cases hur : u = r
      · subst hur
        have eu : indivStep1 r π r = 1 := by simp [indivStep1]
        rw [eu, ev]; omega
      · have eu : indivStep1 r π u = 2 * π u := by simp [indivStep1, hur]
        rw [eu, ev]; intro hcontra
        exact hv u hu (by omega)
  -- singletons only grow ⟹ `nonDiscreteSel` shrinks (as a subset).
  have hsub : nonDiscreteSel π' ⊆ nonDiscreteSel π := by
    intro v hv
    simp only [nonDiscreteSel, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨u, hune, huv⟩ := hv
    by_contra hcon
    exact warmRefine_preserves_singleton adj P
      (hkeep_indiv v (fun w hw hwv => hcon ⟨w, hw, hwv⟩)) u hune huv
  -- `r` is in a non-singleton cell of `π` (it lies in `selCell π`)…
  have hr_in : r ∈ nonDiscreteSel π := by
    obtain ⟨u, hu_ne, hu_eq⟩ := selCell_targets ((selCell π).min'_mem h)
    simp only [nonDiscreteSel, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u, hu_ne, hu_eq⟩
  -- …but becomes a singleton of `π'`.
  have hr_notin : r ∉ nonDiscreteSel π' := by
    intro hrin
    simp only [nonDiscreteSel, Finset.mem_filter, Finset.mem_univ, true_and] at hrin
    obtain ⟨u, hune, huv⟩ := hrin
    have hsing_indiv : ∀ w, w ≠ r → indivStep1 r π w ≠ indivStep1 r π r := by
      intro w hw
      have e1 : indivStep1 r π w = 2 * π w := by simp [indivStep1, hw]
      have e2 : indivStep1 r π r = 1 := by simp [indivStep1]
      rw [e1, e2]; omega
    exact warmRefine_preserves_singleton adj P hsing_indiv u hune huv
  exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨r, hr_in, hr_notin⟩)

/-- **Leaf within `f` levels when the non-singleton count starts `≤ f`.** Induction on `f`: each nonempty step strictly
drops the count (`nonDiscreteSel_warmRefine_shrinks`), so `≤ f` steps suffice; a discrete step stops early. -/
theorem descentPicks_leaf (adj : AdjMatrix n) (P : PMatrix n) :
    ∀ (f : Nat) (χ : Colouring n), (nonDiscreteSel (warmRefine adj P χ)).card ≤ f →
      Discrete (warmRefine adj P (descentColouring adj P χ (descentPicks adj P f χ))) := by
  intro f
  induction f with
  | zero =>
    intro χ hcard
    have : Discrete (warmRefine adj P χ) :=
      discrete_of_nonDiscreteSel_empty (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
    simpa only [descentPicks_zero, descentColouring] using this
  | succ f ih =>
    intro χ hcard
    by_cases h : (selCell (warmRefine adj P χ)).Nonempty
    · rw [descentColouring_descentPicks_succ adj P f χ h]
      exact ih _ (by have := nonDiscreteSel_warmRefine_shrinks adj P χ h; omega)
    · rw [descentPicks_succ_of_empty adj P f χ h]
      simp only [descentColouring]
      exact not_not.mp (fun hnd => h ((selCell_nonempty_iff _).mpr hnd))

/-- **★ W3b — the descent leaf is discrete at fuel `n`.** The full descent from any seed reaches a discrete
warm-refined leaf within `n` levels (`nonDiscreteSel` starts `≤ n`). This is the `Discrete (warmRefine …)` hypothesis
`ifCanon_iso_invariant_of_reconcile` needs at `fuel := n`. -/
theorem descentPicks_leaf_univ (adj : AdjMatrix n) (P : PMatrix n) (χ : Colouring n) :
    Discrete (warmRefine adj P (descentColouring adj P χ (descentPicks adj P n χ))) :=
  descentPicks_leaf adj P n χ (le_trans (Finset.card_le_univ _) (le_of_eq (Fintype.card_fin n)))

/-- **★ W3 corollary — the top-level reconciliation (`hrec` supplier).** Both descents run from the constant seed
`χι` (empty prefix); the induction yields the global `b`. This is the `∃ b … picksH = (picksG.map π).map b` that
`ifCanon_iso_invariant_of_reconcile` consumes to close ①b→. -/
theorem reconcile_descent_top
    {G H : AdjMatrix n} {P : PMatrix n} {π : Equiv.Perm (Fin n)}
    (hiso : ∀ v w, H.adj (π v) (π w) = G.adj v w) (hisoP : ∀ v u, P (π v) (π u) = P v u)
    {χι : Colouring n} (hχιconst : ∀ v w, χι v = χι w)
    (hconf : ∀ done : List (Fin n),
        SelectedCellIsOrbit H P selCell (warmRefine H P (descentColouring H P χι done)) done.toFinset)
    (fuel : Nat) :
    ∃ b : Equiv.Perm (Fin n),
      IsAut b H ∧ (∀ x u, P (b x) (b u) = P x u) ∧
      descentPicks H P fuel χι = ((descentPicks G P fuel χι).map π).map b := by
  have h := reconcile_descent hiso hisoP hχιconst hconf fuel [] [] 1
    IsAut.refl (fun _ _ => rfl)
    (fun v => by simp only [descentColouring, Equiv.Perm.one_apply]; exact hχιconst (π v) v)
    (by simp)
  simpa only [descentColouring, List.nil_append] using h

/-! ## W4 piece 1 — the assembly: iso ⟹ equal descent-leaf canonical form

Compose the two W3 exports through `ifCanon_iso_invariant_of_reconcile` (P6c): `reconcile_descent_top` supplies the
reconciling `b` (`hrec`), `descentPicks_leaf_univ` supplies the two leaf-discreteness hypotheses (`h₁`, `h₂`), and the
`hmid` (discreteness along the transported picks `picksG.map π`) is the one small glue — `descentColouring_transport`
(P4) + `discrete_transport_iff`. Result: for `H = π·G` the two `selCell`-descents reach leaves with EQUAL canonical
labelled forms. This is ①b→ for the index-free `selCell` descent. -/

/-- **★ W4.1 — descent-leaf canonical-form iso-invariance.** For a graph iso `π : G → H`, the constant seed, and the
(list-indexed) confinement hypothesis, the `selCell`-descents of `G` and `H` (run to their discrete leaves at fuel `n`)
produce equal canonical labelled forms. The completeness (`①b →`) statement for the index-free descent. -/
theorem descentLeaf_canonForm_iso_invariant
    {G H : AdjMatrix n} {P : PMatrix n} {π : Equiv.Perm (Fin n)}
    (hiso : ∀ v w, H.adj (π v) (π w) = G.adj v w) (hisoP : ∀ v u, P (π v) (π u) = P v u)
    {χι : Colouring n} (hχιconst : ∀ v w, χι v = χι w)
    (hconf : ∀ done : List (Fin n),
        SelectedCellIsOrbit H P selCell (warmRefine H P (descentColouring H P χι done)) done.toFinset)
    (h₁ : Discrete (warmRefine G P (descentColouring G P χι (descentPicks G P n χι))))
    (h₂ : Discrete (warmRefine H P (descentColouring H P χι (descentPicks H P n χι)))) :
    labelledAdj (Colouring.rankPerm (warmRefine H P (descentColouring H P χι (descentPicks H P n χι))) h₂) H
      = labelledAdj (Colouring.rankPerm (warmRefine G P (descentColouring G P χι (descentPicks G P n χι))) h₁) G := by
  obtain ⟨b, hb, hbP, hrec⟩ := reconcile_descent_top hiso hisoP hχιconst hconf n
  have htrans : ∀ v, warmRefine H P (descentColouring H P χι ((descentPicks G P n χι).map π)) (π v)
      = warmRefine G P (descentColouring G P χι (descentPicks G P n χι)) v := fun v =>
    warmRefine_transport_iso hiso hisoP
      (descentColouring_transport hiso hisoP (descentPicks G P n χι) (fun v => hχιconst (π v) v)) v
  have hmid : Discrete (warmRefine H P (descentColouring H P χι ((descentPicks G P n χι).map π))) :=
    (discrete_transport_iff (g := π) htrans).mp h₁
  exact ifCanon_iso_invariant_of_reconcile hiso hisoP hb hbP
    (fun v => hχιconst (π v) v) (fun v => hχιconst (b v) v) hrec h₁ hmid h₂

end ChainDescent.ConfinementX3Recon
