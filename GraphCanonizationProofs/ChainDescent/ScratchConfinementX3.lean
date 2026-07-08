/-
# ScratchConfinementX3.lean — the X3 cut: index-free single-vertex individualization (WIP, NOT in build.sh)

**What X3 is.** The one open piece of ①b `canon_complete`: the canonizer's canonical form is iso-invariant
(`CanonFormImagesIsoInvariant`, `ScratchConfinementCompleteness`). ①b's ← direction + the lex-min reduction are landed;
X3 is the residual.

**Why the earlier routes are dead (established 2026-07-08, verified against source).**
  · "samePartition ⟹ equal canonForm" — FALSE (refuted at discrete leaves; `rankPerm` reads colour *values*).
  · "make `individualizedColouring` `g`-equivariant" — the seed is index-based *by design* (`v.val+1`), used in 14
    modules; not a local fix.
  · **"the `DirAssignment` lex-min washes out the index" — FALSE, and this is the decisive finding.** `DirAssignment
    P₀ D` ranges over antisymmetric order-matrices on `D × D` only, and the order-matrix `σ` only breaks ties between
    **equal-colour** vertices. But individualization gives each committed vertex a **distinct index-based colour**
    (`IndivStep.default.χ' = if v∈T then 2·(χv·n+v.val)+1 …`; `individualizedColouring = v.val+1`), so committed
    vertices have NO ties — `σ` never re-orders them, and the lex-min cannot remove the baked-in index order. So the
    current `canonForm` (lex-min over `DirAssignment`) is **genuinely not iso-invariant** when `D ≠ ∅`.

**The root cause, precisely.** Individualization *bakes an index order into the committed set*. The only place the
index enters is the committed (`D`) vertices — non-committed vertices are coloured `2·χv` (index-free, purely
structural refinement, `IndivStep.default.χ'` off `T`). So the fix is local to *how a vertex is committed*.

**THE CUT — commit ONE vertex at a time with an INDEX-FREE colour, letting the canonical descent ORDER (level), not
the vertex index, order the committed set.** Then:
  · a single committed vertex needs no internal order (it is one vertex), so no un-canonical order is baked in;
  · the seed transports **literally** under a relabel `g` (index-free ⟹ `indivOne (g r) ∘ g = indivOne r`, an equality
    of functions — NOT merely `samePartition`), so the banked value-level lift `labelledAdj_rankPerm_transport`
    applies directly, dissolving the samePartition-vs-literal gap that blocked every prior route;
  · committed vertices are ordered by the **level** at which the (canonical, partition-invariant) descent picked them
    — an iso-invariant order — instead of by `v.val`;
  · at a single-orbit cell (confinement `SelectedCellIsOrbit`, DONE mod citations) all reps are automorphic, so the
    single-vertex choice is invisible at the labelled level (`baseTransport` + the literal lift).

So X3 reduces to a **Runtime-Phase design change** (single-vertex, index-free, level-ordered individualization) plus a
cross-graph transport assembly resting on BANKED pieces (`warmRefine_transport_iso`, `labelledAdj_rankPerm_transport`,
`baseTransport`, `nonDiscreteSel_equivariant`) and the DONE confinement core — NOT a wash-out-the-index argument (dead)
nor a full `canonForm` redesign. ①a transfers (it is selector-agnostic: `canonForm_isLabelledAdj`); ② is unaffected
(single-vertex still reaches a leaf in ≤ n levels).

**Pieces (taken one at a time; this file starts P1).**
  P1. Index-free single-vertex individualization `indivOne` + its **literal** `g`-equivariance.  ← THIS FILE
  P2. Level-ordered committed colouring (distinct colours by pick-level, index-free) + its equivariance.
  P3. A single-vertex, partition-invariant selector (one rep of the target cell) + `nonDiscreteSel`-style termination.
  P4. Cross-graph descent transport (now LITERAL via P1/P2) — descent on `π·G` is the `π`-image of the descent on `G`.
  P5. Rep-choice invisibility at a single-orbit cell (confinement + `baseTransport` + the literal lift).
  P6. Assemble `CanonFormImagesIsoInvariant` ⟹ ①b →.

Axiom target `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchConfinementCompleteness
import ChainDescent.RouteCTransport

namespace ChainDescent.ConfinementX3

open ChainDescent

variable {n : Nat}

/-! ## P1 — index-free single-vertex individualization

`indivOne r` marks exactly `r` with a fresh colour `1`, everyone else `0`. Unlike `individualizedColouring`
(`v.val+1`, index-based) it carries **no vertex index**, so it commutes *literally* with any relabel. This is the
atom the level-ordered committed colouring (P2) is built from, and the reason the samePartition-vs-literal gap
dissolves. -/

/-- **Index-free single-vertex individualization.** `r` gets colour `1`, all other vertices `0`. No `v.val`. -/
def indivOne (r : Fin n) : Colouring n :=
  fun v => if v = r then 1 else 0

/-- **`indivOne` transports LITERALLY under any permutation.** `indivOne (g r) ∘ g = indivOne r` as functions — the
index-free analogue of `individualizedColouring`'s `samePartition`-only `indiv_samePartition_transport`. This literal
equality (not `samePartition`) is exactly what lets `labelledAdj_rankPerm_transport` close the value-level lift. -/
theorem indivOne_equivariant (g : Equiv.Perm (Fin n)) (r : Fin n) :
    (fun v => indivOne (g r) (g v)) = indivOne r := by
  funext v
  simp only [indivOne, g.injective.eq_iff]

/-- **`indivOne` is a single-orbit-free marker: exactly `r` is `1`.** Membership shape, used by the selector/termination
plumbing (P3) and to see the marked cell is a singleton. -/
theorem indivOne_eq_one_iff (r v : Fin n) : indivOne r v = 1 ↔ v = r := by
  simp only [indivOne]; split <;> simp_all

theorem indivOne_eq_zero_iff (r v : Fin n) : indivOne r v = 0 ↔ v ≠ r := by
  simp only [indivOne]; split <;> simp_all

/-- **`indivOne` singletons `r`** — `r` has a colour (`1`) no other vertex shares. The single-vertex analogue of
`IndivStep.singletons_T`; the committed vertex is a genuine singleton of its own seed. -/
theorem indivOne_singleton (r : Fin n) : ∀ u, u ≠ r → indivOne r u ≠ indivOne r r := by
  intro u hu
  rw [(indivOne_eq_one_iff r r).mpr rfl, indivOne_eq_zero_iff r u |>.mpr hu]
  decide

/-! ## P2 — the single-step index-free individualization (a genuine `IndivStep`)

The descent commits vertices via `IndivStep`. `IndivStep.default` is index-based (`…+v.val…`). Here is the index-free
single-vertex replacement: commit `r` with the fresh **odd** marker `1`, everyone else with `2·χv` (even) — the
odd/even split gives `r` a colour no one shares, and off `{r}` the colouring refines exactly as `χ` did. Crucially it
carries **no `v.val`**, so it transports LITERALLY under a relabel (composing with the seed's literal transport), which
is the inductive engine for the cross-graph descent transport (P4).

Ordering across levels is by **pick-level**, canonically: successive `indivStep1` marks are separated by the refinement
between levels (McKay-style), never by `v.val`. -/

/-- **Single-step index-free individualization (colouring).** `r ↦ 1` (odd marker), `v ≠ r ↦ 2·χv` (even). No `v.val`. -/
def indivStep1 (r : Fin n) (χ : Colouring n) : Colouring n :=
  fun v => if v = r then 1 else 2 * χ v

/-- **`indivStep1` transports LITERALLY.** If the seed transports literally (`χ' ∘ g = χ`, i.e. `∀ v, χ' (g v) = χ v`),
so does one individualization step: `indivStep1 (g r) χ' (g v) = indivStep1 r χ v`. The inductive step of the literal
cross-graph descent transport — the index-free analogue that `IndivStep.default` cannot satisfy. -/
theorem indivStep1_equivariant (g : Equiv.Perm (Fin n)) (r : Fin n) {χ χ' : Colouring n}
    (hχ : ∀ v, χ' (g v) = χ v) (v : Fin n) :
    indivStep1 (g r) χ' (g v) = indivStep1 r χ v := by
  simp only [indivStep1]
  by_cases h : v = r
  · subst h; simp
  · rw [if_neg h, if_neg (fun hh => h (g.injective hh)), hχ v]

/-- **`indivStep1` packaged as a genuine `IndivStep χ {r}`.** So it drops into the descent machinery exactly where
`IndivStep.default` does, but index-free and restricted to a single committed vertex. `singletons_T`: `r`'s marker `1`
is odd, every other colour `2·χv` is even. `refines_off_T`: off `{r}` the colouring is `2·χ`, order-isomorphic to `χ`. -/
def indivStepOne (r : Fin n) (χ : Colouring n) : IndivStep χ {r} where
  χ' := indivStep1 r χ
  singletons_T := by
    intro v hv u hu
    rw [Finset.mem_singleton] at hv; subst hv
    have h1 : indivStep1 v χ v = 1 := by simp [indivStep1]
    have h2 : indivStep1 v χ u = 2 * χ u := by simp [indivStep1, hu]
    rw [h1, h2]; omega
  refines_off_T := by
    intro x y hx hy
    rw [Finset.mem_singleton] at hx hy
    have hxc : indivStep1 r χ x = 2 * χ x := by simp [indivStep1, hx]
    have hyc : indivStep1 r χ y = 2 * χ y := by simp [indivStep1, hy]
    rw [hxc, hyc]; omega

@[simp] theorem indivStepOne_χ' (r : Fin n) (χ : Colouring n) :
    (indivStepOne r χ).χ' = indivStep1 r χ := rfl

/-! ## P3 — a single-vertex selector (one rep per step)

The cut individualizes ONE vertex per step. `pickOne χ` selects a single vertex from the non-discrete part (the
minimum-index non-singleton vertex — a concrete, terminating choice). **It need NOT be equivariant:** in the confinement
(single-orbit) regime the pick is *invisible* at the labelled level — individualizing two same-orbit reps `v₁, v₂` (with
`g v₁ = v₂`, `g` an automorphism fixing the prefix so `χ ∘ g = χ`) gives seeds related LITERALLY by `g`
(`indivStep1_equivariant`), hence labelled-equal via `labelledAdj_rankPerm_transport` (P5). So a plain index-based pick
is fine here; cross-graph correspondence is handled by invisibility, not by selector equivariance.

Reuses `nonDiscreteSel` (the whole non-discrete part, `PartitionInvariant`) as the "is there a non-singleton vertex"
oracle, then takes its `min'`. `TargetsNonsingletonCell` + `NonemptyOnNonDiscrete` transfer from `nonDiscreteSel`'s. -/

open ChainDescent.CanonSound

/-- **Single-vertex selector.** The minimum-index non-singleton vertex (as a singleton), or `∅` if discrete. -/
noncomputable def pickOne (χ : Colouring n) : Finset (Fin n) :=
  if h : (nonDiscreteSel χ).Nonempty then {(nonDiscreteSel χ).min' h} else ∅

/-- `pickOne` only ever picks a vertex in a non-singleton cell (it lies in `nonDiscreteSel χ`). -/
theorem pickOne_targets : TargetsNonsingletonCell (pickOne (n := n)) := by
  intro χ v hv
  unfold pickOne at hv
  split at hv
  · rename_i h
    rw [Finset.mem_singleton] at hv; subst hv
    have hm := (nonDiscreteSel χ).min'_mem h
    simpa only [nonDiscreteSel, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  · simp at hv

/-- `pickOne` is non-empty whenever the colouring is not yet discrete (a singleton, from `nonDiscreteSel` non-empty). -/
theorem pickOne_nonempty : NonemptyOnNonDiscrete (pickOne (n := n)) := by
  intro χ hχ
  have hne : (nonDiscreteSel χ).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (nonDiscreteSel_nonempty χ hχ)
  unfold pickOne
  rw [dif_pos hne]
  simp

/-- `pickOne` picks at most one vertex — its cardinality is `≤ 1` (a singleton or `∅`). The "single-vertex" fact the
cut needs: each descent step commits exactly one vertex, so committed vertices are ordered purely by pick-level. -/
theorem pickOne_card_le_one (χ : Colouring n) : (pickOne χ).card ≤ 1 := by
  unfold pickOne
  split
  · simp
  · simp

/-! ## P4 — cross-graph LITERAL descent transport (the payoff of index-freeness)

The index-free descent, parametrised by the pick sequence it realises. `descentStep adj P r χ = indivStep1 r
(warmRefine adj P χ)` = "refine, then commit `r` index-free". `descentColouring … picks` folds it over a list of picks.

**The payoff:** for a graph iso `g : adj₁ → adj₂`, if the two descents use `g`-CORRESPONDING pick sequences (`picks`
vs `picks.map g`), the colourings transport **LITERALLY** — `descentColouring adj₂ … (picks.map g) (g v) =
descentColouring adj₁ … picks v`, a function equality, NOT merely `samePartition`. This is exactly what the index-based
`IndivStep.default` / `individualizedColouring` could NOT give (they only transport `samePartition`), and it is the whole
reason the cut works: `rankPerm`/`labelledAdj` read colour values, so the value-level lift needs a literal relabel.

The transport is stated for *corresponding* pick sequences; reconciling the two descents' actual (non-corresponding)
picks — same target cell, one orbit under confinement, so related by an automorphism — is P5. -/

/-- One index-free descent step: refine, then commit `r` with the index-free marker. -/
def descentStep (adj : AdjMatrix n) (P : PMatrix n) (r : Fin n) (χ : Colouring n) : Colouring n :=
  indivStep1 r (warmRefine adj P χ)

/-- The index-free descent colouring realised by a pick sequence `picks` (folded in order). -/
def descentColouring (adj : AdjMatrix n) (P : PMatrix n) : Colouring n → List (Fin n) → Colouring n
  | χι₀, [] => χι₀
  | χι₀, r :: rs => descentColouring adj P (descentStep adj P r χι₀) rs

/-- **One step transports literally.** `descentStep` under a graph iso `g` with corresponding pick `g r` and a
literally-transporting seed transports literally: `warmRefine_transport_iso` (banked) carries the refine, then
`indivStep1_equivariant` (P2) carries the commit. -/
theorem descentStep_transport {adj₁ adj₂ : AdjMatrix n} {P₁ P₂ : PMatrix n} {g : Equiv.Perm (Fin n)}
    (hf : ∀ v w, adj₂.adj (g v) (g w) = adj₁.adj v w) (hP : ∀ v u, P₂ (g v) (g u) = P₁ v u)
    (r : Fin n) {χ₁ χ₂ : Colouring n} (hχ : ∀ v, χ₂ (g v) = χ₁ v) (v : Fin n) :
    descentStep adj₂ P₂ (g r) χ₂ (g v) = descentStep adj₁ P₁ r χ₁ v := by
  unfold descentStep
  have hw : ∀ v, warmRefine adj₂ P₂ χ₂ (g v) = warmRefine adj₁ P₁ χ₁ v :=
    fun v => warmRefine_transport_iso hf hP hχ v
  exact indivStep1_equivariant g r hw v

/-- **★ Cross-graph LITERAL descent transport (P4).** For a graph iso `g : adj₁ → adj₂` and `g`-corresponding pick
sequences, the index-free descent colourings are literal `g`-relabels of one another. Induction over the pick list, each
step by `descentStep_transport`. This literal equality is the crux enabler the samePartition-only routes lacked. -/
theorem descentColouring_transport {adj₁ adj₂ : AdjMatrix n} {P₁ P₂ : PMatrix n} {g : Equiv.Perm (Fin n)}
    (hf : ∀ v w, adj₂.adj (g v) (g w) = adj₁.adj v w) (hP : ∀ v u, P₂ (g v) (g u) = P₁ v u) :
    ∀ (picks : List (Fin n)) {χ₁ χ₂ : Colouring n}, (∀ v, χ₂ (g v) = χ₁ v) →
      ∀ v, descentColouring adj₂ P₂ χ₂ (picks.map g) (g v) = descentColouring adj₁ P₁ χ₁ picks v := by
  intro picks
  induction picks with
  | nil => intro χ₁ χ₂ hχ v; exact hχ v
  | cons r rs ih =>
    intro χ₁ χ₂ hχ v
    simp only [descentColouring, List.map_cons]
    exact ih (fun v => descentStep_transport hf hP r hχ v) v

/-! ## P5 — the labelled-value lift (rep-choice invisibility, cross-graph)

The one cross-graph lemma that closes X3's value level. Given two **discrete** colourings related literally by a graph
iso `g` (`ρ₂ ∘ g = ρ₁`, exactly P4's output for the warm-refined leaves), their canonical labellings COINCIDE:
`labelledAdj (rankPerm ρ₂) adj₂ = labelledAdj (rankPerm ρ₁) adj₁`. Proof: `rankPerm_comp` (banked) turns the literal
`g`-relabel of the colouring into a right-multiplication `rankPerm ρ₁ · g.symm` of the rank permutation, and the
`relabelAdj` identity `hrel` then cancels the `g` at the labelled level.

This ONE lemma serves BOTH roles X3 needs:
  · **cross-graph** (`adj₂ = g·adj₁`, `g` the iso): corresponding-pick leaves give equal canonical forms;
  · **within-graph orbit reconciliation** (`adj₁ = adj₂`, `g` an automorphism relating two same-orbit reps): the
    single-vertex pick is invisible — the confinement single-orbit property supplies the automorphism, and index-free
    individualization (P1/P2/P4) supplies the *literal* `ρ₂ ∘ g = ρ₁` this lemma consumes.
It is the cross-graph generalisation of the banked (within-graph) `NodeCountBridge.labelledAdj_rankPerm_transport`. -/

/-- **★ P5 — cross-graph canonical-labelling invariance.** Discrete colourings related literally by a graph iso `g`
(`ρ₂ ∘ g = ρ₁`, with `adj₂` the `g`-relabel of `adj₁`) yield equal labelled canonical forms. Closes X3's value level;
serves both cross-graph transport and within-graph orbit-rep invisibility (see the section note). -/
theorem labelledAdj_rankPerm_cross {adj₁ adj₂ : AdjMatrix n} {g : Equiv.Perm (Fin n)}
    (hrel : ∀ i j, adj₂.adj i j = adj₁.adj (g.symm i) (g.symm j))
    {ρ₁ ρ₂ : Colouring n} (h₁ : Discrete ρ₁) (h₂ : Discrete ρ₂)
    (hρ : ∀ v, ρ₂ (g v) = ρ₁ v) :
    labelledAdj (Colouring.rankPerm ρ₂ h₂) adj₂ = labelledAdj (Colouring.rankPerm ρ₁ h₁) adj₁ := by
  have hρ2 : ρ₂ = fun v => ρ₁ (g.symm v) := by
    funext w; have h := hρ (g.symm w); rwa [Equiv.apply_symm_apply] at h
  subst hρ2
  rw [rankPerm_comp ρ₁ g.symm h₁ h₂]
  funext i j
  simp only [labelledAdj]
  rw [hrel]
  have key : ∀ i, g.symm ((Colouring.rankPerm ρ₁ h₁ * g.symm).symm i)
      = (Colouring.rankPerm ρ₁ h₁).symm i := by
    intro i
    have hi : (Colouring.rankPerm ρ₁ h₁ * g.symm).symm i
        = g ((Colouring.rankPerm ρ₁ h₁).symm i) := by
      rw [Equiv.symm_apply_eq]
      simp [Equiv.Perm.mul_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    rw [hi, Equiv.symm_apply_apply]
  rw [key i, key j]

end ChainDescent.ConfinementX3
