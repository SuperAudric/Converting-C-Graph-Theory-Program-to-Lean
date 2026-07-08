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

end ChainDescent.ConfinementX3
