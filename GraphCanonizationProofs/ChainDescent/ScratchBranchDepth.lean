/-
# Phase 2, ITEM A — the `L = O(d)` branch-depth geometric core (recovery route T0, forms graph)

**What this module builds.** The recovery route's second open factor (`docs/chain-descent-recovery-route.md`
§4 item 2, §6 ITEM A): the number of *branching* levels on any root→leaf descent path is `L = O(d)`, so that
`leaves ≤ Bᴸ = q^{O(d)} = poly(n)`. This lands the module's **pure-geometry core** — the piece the doc names as
the "first concrete step" — and isolates the two remaining seams honestly.

**The mechanism (doc §4 item 2 / §6 ITEM A).** An `O(d)` individualized base *rigidifies* `O^ε_d(q)`, after which
there is no further branching. This module proves the geometric backbone of that claim in two steps and states the
`O(d)` arithmetic:

* **§1 — the spanning determiner (generalises `coords_determineK`).** `coords_determineK`
  (`ChainDescent/FieldGeneric.lean:87`) determines a vertex from its `Q`-profile on the *standard* frame
  `{Pi.single i 1}`. Here we generalise to an **arbitrary base whose span is `⊤`**: with a nondegenerate polar form,
  the exact Gram data to `S` (`SameExactGram`: `Q` and `polar · s` for `s ∈ S`) determines the vertex —
  `spanning_sameExactGram_determines`. Only the *polar* half is needed (bilinearity + `span = ⊤` + nondegeneracy).
* **§1 — orbit-singletons at a spanning base.** Composing with soundness
  (`stabOrbit_imp_sameExactGram_of_anisotropic`, the free half of `CellsAreOrbits`) gives: at a base that **spans**
  and carries an **anisotropic** vector, every `Stab(S)`-orbit is a **singleton** — `stabOrbit_singleton_of_spanning`.
  Once the base spans, the residual symmetry cannot move any vertex.
* **§2 — the `O(d)` branch-count arithmetic.** `branchLevels_le_finrank`: an independent family of `L` vectors has
  `L ≤ finrank K V`; specialised to the forms graph (`V = Fin d → K`), `L ≤ d`. This is the arithmetic behind
  `L = O(d)`, consumed by Phase 1's `CertifiedBoundedTree.depthBound` (with `L := d`) once the descent tree's
  branch-level vectors are supplied (the seam below).

**Span-growth: SOLVED (§3), and it collapses the two seams into one.** The §3 fixed-point kernel proves that a fork
into a **non-trivial** orbit strictly grows the span (`span_lt_span_insert_of_stabOrbit_ne`), so — via the strict-chain
count (`strictChain_le_finrank`) — the number of such forks is `≤ finrank K V = d` (`nontrivialForks_le_finrank`). This
is the span-growth seam of §2, now discharged for the forks that grow the span. The **residual** — forks whose followed
orbit is a *singleton* (`w ∈ span S`) — leaves both the span and `Stab(S)` unchanged, so it can only be a fork because
the coarser refinement *cell* split. That residual is **exactly cell-discretisation**: the two seams of §2 are one seam,
the WL-orbit defect. So `L = (non-trivial-orbit forks, ≤ d, PROVED) + (singleton-orbit forks, = cell-discretisation)`.

**The single remaining seam — cell-discretisation (open, NOT tech debt).** Geometry (§1) gives orbit-singletons at a
spanning base, but branching stops only once the *cells* (what 1-WL sees — the square-class / isotropy-class profile,
strictly coarser than exact Gram) are singletons. Unlike the Witt seam (known-true, large, deferred), this is a genuine
open obligation: it is the same WL-vs-orbit defect as the poly crux (`B ≤ poly(q)`), at the level of the branch *depth*.
It lives in the abstract descent world (`sel`/`AdjMatrix`, Phase 1/4). See the recovery doc §6 ITEM A for its scoping.

Reuses the geometric model of `ScratchOrbitBaseCase`/`ScratchWallKernel` (`Similitude`/`StabOrbit`/`SameExactGram`, all
axiom-clean).

Axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean`, NOT in `build.sh`.
-/
import ChainDescent.ScratchWallKernel

namespace ChainDescent.BranchDepth

open ChainDescent.OrbitBaseCase ChainDescent.Wall QuadraticMap

set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  {Q : QuadraticForm K V}

/-! ## §1 — the spanning determiner and orbit-singletons at a spanning base -/

/-- **The spanning determiner (generalised `coords_determineK`).** With a nondegenerate polar form, the exact Gram
profile to a base `S` whose span is `⊤` determines the vertex: `SameExactGram Q ↑S t t' → t = t'`. Only the polar half
of `SameExactGram` is used — `polar Q t s = polar Q t' s` for all `s ∈ S` forces `polarBilin (t - t')` to vanish on a
spanning set, hence everywhere, hence (nondegeneracy) `t = t'`. Generalises the standard-frame
`coords_determineK` (`ChainDescent/FieldGeneric.lean:87`) to an arbitrary spanning base. -/
theorem spanning_sameExactGram_determines {S : Finset V}
    (hnd : (Q.polarBilin).Nondegenerate)
    (hspan : Submodule.span K (↑S : Set V) = ⊤)
    {t t' : V} (h : SameExactGram Q (↑S : Set V) t t') : t = t' := by
  have hpol : ∀ s ∈ (↑S : Set V), Q.polarBilin (t - t') s = 0 := by
    intro s hs
    rw [map_sub, LinearMap.sub_apply, polarBilin_apply_apply, polarBilin_apply_apply,
      h.2 s hs, sub_self]
  have hzero : Q.polarBilin (t - t') = 0 := by
    apply LinearMap.ext_on hspan
    intro x hx
    rw [LinearMap.zero_apply]
    exact hpol x hx
  have hsep := hnd.1 (t - t') (fun y => by rw [hzero, LinearMap.zero_apply])
  exact sub_eq_zero.mp hsep

/-- **★ Orbit-singletons at a spanning anisotropic base.** At a base `S` that **spans** `V` and carries an
**anisotropic** vector `a` (`Q a ≠ 0`), every `Stab(S)`-orbit is a singleton: `StabOrbit Q ↑S t t' → t = t'`. The
residual similitude freedom, once the base spans and pins the multiplier (`a` anisotropic ⟹ `μ = 1`), cannot move any
vertex. This is the geometric backbone of "an `O(d)` base rigidifies the forms graph" — the doc's §6 ITEM A first
concrete step. (Branching *stops* only once the coarser refinement *cells* are singletons — carried seam 2.) -/
theorem stabOrbit_singleton_of_spanning {S : Finset V} {a : V}
    (haS : a ∈ (↑S : Set V)) (ha : Q a ≠ 0)
    (hnd : (Q.polarBilin).Nondegenerate)
    (hspan : Submodule.span K (↑S : Set V) = ⊤)
    {t t' : V} (h : StabOrbit Q (↑S : Set V) t t') : t = t' :=
  spanning_sameExactGram_determines hnd hspan
    (stabOrbit_imp_sameExactGram_of_anisotropic haS ha h)

/-! ## §2 — the `O(d)` branch-count arithmetic -/

/-- **★ The `O(d)` branch-depth ceiling (arithmetic).** An independent family of `L` vectors in `V` has
`L ≤ finrank K V`. With the span-growth seam (the vectors individualized at the `L` branching levels of a path are
linearly independent — each genuine fork pins a new direction), the number of branching levels is `≤ finrank K V`. For
the forms graph `V = Fin d → K` this is `≤ d` (`branchLevels_le_dim_forms`), so `L = O(d)`. Feeds Phase 1's
`CertifiedBoundedTree.depthBound` with `L := finrank K V`. -/
theorem branchLevels_le_finrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {L : ℕ} (v : Fin L → V) (hv : LinearIndependent K v) :
    L ≤ Module.finrank K V := by
  simpa using hv.fintype_card_le_finrank

/-- **The forms-graph specialisation `L ≤ d`.** On `V = Fin d → K` (`n = q^d` vertices), an independent family of
branch-level vectors numbers `≤ d`, i.e. `L = O(d)` exactly — the recovery route's second poly factor, modulo the
span-growth seam. -/
theorem branchLevels_le_dim_forms {K : Type*} [Field K] {d L : ℕ}
    (v : Fin L → (Fin d → K)) (hv : LinearIndependent K v) : L ≤ d := by
  have h := branchLevels_le_finrank (K := K) (V := Fin d → K) v hv
  simpa using h

/-! ## §3 — the span-growth seam, SOLVED (the fixed-point kernel + the strict-chain count)

The span-growth seam of §2 — "each *branching* level grows the span" — is not free in general, but it *is* free for
the forks that matter. The engine is a single fixed-point fact: a similitude fixing `S` pointwise is **linear**, so it
fixes all of `span S` pointwise. Hence a vertex `w ∈ span S` is a **fixed point** of `Stab(S)` — its orbit is `{w}`.
Contrapositively, a vertex with a **non-trivial** orbit lies **outside** `span S`, so individualizing it **strictly
grows** the span. Composed with the strict-chain bound (a strictly increasing chain of subspaces has `≤ finrank`
steps), this gives: **the number of forks into non-trivial orbits on any path is `≤ finrank K V = d`**.

This *solves* span-growth for the non-trivial-orbit forks and, crucially, **pins its residual to cell-discretisation**:
a fork whose followed orbit is a *singleton* (`w ∈ span S`) leaves both the span and `Stab(S)` unchanged — it can only
be a fork because the coarser refinement *cell* split (1-WL sees new isotropy data `isoClass (Q (· − w))` that the orbit
structure does not). So `L = (#non-trivial-orbit forks, ≤ d, proved here) + (#singleton-orbit forks, = the
cell-vs-orbit defect = cell-discretisation)`. The two seams of §2 are therefore **one** seam: the WL-orbit defect. -/

/-- **The fixed-point kernel.** A similitude fixing `S` pointwise is linear, hence fixes all of `span S` pointwise
(span induction). The source of every orbit-triviality fact below. -/
theorem stab_fixes_span {S : Set V} {g : Similitude Q}
    (hfix : ∀ s ∈ S, g.toLinearEquiv s = s) {w : V} (hw : w ∈ Submodule.span K S) :
    g.toLinearEquiv w = w := by
  refine Submodule.span_induction (p := fun x _ => g.toLinearEquiv x = x) ?_ ?_ ?_ ?_ hw
  · intro x hx; exact hfix x hx
  · simp
  · intro x y _ _ hx hy; rw [map_add, hx, hy]
  · intro a x _ hx; rw [map_smul, hx]

/-- **A vertex in `span S` is a singleton `Stab(S)`-orbit.** Since every `S`-fixing similitude fixes `span S`, a
`w ∈ span S` cannot be moved: `StabOrbit Q ↑S w w' → w = w'`. -/
theorem stabOrbit_trivial_of_mem_span {S : Finset V} {w w' : V}
    (hw : w ∈ Submodule.span K (↑S : Set V)) (h : StabOrbit Q (↑S : Set V) w w') : w = w' := by
  obtain ⟨g, hfix, hgw⟩ := h
  exact (stab_fixes_span hfix hw).symm.trans hgw

/-- **Non-trivial orbit ⟹ outside the span (span-growth kernel).** The contrapositive: a vertex with a *non-trivial*
`Stab(S)`-orbit is not in `span S`. This is what makes a genuine fork add a new dimension. -/
theorem notMem_span_of_stabOrbit_ne {S : Finset V} {w w' : V}
    (h : StabOrbit Q (↑S : Set V) w w') (hne : w ≠ w') :
    w ∉ Submodule.span K (↑S : Set V) :=
  fun hw => hne (stabOrbit_trivial_of_mem_span hw h)

/-- **★ A fork into a non-trivial orbit strictly grows the span.** Individualizing a vertex `w` with a non-trivial
`Stab(S)`-orbit enlarges the span: `span ↑S < span (insert w ↑S)`. The step that drives the `L ≤ d` count. -/
theorem span_lt_span_insert_of_stabOrbit_ne {S : Finset V} {w w' : V}
    (h : StabOrbit Q (↑S : Set V) w w') (hne : w ≠ w') :
    Submodule.span K (↑S : Set V) < Submodule.span K (insert w (↑S : Set V)) := by
  have hnm : w ∉ Submodule.span K (↑S : Set V) := notMem_span_of_stabOrbit_ne h hne
  have hle : Submodule.span K (↑S : Set V) ≤ Submodule.span K (insert w (↑S : Set V)) :=
    Submodule.span_mono (Set.subset_insert w _)
  have hmem : w ∈ Submodule.span K (insert w (↑S : Set V)) :=
    Submodule.subset_span (Set.mem_insert w _)
  exact lt_of_le_of_ne hle (fun heq => hnm (heq.symm ▸ hmem))

/-- **The strict-chain count.** A strictly increasing chain of `L + 1` subspaces has `L ≤ finrank K V` steps (each
proper inclusion strictly raises `finrank`, bounded by `finrank V`). The dimension ceiling behind `L = O(d)`. -/
theorem strictChain_le_finrank {L : ℕ} (W : Fin (L + 1) → Submodule K V) (hW : StrictMono W) :
    L ≤ Module.finrank K V := by
  have key : ∀ i : Fin (L + 1), (i : ℕ) ≤ Module.finrank K (W i) := by
    intro i
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have hlt : Module.finrank K (W j.castSucc) < Module.finrank K (W j.succ) :=
        Submodule.finrank_lt_finrank_of_lt (hW Fin.castSucc_lt_succ)
      have : (j.castSucc : ℕ) + 1 ≤ Module.finrank K (W j.succ) := by omega
      simpa [Fin.val_succ, Fin.val_castSucc] using this
  have h1 : L ≤ Module.finrank K (W (Fin.last L)) := by
    have := key (Fin.last L); simpa using this
  exact le_trans h1 (Submodule.finrank_le _)

/-- **★ Span-growth, solved: non-trivial-orbit forks are `≤ d`.** Given a chain of `L + 1` bases whose spans strictly
increase at every level (which every fork into a non-trivial orbit does, by `span_lt_span_insert_of_stabOrbit_ne`), the
number of levels is `L ≤ finrank K V`. On the forms graph (`V = Fin d → K`) this is `≤ d`. This discharges the
span-growth seam for the forks that grow the span; the *residual* — forks whose followed orbit is a singleton — leaves
the span fixed and is exactly the cell-discretisation gap (see §3 header). -/
theorem nontrivialForks_le_finrank {L : ℕ} (W : Fin (L + 1) → Finset V)
    (hgrow : ∀ i : Fin L,
      Submodule.span K (↑(W i.castSucc) : Set V) < Submodule.span K (↑(W i.succ) : Set V)) :
    L ≤ Module.finrank K V :=
  strictChain_le_finrank (fun i => Submodule.span K (↑(W i) : Set V))
    (Fin.strictMono_iff_lt_succ.mpr hgrow)

end ChainDescent.BranchDepth
