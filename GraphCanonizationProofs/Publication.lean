/-
# Publication.lean — the endgame SHOWCASE skeleton (WIP; NOT in build.sh / defaultTargets)

**What this file is.** The compile-target for the project's final deliverable: a single file whose
`#print axioms` on a handful of headline theorems shows *exactly* the project's trusted base — the Lean
kernel primitives `[propext, Classical.choice, Quot.sound]` plus a short, inspectable list of **named
classical citations** (each a theorem *proved outside the project*). A Lean-literate reviewer audits the
citation list and trusts the machine for everything else.

**How to read it.** The theorem *statements* are the specification; the `sorry` bodies are the remaining --Much of the comments will need to be cleaned up before publishing, i.e. a reviewer doesn't need to be told how to read
work. When the Runtime Phase lands, each `sorry` is replaced by a term that plugs into the completed
project theorems and consumes the citation axioms — at which point `#print axioms` flips from `[sorryAx, …]`
to `[propext, Classical.choice, Quot.sound, <citations>]`. That flip *is* "done".

**Why the shape (see the design write-up).** Correctness is **unconditional** (the algorithm is never
wrong — it returns a complete iso-invariant *or an honest flag*), cost is **conditional** (poly-time *or*
it flagged), and the residue predicate appears **only** in a characterization (a flag ⟺ a genuine
obstruction). This is strictly stronger than "canonizes residuals + poly time" and cleanly separates the
three concerns.

**THE FIREWALL (the one rule that keeps this honest).** An `axiom` here may *only* be a genuine classical
theorem a reviewer accepts as known (G3/CFSG, Skresanov, Liebeck, Ponomarenko, FTPG, …). The project's own
**open frontier** must NEVER become an axiom — it silently downgrades "conditional on known results" to
"conditional on our conjecture", and `#print axioms` cannot tell them apart. The release valve is
`UnhandledResidue`: it is *defined to absorb exactly the open cases*, so everything on the handled side
needs only real citations. If a family's poly-ness is still only a *meta* argument (as Route C's is today),
it either becomes a real `cost ≤ poly` proof or it goes inside `UnhandledResidue`. It cannot become an axiom.

**Phase names** (avoiding the "Phase 1/2/…" collisions):
  · **Seal Phase**    — the symmetric-domain seal (`reachesRigidOrCameron`); node-4 residue + Cameron shrink.
  · **IR Phase**      — the rigid mirror solver (recover the F₂ system → Gaussian); reuses the recovery idea.
  · **Runtime Phase** — the Lean `canonForm?` / `cost` objects + the cost model; where "poly" stops being meta.
  · **Publication Phase** — this file, pristine; the paper.
  · **Maintenance**   — cross-cutting.

Compile standalone (NOT via `lake build`; this file carries `axiom` and temporarily contains `sorry` by design):
  cd GraphCanonizationProofs && lake env lean Publication.lean
Quality note: this is the ONLY file in the project permitted `axiom`. The library stays axiom-clean
`[propext, Classical.choice, Quot.sound]`; the citations are carried there as *hypotheses*, and only HERE
are they instantiated with `axiom` witnesses so `#print axioms` aggregates them into one legible list.
-/
import ChainDescent

namespace Showcase

open ChainDescent

/-! ## 0. Graph isomorphism (on the project's own `AdjMatrix`) -/

/-- Two graphs on the same vertex set are **isomorphic** when some relabelling of `G` is `H`
(reusing the project's `labelledAdj`). Standard graph iso; an equivalence relation. -/
def Iso {n : ℕ} (G H : AdjMatrix n) : Prop :=
  ∃ π : Equiv.Perm (Fin n), labelledAdj π G = H.adj

/-! ## 1. Runtime-Phase objects (STUBS — `opaque`, to be replaced by the real Lean canonizer)

These are the objects the Runtime Phase must *build*. They are `opaque` (sealed, irreducible) so the
obligations below are genuinely open — NOT vacuously true from a placeholder value. Replacing an `opaque`
with the real Lean definition (the descent model + cost accounting) is exactly the Runtime-Phase work.

  · `canonForm? G` — the canonizer's output on `G`: a canonical adjacency (a relabelling of `G`), or
    `none` = an **honest flag** ("this input hides an obstruction I cannot certify cheaply").
  · `cost G`       — the operation count of the descent on `G` = (# descent nodes) × (per-node oracle work),
    a `ℕ` computed from the actual Lean descent. Granularity to be DECLARED in the paper (operation-count
    proxy; each step separately argued poly-size).
  · `UnhandledResidue G` — the STRUCTURAL obstruction predicate (Cameron / hidden-Johnson in the symmetric
    domain; the unhandled IR residue in the rigid domain). Must be an *independent* geometric predicate,
    NOT "the algorithm flagged" (that makes §3 a tautology). See the firewall + the non-vacuity obligation. -/

opaque canonForm? (n : ℕ) (G : AdjMatrix n) : Option (Fin n → Fin n → Nat) := none
opaque cost (n : ℕ) (G : AdjMatrix n) : ℕ := 0
opaque UnhandledResidue (n : ℕ) (G : AdjMatrix n) : Prop := True

/-- Explicit polynomial cost bound `costConst * n ^ costDeg`. The paper pins concrete numerals for
`costConst`, `costDeg` (explicit polynomial ≫ `∃ p : Polynomial …`: more honest, avoids formalizing the
class P, and the reviewer reads the degree off the statement). -/
opaque costConst : ℕ := 0
opaque costDeg : ℕ := 0

/-! ## 2. The trusted base — CITATIONS ONLY (placeholders; the ONLY custom axioms)

In the real file each of these is the *actual* project predicate (e.g. `ChainDescent.PrimitiveCCClassification`
from `Cascade`, `AffineSchemeTwoClosed` from `RouteCSeam`, `Theorem41Statement` from `CoherentConfig`,
`ConePreservingCollineationIsSemiSimilitude` from `RouteCFormAdapters`, the Ponomarenko cyclotomic 2-sep,
the Liebeck affine-rank-3 classification), carried as a *hypothesis* by the library capstones and discharged
here by the `axiom` witness. The placeholders below document the intended trusted base; wiring them to the
real predicates is a mechanical Publication-Phase step.
If any of them get discharged, they can be removed from this list.

FIREWALL CHECK for this list: every entry is a theorem *proved outside the project* (CFSG / finite-geometry
/ classical-group development). Nothing here is a project conjecture. -/

/-- G3 — the primitive-coherent-configuration / Cameron classification (CFSG-based). The one citation
policy allows to stay cited permanently. Source: Babai ITCS'14 / J.Algebra'15; Kivva JCTB'24; Sun–Wilmes. -/
opaque PrimitiveCCClassification : Prop
axiom cameron_classification : PrimitiveCCClassification

/-- Skresanov rank-3 affine 2-closure: the affine scheme of a classical `G₀` has no unexpected
automorphisms (coarse-Aut pinning; underpins all four Route-C families' `|Aut|` side). Source: Skresanov
arXiv:2007.14696 / 2202.03746. -/
opaque AffineSchemeTwoClosed : Prop
axiom skresanov_two_closure : AffineSchemeTwoClosed

/-- Liebeck affine-rank-3 classification (places the classical instances in the node-4 residue). -/
opaque LiebeckAffineRank3 : Prop
axiom liebeck_rank3 : LiebeckAffineRank3

/-- Ponomarenko cyclotomic 2-separability (the 1-dim cyclotomic slice). Source: arXiv:2006.13592 Thm 1.1. -/
opaque PonomarenkoCyclotomic2Sep : Prop
axiom ponomarenko_2sep : PonomarenkoCyclotomic2Sep

/-- Fundamental theorem of projective geometry (cone-preserving collineations are semilinear); needed only
for the `q = pᵉ`, `e > 1` field twist. Source: Artin, *Geometric Algebra*. -/
opaque FundamentalThmProjGeom : Prop
axiom ftpg : FundamentalThmProjGeom

/-! ## 3. THE OBLIGATIONS — the endgame theorem statements

Each is a `sorry`-stubbed compile target. The `-- discharged by:` note records which completed project
theorem(s) + citation(s) the body (held in another file for conciseness) will plug into. When all `sorry`s are filled, `#print axioms canonizer`
= `[propext, Classical.choice, Quot.sound]` ∪ {the citations actually used}. -/

/-- **①a Soundness (UNCONDITIONAL).** When the canonizer answers, its output is a genuine relabelling of the
input — so equal canonical forms ⟹ isomorphic inputs. -/
theorem canon_sound (n : ℕ) (G : AdjMatrix n) (cG : Fin n → Fin n → Nat)
    (h : canonForm? n G = some cG) :
    ∃ π : Equiv.Perm (Fin n), cG = labelledAdj π G := by
  -- discharged by: `SpineChain.canonAdj` (leaf relabelling by the rank permutation) is a `labelledAdj`.
  sorry

/-- **①b Completeness (UNCONDITIONAL).** Whenever it answers on both inputs, the canonical forms coincide
iff the graphs are isomorphic — a complete isomorphism invariant. "Never wrong", for every input. -/
theorem canon_complete (n : ℕ) (G H : AdjMatrix n) (cG cH : Fin n → Fin n → Nat)
    (hG : canonForm? n G = some cG) (hH : canonForm? n H = some cH) :
    Iso G H ↔ cG = cH := by
  -- discharged by: `spine_branch_independent` + `warm_6_2` (direction-invariance) + `canon_sound`.
  sorry

/-- **①c The flag is iso-invariant (UNCONDITIONAL).** Flagging is a property of the isomorphism class, not
of the labelling — so "flagged" is a well-defined statement about a graph up to iso. -/
theorem flag_iso_invariant (n : ℕ) (G H : AdjMatrix n) (h : Iso G H) :
    (canonForm? n G = none) ↔ (canonForm? n H = none) := by
  -- discharged by: the descent's selector is partition-invariant (`target_direction_blind` / spine).
  sorry

/-- **② Poly-or-flag (the budget guarantee — the ONLY cost claim).** The descent either runs within the
explicit polynomial budget or it emits an honest flag. No residue predicate appears here. -/
theorem canon_poly_or_flag (n : ℕ) (G : AdjMatrix n) :
    cost n G ≤ costConst * n ^ costDeg ∨ canonForm? n G = none := by
  -- discharged by: (Runtime Phase) reaches-rigid ⟹ discretizes in poly nodes ⟹ ¬flag ∧ cost ≤ poly;
  --                otherwise flag. This is where "poly" stops being a meta-claim.
  sorry

/-- **③ Flag characterization (where the citations live).** A flag is emitted iff the input genuinely
contains an unhandled obstruction — NOT because the algorithm is weak. This is the theorem that earns the
"or Cameron/hidden-Johnson/IR-residue" escape; its proof consumes the classification citations.
NON-VACUITY OBLIGATION (separate lemma, `unhandledResidue_nonvacuous` below): `UnhandledResidue` is neither
always-true nor defined as "flagged". -/
theorem flag_iff_residue (n : ℕ) (G : AdjMatrix n) :
    canonForm? n G = none ↔ UnhandledResidue n G := by
  -- discharged by: `reachesRigidOrCameron_*` (Seal Phase) + `cameron_classification` (+ Skresanov/Liebeck/
  --                Ponomarenko for the residue identification) + the IR-Phase residual characterization.
  sorry

/-- **Non-vacuity of ③ (the documented vacuity-trap guard).** There exist handled graphs (a flag is not
forced) AND unhandled ones (the excluded set is real). Without this, `flag_iff_residue` is meaningless.
Fill with concrete witnesses (e.g. a forms-graph / CFI instance handled; a hidden-Johnson instance not). -/
theorem unhandledResidue_nonvacuous :
    (∃ (n : ℕ) (G : AdjMatrix n), ¬ UnhandledResidue n G) ∧
    (∃ (n : ℕ) (G : AdjMatrix n), UnhandledResidue n G) := by
  sorry

/-! ## 4. THE HEADLINE — one quotable theorem, composed from the obligations

This body is REAL (no `sorry`): it shows the composition. Its `#print axioms` is therefore exactly the
union of the obligations' axioms — currently `sorryAx`, and at the endgame the citation list. -/

/-- **The canonizer theorem.** For every graph `G`: (i) whenever the canonizer answers on `G` and any `H`,
the outputs coincide iff `G ≅ H` (a complete iso-invariant — never wrong); and (ii) the canonizer runs
within the explicit polynomial budget, unless `G` contains a genuine unhandled obstruction. -/
theorem canonizer (n : ℕ) (G : AdjMatrix n) :
    (∀ (H : AdjMatrix n) (cG cH : Fin n → Fin n → Nat),
        canonForm? n G = some cG → canonForm? n H = some cH → (Iso G H ↔ cG = cH))
    ∧ (cost n G ≤ costConst * n ^ costDeg ∨ UnhandledResidue n G) := by
  refine ⟨fun H cG cH hG hH => canon_complete n G H cG cH hG hH, ?_⟩
  rcases canon_poly_or_flag n G with hpoly | hflag
  · exact Or.inl hpoly
  · exact Or.inr ((flag_iff_residue n G).mp hflag)

/-! ## 5. The axiom footprint (the deliverable)

Run these after the `sorry`s are filled. TARGET (endgame) output for each:
  `[propext, Classical.choice, Quot.sound, <the citations that theorem actually uses>]`
CURRENT output includes `sorryAx` — the visible "remaining work" marker. -/

#print axioms canonizer
-- #print axioms canon_complete
-- #print axioms canon_poly_or_flag
-- #print axioms flag_iff_residue

end Showcase
