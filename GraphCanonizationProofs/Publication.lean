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

Compile standalone (NOT via `lake build`; this file carries `axiom` and temporarily contains `sorry` by design):
  cd GraphCanonizationProofs && lake env lean Publication.lean
Quality note: this is the ONLY file in the project permitted `axiom`. The library stays axiom-clean
`[propext, Classical.choice, Quot.sound]`; the citations are carried there as *hypotheses*, and only HERE
are they instantiated with `axiom` witnesses so `#print axioms` aggregates them into one legible list.

## STATUS (2026-07-17) — the statements here are TARGETS, not finalized design (user steer; blocker-audit item 8).
Finalization is deliberately deferred; read the obligations as the intended shape, not as what the library fills
today. Per-obligation state:
  · ① — swap-ready and mechanical, EXCEPT the import cone: this file imports only `ChainDescent.Spine`, which does
    NOT reach `Descend`/`Stall`/`Residue`/`PrunedSupply`. Fix the import at swap time (one line; the swap has never
    been compile-tested).
  · ② — now fillable PER FIXED DEPTH `d`: pin the canonizer-of-record (encode-free refiner + `lookaheadKey` +
    `prunedSupply d`) and `SupplyCost.descentCost_pruned_lookahead_le` supplies the explicit polynomial for
    `costConst`/`costDeg`. The status comment inside `canon_poly_or_flag` below is SUPERSEDED (see its banner).
  · ③ — TWO LAYERS, not a design conflict: the library's operational residue (`Residue.Residue := ¬Handled`, key/
    supply-parameterized) is the intermediate; this file's structural atoms are the target; the missing object is
    the ATTRIBUTION theorem `¬Handled(record) → D1 ∨ D2`. ⚠ The strong reading "flag ⟹ genuine obstruction" is NOT
    reachable in full: the flag marks a CAPABILITY boundary, not hardness — the leftover can be a single unresolved
    decision, and constructible flagged-but-not-believed-hard inputs exist (odd-part ≥ 7 fold towers, audit item 4).
    Target the graded pair instead: (③a) flag ⟹ ¬Handled(record) + the stall attribution
    (`Composite.forceThenConsume_stall`) — unconditional; (③b) per-family: flag ∧ ⟨family⟩ ⟹ structural atom —
    where the citations live. The atoms stay `opaque` until the per-family carving matures; they must NEVER be
    defined as "the algorithm flagged" (the firewall below stands).
  · The §1 "mutual stall" prose is the TARGET flag semantics, pending the sel rewrite (handoff §6.1 design-pass
    block): today's `Stall.stalled` reads "the LEAST-COLOUR cell stalled", not "the node stalled".
  · Axiom WIRING IS DEFERRED for every entry in §2; per-entry cautions are noted inline (G3 threshold, FTPG's
    corrected predicate, Payne–Thas narrowing).
  · Non-vacuity: the handled half is now fillable in principle (`Residue.handled_emptyAdj` — a trivial witness);
    the load-bearing witnesses (a CFI/forms graph handled AT THE RECORD RESOLVERS; a real unhandled instance at
    the same resolvers) remain the target. The library's `residue_nonvacuous` witness uses `constKey`/`emptySupply`
    and does NOT transfer to the record object.
-/
import ChainDescent.Spine

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

/-! ### `UnhandledResidue` — the firewall valve, given its structural shape.

The obstruction is a property of the **residue scheme the descent reaches** on `G` (an iso-invariant of `G`
via the spine, hence well-defined and NOT "the algorithm flagged"). It is a disjunction of three structural
atoms, one per open source of hardness — so that everything on the *handled* side needs only real citations:

  · (D0) `residueNonSchurian`      — the reached residue is not schurian. **This is a MODELLING GAP, not a genuine
        unhandled residue (2026-07-12).** Every symmetry-only residue is believed to be node-4 (schurian by
        definition) or Cameron, so "non-schurian reached residue" is the `SchurianScheme` model-faithfulness question
        (is the actual 2-WL-closure residue the `orbitalScheme H` model?), a modelling obligation to discharge — NOT
        an honest flag for a real obstruction. Kept in the disjunction as a documented placeholder; the intended end
        shape drops it, leaving `residueHiddenJohnson ∨ residueRigidObstruction`. See endgame-spec §4.1.
  · (D1) `residueHiddenJohnson`    — SYMMETRIC domain: the reached residue is a Cameron scheme of a
        **structurally named** hard type (the hidden-Johnson / un-coordinatizable geometric family — e.g. a
        classical GQ if `d = 4` recognition stalls). **Defined by geometric type, NOT by "the handled
        sub-classes we happened to finish"** — the latter is algorithm-relative and would erode the firewall
        (a family whose poly proof merely didn't land must not silently fall in here). Each carved type is a
        clean iso-invariant predicate on the residue.
  · (D2) `residueRigidObstruction` — RIGID domain: the IR-Phase residual (the "rigid-Cameron-equivalent"),
        `⊥` if the IR Phase proves it non-viable.

Each atom is `opaque` (a Seal/IR/Runtime-Phase deliverable). Its definition is deferred, but the *shape* — a
three-way disjunction with an explicit non-schurian absorber — is fixed here.

**THE FLAG IS THE INTERLEAVED-ENGINE MUTUAL STALL (2026-07-12).** The canonizer is a stepwise alternating fixpoint
`…∘phase2∘phase1…` (IR §11.11): at each pairwise relation the oracle **consumes** it (verified automorphism), or the
rigid solver **forces** it (row-space), or it is **deferred**; the run flags exactly at **mutual stall** — neither move
applies. Consumption is **verify-gated, not threshold-gated**, so a rigid residue (no automorphism) simply stalls and is
never mispruned; abelian symmetry fused behind a real decision is de-fused constructively by the solver kernel. The
residual the stall names is (D2) `residueRigidObstruction` (with any surviving symmetric Cameron core = (D1)); (D0) is a
modelling gap, not a stall residue. This keeps `residue_if_flag` (③) firewall-clean: the flag ⟹ a *structural* residue,
not "the algorithm gave up".

*Superseded framing (kept for provenance): the earlier plan flagged per-phase on a `base > baseMax` threshold and
assume-VT-pruned Phase-1 flags. That standalone-Algorithm-A seal crash-landed on fusion (a threshold prune can misprune
a fused rigid residue), and is replaced by the verify-gated interleaved engine above. The Phase-1 correctness obligation
is now "no non-abelian fusion survives into a rigid medium" (IR §11.14), carried like "or Cameron". -/
opaque residueNonSchurian       (n : ℕ) (G : AdjMatrix n) : Prop
opaque residueHiddenJohnson     (n : ℕ) (G : AdjMatrix n) : Prop
opaque residueRigidObstruction  (n : ℕ) (G : AdjMatrix n) : Prop

def UnhandledResidue (n : ℕ) (G : AdjMatrix n) : Prop :=
  residueNonSchurian n G ∨ residueHiddenJohnson n G ∨ residueRigidObstruction n G

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
policy allows to stay cited permanently. Source: Babai ITCS'14 / J.Algebra'15; Kivva JCTB'24; Sun–Wilmes.
⚠ WIRING CAUTION (2026-07-16 audit): the citable threshold is Sun–Wilmes `exp(Õ(n^{1/3}))` (all ranks; rank 3/4
at quasipoly via Babai/Kivva). NEVER instantiate `hClassify` at the `confinementLargeScheme` quasi-poly threshold
`n^{log₂ n}` — at that threshold the statement is Babai's OPEN conjecture, not a citation. -/
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
for the `q = pᵉ`, `e > 1` field twist. Source: Artin, *Geometric Algebra*.
⚠ WIRING TARGET = the CORRECTED difference-cone predicate (2026-07-16 fix): the original
`ConePreservingCollineationIsSemiSimilitude` (bare cone-preserving bijection antecedent) was false-as-formalized;
wire only the difference-cone form. (`JointVarietyDeterminesFamily` is PROVED outright — no axiom needed; it is
deliberately absent from this list.) -/
opaque FundamentalThmProjGeom : Prop
axiom ftpg : FundamentalThmProjGeom

/-- Buekenhout–Shult / Veldkamp–Tits: an abstract polar space of rank ≥ 3 is CLASSICAL (embeds in `PG(d,q)`
with its form). **CORRECTNESS/classicality only — NOT a complexity bound** (R1's poly-time is an in-project
effective-construction obligation, route-c-plan §7a). Used only for `d ≥ 6`. Source: Buekenhout–Shult,
Geom. Dedicata 1974; Tits, *Buildings of Spherical Type*. -/
opaque PolarSpaceRankGe3Classical : Prop
axiom buekenhout_shult : PolarSpaceRankGe3Classical

/-- Payne–Thas: recognition/coordinatization of a CLASSICAL generalized quadrangle (the `d = 4`, rank-2 case,
outside Buekenhout–Shult). **Correctness only.** The genuine soft spot (non-classical GQs exist), route-c-plan
§7a (e). Source: Payne–Thas, *Finite Generalized Quadrangles*.
⚠ MUST BE NARROWED to a specific characterization theorem before wiring (2026-07-16 audit): there is no general
"classical GQ recognition" theorem — as an unscoped axiom this would be citation-shaped open mathematics. -/
opaque ClassicalGQRecognition : Prop
axiom payne_thas : ClassicalGQRecognition

/-- Witt's theorem: over a field, `O(Q)` acts transitively on isometric isotropic subspaces / frames of a given
type. Discharges `ConfinementP4.FrameSelectorTransitive` — the assume-VT prune (confinement-P4) is sound because
the residual group is transitive on the selected isotropic-point cell, so the cell is one orbit. **Correctness
only** — a classical group-transitivity theorem (Artin, *Geometric Algebra*), NOT a complexity bound, and NOT the
bounded-WL-dim wall (`JointProfileRecoversAt`). Carried as a scoped citation; a **planned in-project build** (first
pieces done), expected to discharge before publication. -/
opaque WittFlagTransitivity : Prop
axiom witt_flag_transitivity : WittFlagTransitivity

/-! ## 3. THE OBLIGATIONS — the endgame theorem statements

Each is a `sorry`-stubbed compile target. The `-- discharged by:` note records which completed project
theorem(s) + citation(s) the body (held in another file for conciseness) will plug into. When all `sorry`s are filled, `#print axioms canonizer`
= `[propext, Classical.choice, Quot.sound]` ∪ {the citations actually used}. -/

/-- **①a Soundness (UNCONDITIONAL).** When the canonizer answers, its output is a genuine relabelling of the
input — so equal canonical forms ⟹ isomorphic inputs. -/
theorem canon_sound (n : ℕ) (G : AdjMatrix n) (cG : Fin n → Fin n → Nat)
    (h : canonForm? n G = some cG) :
    ∃ π : Equiv.Perm (Fin n), cG = labelledAdj π G := by
  -- ★ DISCHARGED (2026-07-13) against the REAL branching object: `ChainDescent.Descend.soundOpt_canonForm?`
  -- (`ChainDescent/Descend.lean`, axiom-clean, in build.sh). `Descend.canonForm? refine R : AdjMatrix n →
  -- Option (Labelled n)` is the computable, resolver-parameterized branching descent (mixed-composition
  -- Stage 0b); `soundOpt_canonForm?` has EXACTLY this shape, and holds for ANY `refine` and ANY resolver.
  -- Remaining = the opaque swap `canonForm? n G := Descend.canonForm? refine R G` (done once, with ②/③,
  -- after `refine` is instantiated with the encode-free round). Then this body is `soundOpt_canonForm? … G cG h`.
  sorry

/-- **①b Completeness (UNCONDITIONAL).** Whenever it answers on both inputs, the canonical forms coincide
iff the graphs are isomorphic — a complete isomorphism invariant. "Never wrong", for every input. -/
theorem canon_complete (n : ℕ) (G H : AdjMatrix n) (cG cH : Fin n → Fin n → Nat)
    (hG : canonForm? n G = some cG) (hH : canonForm? n H = some cH) :
    Iso G H ↔ cG = cH := by
  -- ★ DISCHARGED (2026-07-13): `ChainDescent.Descend.canonForm?_complete` — EXACTLY this shape, for the real
  -- branching object. Completeness is FREE: `CanonSpec.complete_of_isCanonicalFormOpt` (Stage 0a) says
  -- sound ∧ iso-invariant ⟹ complete, and `Descend.isCanonicalFormOpt_canonForm?` supplies both.
  --
  -- ★★ AND ITS TWO HYPOTHESES ARE NOW BOTH DISCHARGED (2026-07-14) — ① CARRIES NOTHING.
  --   · the refiner: `Refine.refineEquivariant_encodeFree` (the encode-free structural round);
  --   · the resolver contract `Descend.NarrowTransport`, via EITHER of its two routes —
  --       `Consume.narrowTransport_consume` (the ORACLE, `Covering` route; holds for EVERY oracle supply,
  --        because the resolver VERIFIES each candidate automorphism itself), or
  --       `Force.narrowEquivariant_forceBy` (the RIGID/FORCE route; sole obligation `KeyEquivariant`).
  -- Ready-made capstones: `Refine.exhaustive_canonizer`, `Consume.consume_canonizer`,
  -- `Force.force_canonizer` / `Force.lookahead_canonizer` — each gives ①a/①b/①c AND totality (never flags),
  -- with NO carried hypothesis at all.
  --
  -- ⛔ DO NOT restate the resolver contract as the single unconditional `Covering`: a covering resolver is
  -- provably VALUE-INVISIBLE (`Descend.canonForm?_eq_deferAll_of_covering`), which pins the object to the
  -- exhaustive branch-min (the retired `canonMin` anchor) and would force the rigid solver to KNOW THE ANSWER.
  --
  -- Remaining = the opaque swap (below), done once together with ②/③.
  sorry

/-- **①c The flag is iso-invariant (UNCONDITIONAL).** Flagging is a property of the isomorphism class, not
of the labelling — so "flagged" is a well-defined statement about a graph up to iso. -/
theorem flag_iso_invariant (n : ℕ) (G H : AdjMatrix n) (h : Iso G H) :
    (canonForm? n G = none) ↔ (canonForm? n H = none) := by
  -- ★ DISCHARGED (2026-07-13): `ChainDescent.Descend.canonForm?_flag_iso_invariant`; its hypotheses are now
  -- BOTH discharged (see ①b above) — ① carries nothing. Free, because `IsoInvariantOpt` is a single equation on
  -- `Option`s — "relabelling changes nothing", the answer AND whether it flagged. No separate flag obligation.
  sorry

/-- **② Poly-or-flag (the budget guarantee — the ONLY cost claim).** The descent either runs within the
explicit polynomial budget or it emits an honest flag. No residue predicate appears here. -/
theorem canon_poly_or_flag (n : ℕ) (G : AdjMatrix n) :
    cost n G ≤ costConst * n ^ costDeg ∨ canonForm? n G = none := by
  -- ⊘ THE STATUS BELOW IS SUPERSEDED (2026-07-17; retained for provenance). The guard design (`Stall.lean`)
  -- replaced the verify-consume-monovariant / fuel-placeholder plan: deferral IS the failure mode, the guarded
  -- descent is a SINGLE PATH of ≤ n+1 nodes or it flags (`Stall.resolvedAll_guard`, by construction), and the
  -- explicit polynomial is `SupplyCost.descentCost_pruned_lookahead_le` (end-to-end, for the canonizer of
  -- record, per fixed depth d). Filling this obligation = pinning the record object (fixes costConst/costDeg)
  -- + the opaque swap. See the file STATUS block.
  -- OPEN — this is now the main remaining obligation of ①/②. STATUS (2026-07-13):
  --  · `cost` is the `cost` PROJECTION of the same definition ①a/①b ride on: `ChainDescent.Descend.descentCost`
  --    (`descend` is written in `CostM`, so cost is co-defined with the value — no separate object, no bridge).
  --  · The OLD `n⁴` bound (`CanonForm.descentCost_le`) does NOT transfer: it was proved with `nbud = n`, i.e.
  --    the assume-VT single-path (`leaves = 1`) justification, which the branching/interleaved object breaks.
  --  · The poly guarantee is now the VERIFY-CONSUME MONOVARIANT (each covering-narrowing strictly reduces
  --    residual symmetry; each force reduces free relations; each defer is bounded by the branching bound)
  --    plus the fusion-severity look-ahead — see `docs/chain-descent-cost-model.md` STATUS and
  --    `docs/chain-descent-mixed-composition.md` Stage 4.
  --  · The flag is the MUTUAL STALL, not `base > baseMax` (the threshold-gated assume-VT flag is retired —
  --    it could misprune a fused rigid residue). `descend`'s current `fuel`-exhaustion `none` is a PLACEHOLDER
  --    for that stall test. NB fuel is PER-LAYER, never threaded, so each resolver is poly-or-flag LOCALLY.
  sorry

/-- **③ Flag characterization (where the citations live).** A flag is emitted iff the input genuinely
contains an unhandled obstruction — NOT because the algorithm is weak. This is the theorem that earns the
"or Cameron/hidden-Johnson/IR-residue" escape; its proof consumes the classification citations.
NON-VACUITY OBLIGATION (separate lemma, `unhandledResidue_nonvacuous` below): `UnhandledResidue` is neither
always-true nor defined as "flagged". -/
theorem residue_if_flag (n : ℕ) (G : AdjMatrix n) :
    canonForm? n G = none → UnhandledResidue n G := by
  -- discharged by: `reachesRigidOrCameron_*` (Seal Phase) + `cameron_classification` (+ Skresanov/Liebeck/
  --                Ponomarenko for the residue identification) + the IR-Phase residual characterization.
  sorry

/-- **Non-vacuity of ③ (the documented vacuity-trap guard).** There exist handled graphs (a flag is not
forced) AND unhandled ones (the excluded set is real). Without this, `residue_if_flag` is meaningless.
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
  · exact Or.inr ((residue_if_flag n G) hflag)

/-! ## 5. The axiom footprint (the deliverable)

Run these after the `sorry`s are filled. TARGET (endgame) output for each:
  `[propext, Classical.choice, Quot.sound, <the citations that theorem actually uses>]`
CURRENT output includes `sorryAx` — the visible "remaining work" marker. -/

#print axioms canonizer
#print axioms unhandledResidue_nonvacuous


end Showcase
