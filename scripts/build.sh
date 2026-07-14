#!/usr/bin/env bash
# Serial build for the chain-descent Lean library.
#
# WHY THIS EXISTS
# ---------------
# `lake build` parallelises across all CPU cores by default (this box reports
# 12). Each Lean worker loads the transitive mathlib environment and peaks at
# ~2.7 GiB RSS. With only ~7.7 GiB of RAM — most of it already held by the
# running VS Code Lean server (`lean --server`, ~3-4 GiB) — even two or three
# concurrent workers blow past physical memory and the build falls into swap
# thrash. Measured: a clean parallel rebuild takes ~12 min (≈40% CPU, dominated
# by *system*/IO time = swapping), while building the same modules one worker at
# a time takes ~60 s. The compilation itself is fast; the 12 minutes was almost
# entirely swap overhead.
#
# This Lake version (Lean v4.30.0-rc2) exposes no `-j`/`--jobs` flag, so we
# serialise by invoking `lake build` once per module in dependency order: each
# call finds its dependencies already built and compiles a single module, so at
# most one ~2.7 GiB worker is resident at a time and the build stays in RAM.
#
# USAGE
#   scripts/build.sh            # serial full build of the chain-descent library
#   scripts/build.sh --verbose  # show lake output per module
#
# If you add or reorder modules, update MODULES below (keep topological order:
# a module must appear after everything it imports).
set -euo pipefail

cd "$(dirname "$0")/../GraphCanonizationProofs"

# Kill any stray batch-build workers from a previous or overlapping run, so two
# concurrent builds never thrash swap fighting over the same modules (a common
# foot-gun: a backgrounded build left running, then a second build launched).
# We target ONLY the batch `lake build` driver and its `lean … .lean -o …` compile
# workers — the VS Code Lean server (`lake serve`, `lean --server`, `lean --worker
# file://…`, none of which carry a `.lean -o` output flag) is left untouched.
pkill -f 'lake build' 2>/dev/null || true
pkill -f '\.lean -o' 2>/dev/null || true
sleep 1   # let killed workers release Lake's build lock before we start

VERBOSE=0
[[ "${1:-}" == "--verbose" || "${1:-}" == "-v" ]] && VERBOSE=1

# Topological order: base first, then modules in increasing dependency depth.
MODULES=(
  ChainDescent              # base / Core (POE, warmRefine, samePartition, §6.2 direction-invariance)
  ChainDescent.Spine        # ← base (§15 descent spine + canonicalization; split from ChainDescent 2026-07-06)
  ChainDescent.CostModel    # ← base, Spine (Runtime-Phase cost model: CostM, per-node cap, spine ② cost≤n⁴; ported 2026-07-09 from ScratchCostModel*)
  ChainDescent.CanonForm    # ← Spine, CostModel (①a soundness + ② capped canonForm? object; ported 2026-07-09 from ScratchCanon{Sound,FormCapped})
  ChainDescent.OrbitRecovery # ← Spine (§16–18 orbit recovery; split from ChainDescent 2026-07-06)
  ChainDescent.ClosureCalculus # ← base (§13/§14 propagation-closure investigation — leaf; split from ChainDescent 2026-07-06)
  ChainDescent.Saturation   # ← Mathlib only (generic; shared by Scheme + Cascade)
  ChainDescent.GaussCount   # ← Mathlib only (Gauss-sum point-count toolkit for the B.1c-ii forms-graph discharge)
  ChainDescent.CFI          # ← base
  ChainDescent.Scheme       # ← base
  ChainDescent.Separability # ← base, Scheme (S-ring/CC separability layer; Ponomarenko–Vasil'ev parameters)
  ChainDescent.CoherentConfig # ← base, Scheme (general multi-fiber CC substrate; Thm 4.1 statement layer)
  ChainDescent.CascadeOracle # ← base, CFI, Scheme
  ChainDescent.LinearOracle # ← CascadeOracle
  ChainDescent.Group        # ← CascadeOracle
  ChainDescent.Cascade      # ← CascadeOracle, Group
  ChainDescent.Confinement  # ← Cascade, CostModel (confinement lemma / Algorithm A core: P1–P4 + Witt → SelectedCellIsOrbit; ported 2026-07-09 from ScratchNodeCountBridge + ScratchConfinement{,P1,P4,P3,Witt,SchurianModel})
  ChainDescent.Phase2Handoff # ← Cascade (RRU rigid-residue handoff interface: rigidResidue as R(G) + Phase-2 solver contract; added 2026-07-10)
  ChainDescent.CanonicalForm # ← Cascade (mixed-composition Stage 0a: canonical-form spec sound∧iso-inv⟹complete + Option/flagging lift SoundOpt/IsoInvariantOpt; added 2026-07-11, lifted 2026-07-13)
  ChainDescent.Descend      # ← Spine, CanonicalForm, CostModel (mixed-composition Stage 0b: THE OBJECT — computable branching resolver-parameterized descent in CostM; index-free indivOne; computable leaf emit; added 2026-07-13)
  ChainDescent.CascadeAffine # ← Cascade, Scheme (§13b/§13c engine + Phase-2 affine beachhead)
  ChainDescent.ClebschConcrete # ← CascadeAffine (concrete ℤ₄² Clebsch scheme + first non-affine δ′ closure, by decide)
  ChainDescent.FormsGraphConcrete # ← CascadeAffine, GaussCount (node-4 forms-graph discharge: IsotropySeparatesAtBase for VO^ε)
  # ── Forms-graph WL-dim pair route — the q=p affine-polar seal.
  # (ported 2026-06-27; restructured from 27 Scratch* files into 14 named modules 2026-06-28.)
  # The `reachesRigidOrCameron_affinePolar` chain: per-anchor c₀≤¾ + bad-anchor β →
  # log-bounded matching base → q=p seal, T.card = O(d log p). All axiom-clean.
  # Reusable assets flagged REUSABLE. Per-decl detail: PublicTheoremIndex.md.
  ChainDescent.Matching             # ← Mathlib (abstract first-moment: |ι|·Fᵐ<|W|ᵐ ⟹ separating base; REUSABLE)
  ChainDescent.PairForm             # ← CascadeAffine, GaussCount (per-pair χ-separation foundation: pairForm, Gauss bridge, M(y,z), normT_le; was PairSep)
  ChainDescent.PencilTBound         # ← PairForm (the |K|·‖T‖ magnitude bound: pencil radical + Schwartz–Zippel + two-bucket; REUSABLE; was Corank+GoodAnchor+Bucket+ChiNorm+TBound)
  ChainDescent.PerAnchorBound       # ← PencilTBound (incr-3 capstone c0_le_threequarters: NS≤¾·|V|; was Count+C0+C0Final)
  ChainDescent.BadAnchorCount       # ← PerAnchorBound, Matching (good-anchor fail c≤15/16·|V| + structural β reduction; was Incr4+Incr4b)
  ChainDescent.Coordinatization     # ← BadAnchorCount (form data → MvPolynomial: pencilDetPoly; REUSABLE; was Incr4c)
  ChainDescent.GoodAnchorNonvacuity # ← Coordinatization (NV exists_hgood: good-anchor non-vacuity, exposes hab/hQu; was Incr4d)
  ChainDescent.FieldGeneric         # ← CascadeAffine, GaussCount (abstract-K predicates ZProfileSeparatesK &c. + soft endpoint + q=p affineE adapter; was FieldGen+BridgeK+FieldGenAdapter)
  ChainDescent.IsotropicIncidenceCountK # ← FieldGeneric, GaussCount (Lemma A over abstract K; was LemmaAK)
  ChainDescent.IsotropicIncidenceCount # ← CascadeAffine, GaussCount (Lemma A over ZMod p: isotropic-incidence count = explicit Gram-function; card_quadForm_eq, configGaussSum_eq_det; was LemmaA)
  ChainDescent.ProfileReduction     # ← FormsGraphConcrete, CascadeAffine (ZProfileSeparates reduction D1 + B-M1 incidence; was Crux+LemmaB)
  ChainDescent.ObservableCountBridge # ← IsotropicIncidenceCount, ProfileReduction, PairForm (the χ(det G₂)↔Z_u(S) bridge over ZMod p; capstone jointIsoCount_ne_of_chiSep_pair; was BridgeA/B/C/D)
  ChainDescent.ObservableCountBridgeK # ← ObservableCountBridge, IsotropicIncidenceCountK, PairForm (bridge over abstract K: jointIsoCountK_ne_of_chiSep_pair; was BridgeAllK)
  ChainDescent.AffinePolarSeal      # ← Matching, BadAnchorCount, GoodAnchorNonvacuity, ObservableCountBridgeK, FieldGeneric (matching assembly + q=p seal reachesRigidOrCameron_affinePolar; was Incr5)
  # ── Route C — the constructive form-recovery POLY route (ported 2026-07-05 from Scratch{RouteC,Seam,SeamTransport,SeamDispatch,RecoveredFormTransfer} + the NodeCountBridge transport helpers).
  # Recover the form Q from the abstract graph ⟹ Aut = known classical group ⟹ canonicalize; sidesteps the node-4 WL wall.
  # Four family seals (affine-polar/alternating/half-spin/Suzuki) + the atom-free seam (L1 htransport discharged). All axiom-clean.
  ChainDescent.RouteCTransport      # ← Cascade (cross-graph WL-transport toolkit: SchemeRealizes + …_transport_iso tower + separatesAtBoundedBase_transport)
  ChainDescent.Refine       # ← Descend, RouteCTransport (THE REFINER INSTANCE: the encode-free structural round — ranks sigKey lists under lexLeList, never forms an Encodable.encode value; discharges RefineEquivariant + RefineSplits ⟹ the exhaustive canonizer is UNCONDITIONALLY a canonical form that answers; added 2026-07-13)
  ChainDescent.Consume      # ← Descend, Refine (STAGE 3: the ORACLE resolver instance, the `Covering` route. Untrusted `Supply` + a DECIDABLE IsColAut check ⟹ `coveringAt_consume` holds for EVERY supply; keeps one orbit rep per branch cell. Capstone `consume_canonizer`: canonical form + never flags, with NO hypothesis on the oracle; added 2026-07-14)
  ChainDescent.Force        # ← Descend, Refine (STAGE 3: the RIGID/FORCE resolver route, the `NarrowEquivariant` route. `forceBy key` = keep the branches of least key; the ONLY ① obligation is `KeyEquivariant` (the key never breaks ties by vertex index) ⟹ the rigid solver drops in as a stronger key and owes nothing else. `forceBy_no_narrowing_on_orbit`: force provably CANNOT fire on a symmetric cell — complementary to consume. Concrete firing key `lookaheadKey`; added 2026-07-14)
  ChainDescent.MatchSupply  # ← Consume, Refine (THE CASCADE ORACLE, STRUCTURALLY: `matchSupply` = matchOracle's construct-and-check colour match (§C.4) rebuilt over (adj,χ). `matchCandidate_eq_of_isColAut`: the construction RECONSTRUCTS the automorphism EXACTLY, so `cellIsOrbit_matchSupply` fires at any `Discretizing` node — the cascade oracle's hdisc-only strength, no CellsAreOrbits. ★ Being STRUCTURAL it also fixes ①c (the demo supplies are non-equivariant and break the flag). ⚠ MEASURED: one-step is NOT ENOUGH — C₇ does not discretize after one individualization, so it FLAGS on cycles. The multi-step/cross-branch harvest is the gap. Added 2026-07-14)
  ChainDescent.Composite    # ← Consume, Force (STAGE 3c: THE MIXED RESOLVER — `forceThenConsume`, both moves at one cell. `descend` takes ONE resolver, so the interleaved engine (IR §11.11) was not instantiable from the two separate instances. Admitted by the generalized contract route `CoveringOfAt`+`NarrowFnEquivariant` (Descend §9): force narrows equivariantly to N, consume covers N. Sound because `Force.mem_keepMin_of_aut` makes the forced set a UNION OF ORBITS. Capstone `composite_canonizer`; FIRING on BOTH domains: `forceThenConsume_singleton_of_{cellIsOrbit,separating}`; added 2026-07-14)
  ChainDescent.Cost         # ← Composite (② — THE COST PROJECTION: `descentCost` is the `cost` projection of the SAME definition ①a/①b/①c ride on, so ② needs no bridge. The branching object's cost is governed by ONE quantity — the fan-out the resolvers leave — so `ResolvedAll` (every cell narrowed to ≤1) ⟹ single path ⟹ `descentCost_le_of_resolved` = O(n·(c₁+c₂)). Content is in what DISCHARGES it: the firing theorems ⟹ `poly_of_cells_resolved` — a graph whose every cell is supply-connected OR key-separated is canonized in POLY TIME. `ResolvedAll` is a lower bound on the handled set, NOT a wall; added 2026-07-14)
  ChainDescent.Stall        # ← Cost (★ THE MUTUAL-STALL FLAG. Deferral is not a cheap mode of a healthy run — it IS the failure: every node consumes or forces, and a node that can do NEITHER is the residue. So `guard R` FLAGS (returns the empty narrowing; `aggregate [] = none` ⟹ no `descend` signature change) instead of branching ⟹ `resolvedAll_guard` holds BY CONSTRUCTION ⟹ `descentCost_guard_le` is polynomial with NO hypothesis: poly-AND-flag, never poly-OR-exponential. ⚠ NEW OBLIGATION: the flag needs `StallEquivariant` (a non-equivariant supply breaks ①c — witnessed in PerformanceTest); soundness still needs nothing from the supply. Added 2026-07-14)
  ChainDescent.Residue      # ← Stall (③ — THE RESIDUE AS THE COMPLEMENT OF A POSITIVE CAPABILITY. `Handled key S adj` = every cell is supply-connected OR key-separated; proved FORWARDS: `answers_of_handled` (a handled graph never flags) + poly (already unconditional). `Residue := ¬Handled` is a DEFINITION, not an opaque atom ⟹ `residue_if_flag` = Publication ③ for the real object, and `residue_nonvacuous` is PROVABLE (it was undischargeable in principle while the atoms were `opaque`). Also `guarded_mixed_canonizer` = ① for the guarded composite via the general CoveringOfAt route, modulo KeyEquivariant + StallEquivariant; added 2026-07-14)
  ChainDescent.Regression   # ← Residue, MatchSupply (BUILD-GATING REGRESSION SUITE — cheap, ~12s of eval. Catches what theorems cannot: instance-wiring bugs (the theorems quantify over ARBITRARY key/Supply, so a broken concrete instance satisfies all of them and canonizes nothing), FIRING regressions (`NarrowProper` is satisfied by a resolver returning the whole cell), and the measured counterexample that a NON-equivariant supply breaks ①c. ⚠ `ChainDescent.PerformanceTest` is DELIBERATELY NOT IN THIS LIST — it is the heavy #eval/measurement file (n=12 Frucht graph); run it on demand with `lake build ChainDescent.PerformanceTest`. Added 2026-07-14)
  # ── Nullstellensatz discharge — the quadric Nullstellensatz `NondegQuadricDeterminesForm` proved outright
  # (ported 2026-07-06 from the Scratch{Nullstellensatz,…Structural,…Count,…Hlink} files). A nondegenerate
  # quadric of even finrank ≥ 4 over an odd finite field is determined up to scalar by its isotropic cone.
  # Structural route: hspan (`cone_punctured_span`) + hlink (`aniso_polar_diameter_two`) into
  # `nullstellensatz_of_structural`; the finite-geometry counting is Gauss-sum based (`section_iso_count`),
  # primitive ℂ-char built internally. Capstone `nondegQuadric_zmod_of_even` = `NondegQuadricDeterminesForm`
  # (even d); discharges the citation carried by `recoveredForm_colouring_equivariant`. All axiom-clean.
  ChainDescent.Nullstellensatz            # ← Mathlib (field-general assembly: nullstellensatz_of_structural / _of_connectivity)
  ChainDescent.NullstellensatzStructural  # ← Nullstellensatz (bedrock: isotropic existence/span, associated-form nondeg)
  ChainDescent.NullstellensatzCount       # ← PairForm, Coordinatization, Nullstellensatz(Structural) (Gauss counting: section_iso_count, cone_punctured_span)
  ChainDescent.NullstellensatzHlink       # ← NullstellensatzCount (hlink + the discharge theorems nondegQuadric_{determines_of,zmod}_of_even)
  ChainDescent.RouteCFormAdapters   # ← CascadeAffine, NullstellensatzHlink (the four Route-C form-family poly seals via the FormAdapter engine + multi-quadric bridges)
  ChainDescent.RouteCSeam           # ← CascadeAffine, RouteCTransport (SealDisj + generic dispatch + affine-polar atom-free capstone + finer→coarser group-pinning)
  ChainDescent.RouteCNode4          # ← AffinePolarSeal, RouteCSeam (L4: affine-polar node-4 discharge with the pair-route separation discharged + transported — NO hFormCert)
)

start=$(date +%s)
for m in "${MODULES[@]}"; do
  s=$(date +%s)
  if [[ $VERBOSE -eq 1 ]]; then
    lake build "$m"
  else
    lake build "$m" >/dev/null
  fi
  e=$(date +%s)
  swap=$(free -m | awk '/Swap:/{print $3}')
  printf '  ✔ %-28s %4ds  (swap %sMiB)\n' "$m" "$((e - s))" "$swap"
done
printf '✔ serial build complete in %ds\n' "$(( $(date +%s) - start ))"
