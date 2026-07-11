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
  ChainDescent.CanonicalForm # ← Cascade (mixed-composition Stage 0: canonical-form spec sound∧iso-inv⟹complete + lexMin selection combinator; added 2026-07-11)
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
