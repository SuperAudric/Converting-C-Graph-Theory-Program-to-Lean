#!/usr/bin/env bash
# Serial build for the chain-descent Lean library.
#
# WHY SERIAL. `lake build` parallelises across all cores, but each Lean worker
# loads the full mathlib environment (~2.7 GiB RSS) and this box has ~7.7 GiB
# (most held by the VS Code Lean server). Two or three concurrent workers thrash
# swap: a clean parallel rebuild took ~12 min (almost all swap overhead) vs ~60 s
# building one module at a time. This Lake (Lean v4.30.0-rc2) exposes no `-j`, so
# we invoke `lake build` once per module in dependency order — at most one worker
# resident, build stays in RAM.
#
# USAGE
#   scripts/build.sh            # serial full build
#   scripts/build.sh --verbose  # show lake output per module
#
# MODULES is in topological order (a module appears after everything it imports),
# so `lake build` never has to build a dependency mid-list; if you reorder wrongly
# lake fails loudly. Each line is `Module   # terse what-it-is`, grouped into the
# category sections you'd scan to find where a piece lives — the tag is only an
# orientation pointer; the actual contents live in that module's own `.lean`
# doc-block and in PublicTheoremIndex.md (the authoritative "what is proved").
# A few themes are split across sections by import order (e.g. the rigid `gen`
# chain sits after the Kernel supplies because it imports KernelGauss) — noted inline.
set -euo pipefail

cd "$(dirname "$0")/../GraphCanonizationProofs"

# Kill stray batch-build workers from a previous/overlapping run so two builds
# never thrash swap over the same modules. Targets ONLY the batch `lake build`
# driver and its `lean … .lean -o …` compile workers — the VS Code Lean server
# (`lean --server` / `--worker`, no `.lean -o` flag) is left untouched.
pkill -f 'lake build' 2>/dev/null || true
pkill -f '\.lean -o' 2>/dev/null || true
sleep 1   # let killed workers release Lake's build lock before we start

VERBOSE=0
[[ "${1:-}" == "--verbose" || "${1:-}" == "-v" ]] && VERBOSE=1

MODULES=(
  # ── Core substrate — spine, cost model, ①a/② correctness object ──
  ChainDescent                        # base: POE, warmRefine, samePartition, §6.2 direction-invariance
  ChainDescent.Spine                  # §15 descent spine + canonicalization invariants
  ChainDescent.CostModel              # CostM monad, per-node cap, spine ② cost ≤ n⁴
  ChainDescent.CanonForm              # ①a soundness + ② capped canonForm? object
  ChainDescent.OrbitRecovery          # §16–18 orbit-recovery lemmas
  ChainDescent.ClosureCalculus        # §13/§14 propagation-closure investigation (leaf)

  # ── Shared math substrate — schemes, CFI, coherent configs, oracles ──
  ChainDescent.Saturation             # generic saturation engine (shared by Scheme + Cascade)
  ChainDescent.GaussCount             # Gauss-sum point-count toolkit (forms-graph discharge)
  ChainDescent.CFI                    # CFI gadgets, gauge flips, Z₂^β cycle space
  ChainDescent.Scheme                 # de-classed metric/DRG scheme family
  ChainDescent.Separability           # S-ring/CC separability layer (Ponomarenko–Vasil'ev)
  ChainDescent.CoherentConfig         # general multi-fiber CC substrate (Thm 4.1 layer)
  ChainDescent.CascadeOracle          # unified matchOracle / matchOracleSeq
  ChainDescent.LinearOracle           # linear (abelian/CFI) oracle
  ChainDescent.Group                  # permutation-group scaffolding
  ChainDescent.Cascade                # Leg-A recovery + Part-A stabilizer chain + seal capstones

  # ── Algorithm A (confinement) + Phase-2 handoff ──
  ChainDescent.Confinement            # confinement lemma / Algorithm-A core (P1–P4 + Witt)
  ChainDescent.Phase2Handoff          # Phase-2 solver contract (Solver/Sound/IsoInvariant); RRU retired

  # ── The descent object (mixed composition) ──
  ChainDescent.CanonicalForm          # canonical-form spec: sound ∧ iso-inv ⟹ complete
  ChainDescent.Descend                # THE OBJECT: branching resolver-parameterized descent in CostM
  ChainDescent.Select                 # node-resolver interface (descendS); [] = mutual-stall flag

  # ── Affine-polar / forms-graph WL-dim seal (Route C, pair route) ──
  ChainDescent.CascadeAffine          # §13b/§13c separation engine + affine beachhead + seal wiring
  ChainDescent.ClebschConcrete        # concrete ℤ₄² Clebsch scheme + first non-affine δ′ closure
  ChainDescent.FormsGraphConcrete     # node-4 forms-graph discharge (VO^ε)
  ChainDescent.Matching               # abstract first-moment separating-base (REUSABLE)
  ChainDescent.PairForm               # per-pair χ-separation foundation (pairForm, Gauss bridge)
  ChainDescent.PencilTBound           # |K|·‖T‖ magnitude bound (REUSABLE)
  ChainDescent.PerAnchorBound         # per-anchor c₀ ≤ ¾·|V| bound
  ChainDescent.BadAnchorCount         # good-anchor fail bound + structural β reduction
  ChainDescent.Coordinatization       # form data → MvPolynomial pencilDetPoly (REUSABLE)
  ChainDescent.GoodAnchorNonvacuity   # good-anchor non-vacuity
  ChainDescent.FieldGeneric           # abstract-K separation predicates + q=p adapter
  ChainDescent.IsotropicIncidenceCountK  # Lemma A over abstract K
  ChainDescent.IsotropicIncidenceCount   # Lemma A over ZMod p (Gram-function count)
  ChainDescent.ProfileReduction       # ZProfileSeparates reduction + incidence
  ChainDescent.ObservableCountBridge  # χ(det G₂) ↔ Z_u(S) bridge over ZMod p
  ChainDescent.ObservableCountBridgeK # the bridge over abstract K
  ChainDescent.AffinePolarSeal        # matching assembly + q=p seal reachesRigidOrCameron_affinePolar

  # ── Route C form-recovery transport ──
  ChainDescent.RouteCTransport        # cross-graph WL-transport toolkit (SchemeRealizes)
  ChainDescent.ImprimitiveDischarge   # hImprim discharge (primitivity transport)

  # ── The resolvers (refiner, consume, force, composite, cost, flag, residue) ──
  ChainDescent.Refine                 # THE REFINER: encode-free structural round (RefineEquivariant/Splits)
  ChainDescent.Consume                # oracle resolver (Covering route): untrusted Supply + IsColAut check
  ChainDescent.Force                  # force resolver (NarrowEquivariant): forceBy key, KeyEquivariant
  ChainDescent.MatchSupply            # cascade oracle as a supply (fires at a Discretizing node)
  ChainDescent.Composite              # mixed resolver forceThenConsume; fires on both domains
  ChainDescent.Cost                   # ② cost projection: ResolvedAll ⟹ single path ⟹ poly
  ChainDescent.Stall                  # the mutual-stall flag (guard flags; poly-AND-flag, never OR-exp)
  ChainDescent.Residue                # Residue := ¬Handled (a definition, not an atom); ③ for the real object

  # ── Seal↔canonizer bridges + oracle-strength supplies ──
  ChainDescent.SealBridge             # P0: seal↔canonizer vocabulary bridge (CellsAreOrbits → horb)
  ChainDescent.SupplyTransport        # P1: flag iso-invariance via GensEquivariant; first mixed canonizer
  ChainDescent.DeepMatchSupply        # P2: bounded-depth oracle (≤d seqs; cost n^{O(d)})
  ChainDescent.OrbitPrune             # P3: SameOrbits pruning license (zero ① obligation on pruned supply)
  ChainDescent.SealDepthBridge        # P2b: depth bridge (CascadesFrom ⟹ SeparatesAt)
  ChainDescent.PrunedSupply           # P3c: single-reference match (|table|, not |table|²)
  ChainDescent.TreePrune              # P3c: tree-pruned enumeration (kills the n^d sequence blow-up)
  ChainDescent.PartialMatch           # F1: support-local bounded-depth oracle (F_k tower)
  ChainDescent.HandledBridge          # Handled population: handled_of_seal (first Residue.Handled instances)
  ChainDescent.SupplyCost             # ② cashed out: poly supplyCost per built supply
  ChainDescent.SelectNode             # fused instance selNode; selNode_stall_iff = the true mutual stall

  # ── Rigid seal (Algorithm R) — seam + reduction layers ──
  ChainDescent.RigidSeal              # R0a: leafColKey separates non-aut pairs (discretizing) + compKey seam
  ChainDescent.ForcingCircuits        # P1: F₂ extraction-soundness (forced_certificate)
  ChainDescent.RigidSolverInterface   # P3-I: pointed-solver contract → compKey obligations
  ChainDescent.RigidSolverSound       # P3-Sound: soundness free; ① = one canonical labelling gen
  ChainDescent.ForcingModel           # P2: graph↔F₂ forcing-model bridge (Layer B, carried)
  ChainDescent.RigidSolveF2           # P3-F₂ core: F₂ rigid-solve determinacy (unique_solution_of_rigid)

  # ── Consume supply constructors — fold / deck / kernel ──
  ChainDescent.FoldSupply             # F2a: structural fold supply (fibers/copies off cell structure)
  ChainDescent.DeckSupply             # F2b: constraint-propagation supply (deck of any order)
  ChainDescent.HolKey                 # F3a: holonomy force key + KeySeparates firing
  ChainDescent.FoldFast               # F2a evaluation twin (foldSupplyFast, materialised tables)
  ChainDescent.Deck2                  # F2c: second-seed propagation (commuting-gauge composites)
  ChainDescent.KernelSupply           # C3a: F₂ kernel supply (CFI cycle-space; all-or-nothing gate)
  ChainDescent.KernelGauss            # C3a: F₂ correctness span(kernelBasis) = L
  ChainDescent.KernelFlip             # C3a: rail structure + flip-composition product (flipFunK_xor)
  ChainDescent.KernelRef              # C3a: set-level reference + sameOrbits_kernelRef
  ChainDescent.KernelTransport        # C3a: σ-equivariance of the reference + record capstones

  # ── Rigid seal — the `gen` labelling chain (A)–(D) (here by import: needs KernelGauss + RigidSeal) ──
  ChainDescent.RigidRREF              # gen (A,B): canonical F₂ RREF = a function of the subspace
  ChainDescent.RigidFrame             # gen (C): χ-rank frame ⟹ σ-invariant (framedRREF_transport)
  ChainDescent.RigidGen               # gen (D): rankPerm labelling; rigid linear ① on RefEquivariant
  ChainDescent.RigidRefine            # concrete ref (Route B′): coordinate-free forcing; rowspace_transport

  # ── Deepen supply (base symmetry) ──
  ChainDescent.DeepenSupply           # C3b: anchor-deepening supply (all-anchors; base symmetry)
  ChainDescent.DeepenTransport        # C3b: pipeline transports except the vertex pick (chooseIdK_transport)
  ChainDescent.DeepenCrux             # C3b: crux decomposed + soundness half (deepenGens_sound)
  ChainDescent.DeepenTinhofer         # C3b track A: ①c modulo {Tinhofer}; rigid handoff lemmas
  ChainDescent.DeepenCertified        # C3b: Tinhofer as a RUN-TIME CERTIFICATE (Certified ⟹ Tinhofer)
  ChainDescent.DeepenComplete         # R1 scoping: GoodAnchor / OrbitComplete ⟹ transport ⟹ ①c (raw supply)
  ChainDescent.DeepenLocated          # C3b: consume failure LOCATED at a reachable Tinhofer+obstructed node
  ChainDescent.DeepenKey              # C3b: orbKey — the equivariant force key (KeyEquivariant, no hypothesis)
  ChainDescent.CaoFibring             # CAO-propagation Step 1: orbitals ↔ stabilizer orbits; the Step-2 bridge
  ChainDescent.CaoRound               # CAO-propagation: Step 2 at the REAL closure + the round-1 barrier (§12.3)
  ChainDescent.DeepenExact            # C3b: orbKey exact ⟹ consume failure MAKES FORCE FIRE
  ChainDescent.DeepenGuard            # C3b: POLY relabelling-invariant guard (orbKeyG, equivariant supply)
  ChainDescent.DeepenGuardComplete    # ★ Tinhofer ↔ CertifiedG deepenSupply: guard COMPLETE ⟹ transports, no SupplyEquivariant; ① at a COMPUTABLE object
  ChainDescent.DeepenPair             # Q2 foundation: pairStep = step∘step, whole step interface INHERITED (finer cells, no blast radius)
  ChainDescent.KeyComplete            # KeySeparates: consume's guard absorbed into force's separation obligation
  ChainDescent.ForcePick              # forceThenPick: the exhaustiveness corollary cashed (no stall channel)
  ChainDescent.RecordCost             # ② for the OBJECT OF RECORD: the four supplies + holKeyFast, billed
  ChainDescent.TwinFamily             # W1: Tinhofer/twin families Handled at EXECUTABLE objects (①/②/③) — after RecordCost for the cost lemmas
  ChainDescent.RecordDeepen           # ★ ③ WIRED INTO THE RECORD SUPPLY: recordSupplyFast ++ deepenSupplyCert is Handled on every Tinhofer graph
  ChainDescent.RestrictedTransport    # W1: ① relativized to a graph class ⟹ TINHOFER GRAPHS ARE CANONIZED (no supply)
  ChainDescent.DeepenTransportOn      # ① ON A CLASS at the DEEPEN object: OrbitComplete ⟹ NarrowTransportOn; option (v) packaged
  ChainDescent.RecordKey              # lex-product key combinator + the record's composed force key (①+②)

  # ── W2 solvability route (gauge complex → solvable) ──
  ChainDescent.GaugeComplex           # W2 Tier-A: split-vs-count localization spine
  ChainDescent.GaugeBridge            # W2 Tier-B: GaugeContract + holonomy_iff_gauge
  ChainDescent.GaugeAbelian           # W2: abelian branch (kerF2; abelian ⟹ solvable)
  ChainDescent.GaugeSolvable          # W2: solvable branch (of_solvable_tower; hstep = carried Luks)
  ChainDescent.GaugeIsolation         # W2: C3 Recover R-a (gauge isolation in the rigid regime)
  ChainDescent.GaugeNonabelian        # W2: C3 Recover R-c (non-abelian gauge ⟹ reduces to abelian)
  ChainDescent.GaugeLayer             # W2: extraction bricks L1–L3 (per-layer modules; L4 carried)

  # ── Regression gate ──
  ChainDescent.Regression             # build-gating regression suite (~1 min; PerformanceTest is off-build, run on demand)

  # ── Nullstellensatz + Route C form-family seals ──
  ChainDescent.Nullstellensatz            # quadric Nullstellensatz assembly (field-general)
  ChainDescent.NullstellensatzStructural  # isotropic existence/span, associated-form nondeg
  ChainDescent.NullstellensatzCount       # Gauss counting (section_iso_count, cone_punctured_span)
  ChainDescent.NullstellensatzHlink       # hlink + NondegQuadricDeterminesForm discharge
  ChainDescent.RouteCFormAdapters         # four Route-C form-family poly seals (FormAdapter engine)
  ChainDescent.RouteCSeam                 # Route-C dispatch + affine-polar atom-free capstone
  ChainDescent.RouteCNode4                # affine-polar node-4 discharge (no hFormCert)
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
