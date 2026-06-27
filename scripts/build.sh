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
  ChainDescent              # base (everything imports this)
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
  ChainDescent.CascadeAffine # ← Cascade, Scheme (§13b/§13c engine + Phase-2 affine beachhead)
  ChainDescent.ClebschConcrete # ← CascadeAffine (concrete ℤ₄² Clebsch scheme + first non-affine δ′ closure, by decide)
  ChainDescent.FormsGraphConcrete # ← CascadeAffine, GaussCount (node-4 forms-graph discharge: IsotropySeparatesAtBase for VO^ε)
  # ── Forms-graph WL-dim pair route (ported 2026-06-27) — the q=p affine-polar seal.
  # The `reachesRigidOrCameron_affinePolar` chain: per-anchor c₀≤¾ (incr 3) + bad-anchor β
  # (incr 4) → log-bounded matching base (incr 5) → q=p seal, T.card = O(d log p). All
  # axiom-clean. Reusable assets flagged REUSABLE. Map: plan §13; detail: PublicTheoremIndex.
  ChainDescent.ScratchMatching      # ← Mathlib (abstract first-moment: |ι|·Fᵐ<|W|ᵐ ⟹ separating base; REUSABLE)
  ChainDescent.ScratchPairSep       # ← CascadeAffine, GaussCount (per-pair χ-separation route, 24 lemmas)
  ChainDescent.ScratchCorank        # ← CascadeAffine (polarRad Submodule + proper-subspace bound |rad|·q≤|V|, corank-uniform)
  ChainDescent.ScratchGoodAnchor    # ← Corank (Schwartz–Zippel mvPoly_zeros_count_le + degenerate_count_le≤d·q; REUSABLE)
  ChainDescent.ScratchBucket        # ← Mathlib (abstract two-bucket sum bound ∑g≤Ca·Ma+Cb·Mb; REUSABLE)
  ChainDescent.ScratchChiNorm       # ← Mathlib (‖χ-into-ℂ‖ = [·≠0]; small reusable)
  ChainDescent.ScratchTBound        # ← Bucket, GoodAnchor, ChiNorm (the |K|·‖T‖ magnitude bound)
  ChainDescent.ScratchCount         # ← Mathlib (counting identity 2·NS ≤ 2·z_u+n+T_ℤ)
  ChainDescent.ScratchC0            # ← Count (ℤ↔ℂ connect: 2·NS ≤ 2·z_u+n+‖T_ℂ‖)
  ChainDescent.ScratchC0Final       # ← TBound, C0 (incr-3 capstone c0_le_threequarters: NS≤¾·|V|)
  ChainDescent.ScratchIncr4         # ← C0Final, Matching (good-anchor fail: good_anchor_fail_le_const ≤15/16·|V|)
  ChainDescent.ScratchIncr4b        # ← Incr4 (structural: hgood⟹hnz/hPu/hPv; good ⟺ hgood∧Q(t₀−u),Q(t₀−v)≠0)
  ChainDescent.ScratchIncr4c        # ← Incr4b (coordinatization → pencilDetPoly: form data as MvPolynomial; REUSABLE)
  ChainDescent.ScratchIncr4d        # ← Incr4c (NV exists_hgood: good-anchor non-vacuity, exposes hab/hQu)
  ChainDescent.ScratchFieldGen      # ← CascadeAffine (abstract-K V-indexed predicates: ZProfileSeparatesK &c.)
  ChainDescent.ScratchLemmaAK       # ← FieldGen, GaussCount (Lemma A over abstract K — isotropic-incidence closed form)
  ChainDescent.ScratchLemmaA        # ← CascadeAffine, GaussCount (Lemma A over ZMod p: card_quadForm_eq closed form)
  ChainDescent.ScratchBridgeA       # ← LemmaA (B1a |S|=2 even-d collapse: configGaussSum_eq_det + χ-kills-squares)
  ChainDescent.ScratchCrux          # ← FormsGraphConcrete (ZProfileSeparates reduction D1 — jointIsoCount)
  ChainDescent.ScratchLemmaB        # ← CascadeAffine (B-M1: fine isotropy profile ⟹ isotropic-incidence agreement)
  ChainDescent.ScratchBridgeB       # ← BridgeA, Crux, LemmaB (wrap i: jointIsoCount ↔ Lemma-A fullcount)
  ChainDescent.ScratchBridgeC       # ← BridgeB (wrap ii: |S|=2 config-indexing + level-set reduction)
  ChainDescent.ScratchBridgeD       # ← BridgeC, PairSep (wrap iii χ(D)=χ(I_w) + ℂ per-pair jointIsoCount_ne_of_chiSep_pair)
  ChainDescent.ScratchBridgeAllK    # ← BridgeD, LemmaAK (bridge over abstract K: jointIsoCountK_ne_of_chiSep_pair)
  ChainDescent.ScratchBridgeK       # ← FieldGen (soft endpoint: Z-separating base ⟹ ZProfileSeparatesK)
  ChainDescent.ScratchFieldGenAdapter # ← FieldGen (q=p adapter via affineE → …viaIsotropySeparatesK_wittFree)
  ChainDescent.ScratchIncr5         # ← Matching, Incr4d, BridgeAllK, BridgeK, FieldGenAdapter (matching assembly + q=p seal reachesRigidOrCameron_affinePolar)
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
