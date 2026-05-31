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

VERBOSE=0
[[ "${1:-}" == "--verbose" || "${1:-}" == "-v" ]] && VERBOSE=1

# Topological order: base first, then modules in increasing dependency depth.
MODULES=(
  ChainDescent              # base (everything imports this)
  ChainDescent.CFI          # ← base
  ChainDescent.Scheme       # ← base
  ChainDescent.CascadeOracle # ← base, CFI, Scheme
  ChainDescent.LinearOracle # ← CascadeOracle
  ChainDescent.Group        # ← CascadeOracle
  ChainDescent.Cascade      # ← CascadeOracle, Group
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
