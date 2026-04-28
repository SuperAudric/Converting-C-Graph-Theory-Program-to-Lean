#!/usr/bin/env bash
# Run long-running tests in the background with persistent logging.
#
# Usage:
#   ./scripts/run-long-tests.sh [FILTER]
#
# FILTER defaults to all LongRunning tests. Examples:
#   ./scripts/run-long-tests.sh "Category=LongRunning"
#   ./scripts/run-long-tests.sh "DisplayName~K7&Category=LongRunning"
#   ./scripts/run-long-tests.sh "DisplayName~Petersen&Category=LongRunning"
#   ./scripts/run-long-tests.sh "FullyQualifiedName~AllPermutations_UniqueCanonicalCount_MatchesExpected_Extended"

set -euo pipefail

# ── Config ───────────────────────────────────────────────────────────────────
FILTER="${1:-Category=LongRunning}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TEST_PROJECT="$ROOT/GraphCanonizationProject.Tests"
LOG_DIR="$TEST_PROJECT/TestResults"
TIMESTAMP=$(date +%Y%m%d-%H%M%S)
LOG_FILE="$LOG_DIR/long-tests-$TIMESTAMP.log"
TRX_FILE="$LOG_DIR/long-tests-$TIMESTAMP.trx"
PID_FILE="$LOG_DIR/long-tests-$TIMESTAMP.pid"

mkdir -p "$LOG_DIR"

# ── Build ────────────────────────────────────────────────────────────────────
echo "Building..."
dotnet build "$TEST_PROJECT" --no-restore -v quiet 2>&1 | tee "$LOG_FILE"

# ── Launch ───────────────────────────────────────────────────────────────────
{
    echo ""
    echo "=== Long test run ==="
    echo "    Started:  $TIMESTAMP"
    echo "    Filter:   $FILTER"
    echo "    Log:      $LOG_FILE"
    echo "    Results:  $TRX_FILE"
    echo ""
} | tee -a "$LOG_FILE"

nohup dotnet test "$TEST_PROJECT" \
    --no-build \
    --filter "$FILTER" \
    --logger "console;verbosity=detailed" \
    --logger "trx;LogFileName=$TRX_FILE" \
    >> "$LOG_FILE" 2>&1 &

echo $! > "$PID_FILE"
PID=$(cat "$PID_FILE")

# ── Report ───────────────────────────────────────────────────────────────────
echo "Tests running in background (PID $PID)"
echo ""
echo "  Watch live:  tail -f '$LOG_FILE'"
echo "  Check alive: kill -0 $PID 2>/dev/null && echo running || echo finished"
echo "  Stop:        kill $PID"
echo ""
echo "When done, load results in VSCode:"
echo "  Command Palette → 'Test: Load Test Results...' → $TRX_FILE"
