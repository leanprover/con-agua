#!/usr/bin/env bash
# scripts/check-no-warnings.sh LOG: fail if a `scripts/lake build` log holds a warning from this
# repository's code (ConAgua, ConAguaAsm, the vendored libraries). The only warnings allowed are
# Kraken's own (a Lake git dependency we do not edit). CI runs it on the build step's log.
#
# Why a log check and not `lake build --wfail` or `warningAsError` in the lakefile: --wfail also fails
# on Kraken's replayed warnings, and the lean option would turn every warning (an unused variable in
# a half-finished proof) into an error for every local build and change every module's cache key.
set -euo pipefail
log="${1:?usage: $0 BUILD-LOG}"
bad=$(grep -E '^(warning|error): ' "$log" | grep -vE '^warning: Kraken/' || true)
if [[ -n "$bad" ]]; then
  echo "check-no-warnings: the build log has warnings outside Kraken:" >&2
  echo "$bad" | sort | uniq -c | sort -rn | head -40 >&2
  echo "Fix them (python3 scripts/fix-lean-warnings.py LOG does the mechanical kinds)." >&2
  exit 1
fi
echo "check-no-warnings: ok ($(grep -cE '^warning: Kraken/' "$log" || true) Kraken warnings ignored)"
