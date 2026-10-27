#!/usr/bin/env bash
# scripts/check-no-warnings.sh LOG: fail if a `scripts/lake build` log holds a warning from this
# repository's code (ConAgua, ConAguaAsm). The only warnings allowed are Kraken's own (a Lake git
# dependency we do not edit) and those of the vendored upstream files (`vendor/`: con-leche's
# Challenge.lean has two `sorry`s by design, con-ron has an unused simp argument; the vendor gate
# keeps them equal to upstream plus our patches). CI runs it on the build step's log.
#
# Why a log check and not `lake build --wfail` or `warningAsError` in the lakefile: --wfail also fails
# on Kraken's replayed warnings, and the lean option would turn every warning (an unused variable in
# a half-finished proof) into an error for every local build and change every module's cache key.
#
# The log must come from a build in which Lake compiled the modules itself (CI: the cache restored by
# actions/cache keeps Lake's own traces, whose logs are replayed; or a local `LAKE_COLD=1 scripts/lake
# build` in a worktree without `.lake/build`). A module restored from the shared artifact cache has a
# synthetic trace with an empty log, so its warnings are not printed and an ordinary local build log
# would pass this check wrongly (that is how batch 1 missed 700 warnings).
set -euo pipefail
log="${1:?usage: $0 BUILD-LOG}"
bad=$(grep -E '^(warning|error): ' "$log" | grep -vE '^warning: (Kraken|vendor)/' || true)
if [[ -n "$bad" ]]; then
  echo "check-no-warnings: the build log has warnings outside Kraken:" >&2
  echo "$bad" | sort | uniq -c | sort -rn | head -40 >&2
  echo "Fix them (python3 scripts/fix-lean-warnings.py LOG does the mechanical kinds)." >&2
  exit 1
fi
echo "check-no-warnings: ok (Kraken and vendor warnings ignored)"
