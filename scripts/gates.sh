#!/usr/bin/env bash
# scripts/gates.sh — the landing gates, path-selected (PLAN.md, "Landing").
#
#   scripts/gates.sh [--changed [BASE]]   the steps the change since BASE (default: the merge-base
#                                         of HEAD and master) can affect, per scripts/gate_select.py
#                                         (the default; uncommitted changes count)
#   scripts/gates.sh --only a,b,c         just these steps (the merge queue's re-gate)
#   scripts/gates.sh --all                every step
#   scripts/gates.sh --list [BASE]        print the selected steps and why, run nothing
#
# Steps, in order (stops at the first failure):
#   links       scripts/overview-links.sh            OVERVIEW.md/README.md line anchors
#   vendor      scripts/bump-con-ron.sh --check      vendor/ = upstream + patches
#   modules     scripts/modules_check.py             every module is built by a target
#   provenance  scripts/provenance.py check          every FunDecl's twin citation is exact
#   reasons     scripts/reasons.py --check           (when the script exists)
#   build       scripts/lake build ConAgua           (timeout 50 min)
#   core-fns, loop-fns, leaf-fns, preloop-ws         the generated call closures are current
#   e2e         make checker; scripts/diff-e2e.py --parallel 16   verdicts on every fixture
#
# The lanes run this in their worktree after merging master (`scripts/gates.sh`), the merge queue
# runs `--changed <master>` on its merge: the same selection. One OK/FAIL/SKIP line per step; the full output
# of each step goes to $GATES_LOGDIR (default _tmp/gates-<hash of the checkout>/<n>-<step>.log).
# A green run on a clean tree stamps _tmp/mq/green/<commit> (scripts/submit.sh looks for it).
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

mode=changed base=""
case "${1-}" in
  --only) mode=only; only=",${2-},"; shift 2 ;;
  --all) mode=all; shift ;;
  --list) mode=list; shift; base="${1-}" ;;
  --changed) shift; base="${1-}" ;;
  "") ;;
  *) echo "usage: $0 [--changed [BASE] | --only a,b,c | --all | --list [BASE]]" >&2; exit 2 ;;
esac

if [ "$mode" = changed ] || [ "$mode" = list ]; then
  why=""; [ "$mode" = list ] && why=--why
  sel=$(python3 scripts/gate_select.py ${base:+--base "$base"} $why) || exit 2
  if [ "$mode" = list ]; then echo "$sel"; exit 0; fi
  only=",$sel,"
fi
[ "$mode" = all ] && only=""

logdir="${GATES_LOGDIR:-$root/_tmp/gates-$(printf '%s' "$root" | sha256sum | cut -c1-12)}"
rm -rf "$logdir"; mkdir -p "$logdir"
if [ -n "$only" ]; then shown="steps ${only:1:-1}"; else shown="all steps"; fi
echo "gates: $shown; logs in $logdir"
n=0 ran=0 skipped=0

run() { # run <name> <cmd...>
  n=$((n + 1))
  local name=$1; shift
  if [ -n "$only" ] && [[ "$only" != *",$name,"* ]]; then
    skipped=$((skipped + 1)); printf 'SKIP %-12s\n' "$name"; return 0
  fi
  local log="$logdir/$n-$name.log" start rc
  start=$(date +%s)
  if "$@" > "$log" 2>&1; then
    ran=$((ran + 1))
    printf 'OK   %-12s (%ds)\n' "$name" "$(( $(date +%s) - start ))"
  else
    rc=$?
    printf 'FAIL %-12s (%ds, exit %d) -- %s\n' "$name" "$(( $(date +%s) - start ))" "$rc" "$log"
    echo "--- last 30 lines ---"; tail -30 "$log"
    exit 1
  fi
}

reasons() { if [ -f scripts/reasons.py ]; then python3 scripts/reasons.py --check; else echo "no scripts/reasons.py"; fi; }
e2e() { make -s checker && timeout 1800 python3 scripts/diff-e2e.py --parallel 16; }

run links      scripts/overview-links.sh
run vendor     scripts/bump-con-ron.sh --check
run modules    python3 scripts/modules_check.py
run provenance python3 scripts/provenance.py check
run reasons    reasons
run build      timeout 10800 scripts/lake build ConAgua
run core-fns   timeout 600 python3 scripts/core_fns.py --check
run loop-fns   timeout 600 python3 scripts/loop_fns.py --check
run leaf-fns   timeout 600 python3 scripts/leaf_fns.py --check
run preloop-ws timeout 900 python3 scripts/preloop_ws.py --check
run e2e        e2e

echo "gates: $ran OK, $skipped skipped"
if [ "$mode" != only ] && [ -z "$(git status --porcelain --untracked-files=no)" ]; then
  mkdir -p "$root/_tmp/mq/green"
  echo "${only:-all}" > "$root/_tmp/mq/green/$(git rev-parse HEAD)"
fi
exit 0
