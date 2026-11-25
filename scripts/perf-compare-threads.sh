#!/usr/bin/env bash
# The threaded compared run's performance: a challenge against its solution (by default Init
# against itself, two paths of the same export) at 1 and 16 threads, the checker against con-ron
# (`--compare --jobs=N`), interleaved (checker, con-ron, checker, con-ron, ...) REPS times; each
# line: instructions:u, wall, peak RSS, verdict.
#
#   scripts/perf-compare-threads.sh CHECKER [REPS] [JOBS...]
#     CHECKER  the checker binary
#     REPS     repetitions per configuration (default 3)
#     JOBS     thread counts (default: 1 16); 1 runs the checker's sequential `--compare`
#
# Environment: CON_RON (con-ron's binary), CMP_C, CMP_S (the two files), PERF1 (the one-run
# measurer: `PERF1 LABEL CMD...` prints one line). Run on an idle machine: the 16-thread rows need
# 16 idle cores.
set -u
T=$(cd "$(dirname "$0")/.." && git rev-parse --path-format=absolute --git-common-dir)/../_tmp
BIN=${1:?usage: perf-compare-threads.sh CHECKER [REPS] [JOBS...]}
REPS=${2:-3}
shift; [ $# -gt 0 ] && shift
JOBS=("$@"); [ ${#JOBS[@]} -gt 0 ] || JOBS=(1 16)
CR=${CON_RON:-$T/ref/con-ron-integrate/target/release/con-ron}
PERF1=${PERF1:-$T/compare/perf1.sh}
C=${CMP_C:-$T/compare/initC.ndjson}
S=${CMP_S:-$T/compare/initS.ndjson}
for f in "$BIN" "$CR" "$PERF1" "$C" "$S"; do
  [ -e "$f" ] || { echo "perf-compare-threads.sh: missing $f" >&2; exit 2; }
done
echo "# checker $BIN ($(sha1sum < "$BIN" | cut -c1-12)), con-ron $CR ($(sha1sum < "$CR" | cut -c1-12)), $(date -Is)"
for j in "${JOBS[@]}"; do
  for r in $(seq "$REPS"); do
    if [ "$j" = 1 ]; then ours=("$BIN" --compare -- "$C" "$S"); else ours=("$BIN" "--jobs=$j" --compare -- "$C" "$S"); fi
    bash "$PERF1" "checker j=$j r=$r" "${ours[@]}"
    bash "$PERF1" "con-ron j=$j r=$r" "$CR" "--jobs=$j" --compare -- "$C" "$S"
  done
done
