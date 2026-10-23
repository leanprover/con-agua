#!/usr/bin/env bash
# scripts/land.sh <branch> [build targets...]
# Land a lane branch on master, one lane at a time (PLAN.md, "Landing").
# Takes an exclusive lock (_tmp/land.lock), so landings are sequential and the main checkout is never
# mid-merge for two lanes at once. Waits for the lock rather than failing.
#   1. In the main checkout (must be clean, on master): git merge --no-ff <branch>.
#   2. Builds the given targets (default: ConAgua) with scripts/lake (which also seeds the shared cache).
#   3. On a merge conflict or build failure: aborts/resets the merge, releases the lock, exits non-zero,
#      so the lane fixes it in its own worktree (merge master there first) and runs land.sh again.
set -euo pipefail
branch="$1"; shift || true
# always build the whole library (ConAgua) plus whatever extra targets the lane names
targets=(ConAgua "$@")
root="$(git -C "$(dirname "$0")/.." rev-parse --show-toplevel)"
# the main checkout is the first worktree
main="$(git -C "$root" worktree list --porcelain | awk 'NR==1{print $2}')"
lock="$main/_tmp/land.lock"
exec 9>"$lock"
echo "land.sh: waiting for the landing lock ($lock)..." >&2
flock 9
echo "land.sh: got the lock; landing $branch" >&2
cd "$main"
[ "$(git rev-parse --abbrev-ref HEAD)" = master ] || { echo "main checkout not on master" >&2; exit 2; }
if [ -n "$(git status --porcelain --untracked-files=no)" ]; then echo "main checkout not clean" >&2; git status --short >&2; exit 2; fi
before="$(git rev-parse HEAD)"
# The branch must already contain master: the lane merges master and builds in its own worktree
# (in parallel, outside the lock); then the build below is a cache hit and the lock is held briefly.
if ! git merge-base --is-ancestor HEAD "$branch"; then
  echo "land.sh: $branch does not contain current master ($(git rev-parse --short HEAD)); merge master into it, build in your worktree, then retry" >&2
  exit 4
fi
if ! git merge --no-ff --no-edit "$branch"; then
  git merge --abort || true
  echo "land.sh: merge conflict; merge master into $branch in your worktree, then retry" >&2; exit 1
fi
if ! timeout 3000 scripts/lake build "${targets[@]}" || ! python3 scripts/core_fns.py --check || ! timeout 600 python3 scripts/loop_fns.py --check || ! timeout 600 python3 scripts/leaf_fns.py --check; then
  git reset --hard "$before"
  echo "land.sh: build or generated-file check (core_fns.py / loop_fns.py / leaf_fns.py --check) failed after merging; master reset to $before; fix in your worktree and retry" >&2; exit 1
fi
echo "land.sh: landed $branch as $(git rev-parse --short HEAD)" >&2
