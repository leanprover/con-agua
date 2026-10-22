#!/usr/bin/env bash
# Create a fresh agent worktree under _tmp/wt/ wired up to share state with
# the main tree: the Lake artifact cache (so `scripts/lake build` restores
# instead of rebuilding) and the Kraken package checkout (so it needs no
# re-clone/rebuild). See DESIGN.md, "The shared Lake artifact cache".
#
# Usage: scripts/new-worktree.sh <path-under-_tmp/wt> [<branch-or-rev>]
# Example: scripts/new-worktree.sh _tmp/wt/mylane master
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: $0 <path-under-_tmp/wt> [<branch-or-rev>]" >&2
  exit 1
fi

wt_path="$1"
rev="${2:-master}"
root="$(git rev-parse --show-toplevel)"

case "$wt_path" in
  _tmp/wt/*) ;;
  *) echo "refusing to create a worktree outside _tmp/wt/: $wt_path" >&2; exit 1 ;;
esac

git -C "$root" worktree add "$wt_path" "$rev"

abs_wt="$root/$wt_path"

# Share _tmp/ (and with it _tmp/lake-cache-v2) with the main tree, so
# scripts/lake's `git rev-parse --show-toplevel`/_tmp/lake-cache-v2 resolves to
# the one shared cache from inside the worktree too.
if [[ ! -e "$abs_wt/_tmp" ]]; then
  ln -s "$root/_tmp" "$abs_wt/_tmp"
fi

# Share the Kraken package checkout (source + its own small build dir): it's
# pinned by rev in lakefile.toml, identical across worktrees, and a fresh
# worktree would otherwise re-clone it from GitHub. Never run `lake update`
# against a worktree's symlinked copy -- do that in the main tree.
mkdir -p "$abs_wt/.lake"
if [[ ! -e "$abs_wt/.lake/packages" ]]; then
  ln -s "$root/.lake/packages" "$abs_wt/.lake/packages"
fi

echo "Worktree ready at $abs_wt (rev $rev)."
echo "Build with: (cd $abs_wt && scripts/lake build)"
