#!/usr/bin/env bash
# scripts/bump-con-ron.sh: re-vendor con-ron (and the con-leche it pins), mechanically.
# PLAN.md, "Bumping the twin"; vendor/README.md.
#
#   scripts/bump-con-ron.sh <rev>              bump to con-ron <rev> (a commit, tag or origin/HEAD)
#   scripts/bump-con-ron.sh --refresh-patches  rewrite vendor/patches/ from vendor/ (after editing a
#                                              vendored file: every edit must be in a patch)
#   scripts/bump-con-ron.sh --check            vendor/ == upstream at vendor/UPSTREAM + the patches?
#
# The vendored state is: vendor/UPSTREAM (the two revisions), the pristine upstream files at those
# revisions (con-ron: proof/ConRon/**, proof/ConRon.lean; con-leche: ConLeche/**, ConLeche.lean,
# pins/**, scripts/natop_prefix.json), and the patch series vendor/patches/<repo>/NNNN-*.patch
# applied on top in order. Pristine trees come from the reference clones _tmp/ref/<repo> (cloned
# and fetched as needed).
#
# A bump (run it in a worktree, on a branch, with vendor/ committed and clean):
#   1. checks that vendor/ is exactly old pristine + patches (else: --refresh-patches first);
#   2. resolves <rev>, reads the con-leche rev from con-ron's proof/lake-manifest.json there;
#   3. replaces each vendored tree by the new pristine one and re-applies the patch series with
#      `git apply --3way` (the patches carry full blob ids of the old pristine files, so a hunk
#      that does not apply becomes a three-way merge); conflicts are reported and left in the
#      working tree with markers;
#   4. writes vendor/UPSTREAM, regenerates scripts/census-rust.tsv from the new Rust;
#   5. runs `scripts/provenance.py update --old <old con-ron rev>` (no build needed): relocates
#      the `con-ron:`/`con-leche:` citations of our L code, puts a CHANGED marker on every item
#      whose cited twin code (or a helper right below it) changed, prints the diffs; the
#      findings also go to _tmp/bump-<short>/provenance.json. This is the work queue;
#   6. builds (`scripts/lake build`), log in _tmp/bump-<short>/build.log, and prints the files
#      with errors;
#   7. runs the census (counts only).
# Nothing is committed. Afterwards: fix the build (an edit to a vendored file goes into a patch:
# --refresh-patches), commit, and announce the bump (DESIGN.md): what changed upstream (the
# changed-files list above).
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
cd "$root"
REPOS=(con-leche con-ron)

url_of() { awk -v r="$1" '$1 == r { print $3 }' vendor/UPSTREAM; }
rev_of() { awk -v r="$1" '$1 == r { print $2 }' vendor/UPSTREAM; }
# The reference clones live in the main checkout's _tmp/ref, shared by all worktrees (a lane's
# worktree has no _tmp/ref of its own; resolving it there made --check clone afresh or silently
# compare against an empty pristine tree).
main_root="$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")"
ref_dir() { echo "$main_root/_tmp/ref/$1"; }

ensure_ref() { # repo [rev]
  local d; d="$(ref_dir "$1")"
  if [[ ! -d "$d/.git" ]]; then
    mkdir -p "$(dirname "$d")"
    git clone -q "$(url_of "$1")" "$d"
  fi
  if [[ -n "${2:-}" ]] && ! git -C "$d" cat-file -e "$2^{commit}" 2>/dev/null; then
    git -C "$d" fetch -q origin
    git -C "$d" cat-file -e "$2^{commit}" || { echo "bump-con-ron: $2 not in $d, even after fetch" >&2; exit 1; }
  fi
}

# Extract the vendored file set of <repo> at <rev> into <dir>/vendor/<repo>.
pristine() { # repo rev dir
  local d="$3/vendor/$1"
  mkdir -p "$d"
  case "$1" in
    con-ron)
      git -C "$(ref_dir con-ron)" archive "$2" proof/ConRon proof/ConRon.lean \
        | tar -x --strip-components=1 -C "$d" ;;
    con-leche)
      git -C "$(ref_dir con-leche)" archive "$2" ConLeche ConLeche.lean pins scripts/natop_prefix.json \
        | tar -x -C "$d" ;;
  esac
}

# The files of the vendored set as they sit in vendor/<repo> (relative to $root).
vendored_paths() { # repo
  case "$1" in
    con-ron) echo vendor/con-ron/ConRon vendor/con-ron/ConRon.lean ;;
    con-leche) echo vendor/con-leche/ConLeche vendor/con-leche/ConLeche.lean vendor/con-leche/pins \
                    vendor/con-leche/scripts/natop_prefix.json ;;
  esac
}

# A tree object of <worktree-dir>'s vendor/<repo> (writes the blobs into our object store, so
# `git apply --3way` finds the preimages later).
tree_of() { # repo worktree-dir
  local idx; idx="$(mktemp -p "$root/_tmp" idx.XXXXXX)"
  rm -f "$idx"
  # shellcheck disable=SC2046
  (cd "$2" && GIT_INDEX_FILE="$idx" git --git-dir="$(git -C "$root" rev-parse --absolute-git-dir)" \
     --work-tree=. add -f -A -- $(vendored_paths "$1"))
  GIT_INDEX_FILE="$idx" git write-tree
  rm -f "$idx"
}

scratch() { local d; mkdir -p "$root/_tmp"; d="$(mktemp -d -p "$root/_tmp" bump.XXXXXX)"; echo "$d"; }

# Write the patch series of <repo> into <outdir>: the diff old-pristine -> vendor, one patch per
# existing patch file (over the files that file touched, keeping its description: the text before
# its first `diff --git`), and the rest into NNNN-new.patch.
make_patches() { # repo outdir
  local repo="$1" out="$2" tmp t0 t1
  tmp="$(scratch)"
  ensure_ref "$repo" "$(rev_of "$repo")"
  pristine "$repo" "$(rev_of "$repo")" "$tmp"
  t0="$(tree_of "$repo" "$tmp")"
  t1="$(tree_of "$repo" "$root")"
  rm -rf "$tmp"
  mkdir -p "$out"
  local claimed="" p files n=0
  for p in "vendor/patches/$repo"/*.patch; do
    [[ -e "$p" ]] || continue
    n=$((n + 1))
    files="$(sed -n 's|^diff --git a/\([^ ]*\) b/.*|\1|p' "$p" | tr '\n' ' ')"
    claimed="$claimed $files"
    # keep the description (everything before the first diff), regenerate the diff
    sed '/^diff --git/,$d' "$p" > "$out/$(basename "$p")"
    # shellcheck disable=SC2086
    git diff --full-index --binary "$t0" "$t1" -- $files > "$out/diff"
    if [[ -s "$out/diff" ]]; then cat "$out/diff" >> "$out/$(basename "$p")"
    else rm -f "$out/$(basename "$p")"; echo "$repo: $(basename "$p") is now empty, dropped" >&2; fi
    rm -f "$out/diff"
  done
  local all rest=""
  all="$(git diff --name-only "$t0" "$t1")"
  for f in $all; do
    [[ " $claimed " == *" $f "* ]] || rest="$rest $f"
  done
  if [[ -n "$rest" ]]; then
    local name; name="$(printf '%04d-new.patch' $((n + 1)))"
    # shellcheck disable=SC2086
    git diff --full-index --binary "$t0" "$t1" -- $rest > "$out/$name"
    echo "$repo: edits outside every patch went into $out/$name (rename it, say why in vendor/README.md):$rest" >&2
  fi
}

check() {
  local ok=0 tmp repo
  tmp="$(scratch)"
  for repo in "${REPOS[@]}"; do
    make_patches "$repo" "$tmp/$repo" 2>"$tmp/$repo.err" || { cat "$tmp/$repo.err" >&2; rm -rf "$tmp"; return 2; }
    if ! diff -r -q "vendor/patches/$repo" "$tmp/$repo" >/dev/null 2>&1; then
      echo "vendor/$repo differs from upstream $(rev_of "$repo" | cut -c1-8) + vendor/patches/$repo:"
      diff -r -q "vendor/patches/$repo" "$tmp/$repo" || true
      ok=1
    fi
  done
  rm -rf "$tmp"
  [[ $ok == 0 ]] && echo "vendor/ = upstream at vendor/UPSTREAM + vendor/patches/: ok"
  return $ok
}

refresh() {
  local tmp repo
  tmp="$(scratch)"
  for repo in "${REPOS[@]}"; do
    make_patches "$repo" "$tmp/$repo"
    rm -f "vendor/patches/$repo"/*.patch
    mkdir -p "vendor/patches/$repo"
    cp "$tmp/$repo"/*.patch "vendor/patches/$repo"/ 2>/dev/null || true
  done
  rm -rf "$tmp"
  git status --short vendor/patches
}

bump() {
  local want="$1" new_cr new_cl old_cr old_cl short log
  if [[ -n "$(git status --porcelain -- vendor scripts/census-rust.tsv)" ]]; then
    echo "vendor/ has uncommitted changes; commit or stash them first" >&2; exit 1
  fi
  echo "== checking vendor/ against its patch series"
  check || { echo "run --refresh-patches and commit first" >&2; exit 1; }
  old_cr="$(rev_of con-ron)"; old_cl="$(rev_of con-leche)"
  ensure_ref con-ron "$want"
  git -C "$(ref_dir con-ron)" fetch -q origin || true
  new_cr="$(git -C "$(ref_dir con-ron)" rev-parse --verify "$want^{commit}")"
  new_cl="$(git -C "$(ref_dir con-ron)" show "$new_cr:proof/lake-manifest.json" \
            | python3 -c 'import json,sys; print(next(p["rev"] for p in json.load(sys.stdin)["packages"] if "con-leche" in p["name"]))')"
  ensure_ref con-leche "$new_cl"
  short="${new_cr:0:8}"
  local work="$root/_tmp/bump-$short"
  mkdir -p "$work"
  echo "== con-ron  ${old_cr:0:8} -> ${new_cr:0:8} ($(git -C "$(ref_dir con-ron)" rev-list --count "$old_cr..$new_cr") commits)"
  echo "== con-leche ${old_cl:0:8} -> ${new_cl:0:8}"
  for f in proof/lean-toolchain; do
    local tc; tc="$(git -C "$(ref_dir con-ron)" show "$new_cr:$f")"
    echo "   con-ron's toolchain at the new rev: $tc (ours: $(cat lean-toolchain); vendor/README.md has the toolchain patches)"
  done
  # make sure the old pristine blobs are in our object store (the patches' preimages)
  local tmp; tmp="$(scratch)"
  pristine con-ron "$old_cr" "$tmp"; tree_of con-ron "$tmp" >/dev/null
  pristine con-leche "$old_cl" "$tmp"; tree_of con-leche "$tmp" >/dev/null
  rm -rf "$tmp"
  local conflicts="" repo p rev
  for repo in "${REPOS[@]}"; do
    rev="$new_cr"; [[ $repo == con-leche ]] && rev="$new_cl"
    # shellcheck disable=SC2046
    rm -rf $(vendored_paths "$repo")
    pristine "$repo" "$rev" "$root"
    # shellcheck disable=SC2046
    git add -A -- $(vendored_paths "$repo")
    for p in "vendor/patches/$repo"/*.patch; do
      [[ -e "$p" ]] || continue
      if git apply --3way "$p" >"$work/apply.log" 2>&1; then
        echo "   applied $p"
      else
        echo "   CONFLICT $p:"; sed 's/^/     /' "$work/apply.log"
        conflicts="$conflicts $p"
      fi
    done
  done
  sed -i "s/^con-ron\t[0-9a-f]*/con-ron\t$new_cr/; s/^con-leche\t[0-9a-f]*/con-leche\t$new_cl/" vendor/UPSTREAM
  tmp="$(scratch)"
  git -C "$(ref_dir con-ron)" archive "$new_cr" crates | tar -x -C "$tmp"
  python3 scripts/census.py --rust "$tmp" | sed 's/^/   /'
  rm -rf "$tmp"
  echo "== the work queue (scripts/provenance.py update --old ${old_cr:0:8}; markers inserted)"
  python3 scripts/provenance.py update --old "$old_cr" --json "$work/provenance.json" \
    | sed 's/^/   /' || true
  echo "== changed upstream files:"
  git -C "$(ref_dir con-ron)" diff --stat "$old_cr" "$new_cr" -- proof/ConRon proof/ConRon.lean | sed 's/^/   con-ron /'
  git -C "$(ref_dir con-leche)" diff --stat "$old_cl" "$new_cl" -- ConLeche ConLeche.lean pins | sed 's/^/   con-leche /'
  if [[ -n "$conflicts" ]]; then
    echo "== conflicts in:$conflicts"
    git diff --name-only --diff-filter=U | sed 's/^/   /'
    echo "   resolve (git add), then --refresh-patches, build, scripts/census.py" >&2
    exit 1
  fi
  log="$work/build.log"
  echo "== building (log: $log)"
  local bok=0
  timeout 5400 scripts/lake build >"$log" 2>&1 || bok=1
  if [[ $bok == 1 ]]; then
    echo "   build FAILED; files with errors:"
    grep -o '^error: [^:]*\.lean' "$log" | sort | uniq -c | sed 's/^/   /' || true
    echo "   (the census needs a build; fix, then run scripts/census.py)"
    exit 1
  fi
  echo "   build ok"
  echo "== the census"
  timeout 1800 python3 scripts/census.py
}

case "${1:-}" in
  --check) check ;;
  --refresh-patches) refresh ;;
  ""|-h|--help) sed -n '2,33p' "$0" ;;
  *) bump "$1" ;;
esac
