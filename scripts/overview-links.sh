#!/usr/bin/env bash
# scripts/overview-links.sh — the document link gate (ported from con-leche's
# tests/overview-links.sh).
#
# WHY.  OVERVIEW.md (and README.md, once the maintainer writes it) anchor
# their claims in the code: nearly every paragraph cites a *line range* of a
# source file through a link `$BASE/<path>#L<a>-L<b>`.  Line anchors are the
# most perishable kind of documentation: one inserted `import` slides every
# anchor below it, and nothing in the build notices.  Worse, a link can keep
# pointing at valid lines that no longer say what the prose claims.
#
# WHAT IT CHECKS.  The gate does not decide whether the prose is true; it
# makes the *cited text* a committed artefact.  It extracts every `$BASE`
# link from each document in document order, copies the linked lines (with
# their numbers) into one text under a `>>> <document>` banner per document,
# and diffs that against scripts/overview-links-expected.txt.  So
#
#   * moving the linked lines changes their numbers and fails the gate: update
#     the link's anchor;
#   * editing the linked lines changes the text and fails the gate: re-read the
#     paragraph that cites them, the document may be stale;
#   * a missing file, or an anchor past the end of the file, is an error naming
#     the link.
#
# After checking that the prose still matches, regenerate with
#
#     scripts/overview-links.sh --update
#
# and commit the expectation with the change that moved the lines.
#
# ERRORS RATHER THAN DIFFS.  A link into this repository at another ref than
# `master` (`blob/<sha>/…`) is rejected: the documents track master.  A
# relative link (`docs/deviations.md`, `ConAgua/L/`) has no cited text, but its
# target must exist.  Other links (external URLs, anchors within the document)
# are not this gate's business.
#
# README.md is the maintainer's: an agent may turn an existing code name into a
# link and repoint a link that rotted, and changes no other character of it.
#
# NO BUILD REQUIRED: it reads the documents and the cited files only.
# scripts/land.sh runs it after the build.

set -u
cd "$(dirname "$0")/.."

# The one place that names where the documents link to.  Every line-anchored
# link in the documents starts with this prefix.
BASE="https://github.com/leanprover/con-agua/blob/master"

# The documents, in the order their sections appear in the expectation.
# A document that does not exist (README.md before the maintainer writes it)
# gets an empty section.
DOCS="OVERVIEW.md README.md"
EXPECTED=scripts/overview-links-expected.txt

update=0
case "${1:-}" in
  --update) update=1 ;;
  "") ;;
  *) echo "usage: scripts/overview-links.sh [--update]" >&2; exit 2 ;;
esac

if [ ! -f OVERVIEW.md ]; then
  echo "overview-links: FAIL — OVERVIEW.md not found" >&2
  exit 1
fi

tmp=$(mktemp) || exit 3
trap 'rm -f "$tmp"' EXIT

# The extractor: reads the documents in order, walks their links in order,
# writes the cited text to $1, or reports EVERY structural error (a rename
# should show all its dead links at once) and exits 1.
if ! python3 - "$tmp" "$BASE" $DOCS <<'PY'
import re, sys, os

out, base, docs = sys.argv[1], sys.argv[2], sys.argv[3:]
# BASE is .../blob/<ref>; the repository part is what precedes /blob/.
repo, ref = base.rsplit('/blob/', 1)

LINK = re.compile(re.escape(base) + r'/([^)\s#>]+)#L(\d+)(?:-L(\d+))?')
# Any link into this repository, to catch other refs and unanchored blob links.
ANY = re.compile(re.escape(repo) + r'/(blob|tree)/([^/\s)]+)/([^)\s#>]*)(#[^)\s>]*)?')
DEST = re.compile(r'\]\(([^)\s]+)\)')

errors, blocks = [], []
for doc in docs:
    # A document that does not exist yet (README.md) has an empty section, so that
    # writing it without line-anchored links leaves the expectation unchanged.
    if not os.path.isfile(doc):
        blocks.append(f">>> {doc}\n")
        continue
    with open(doc, encoding='utf-8') as f:
        text = f.read()

    for m in ANY.finditer(text):
        kind, r, path, anchor = m.groups()
        if r != ref:
            errors.append(f"{doc}: {m.group(0)}\n    pins the ref `{r}`; link `{ref}` ({base}).")
        elif not os.path.exists(path.rstrip('/') or '.'):
            errors.append(f"{doc}: {m.group(0)}\n    `{path}` does not exist.")

    segments = []
    for m in LINK.finditer(text):
        path, a, b = m.group(1), int(m.group(2)), m.group(3)
        b = int(b) if b is not None else a
        anchor = f"#L{a}" if b == a else f"#L{a}-L{b}"
        if not os.path.isfile(path):
            errors.append(f"{doc}: {m.group(0)}\n    file `{path}` does not exist.")
            continue
        with open(path, encoding='utf-8') as f:
            lines = f.read().split('\n')
        if lines and lines[-1] == '':
            lines.pop()
        n = len(lines)
        if a < 1 or b < a or b > n:
            errors.append(f"{doc}: {m.group(0)}\n    range L{a}-L{b} is outside `{path}` ({n} lines).")
            continue
        body = ''.join(f"{i:6d}  {lines[i-1]}\n" for i in range(a, b + 1))
        segments.append(f"== {path}{anchor}\n{body}")

    for m in DEST.finditer(text):
        dest = m.group(1)
        if dest.startswith(('http://', 'https://', '#', 'mailto:')):
            continue
        target = dest.split('#', 1)[0]
        if target and not os.path.exists(target):
            errors.append(f"{doc}: [..]({dest})\n    target `{target}` does not exist.")

    blocks.append(f">>> {doc}\n\n" + "\n".join(segments))

if errors:
    sys.stderr.write("overview-links: FAIL — %d bad link(s):\n" % len(errors))
    for e in errors:
        sys.stderr.write("  " + e + "\n")
    sys.exit(1)

header = (
    "# GENERATED by scripts/overview-links.sh --update — do not edit by hand.\n"
    "#\n"
    "# Every line-anchored link of the gated documents, in document order,\n"
    "# with the lines it points at.  A diff here means a citation moved or\n"
    "# its text changed: re-read the paragraph that cites it, fix the link\n"
    "# or the prose, then regenerate.\n"
    "\n")
with open(out, 'w', encoding='utf-8') as f:
    f.write(header)
    f.write("\n".join(blocks))
    f.write("\n")
PY
then
  exit 1
fi

nlinks=$(grep -c '^== ' "$tmp")
nfiles=$(grep '^== ' "$tmp" | sed 's/#L.*//' | sort -u | wc -l)
ndocs=$(grep -c '^>>> ' "$tmp")

if [ "$update" = 1 ]; then
  if [ -f "$EXPECTED" ] && cmp -s "$tmp" "$EXPECTED"; then
    echo "overview-links: $nlinks links, $nfiles files, $ndocs documents, expectation already current"
  else
    cp "$tmp" "$EXPECTED"
    echo "overview-links: $nlinks links, $nfiles files, $ndocs documents, wrote $EXPECTED"
  fi
  exit 0
fi

if [ ! -f "$EXPECTED" ]; then
  echo "overview-links: FAIL — $EXPECTED missing; run scripts/overview-links.sh --update" >&2
  exit 1
fi

if diff -u "$EXPECTED" "$tmp"; then
  echo "overview-links: $nlinks links, $nfiles files, $ndocs documents, OK"
  exit 0
fi

# Name the documents whose section changed.
bad=""
for doc in $DOCS; do
  a=$(awk -v d="$doc" '/^>>> /{p=($2==d)} p' "$EXPECTED")
  b=$(awk -v d="$doc" '/^>>> /{p=($2==d)} p' "$tmp")
  if [ "$a" != "$b" ]; then bad="$bad $doc"; fi
done

cat >&2 <<MSG

overview-links: FAIL — the cited lines are not what$bad
was written against.  \`-\` is the committed expectation, \`+\` the tree.

  * If a citation MOVED (same text, shifted numbers), update the
    \`#L<a>-L<b>\` anchor in the document.
  * If the cited lines CHANGED, re-read the paragraph that cites them:
    the document may now be stale.  (README.md is the maintainer's: an
    agent may repoint a link and change nothing else.)

Then regenerate:  scripts/overview-links.sh --update
MSG
exit 1
