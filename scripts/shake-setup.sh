#!/usr/bin/env bash
# scripts/shake-setup.sh: build Lean's import minimizer (`lake shake`) for this tree, which
# `scripts/shake.py` runs. Copied from con-leche's `scripts/shake-setup.sh` (task #223).
#
# The toolchain ships `shake` as `lake shake` (sources at
#   $(lean --print-prefix)/src/lean/lake/Lake/CLI/Shake.lean),
# but `Lake.Shake.run` refuses a closure with a classic (non-`module`) file, and most of ConAgua
# (everything that mentions con-ron's arena) is classic. So this script copies that one file into a
# scratch Lake project under `_tmp/shake-tool/` (nothing is added to this package's manifest) and
# applies three patches, each about classic files only:
#
#   1. drop the "only works with `module`s" guard (a classic file records every import as
#      `isExported := true, importAll := false`, which is `public import`, so the analysis is the same);
#   2. `decodeImport` reads a classic file's `import X` as exported (else `--fix` does nothing there);
#   3. the `--fix` writer spells an added import `import X` in a classic file.
#
# The scratch project is built with plain `lake` and LAKE_ARTIFACT_CACHE=false: it is not a
# worktree of this repository and shares nothing with the project's Lake cache.
# Usage: scripts/shake-setup.sh  (builds _tmp/shake-tool/<toolchain>/.lake/build/bin/shaketool; ~10 s)
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
# one build per toolchain (`_tmp` is shared between worktrees)
dir="$root/_tmp/shake-tool/$(tr -c "A-Za-z0-9.\n-" _ < "$root/lean-toolchain")"
src="$(cd "$root" && lean --print-prefix)/src/lean/lake/Lake/CLI/Shake.lean"
mkdir -p "$dir"
cp "$root/lean-toolchain" "$dir/"
cp "$src" "$dir/Shake.lean"

python3 - "$dir/Shake.lean" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read()

g = """  if env.header.moduleData.any (!·.isModule) then
    throw <| .userError "`lake shake` only works with `module`s currently"
"""
assert g in s, "patch 1: guard not found (toolchain drift?)"
s = s.replace(g, "  -- PATCH 1 (con-leche #223, classic files): upstream's `module`-only guard dropped.\n")

d = """def decodeImport : TSyntax ``Parser.Module.import → Import
  | `(Parser.Module.import| $[public%$pubTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $id) =>
    { module := id.getId, isExported := pubTk?.isSome, isMeta := metaTk?.isSome, importAll := allTk?.isSome }
  | stx => panic! s!"unexpected syntax {stx}\""""
assert d in s, "patch 2: decodeImport not found (toolchain drift?)"
s = s.replace(d, """-- PATCH 2 (con-leche #223, classic files): a classic file has no `public` token, yet its
-- olean records the import as exported.
def decodeImport (isModuleFile : Bool) : TSyntax ``Parser.Module.import → Import
  | `(Parser.Module.import| $[public%$pubTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $id) =>
    { module := id.getId, isExported := pubTk?.isSome || !isModuleFile,
      isMeta := metaTk?.isSome, importAll := allTk?.isSome }
  | stx => panic! s!"unexpected syntax {stx}\"""")

s = s.replace("""  for impStx in imports do
    let imp := decodeImport impStx""",
              """  for impStx in imports do
    let imp := decodeImport module?.isSome impStx""", 1)
s = s.replace("""      let (_, _, imports) := decodeHeader stx
      for stx in imports do
        if toRemove.any fun imp => imp == decodeImport stx then""",
              """      let (module?, _, imports) := decodeHeader stx
      for stx in imports do
        if toRemove.any fun imp => imp == decodeImport module?.isSome stx then""", 1)
s = s.replace("""    let (_, _, imports) := decodeHeader stx
    let text := inputCtx.fileMap.source""",
              """    let (module?, _, imports) := decodeHeader stx
    let text := inputCtx.fileMap.source""", 1)
s = s.replace("""      let mod := decodeImport stx""",
              """      let mod := decodeImport module?.isSome stx""", 1)

a = """    for mod in add do
      if !seen.contains mod then
        seen := seen.insert mod
        out := out ++ s!"{mod}\\n\""""
assert a in s, "patch 3: fix writer not found (toolchain drift?)"
s = s.replace(a, """    for mod in add do
      if !seen.contains mod then
        seen := seen.insert mod
        -- PATCH 3 (con-leche #223, classic files): a classic file has no `public import` syntax.
        out := out ++ (if module?.isSome then s!"{mod}\\n" else s!"import {mod.module}\\n")""", 1)

s = s.replace("\nprelude\n", "\n\n", 1)   # the vendored copy is not part of Init
open(p, "w").write(s)
print("Shake.lean vendored and patched")
PY

cat > "$dir/lakefile.toml" <<'EOF'
name = "shaketool"
defaultTargets = ["shaketool"]

[[lean_lib]]
name = "Shake"

[[lean_exe]]
name = "shaketool"
root = "Tool"
EOF

cat > "$dir/Tool.lean" <<'EOF'
module
import Shake
import Lean.Util.Path
open Lean
/-- A driver for the vendored `Lake.Shake.run`.  Source roots come from
`SHAKE_SRC` (colon-separated), oleans from `LEAN_PATH`. -/
public def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut a : Lake.Shake.Args := {}
  let mut mods := #[]
  let mut only := #[]
  let mut nextOnly := false
  for s in args do
    if nextOnly then only := only.push s.toName; nextOnly := false
    else if s == "--explain" then a := { a with explain := true }
    else if s == "--trace" then a := { a with trace := true }
    else if s == "--fix" then a := { a with fix := true }
    else if s == "--keep-implied" then a := { a with keepImplied := true }
    else if s == "--keep-prefix" then a := { a with keepPrefix := true }
    else if s == "--only" then nextOnly := true
    else mods := mods.push s.toName
  a := { a with mods := mods, onlyMods := only }
  let sp : SearchPath := ((← IO.getEnv "SHAKE_SRC").getD ".").splitOn ":" |>.map (⟨·⟩)
  Lake.Shake.run a sp
EOF

cd "$dir" && LAKE_ARTIFACT_CACHE=false lake build
echo "built: $dir/.lake/build/bin/shaketool"
