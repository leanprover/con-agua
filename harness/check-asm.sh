#!/usr/bin/env bash
# Assemble and disassemble every program the compiler proof covers (the scanner, the `lit` store,
# the arena walk) and check, instruction by instruction, that what `as`/`objdump` actually encode
# agrees with what `asmText` (Kraken's AT&T printer) printed. This is the trusted-base check: the
# printer and the assembler are *not* proved, so
# `compile_correct` only holds of the real machine if their printed/assembled text means what
# Kraken's instruction semantics says, and this is as close to checking that automatically as we
# get. See DESIGN.md ("the compiler", lane `walk`) and docs/gaps/kraken-att-imul-three-operand.lean
# (the mismatch this script would have caught before it was found by hand).
#
# Usage: harness/check-asm.sh (from anywhere in the repo; rebuilds the emitters it needs).
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

echo "+ lake build (the three Emit* drivers)"
lake build ConAgua.Compiler.EmitScan ConAgua.Arena.EmitStore ConAgua.Arena.WalkEmit

declare -A progs=(
  [scan]="ConAgua/Compiler/EmitScan.lean"
  [store]="ConAgua/Arena/EmitStore.lean"
  [walk]="ConAgua/Arena/WalkEmit.lean"
)

status=0
for name in scan store walk; do
  s="$work/$name.s"
  echo "+ lake env lean --run ${progs[$name]} $s"
  lake env lean --run "${progs[$name]}" "$s"
  if ! python3 "$root/harness/check_asm.py" "$s" "$name"; then
    status=1
  fi
done

exit "$status"
