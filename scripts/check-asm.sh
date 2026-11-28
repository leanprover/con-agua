#!/usr/bin/env bash
# Assemble and disassemble every program the compiler proof covers (the scanner, the `lit` store,
# the arena walk, and the whole checker: the committed file `x86/checker.s`, whose code the final
# theorems are about, docs/design/asmfile.md) and check, instruction by instruction, that what `as`/`objdump` actually encode
# agrees with what `asmText` (Kraken's AT&T printer) printed. This is the trusted-base check: the
# printer and the assembler are *not* proved, so
# `compile_correct` only holds of the real machine if their printed/assembled text means what
# Kraken's instruction semantics says, and this is as close to checking that automatically as we
# get. See DESIGN.md ("the compiler", lane `walk`) and docs/gaps/kraken-att-imul-three-operand.lean
# (the mismatch this script would have caught before it was found by hand).
#
# Usage: scripts/check-asm.sh (from anywhere in the repo; rebuilds the emitters it needs).
# The gate `check-asm` of scripts/gates.sh (selected by scripts/gate_select.py) and a CI step.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

echo "+ lake build (the Emit* drivers)"
"$root/scripts/lake" -d x86 build ConAguaX86.Compiler.EmitScan ConAguaX86.Arena.EmitStore ConAguaX86.Arena.WalkEmit

declare -A progs=(
  [scan]="x86/ConAguaX86/Compiler/EmitScan.lean"
  [store]="x86/ConAguaX86/Arena/EmitStore.lean"
  [walk]="x86/ConAguaX86/Arena/WalkEmit.lean"
)

status=0
for name in scan store walk checker; do
  if [ "$name" = checker ]; then
    s="$root/x86/checker.s"
  else
    s="$work/$name.s"
    echo "+ lake -d x86 env lean --run ${progs[$name]} $s"
    "$root/scripts/lake" -d x86 env lean --run "${progs[$name]}" "$s"
  fi
  if ! python3 "$root/scripts/check_asm.py" "$s" "$name"; then
    status=1
  fi
done

exit "$status"
