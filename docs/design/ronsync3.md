# Lane ronsync3: the con-ron sync 01ecb31c → 4ca283d1

Lane of 2026-11-11 (Opus), from master `b4ce0391e`. con-ron `01ecb31c → 4ca283d1`, con-leche
`210a580e → eb2c5939`, upstream tasks #149, #150, #151. Starting kit: docs/design/presync3.md §4;
rules: `scripts/sync-rules/ronsync3.txt`. Decided before the lane: `--olean` stays out (D44); the
`IIndCaps` record keeps its 15-word `EREC` layout (the five dropped fields' words unwritten and
unread), the ROM's `encCaps` drops them; every new or rewritten function gets a generated model and
a declarative refinement (exceptions: `pow_nat`, `size_bytes`); no walk tactic.

## 1. Progress log

* 2026-11-11 23:55 start. Report (`_tmp/bump-4ca283d1/report.{txt,md}`): as presync3 §1 (173 L
  items, 698 mentioners / 404 theorems in 213 files; patches con-leche/0001 and con-ron/0002
  conflict in con-leche's `Kernel/Expr.lean`, `Kernel/Name.lean`). Sent to the coordinator.
