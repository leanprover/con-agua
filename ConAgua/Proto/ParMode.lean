import ConAgua.Checker.Prog
import ConAgua.Compiler.Run
import ConAgua.Compiler.Abi

/-!
# Prototype (unproved): parallel checking with threads over a frozen buffer (lane `parmode`)

Not in the lake globs. `scripts/lake env lean --run ConAgua/Proto/ParMode.lean OUT.s` writes an
assembler file with three entries (docs/design/parmode.md):

* `ca_start(in, in_len, pins, pins_len, base, base_len)`: the sequential checker, unchanged in
  behaviour (`check` dispatches on the global `MODE`, which is `0` in a zero region).
* `ca_start_a(…same…)`: `MODE := 1`; the stages and phase A, then `par_compact`, which copies the
  persistent tier of every structure phase B reads into the word array `OUT`: a header (`HDRF`)
  and, per frozen array, its live prefix. Returns `2^63 + k` (`k` pending checks).
* `ca_check_b(buf, buf_len, j, region, region_len)`: the table in `region` (own stack, own
  arrays), every frozen array's descriptor pointing into `buf`, `MODE := 2`, `PJ := j`; `check_b`
  copies the seed arrays (`CTLF` → `CTL`, `POOLF` → `POOL`) on the region's first call, then runs
  `check_pending(j)`.

The L changes (`check`, `check_a`, `check_b`, `par_compact`, and the env index tiered by the name
handle's tier: `env_row_get`/`env_row_set`) are spliced into `checkerProg` here, so the proved
program is untouched.
-/

open L L.Compiler L.Checker L.Arena L.Front

namespace ParMode

abbrev MODE : GVar := ⟨0⟩
abbrev PJ : GVar := ⟨1⟩
abbrev INIT : GVar := ⟨2⟩

abbrev OUT : ArrId := 240
abbrev HDRF : ArrId := 241
abbrev CTLF : ArrId := 242
abbrev POOLF : ArrId := 243

/-- `CTL[k]`. -/
def ctl (k : Nat) : Expr := .ld64 1 (.const k.toUInt64)
def cst (k : Nat) : Expr := .const k.toUInt64
def mul (a b : Expr) : Expr := .bin .mul a b
def add (a b : Expr) : Expr := .bin .add a b

/-- The cons tables: record array, slot array, words per record, count slot. -/
def stores : List (ArrId × ArrId × Nat × Nat) :=
  [(2, 3, 4, 2), (4, 5, 2, 4), (6, 7, 1, 6), (8, 9, 1, 8), (10, 11, 2, 10), (12, 13, 2, 12),
   (14, 15, 1, 14), (16, 17, 1, 16), (18, 19, 2, 18), (20, 21, 3, 20), (22, 23, 1, 22),
   (25, 26, 2, 26), (27, 28, 2, 28), (29, 30, 2, 30), (31, 32, 3, 32), (33, 34, 1, 34),
   (35, 36, 4, 36), (37, 38, 2, 38), (39, 40, 3, 40)]

/-- The one-word columns (derived, hash/level) and their store's count slot. -/
def cols : List (ArrId × Nat) :=
  [(42, 4), (43, 28), (44, 30), (45, 20), (46, 32),
   (55, 6), (56, 10), (57, 12), (58, 40), (59, 16), (60, 18), (61, 26)]

/-- How a frozen array is filled: a prefix of the source array, or a KSTP slot table moved to
offset `0` (words `0`, `1` = `n - SN0`, `0`; then the `2 n` table words from `2 + o`). -/
inductive Fz where
  | pre (src : ArrId) (ext : Expr)
  | slot (sa : ArrId)

/-- The frozen arrays after the header: (id in entry 2, how entry 1 fills it). -/
def frozen : List (ArrId × Fz) :=
  [(CTLF, .pre 1 (cst 256)), (POOLF, .pre 0 (ctl 0))] ++
  stores.flatMap (fun (ra, sa, w, ca) => [(ra, .pre ra (mul (ctl ca) (cst w))), (sa, .slot sa)]) ++
  cols.map (fun (c, ca) => (c, .pre c (ctl ca))) ++
  [(128, .pre 128 (cst 71)),
   (132, .pre 132 (mul (cst 2) (ctl 34))), (133, .pre 133 (mul (cst 2) (ctl 36))),
   (134, .pre 134 (mul (cst 2) (ctl 38))),
   (136, .pre 136 (ctl 129)), (137, .pre 137 (mul (cst 3) (ctl 130)))]

/-- Header words: `0` magic, `1` total words, `2` pending count, `3` view, `4` frozen count;
then `(off, len)` of `HDRF` at `8`, of frozen entry `i` at `10 + 2 i`. -/
def hdrW : Nat := 10 + 2 * frozen.length
def magic : Word := 0x5041524d4f444531

def seqs : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: ss => .seq s (seqs ss)

/-- `par_compact(v)`: locals `v o e q r n`. -/
def compactL : FunDecl :=
  let o : Var := 1
  let e : Var := 2
  let q : Var := 3
  let r : Var := 4
  let n : Var := 5
  let fill : Fz → Stmt
    | .pre src ext => seqs [.set e ext, .copy64 (.plain OUT) (.var o) (.plain src) (cst 0) (.var e)]
    | .slot sa => seqs [
        .set n (mul (cst 2) (add (.ld64 sa (cst 0)) (.const SN0))),
        .set e (add (.var n) (cst 2)),
        .st64 OUT (.var o) (.ld64 sa (cst 0)),
        .st64 OUT (add (.var o) (cst 1)) (cst 0),
        .set q (add (.var o) (cst 2)),
        .set r (add (.ld64 sa (cst 1)) (cst 2)),
        .copy64 (.plain OUT) (.var q) (.plain sa) (.var r) (.var n)]
  let body := seqs <|
    [.set o (cst hdrW)] ++
    (frozen.zipIdx.map fun ((_, fz), i) => seqs [
      fill fz,
      .st64 OUT (cst (10 + 2 * i)) (.var o),
      .st64 OUT (cst (11 + 2 * i)) (.var e),
      .set o (add (.var o) (.var e))]) ++
    [.st64 OUT (cst 0) (.const magic), .st64 OUT (cst 1) (.var o), .st64 OUT (cst 2) (ctl 130),
     .st64 OUT (cst 3) (.var 0), .st64 OUT (cst 4) (cst frozen.length),
     .st64 OUT (cst 8) (cst 0), .st64 OUT (cst 9) (cst hdrW),
     .ret [.var o]]
  { nparams := 1, nlocals := 6, body }

def checkL' : FunDecl := lfn () locals (r, z) {
  if MODE == 1 { r := call check_a(); return r };
  if MODE == 2 { r := call check_b(); return r };
  z := call cap_check();
  z := call pb_check();
  z := call intern_reserved_pins();
  z := call builtin_prelude();
  r := call front_run();
  if r != 0 { return 1 };
  z := call prepare_prelude();
  z := call intern_all_pins();
  z := call install_then_check();
  return 71757147230292
}

def checkAL : FunDecl := lfn () locals (r, z, cnt, v) {
  z := call cap_check();
  z := call pb_check();
  z := call intern_reserved_pins();
  z := call builtin_prelude();
  r := call front_run();
  if r != 0 { return 1 };
  z := call prepare_prelude();
  z := call intern_all_pins();
  cnt := DECL.u64[0];
  v := call install_fold_go(0, cnt, 0);
  z := call par_compact(v);
  return 9223372036854775808 + CTL.u64[130]
}

def checkBL : FunDecl := lfn () locals (z, n) {
  if INIT == 0 {
    n := len(CTLF.u64);
    copy!(CTL.u64, 0, CTLF.u64, 0, n);
    n := len(POOLF.u64);
    copy!(POOL.u64, 0, POOLF.u64, 0, n);
    INIT := 1
  };
  if CTL.u64[130] <= PJ { abort };
  z := call check_pending(PJ, HDRF.u64[3]);
  return 71757147230292
}

/-- The env index, tiered by the name handle's tier: row of node `i` of tier `t` at
`EIX⟨t⟩[2 i]` (was `EIX[4 i + 2 t]`). -/
def envRowGetT : FunDecl := lfn (w) locals (g, t, ix) {
  g := w >> 28;
  t := (w >> 27) & 1;
  ix := (w & 134217727) << 1;
  if g == 0 { return (EIXA⟨t⟩[ix], EIXA⟨t⟩[ix + 1]) };
  if g == 1 { return (EIXS⟨t⟩[ix], EIXS⟨t⟩[ix + 1]) };
  if g == 2 { return (EIXN⟨t⟩[ix], EIXN⟨t⟩[ix + 1]) };
  abort
}

def envRowSetT : FunDecl := lfn (w, c, p) locals (g, t, ix) {
  g := w >> 28;
  t := (w >> 27) & 1;
  ix := (w & 134217727) << 1;
  if 2 < g { abort };
  if g == 0 { EIXA⟨t⟩[ix] := c; EIXA⟨t⟩[ix + 1] := p; return 0 };
  if g == 1 { EIXS⟨t⟩[ix] := c; EIXS⟨t⟩[ix + 1] := p; return 0 };
  EIXN⟨t⟩[ix] := c; EIXN⟨t⟩[ix + 1] := p; return 0
}

def overrides : Prog :=
  [("check", checkL'), ("check_a", checkAL), ("check_b", checkBL), ("par_compact", compactL),
   ("env_row_get", envRowGetT), ("env_row_set", envRowSetT)]

def prog : Prog :=
  overrides ++ checkerProg.filter (fun (f, _) => !(overrides.any (·.1 == f)))

/-! ## Phase B's arrays (the closure of `check_b`) -/

partial def _root_.L.Expr.arrsE : Expr → List ArrId
  | .bin _ a b | .cmpw _ a b => a.arrsE ++ b.arrsE
  | .ld8 a i | .ld64 a i => a :: i.arrsE
  | .len8 a | .len64 a => [a]
  | .ldc _ i => i.arrsE
  | .ld64t a t i => a :: (a + 256) :: t.arrsE ++ i.arrsE
  | .len64t a t => a :: (a + 256) :: t.arrsE
  | .ld8x8 (.arr a) i => a :: i.arrsE
  | .ld8x8 _ i => i.arrsE
  | _ => []
partial def _root_.L.Cond.arrsC : Cond → List ArrId
  | .cmp _ a b => Expr.arrsE a ++ Expr.arrsE b
  | .and p q | .or p q => p.arrsC ++ q.arrsC
  | .not p => p.arrsC
def warr : WArr → List ArrId
  | .plain a => [a]
  | .tier a _ => [a, a + 256]
partial def _root_.L.Stmt.arrsS : Stmt → List ArrId
  | .seq s t => s.arrsS ++ t.arrsS
  | .ite c s t => Cond.arrsC c ++ s.arrsS ++ t.arrsS
  | .while c s => Cond.arrsC c ++ s.arrsS
  | .set _ e | .gset _ e => Expr.arrsE e
  | .st8 a i e | .st64 a i e => a :: Expr.arrsE i ++ Expr.arrsE e
  | .st64t a t i e => a :: (a + 256) :: Expr.arrsE t ++ Expr.arrsE i ++ Expr.arrsE e
  | .ret es | .call _ _ es => es.flatMap Expr.arrsE
  | .copy64 d di s si n => warr d ++ warr s ++ Expr.arrsE di ++ Expr.arrsE si ++ Expr.arrsE n
  | .copy8w d di _ si n => warr d ++ Expr.arrsE di ++ Expr.arrsE si ++ Expr.arrsE n
  | .scan8 _ _ i e _ => Expr.arrsE i ++ Expr.arrsE e
  | _ => []
partial def _root_.L.Stmt.callsS : Stmt → List FnName
  | .seq s t => s.callsS ++ t.callsS
  | .ite _ s t => s.callsS ++ t.callsS
  | .while _ s => s.callsS
  | .call _ f _ => [f]
  | _ => []
partial def clo (p : Prog) (todo seen : List FnName) : List FnName :=
  match todo with
  | [] => seen
  | f :: r => if f ∈ seen then clo p r seen else
    match p.lookup f with
    | some fd => clo p (fd.body.callsS ++ r) (f :: seen)
    | none => clo p r (f :: seen)

def frozenIds : List ArrId := HDRF :: frozen.map (·.1)

/-- The word arrays phase B touches that are not frozen: they get slots in the worker region. -/
def ownedIds : List ArrId :=
  let fs := clo prog ["check_b"] []
  let as := fs.flatMap (fun f => match prog.lookup f with | some fd => fd.body.arrsS | none => [])
  ((as.eraseDups.filter (fun a => !(frozenIds.contains a)))).mergeSort

/-! ## The stubs (assembler text) -/

def slot : Nat := abiSlot

/-- `ca_start_a`: `MODE := 1`, then `ca_start` (declines there if the region is too small). -/
def stubA (tab : Tab) : String :=
  s!"ca_start_a:\nmovq ${(abiNeed tab)}, %rax\ncmpq %rax, %r9\njb ca_start\n" ++
  s!"movq $1, {tab.globOff MODE}(%r8)\njmp ca_start\n"

/-- The worker region: slot 0 the table, slot 1 the stack, slot `2 + k` owned array `k`. -/
def workerNeed : Nat := slot * (2 + ownedIds.length)

/-- `ca_check_b(buf rdi, buf_len rsi, j rdx, region rcx, region_len r8)`. -/
def stubB (tab : Tab) : String := Id.run do
  let mut s := s!"ca_check_b:\nmovq ${workerNeed}, %rax\ncmpq %rax, %r8\njb ca_abi_decline\n"
  s := s ++ s!"movq ${slot + abiStack}, %rax\naddq %rcx, %rax\nmovq %rax, 0(%rcx)\n"
  s := s ++ s!"movq ${slot}, %rax\naddq %rcx, %rax\nmovq %rax, 8(%rcx)\n"
  -- byte arrays: none in phase B
  for a in List.range tab.nb do
    s := s ++ s!"movq $0, {tab.base8 a}(%rcx)\nmovq $0, {tab.len8 a}(%rcx)\n"
  for a in List.range tab.nw do
    match frozenIds.idxOf? a with
    | some i =>
      s := s ++ s!"movq {8 * (8 + 2 * i)}(%rdi), %rax\nshlq $3, %rax\naddq %rdi, %rax\nmovq %rax, {tab.base64 a}(%rcx)\n"
      s := s ++ s!"movq {8 * (9 + 2 * i)}(%rdi), %rax\nmovq %rax, {tab.len64 a}(%rcx)\n"
    | none =>
      match ownedIds.idxOf? a with
      | some k =>
        s := s ++ s!"movq ${slot * (2 + k)}, %rax\naddq %rcx, %rax\nmovq %rax, {tab.base64 a}(%rcx)\n"
        s := s ++ s!"movq ${abiWords}, %rax\nmovq %rax, {tab.len64 a}(%rcx)\n"
      | none =>
        s := s ++ s!"movq $0, {tab.base64 a}(%rcx)\nmovq $0, {tab.len64 a}(%rcx)\n"
  -- the constant data
  let mut d := tab.romBase
  for v in romVals tab.rom do
    match v with
    | .imm w => s := s ++ s!"movq ${w.toNat}, %rax\nmovq %rax, {d}(%rcx)\n"
    | _ => pure ()
    d := d + 8
  s := s ++ s!"movq %rdx, {tab.globOff PJ}(%rcx)\nmovq $2, {tab.globOff MODE}(%rcx)\n"
  s := s ++ "movq %rcx, %rdi\nmovq $" ++ toString abiFuel ++ ", %rsi\njmp ca_enter\n"
  return s

end ParMode

open ParMode in
def main (args : List String) : IO Unit := do
  let out := args.headD "par.s"
  let p := ParMode.prog
  let (nb, nw) := Prog.arrs p
  let tab := Prog.tab p nb nw
  let code := compileProg tab p "check"
  let base := asmTextAbi tab code
  -- put the two stubs right after the `.text` header of the sequential file
  let hdr := ".text\n.globl " ++ abiStartL ++ "\n"
  let rest := (base.drop hdr.length).toString
  let txt := hdr ++ ".globl ca_start_a\n.globl ca_check_b\n" ++ stubA tab ++ stubB tab ++ rest ++
    s!".section .rodata\n.globl ca_nw\n.globl ca_nb\n.globl ca_diag\n.globl ca_out_off\n.globl ca_worker_size\n" ++
    s!"ca_nw: .quad {tab.nw}\nca_nb: .quad {tab.nb}\nca_diag: .quad -1\n" ++
    s!"ca_out_off: .quad {abiSlot * abiSlot64 tab OUT}\nca_worker_size: .quad {workerNeed}\n"
  IO.FS.writeFile out txt
  IO.println s!"wrote {out}: nb {tab.nb}, nw {tab.nw}, ng {tab.ng}, frozen {frozenIds.length}, owned {ownedIds.length}: {ownedIds}"
  IO.println s!"header words {hdrW}; worker region {workerNeed}"
