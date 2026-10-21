module

public import ConAgua.L.Notation
public import ConAgua.L.Logic
public import ConAgua.Scan.Common
public import ConAgua.Scan.Values
public import ConAgua.Scan.Member
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The record loops (`scan_fast.rs:1434-3724`), validating only

One L function per record kind, as in Rust: `scan_X(i)` is Rust's `scan_X` (the opening brace)
with its `scan_X_loop` spliced in. The loop calls `next_member` and dispatches on the key code:
each key of the record checks its `seen` bit, scans its value, and sets the bit; any other key
is an error (`UnknownKey`). Each is proved against the generic model `objN` of
`ConAgua.Scan.Member` with the record's `bit`, `val`, `mask`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Records

open L.Scan.Member
open L.Scan.Values

/-- The input buffer. -/
abbrev IN : ArrId := 0

grind_pattern [lang_grind] slotNatN_pos => slotNatN b ks v

/-! ## `app`: `{"arg":A,"fn":F}` -/

def appLoop : Stmt := lblk (i, w, seen, tag, ks, k, v, e) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return 0 };
    if tag == 1 {
      if w != 0 && seen != 0 { return 0 };
      if (seen & 3) != 3 { return 0 };
      return ks + 1
    };
    if k == 3 {  -- `arg`
      if (seen & 1) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 1
    } else if k == 13 {  -- `fn`
      if (seen & 2) != 0 { return 0 };
      e := call slot_nat(ks, v);
      if e == 0 { return 0 };
      seen := seen | 2
    } else {
      return 0
    };
    i := e;
    w := 0
  }
}

def scanApp : FunDecl := lfn (i) locals (w, seen, tag, ks, k, v, e) {
  if i < len(IN.u8) && IN.u8[i] == 123 {
    i += 1;
    w := 1;
    ⟪appLoop⟫
  };
  return 0
}

def appBit (k : Word) : Word := if k = 3 then 1 else if k = 13 then 2 else 0
def appVal (b : Array UInt8) (_k ks v : Word) : Word := slotNatN b ks v

section app
variable (p : Prog) (b : Array UInt8) (hb : b.size < 2 ^ 63)
    (hpw : p.lookup "skip_ws" = some L.Scan.Leaves.skipWs)
    (hpd : p.lookup "skip_digits" = some L.Scan.Leaves.skipDigits)
    (hpk : p.lookup "key_end" = some L.Scan.Leaves.keyEnd)
    (hpn : p.lookup "num_end" = some L.Scan.Leaves.numEnd)
    (hpa : p.lookup "key_at" = some L.Scan.Key.keyAt)
    (hpv : p.lookup "value_at" = some L.Scan.Key.valueAt)
    (hpm : p.lookup "next_member" = some nextMember)
    (hps : p.lookup "slot_nat" = some slotNat)
    (hpx : p.lookup "scan_app" = some scanApp)
include hb hpw hpd hpk hpn hpa hpv hpm hps

attribute [local lang_grind] appBit appVal Mbr.err

theorem appLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n appLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN appBit (appVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := appLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa hpv hpm n,
        slotNat_spec p b hb hpd hpn hps n] <;> finish

theorem appLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) appLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [objN appBit (appVal b) 3 b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (appLoop_spec p b hb hpw hpd hpk hpn hpa hpv hpm hps (n + 1) s₀)

include hpx in
theorem scanApp_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scan_app" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [objEntryN appBit (appVal b) 3 b i]; ⊤⦄ := by
  rw [invoke_eq _ hpx]
  simp only [callFn, scanApp]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, objEntryN] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8,
        appLoop_step_spec p b hb hpw hpd hpk hpn hpa hpv hpm hps n] <;> finish

end app

end L.Scan.Records
