import ConAgua.Arena.IndInstallSpec11

/-!
# Refinements of `IndInstall`, part 12 (lane `indproofs2`, helper `install`): `blockCapsAt`

Every field is computed first (the branch words, `lv_zero_caps`' three words through its stub
contract, the two `EREC` name slices), then the 15-word record is written in `IW` at once
(`recW`). Its decoding (`CapsAt`) is stated for every array that holds the 15 words and agrees with
the record pool below its top: `cons_block_inds` copies the words into the former's `EREC` record.
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The word models -/

/-- `block_caps_head`'s results. -/
def capsHead (m : Mem) (pp mi : Word) : List Word :=
  if rdW (m.arr64 IW) (pp + 1) ≤ mi then [0, 0, 0, 0]
  else
    let ms := rdW (m.arr64 IW) (rdW (m.arr64 IW) pp + mi)
    if rdW (m.arr64 IW) (ms + 3) = 0 then [0, 0, 0, ms]
    else [rdW (m.arr64 IW) (ms + 2), rdW (m.arr64 IW) (ms + 3), Cmp.evalW .eq (rdW (m.arr64 IW) (ms + 3)) 1, ms]

theorem capsHead_spec (p : Prog) (hp : p.lookup "block_caps_head" = some blockCapsHead) (n : Nat)
    (s₀ : St) (pp mi : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "block_caps_head" [pp, mi]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r = capsHead s₀.mem pp mi; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCapsHead]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
    finish (gen := 20) [capsHead, rdW_eq]

/-- `block_caps_one`'s results. -/
def capsOne (m : Mem) (pp ms isRec : Word) : List Word :=
  let nIdx := rdW (m.arr64 IW) (ms + 1)
  let c := rdW (m.arr64 IW) (rdW (m.arr64 IW) (ms + 2))
  let nF := rdW (m.arr64 IW) (c + 1)
  let isP := Cmp.evalW .ne (rdW (m.arr64 IW) (pp + 8)) 0
  [Cmp.evalW .eq nIdx 0 &&& Cmp.evalW .eq isP 0 &&& Cmp.evalW .eq isRec 0,
   rdW (m.arr64 EREC) (rdW (m.arr64 IW) c), rdW (m.arr64 IW) (pp + 4), nF,
   Cmp.evalW .eq nIdx 0 &&& Cmp.evalW .eq nF 0 &&& Cmp.evalW .eq isRec 0,
   Cmp.evalW .eq (rdW (m.arr64 IW) (pp + 1)) 1 &&& Cmp.evalW .eq nF 0 &&& isP]

theorem capsOne_spec (p : Prog) (hp : p.lookup "block_caps_one" = some blockCapsOne) (n : Nat)
    (s₀ : St) (pp ms isRec : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "block_caps_one" [pp, ms, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r = capsOne s₀.mem pp ms isRec; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCapsOne]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
    finish (gen := 20) [capsOne, rdW_eq]

/-- After the first and second `rec5`. -/
def icaK7 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([q], m)
def icaK6 (q a0 a1 np c0 c1 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => icaK7 q (recW m 5 [a0, a1, np, c0, c1])
def icaK5b (w2 w6 z0 z1 z2 a0 a1 np c0 c1 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rq, m) => icaK6 (rq.headD 0) a0 a1 np c0 c1 (recW m 5 [w2, w6, z0, z1, z2])
/-- After the second copy: the record, three `rec5`s. -/
def icaK5 (pp w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => icaK5b w2 w6 z0 z1 z2 a0 a1 (rdW (m5.arr64 IW) (pp + 4)) (r5.headD 0) (r5.tail.headD 0)
      (recW m5 5 [w0, w1, w2, w3, w4])
/-- After the ctor names. -/
def icaK4 (p : Prog) (n : Nat) (pp w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => icaK5 pp w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1
      (callW p n "block_caps_at_er_copy" [r4.headD 0, r4.tail.headD 0] m4)
/-- After the member names' copy. -/
def icaK3 (p : Prog) (n : Nat) (pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => icaK4 p n pp w0 w1 w2 w3 w4 w6 z0 z1 z2 (r3.headD 0) (r3.tail.headD 0)
      (callW p n "block_caps_ctor_names" [coff, clen] m3)
/-- After the member names. -/
def icaK2 (p : Prog) (n : Nat) (pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => icaK3 p n pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2
      (callW p n "block_caps_at_er_copy" [r2.headD 0, r2.tail.headD 0] m2)

/-- **The model of `block_caps_fin`** (body fuel `n`). -/
def icfW (p : Prog) (n : Nat) (m : Mem) (pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 : Word) :
    Option (List Word × Mem) :=
  icaK2 p n pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 (callW p n "block_shape_member_names" [pp] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1 np c0 c1 q : Word)
  (r : List Word)
theorem icaK2_some : icaK2 p n pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 (some (r, m)) =
    icaK3 p n pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2
      (callW p n "block_caps_at_er_copy" [r.headD 0, r.tail.headD 0] m) := rfl
theorem icaK3_some : icaK3 p n pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 (some (r, m)) =
    icaK4 p n pp w0 w1 w2 w3 w4 w6 z0 z1 z2 (r.headD 0) (r.tail.headD 0)
      (callW p n "block_caps_ctor_names" [coff, clen] m) := rfl
theorem icaK4_some : icaK4 p n pp w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1 (some (r, m)) =
    icaK5 pp w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1
      (callW p n "block_caps_at_er_copy" [r.headD 0, r.tail.headD 0] m) := rfl
theorem icaK5_some : icaK5 pp w0 w1 w2 w3 w4 w6 z0 z1 z2 a0 a1 (some (r, m)) =
    icaK5b w2 w6 z0 z1 z2 a0 a1 (rdW (m.arr64 IW) (pp + 4)) (r.headD 0) (r.tail.headD 0)
      (recW m 5 [w0, w1, w2, w3, w4]) := rfl
theorem icaK5b_some : icaK5b w2 w6 z0 z1 z2 a0 a1 np c0 c1 (some (r, m)) =
    icaK6 (r.headD 0) a0 a1 np c0 c1 (recW m 5 [w2, w6, z0, z1, z2]) := rfl
theorem icaK6_some : icaK6 q a0 a1 np c0 c1 (some (r, m)) = icaK7 q (recW m 5 [a0, a1, np, c0, c1]) := rfl
theorem icaK7_some : icaK7 q (some (r, m)) = some ([q], m) := rfl
end arms
attribute [ind_grind] icaK2_some icaK3_some icaK4_some icaK5_some icaK5b_some icaK6_some icaK7_some

theorem icf_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (hr5 : p.lookup "rec5" = some rec5)
    (hp : p.lookup "block_caps_fin" = some blockCapsFin) (n : Nat) (s₀ : St)
    (pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "block_caps_fin"
      [pp, coff, clen, w0, w1, w2, w3, w4, w6, z0, z1, z2]
    ⦃fun r s' => LocEq s' s₀ ∧ icfW p n s₀.mem pp coff clen w0 w1 w2 w3 w4 w6 z0 z1 z2 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCapsFin]
  vcgen [exec, step, L.evalE_spec, evalC, evalArgs, setLoc, setLocs,
    callW_spec p n "block_shape_member_names", callW_spec p n "block_caps_at_er_copy",
    callW_spec p n "block_caps_ctor_names", rec5_specW p ha n hr5]
  all_goals simp_all [LocEq, Expr.pval, L.Arena.rd64_rdWC, BinOp.eval, Cmp.eval, Cmp.evalW, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal,
    Sig.retOr, -UInt64.not_lt, -UInt64.not_le,
    icfW, icaK2_some, icaK3_some, icaK4_some, icaK5_some, icaK5b_some, icaK6_some, icaK7_some]

/-- The returned pointer. -/
def icaKF : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- After `lv_zero_caps`: the record. -/
def icaK1 (p : Prog) (n : Nat) (pp coff clen : Word) (ws : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => icaKF (callW p n "block_caps_fin" [pp, coff, clen, ws.headD 0, ws.tail.headD 0,
      ws.tail.tail.headD 0, ws.tail.tail.tail.headD 0, ws.tail.tail.tail.tail.headD 0,
      ws.tail.tail.tail.tail.tail.headD 0, r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0] m1)
/-- After the branch words. -/
def icaKW (p : Prog) (n : Nat) (pp coff clen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ws, m) => icaK1 p n pp coff clen ws (callW p n "lv_zero_caps" [rdW (m.arr64 IW) (pp + 6)] m)
/-- After `block_caps_head`. -/
def icaKH (p : Prog) (n : Nat) (pp isRec : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (h, m) => icaKW p n pp (h.headD 0) (h.tail.headD 0)
      (if h.tail.tail.headD 0 = 1 then callW p n "block_caps_one" [pp, h.tail.tail.tail.headD 0, isRec] m
       else some ([0, 0, 0, 0, 0, 0], m))

/-- **The model of `block_caps_at(p, mi, is_rec)`** (body fuel `n`). -/
def icaW (p : Prog) (n : Nat) (m : Mem) (pp mi isRec : Word) : Option (List Word × Mem) :=
  icaKH p n pp isRec (callW p n "block_caps_head" [pp, mi] m)

section arms2
variable (p : Prog) (n : Nat) (m : Mem) (pp coff clen isRec : Word) (ws r : List Word)
theorem icaK1_some : icaK1 p n pp coff clen ws (some (r, m)) =
    icaKF (callW p n "block_caps_fin" [pp, coff, clen, ws.headD 0, ws.tail.headD 0,
      ws.tail.tail.headD 0, ws.tail.tail.tail.headD 0, ws.tail.tail.tail.tail.headD 0,
      ws.tail.tail.tail.tail.tail.headD 0, r.headD 0, r.tail.headD 0, r.tail.tail.headD 0] m) := rfl
theorem icaKF_some : icaKF (some (r, m)) = some ([r.headD 0], m) := rfl
theorem icaKW_some : icaKW p n pp coff clen (some (ws, m)) =
    icaK1 p n pp coff clen ws (callW p n "lv_zero_caps" [rdW (m.arr64 IW) (pp + 6)] m) := rfl
theorem icaKH_one (h : r.tail.tail.headD 0 = 1) : icaKH p n pp isRec (some (r, m)) =
    icaKW p n pp (r.headD 0) (r.tail.headD 0)
      (callW p n "block_caps_one" [pp, r.tail.tail.tail.headD 0, isRec] m) := by
  simp only [icaKH, h, ↓reduceIte]
theorem icaKH_rest (h : ¬ r.tail.tail.headD 0 = 1) : icaKH p n pp isRec (some (r, m)) =
    icaKW p n pp (r.headD 0) (r.tail.headD 0) (some ([0, 0, 0, 0, 0, 0], m)) := by
  simp only [icaKH, h, ↓reduceIte]
end arms2
attribute [ind_grind] icaK1_some icaKF_some icaKW_some icaKH_one icaKH_rest

set_option maxHeartbeats 1600000 in
theorem ica_spec (p : Prog) (hp : p.lookup "block_caps_at" = some blockCapsAt) (n : Nat)
    (s₀ : St) (pp mi isRec : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "block_caps_at" [pp, mi, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ icaW p n s₀.mem pp mi isRec = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCapsAt]
  vcgen [exec, step, L.evalE_spec, evalC, evalArgs, setLoc, setLocs,
    callW_spec p n "block_caps_head", callW_spec p n "block_caps_one",
    callW_spec p n "lv_zero_caps", callW_spec p n "block_caps_fin"]
  all_goals simp_all [LocEq, Expr.pval, L.Arena.rd64_rdWC, BinOp.eval, Cmp.eval, Cmp.evalW, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal,
    Sig.retOr, -UInt64.not_lt, -UInt64.not_le,
    icaW, icaKH, icaK1_some, icaKF_some, icaKW_some]

end L.Ind
