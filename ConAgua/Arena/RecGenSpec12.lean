import ConAgua.Arena.RecGenSpec11
import ConAgua.Arena.IndSumSpec9
import ConAgua.Arena.DeclHeader

/-!
# `RecGen`: `classFeR` (lane `indproofs2`, helper `rec3`)

The rule-less generated recursors pushed temporarily, the displaced rows returned for the pop. As
`cons_sum_ctors` (`IndSumSpec9.lean`): a fresh `.recInfo` record (`class_fe_r_rec`), lane `decls2`'s
`env_push` through `callW`, the row read by `env_row_get` (`DeclHeader.lean`'s `rowCW`/`rowPW`),
decoded by `env_pop_temp`'s `prevD`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `class_fe_r_rec` -/

/-- The memory after `class_fe_r_rec`'s nine writes (each copy reads the memory of its time). -/
def cfrMem (m1 : Mem) (q cv mi rp3 : Word) : Mem :=
  let m2 := m1.set64 EREC q 5
  let m3 := m2.set64 EREC (q + 1) (rdW (m2.arr64 EREC) cv)
  let m4 := m3.set64 EREC (q + 2) (rdW (m3.arr64 EREC) (cv + 1))
  let m5 := m4.set64 EREC (q + 3) (rdW (m4.arr64 EREC) (cv + 2))
  let m6 := m5.set64 EREC (q + 4) (rdW (m5.arr64 EREC) (cv + 3))
  ((((m6.set64 EREC (q + 5) mi).set64 EREC (q + 6) rp3).set64 EREC (q + 7) 0).set64 EREC (q + 8) 0)

/-- The model of `class_fe_r_rec(cv, mi, rp3)`. -/
def cfrRecW (m : Mem) (cv mi rp3 : Word) : Option (Word × Mem) :=
  match erAllocW m 9 with
  | none => none
  | some (q, m1) =>
    if 4294967296 ≤ rdW ((cfrMem m1 q cv mi rp3).arr64 EREC) (q + 1) then none
    else some (q, cfrMem m1 q cv mi rp3)

theorem cfrRec_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hp : p.lookup "class_fe_r_rec" = some classFeRRec) (n : Nat) (s₀ : St) (cv mi rp3 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fe_r_rec" [cv, mi, rp3]
    ⦃fun r s' => LocEq s' s₀ ∧ cfrRecW s₀.mem cv mi rp3 = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, classFeRRec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        erecAlloc_specW p ha n] <;>
      finish [cfrRecW, cfrMem]

/-! ## `class_fe_r_go`: the word model -/

/-- The recursor record's major index and rule prefix (`0`, `0` off the list). -/
def ferMi (m : Mem) (ro rl M : Word) : Word :=
  if M < rl then rdW (m.arr64 IW) (rdW (m.arr64 IW) (ro + M) + 2) else 0
def ferRp (m : Mem) (ro rl M : Word) : Word :=
  if M < rl then rdW (m.arr64 IW) (rdW (m.arr64 IW) (ro + M) + 1) else 0

def ferK5 (v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => some ([v, r5.headD 0, r5.tail.headD 0], m5)

def ferK4 (n : Nat) (y : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => ferK5 (r4.headD 0) (consW n m4 y (r4.tail.headD 0) (r4.tail.tail.headD 0))

mutual
/-- **The model of `class_fe_r_go`.** -/
def ferW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, cvo, cvl, rcl, ro, rl, vis, M =>
    if cvl = 0 then some ([vis, 0, 0], m)
    else if rcl = 0 then some ([vis, 0, 0], m)
    else if 2 < tagW (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo)) then none
    else ferK1 p n cvo cvl rcl ro rl M (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo))
      (rowCW m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo))) (rowPW m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo)))
      vis (cfrRecW m (rdW (m.arr64 IW) cvo) (ferMi m ro rl M) (ferRp m ro rl M))
def ferK1 (p : Prog) (n : Nat) (cvo cvl rcl ro rl M nm c q vis : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (kq, m1) => ferK2 p n cvo cvl rcl ro rl M nm c q (callW p n "env_push" [vis, kq] m1)
def ferK2 (p : Prog) (n : Nat) (cvo cvl rcl ro rl M nm c q : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, m2) => ferK3 p n cvo cvl rcl ro rl M (rv.headD 0) (recW m2 3 [nm, c, q])
def ferK3 (p : Prog) (n : Nat) (cvo cvl rcl ro rl M v : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (re, m3) => ferK4 n (re.headD 0) (ferW p n m3 (cvo + 1) (cvl - 1) (rcl - 1) ro rl v (M + 1))
end

/-- **The model of `class_fe_r`.** -/
def ferAW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, pp, cgo, cgl, _, rcl, vis =>
    ferK5' (ferW p n m cgo cgl rcl (rdW (m.arr64 IW) (pp + 2)) (rdW (m.arr64 IW) (pp + 3)) vis 0)
where
  ferK5' : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (r, m') => some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m')

section arms
variable (p : Prog) (n : Nat) (m m1 m2 m3 m4 m5 : Mem)
  (cvo cvl rcl ro rl vis M nm c q kq v y pp cgo cgl rco : Word) (r1 r2 r3 r4 r5 : List Word)
theorem ferMi_hit (h : M < rl) : ferMi m ro rl M = rdW (m.arr64 IW) (rdW (m.arr64 IW) (ro + M) + 2) := by
  simp [ferMi, h]
theorem ferMi_miss (h : ¬ M < rl) : ferMi m ro rl M = 0 := by simp [ferMi, h]
theorem ferRp_hit (h : M < rl) : ferRp m ro rl M = rdW (m.arr64 IW) (rdW (m.arr64 IW) (ro + M) + 1) := by
  simp [ferRp, h]
theorem ferRp_miss (h : ¬ M < rl) : ferRp m ro rl M = 0 := by simp [ferRp, h]
theorem ferW_nil1 (h : cvl = 0) : ferW p (n + 1) m cvo cvl rcl ro rl vis M = some ([vis, 0, 0], m) := by
  simp [ferW, h]
theorem ferW_nil2 (h1 : ¬ cvl = 0) (h : rcl = 0) :
    ferW p (n + 1) m cvo cvl rcl ro rl vis M = some ([vis, 0, 0], m) := by
  simp only [ferW]; rw [if_neg h1, if_pos h]
theorem ferW_tag (h1 : ¬ cvl = 0) (h2 : ¬ rcl = 0) (h : 2 < tagW (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo))) :
    ferW p (n + 1) m cvo cvl rcl ro rl vis M = none := by
  simp only [ferW]; rw [if_neg h1, if_neg h2, if_pos h]
theorem ferW_cons (h1 : ¬ cvl = 0) (h2 : ¬ rcl = 0) (h : ¬ 2 < tagW (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo))) :
    ferW p (n + 1) m cvo cvl rcl ro rl vis M =
      ferK1 p n cvo cvl rcl ro rl M (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo))
        (rowCW m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo))) (rowPW m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvo)))
        vis (cfrRecW m (rdW (m.arr64 IW) cvo) (ferMi m ro rl M) (ferRp m ro rl M)) := by
  simp only [ferW]; rw [if_neg h1, if_neg h2, if_neg h]
theorem ferK1_some : ferK1 p n cvo cvl rcl ro rl M nm c q vis (some (kq, m1)) =
    ferK2 p n cvo cvl rcl ro rl M nm c q (callW p n "env_push" [vis, kq] m1) := by rw [ferK1]
theorem ferK2_some : ferK2 p n cvo cvl rcl ro rl M nm c q (some (r2, m2)) =
    ferK3 p n cvo cvl rcl ro rl M (r2.headD 0) (recW m2 3 [nm, c, q]) := by rw [ferK2]
theorem ferK3_some : ferK3 p n cvo cvl rcl ro rl M v (some (r3, m3)) =
    ferK4 n (r3.headD 0) (ferW p n m3 (cvo + 1) (cvl - 1) (rcl - 1) ro rl v (M + 1)) := by rw [ferK3]
theorem ferK4_some : ferK4 n y (some (r4, m4)) =
    ferK5 (r4.headD 0) (consW n m4 y (r4.tail.headD 0) (r4.tail.tail.headD 0)) := rfl
theorem ferK5_some : ferK5 v (some (r5, m5)) = some ([v, r5.headD 0, r5.tail.headD 0], m5) := rfl
theorem cfaW_eq : ferAW p (n + 1) m pp cgo cgl rco rcl vis =
    ferAW.ferK5' (ferW p n m cgo cgl rcl (rdW (m.arr64 IW) (pp + 2)) (rdW (m.arr64 IW) (pp + 3)) vis 0) := rfl
theorem ferK5'_some : ferAW.ferK5' (some (r1, m1)) =
    some ([r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0], m1) := rfl
end arms
attribute [ind_grind] ferMi_hit ferMi_miss ferRp_hit ferRp_miss ferW_nil1 ferW_nil2 ferW_tag ferW_cons
  ferK1_some ferK2_some ferK3_some ferK4_some ferK5_some cfaW_eq ferK5'_some

/-- The lookups of `class_fe_r`. -/
structure CfrProg (p : Prog) : Prop where
  rp : RecProg p
  ix : p.lookup "env_ix" = some envIxL
  rg : p.lookup "env_row_get" = some envRowGetL
  ia : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  rec3 : p.lookup "rec3" = some rec3
  frec : p.lookup "class_fe_r_rec" = some classFeRRec
  go : p.lookup "class_fe_r_go" = some classFeRGo
  top : p.lookup "class_fe_r" = some classFeRL

set_option maxHeartbeats 1000000 in
theorem classFeRGo_spec (p : Prog) (h : CfrProg p) (n : Nat) :
    ∀ (s₀ : St) (cvo cvl rcl ro rl vis M : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fe_r_go" [cvo, cvl, rcl, ro, rl, vis, M]
    ⦃fun r s' => LocEq s' s₀ ∧ ferW p n s₀.mem cvo cvl rcl ro rl vis M = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ cvo cvl rcl ro rl vis M
    rw [invoke_eq _ h.go]; simp only [callFn, classFeRGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ cvo cvl rcl ro rl vis M
    rw [invoke_eq _ h.go]
    simp only [callFn, classFeRGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        rowGet_specW p h.ix h.rg n, cfrRec_specW p h.rp.alloc h.frec n, callW_spec p n "env_push",
        rec3_specW p h.ia n h.rec3, slCons_specW p h.ia h.copy h.cons n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, loc_init4, loc_init5, loc_init6]

theorem classFeR_spec (p : Prog) (h : CfrProg p) (n : Nat) (s₀ : St) (pp cgo cgl rco rcl vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fe_r" [pp, cgo, cgl, rco, rcl, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ ferAW p n s₀.mem pp cgo cgl rco rcl vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.top]
  simp only [callFn, classFeRL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, classFeRGo_spec p h n] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5]

end L.Ind
