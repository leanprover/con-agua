import ConAgua.Verdict.PosE3Fm

/-!
# `nest_ctors`' error model (lane `verdicts-b`, helper `ia2`, fork `kn2b`)

The generator's `errors` model with the recursive call through `callE` (as `PosE3Fm.lean`); its
spec by hand.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace L.Ind

open L.Arena

def ncE.k_nest_ctors (p : Prog) : Except L.Err (List L.Word × L.Mem) → Except L.Err (List L.Word × L.Mem)
  | Except.error ε => Except.error ε
  | Except.ok (r, m₁) =>
    Except.ok ([(List.headD r 0), (List.headD (List.tail r) 0), (List.headD (List.tail (List.tail r)) 0)], (m₁))
def ncE.k_sl_snoc (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (root : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (hi : L.Word) (us : L.Word) (dsOff : L.Word) (dsLen : L.Word)
    (namesOff : L.Word) (namesLen : L.Word) (holesOff : L.Word) (holesLen : L.Word) (csOff : L.Word)
    (csLen : L.Word) (ns2 : L.Word) :
    Except L.Err (List L.Word × L.Mem) → Except L.Err (List L.Word × L.Mem)
  | Except.error ε => Except.error ε
  | Except.ok (r, m₁) =>
    (ncE.k_nest_ctors (p)
      (L.callE p n "nest_ctors"
        [(vis), (ctx), (root), (fuel), (progOff), (progLen), (hi), (us), (dsOff), (dsLen), (namesOff), (namesLen),
          (holesOff), (holesLen), ((csOff) + (1 : L.Word)), ((csLen) - (1 : L.Word)), (ns2), (List.headD r 0),
          (List.headD (List.tail r) 0)]
        (m₁)))
def ncE.k_rec3 (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (root : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (hi : L.Word) (us : L.Word) (dsOff : L.Word) (dsLen : L.Word)
    (namesOff : L.Word) (namesLen : L.Word) (holesOff : L.Word) (holesLen : L.Word) (csOff : L.Word)
    (csLen : L.Word) (outsOff : L.Word) (outsLen : L.Word) (ns2 : L.Word) :
    Except L.Err (List L.Word × L.Mem) → Except L.Err (List L.Word × L.Mem)
  | Except.error ε => Except.error ε
  | Except.ok (r, m₁) =>
    (ncE.k_sl_snoc (p) (n) (vis) (ctx) (root) (fuel) (progOff) (progLen) (hi) (us) (dsOff) (dsLen) (namesOff) (namesLen)
      (holesOff) (holesLen) (csOff) (csLen) (ns2)
      (L.callE p n "sl_snoc" [(outsOff), (outsLen), (List.headD r 0)] (m₁)))
def ncE.k_nest_ctors_one (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (root : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (hi : L.Word) (us : L.Word) (dsOff : L.Word) (dsLen : L.Word)
    (namesOff : L.Word) (namesLen : L.Word) (holesOff : L.Word) (holesLen : L.Word) (csOff : L.Word)
    (csLen : L.Word) (outsOff : L.Word) (outsLen : L.Word) :
    Except L.Err (List L.Word × L.Mem) → Except L.Err (List L.Word × L.Mem)
  | Except.error ε => Except.error ε
  | Except.ok (r, m₁) =>
    (ncE.k_rec3 (p) (n) (vis) (ctx) (root) (fuel) (progOff) (progLen) (hi) (us) (dsOff) (dsLen) (namesOff) (namesLen)
      (holesOff) (holesLen) (csOff) (csLen) (outsOff) (outsLen) (List.headD (List.tail (List.tail (List.tail r))) 0)
      (L.callE p n "rec3"
        [(List.headD r 0), (List.headD (List.tail r) 0), (List.headD (List.tail (List.tail r)) 0)] (m₁)))
def ncE (p : Prog) (n : Nat) (m : L.Mem) (vis : L.Word) (ctx : L.Word) (root : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (hi : L.Word) (us : L.Word) (dsOff : L.Word) (dsLen : L.Word)
    (namesOff : L.Word) (namesLen : L.Word) (holesOff : L.Word) (holesLen : L.Word) (csOff : L.Word)
    (csLen : L.Word) (ns : L.Word) (outsOff : L.Word) (outsLen : L.Word) :
    Except L.Err (List L.Word × L.Mem) :=
  match n with
  | 0 => Except.error L.Err.outOfFuel
  | n + 1 =>
    if (csLen) = 0 then Except.ok ([(outsOff), (outsLen), (ns)], (m))
    else
      (ncE.k_nest_ctors_one (p) (n) (vis) (ctx) (root) (fuel) (progOff) (progLen) (hi) (us) (dsOff) (dsLen) (namesOff)
        (namesLen) (holesOff) (holesLen) (csOff) (csLen) (outsOff) (outsLen)
        (L.callE p n "nest_ctors_one"
          [(vis), (ctx), (root), (fuel), (progOff), (progLen), (hi), (us), (dsOff), (dsLen), (namesOff), (namesLen),
            (holesOff), (holesLen), (rdW (L.Mem.arr64 (m) IW) (rdW (L.Mem.arr64 (m) IW) (csOff))),
            (rdW (L.Mem.arr64 (m) IW) ((rdW (L.Mem.arr64 (m) IW) (csOff)) + (1 : L.Word))), (ns)]
          (m)))
theorem ncE.arm1 (p : Prog) (n : Nat) (m : L.Mem) (vis : L.Word) (ctx : L.Word) (root : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (hi : L.Word) (us : L.Word) (dsOff : L.Word) (dsLen : L.Word)
    (namesOff : L.Word) (namesLen : L.Word) (holesOff : L.Word) (holesLen : L.Word) (csOff : L.Word)
    (csLen : L.Word) (ns : L.Word) (outsOff : L.Word) (outsLen : L.Word) (hc1 : (csLen) = 0) :
    ncE p (n + 1) m vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff csLen
        ns outsOff outsLen =
      Except.ok ([(outsOff), (outsLen), (ns)], (m)) :=
  by rw [ncE.eq_2, ite_eq_left hc1]
grind_pattern [arena_grind]ncE.arm1 =>
  ncE p (n + 1) m vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff csLen ns
    outsOff outsLen
theorem ncE.arm2 (p : Prog) (n : Nat) (m : L.Mem) (vis : L.Word) (ctx : L.Word) (root : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (hi : L.Word) (us : L.Word) (dsOff : L.Word) (dsLen : L.Word)
    (namesOff : L.Word) (namesLen : L.Word) (holesOff : L.Word) (holesLen : L.Word) (csOff : L.Word)
    (csLen : L.Word) (ns : L.Word) (outsOff : L.Word) (outsLen : L.Word) (hc1 : (csLen) ≠ 0) :
    ncE p (n + 1) m vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff csLen
        ns outsOff outsLen =
      (ncE.k_nest_ctors_one (p) (n) (vis) (ctx) (root) (fuel) (progOff) (progLen) (hi) (us) (dsOff) (dsLen) (namesOff)
        (namesLen) (holesOff) (holesLen) (csOff) (csLen) (outsOff) (outsLen)
        (L.callE p n "nest_ctors_one"
          [(vis), (ctx), (root), (fuel), (progOff), (progLen), (hi), (us), (dsOff), (dsLen), (namesOff), (namesLen),
            (holesOff), (holesLen), (rdW (L.Mem.arr64 (m) IW) (rdW (L.Mem.arr64 (m) IW) (csOff))),
            (rdW (L.Mem.arr64 (m) IW) ((rdW (L.Mem.arr64 (m) IW) (csOff)) + (1 : L.Word))), (ns)]
          (m))) :=
  by rw [ncE.eq_2, ite_eq_right hc1]
grind_pattern [arena_grind]ncE.arm2 =>
  ncE p (n + 1) m vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff csLen ns
    outsOff outsLen
theorem ncE.k_nest_ctors.arm1 (p : Prog) (r : List L.Word) (m₁ : L.Mem) :
    ncE.k_nest_ctors p (Except.ok (r, m₁)) =
      Except.ok
        ([(List.headD r 0), (List.headD (List.tail r) 0), (List.headD (List.tail (List.tail r)) 0)], (m₁)) :=
  by rw [ncE.k_nest_ctors.eq_2]
grind_pattern [arena_grind]ncE.k_nest_ctors.arm1 => ncE.k_nest_ctors p (Except.ok (r, m₁))
theorem ncE.k_nest_ctors.none (p : Prog) (ε : L.Err) : ncE.k_nest_ctors p (Except.error ε) = Except.error ε := by
  rw [ncE.k_nest_ctors.eq_1]
grind_pattern [arena_grind]ncE.k_nest_ctors.none => ncE.k_nest_ctors p (Except.error ε)
theorem ncE.k_sl_snoc.arm1 (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (root : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (hi : L.Word) (us : L.Word) (dsOff : L.Word) (dsLen : L.Word)
    (namesOff : L.Word) (namesLen : L.Word) (holesOff : L.Word) (holesLen : L.Word) (csOff : L.Word)
    (csLen : L.Word) (ns2 : L.Word) (r : List L.Word) (m₁ : L.Mem) :
    ncE.k_sl_snoc p n vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff
        csLen ns2 (Except.ok (r, m₁)) =
      (ncE.k_nest_ctors (p)
        (L.callE p n "nest_ctors"
          [(vis), (ctx), (root), (fuel), (progOff), (progLen), (hi), (us), (dsOff), (dsLen), (namesOff), (namesLen),
            (holesOff), (holesLen), ((csOff) + (1 : L.Word)), ((csLen) - (1 : L.Word)), (ns2), (List.headD r 0),
            (List.headD (List.tail r) 0)]
          (m₁))) :=
  by rw [ncE.k_sl_snoc.eq_2]
grind_pattern [arena_grind]ncE.k_sl_snoc.arm1 =>
  ncE.k_sl_snoc p n vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff csLen
    ns2 (Except.ok (r, m₁))
theorem ncE.k_sl_snoc.none (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (root : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (hi : L.Word) (us : L.Word) (dsOff : L.Word) (dsLen : L.Word)
    (namesOff : L.Word) (namesLen : L.Word) (holesOff : L.Word) (holesLen : L.Word) (csOff : L.Word)
    (csLen : L.Word) (ns2 : L.Word) (ε : L.Err) :
    ncE.k_sl_snoc p n vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff
        csLen ns2 (Except.error ε) =
      Except.error ε :=
  by rw [ncE.k_sl_snoc.eq_1]
grind_pattern [arena_grind]ncE.k_sl_snoc.none =>
  ncE.k_sl_snoc p n vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff csLen
    ns2 (Except.error ε)
theorem ncE.k_rec3.arm1 (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (root : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (hi : L.Word) (us : L.Word) (dsOff : L.Word) (dsLen : L.Word)
    (namesOff : L.Word) (namesLen : L.Word) (holesOff : L.Word) (holesLen : L.Word) (csOff : L.Word)
    (csLen : L.Word) (outsOff : L.Word) (outsLen : L.Word) (ns2 : L.Word) (r : List L.Word) (m₁ : L.Mem) :
    ncE.k_rec3 p n vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff csLen
        outsOff outsLen ns2 (Except.ok (r, m₁)) =
      (ncE.k_sl_snoc (p) (n) (vis) (ctx) (root) (fuel) (progOff) (progLen) (hi) (us) (dsOff) (dsLen) (namesOff)
        (namesLen) (holesOff) (holesLen) (csOff) (csLen) (ns2)
        (L.callE p n "sl_snoc" [(outsOff), (outsLen), (List.headD r 0)] (m₁))) :=
  by rw [ncE.k_rec3.eq_2]
grind_pattern [arena_grind]ncE.k_rec3.arm1 =>
  ncE.k_rec3 p n vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff csLen
    outsOff outsLen ns2 (Except.ok (r, m₁))
theorem ncE.k_rec3.none (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (root : L.Word) (fuel : L.Word)
    (progOff : L.Word) (progLen : L.Word) (hi : L.Word) (us : L.Word) (dsOff : L.Word) (dsLen : L.Word)
    (namesOff : L.Word) (namesLen : L.Word) (holesOff : L.Word) (holesLen : L.Word) (csOff : L.Word)
    (csLen : L.Word) (outsOff : L.Word) (outsLen : L.Word) (ns2 : L.Word) (ε : L.Err) :
    ncE.k_rec3 p n vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff csLen
        outsOff outsLen ns2 (Except.error ε) =
      Except.error ε :=
  by rw [ncE.k_rec3.eq_1]
grind_pattern [arena_grind]ncE.k_rec3.none =>
  ncE.k_rec3 p n vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff csLen
    outsOff outsLen ns2 (Except.error ε)
theorem ncE.k_nest_ctors_one.arm1 (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (root : L.Word)
    (fuel : L.Word) (progOff : L.Word) (progLen : L.Word) (hi : L.Word) (us : L.Word) (dsOff : L.Word)
    (dsLen : L.Word) (namesOff : L.Word) (namesLen : L.Word) (holesOff : L.Word) (holesLen : L.Word)
    (csOff : L.Word) (csLen : L.Word) (outsOff : L.Word) (outsLen : L.Word) (r : List L.Word) (m₁ : L.Mem) :
    ncE.k_nest_ctors_one p n vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen
        csOff csLen outsOff outsLen (Except.ok (r, m₁)) =
      (ncE.k_rec3 (p) (n) (vis) (ctx) (root) (fuel) (progOff) (progLen) (hi) (us) (dsOff) (dsLen) (namesOff) (namesLen)
        (holesOff) (holesLen) (csOff) (csLen) (outsOff) (outsLen)
        (List.headD (List.tail (List.tail (List.tail r))) 0)
        (L.callE p n "rec3"
          [(List.headD r 0), (List.headD (List.tail r) 0), (List.headD (List.tail (List.tail r)) 0)] (m₁))) :=
  by rw [ncE.k_nest_ctors_one.eq_2]
grind_pattern [arena_grind]ncE.k_nest_ctors_one.arm1 =>
  ncE.k_nest_ctors_one p n vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff
    csLen outsOff outsLen (Except.ok (r, m₁))
theorem ncE.k_nest_ctors_one.none (p : Prog) (n : Nat) (vis : L.Word) (ctx : L.Word) (root : L.Word)
    (fuel : L.Word) (progOff : L.Word) (progLen : L.Word) (hi : L.Word) (us : L.Word) (dsOff : L.Word)
    (dsLen : L.Word) (namesOff : L.Word) (namesLen : L.Word) (holesOff : L.Word) (holesLen : L.Word)
    (csOff : L.Word) (csLen : L.Word) (outsOff : L.Word) (outsLen : L.Word) (ε : L.Err) :
    ncE.k_nest_ctors_one p n vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen
        csOff csLen outsOff outsLen (Except.error ε) =
      Except.error ε :=
  by rw [ncE.k_nest_ctors_one.eq_1]
grind_pattern [arena_grind]ncE.k_nest_ctors_one.none =>
  ncE.k_nest_ctors_one p n vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff
    csLen outsOff outsLen (Except.error ε)

theorem ncE_spec (p : Prog) (hf : p.lookup "nest_ctors" = some nestCtorsL) (n : Nat) (s₀ : St)
    (vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff csLen ns outsOff
      outsLen : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors"
      [vis, ctx, root, fuel, progOff, progLen, hi, us, dsOff, dsLen, namesOff, namesLen, holesOff, holesLen, csOff,
        csLen, ns, outsOff, outsLen]
    ⦃fun r s' => LocEq s' s₀ ∧
      ncE p n s₀.mem vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff csLen
        ns outsOff outsLen = .ok (r, s'.mem);
     fun ε => ε.code ≠ 0 →
      ncE p n s₀.mem vis ctx root fuel progOff progLen hi us dsOff dsLen namesOff namesLen holesOff holesLen csOff csLen
        ns outsOff outsLen = .error ε⦄ := by
  cases n with
  | zero =>
    rw [_root_.L.invoke_eq _ (hf)]; simp only [_root_.L.callFn, _root_.L.Ind.nestCtorsL]
    vcgen [_root_.L.exec] <;> grind
  | succ n =>
    rw [_root_.L.invoke_eq _ (hf)]; simp only [_root_.L.callFn, _root_.L.Ind.nestCtorsL]
    vcgen [_root_.L.exec, _root_.L.step, _root_.L.evalE, _root_.L.evalC, _root_.L.evalArgs, _root_.L.setLoc,
            _root_.L.setLocs, _root_.L.ld8_specE, _root_.L.st64, _root_.L.setG, ld64_rdW_specE, evalE_tld, tld,
            evalE_cnt, tcntM, evalE_tierE, evalE_idxE, callE_spec p n "nest_ctors",
            _root_.L.callE_spec p n "nest_ctors_one", _root_.L.callE_spec p n "rec3", _root_.L.callE_spec p n "sl_snoc"] <;>
          (try
              simp_all [_root_.L.LocEq, _root_.L.St.setLoc_loc, _root_.L.St.setLoc_mem, _root_.L.St.setLocs_nil,
                _root_.L.St.setLocs_cons, _root_.L.Locals.init_nil, _root_.L.Locals.init_cons_zero,
                _root_.L.Locals.init_cons_succ, _root_.L.Sig.retVal, _root_.L.Sig.retOr, _root_.L.BinOp.eval,
                _root_.L.Cmp.eval, List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil, ncE,
                ncE.k_nest_ctors, ncE.k_sl_snoc, ncE.k_rec3, ncE.k_nest_ctors_one]) <;>
        grind [lang_grind, arena_grind]

l_model nwE_spec (p : Prog) (hf : p.lookup "nest_ctors_walk" = some nestCtorsWalkL)
  fns [hf ↦ nwE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model ncrE_spec (p : Prog) (hf : p.lookup "nest_ctors_crest" = some nestCtorsCrestL)
  fns [hf ↦ ncrE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model noE_spec (p : Prog) (hf : p.lookup "nest_ctors_one" = some nestCtorsOneL)
  fns [hf ↦ noE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

end L.Ind
