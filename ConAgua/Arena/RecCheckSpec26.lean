import ConAgua.Arena.RecCheckSpec25

/-!
# `RecCheck`: `targetMajorOf`'s MEMBER branch (lane `indproofs3`, helper `rec2`)

`target_major_of_member`: the member at the block's levels and parameters.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `target_major_of_member`. -/
structure TmmLook (p : Prog) : Prop where
  tcm : TcmLook p
  eq : p.lookup "sl_eq" = some slEq
  mkt : p.lookup "mk_target_major" = some mkTargetMajor
  tmm : p.lookup "target_major_of_member" = some targetMajorOfMember

/-! ## The model -/

def tmmK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

def tmmK2 (n : Nat) (ao al fvo fvl I us nP nidx co cl t pfo pfl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m) =>
    match eqW n m ao (if nP < al then nP else al) fvo (if nP < fvl then nP else fvl) with
    | none => none
    | some e =>
      if us ≠ rb.headD 0 then none
      else if e = 0 then none
      else tmmK3 (mkTMW m I us fvo (if nP < fvl then nP else fvl) nP nidx co cl (t + 1) 0 0 pfo pfl)

def tmmK1 (n : Nat) (ao al fvo fvl I us nP nidx co cl t pfo pfl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rl, m) => tmmK2 n ao al fvo fvl I us nP nidx co cl t pfo pfl (plW n m (rl.headD 0) (rl.tail.headD 0))

/-- **The model of `target_major_of_member`** (body fuel `n`). -/
def tmmW (n : Nat) (m : Mem) (pp cao cal pfo pfl fvo fvl ao al I us t : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 IW) (pp + 1) ≤ t then none
  else if cal ≤ t then none
  else tmmK1 n ao al fvo fvl I us (rdW (m.arr64 IW) (pp + 4))
    (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) pp + t) + 1))
    (rdW (m.arr64 IW) (rdW (m.arr64 IW) (cao + t))) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (cao + t) + 1)) t pfo pfl
    (lpsW n m pp)

section arms
variable (n : Nat) (m : Mem) (ao al fvo fvl I us nP nidx co cl t pfo pfl : Word) (r rb rl : List Word)
theorem tmmK3_some : tmmK3 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem tmmK1_some : tmmK1 n ao al fvo fvl I us nP nidx co cl t pfo pfl (some (rl, m)) =
    tmmK2 n ao al fvo fvl I us nP nidx co cl t pfo pfl (plW n m (rl.headD 0) (rl.tail.headD 0)) := rfl
theorem tmmK2_some : tmmK2 n ao al fvo fvl I us nP nidx co cl t pfo pfl (some (rb, m)) =
    match eqW n m ao (if nP < al then nP else al) fvo (if nP < fvl then nP else fvl) with
    | none => none
    | some e =>
      if us ≠ rb.headD 0 then none
      else if e = 0 then none
      else tmmK3 (mkTMW m I us fvo (if nP < fvl then nP else fvl) nP nidx co cl (t + 1) 0 0 pfo pfl) := rfl
end arms
attribute [ind_grind] tmmK3_some tmmK1_some tmmK2_some

set_option maxHeartbeats 1600000 in
theorem tmm_spec (p : Prog) (L : TmmLook p) (n : Nat) (s₀ : St) (pp cao cal pfo pfl fvo fvl ao al I us t : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_major_of_member"
      [pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, I, us, t]
    ⦃fun r s' => LocEq s' s₀ ∧ tmmW n s₀.mem pp cao cal pfo pfl fvo fvl ao al I us t = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.tmm]
  simp only [callFn, targetMajorOfMember]
  sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      blockShapeLps_spec p L.tcm.ha L.tcm.erc L.tcm.eri L.tcm.lps n,
      plW_spec p L.tcm.ha L.tcm.ic L.tcm.sc L.tcm.sg L.tcm.pf L.tcm.pp L.tcm.ip L.tcm.plg L.tcm.pl n,
      slEq_spec p L.eq n, mkTargetMajor_spec p L.tcm.ha L.mkt n] <;>
    finish (gen := 40) (instances := 20000) [tmmW, rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7,
      loc_init8, loc_init9, loc_init10, loc_init11, loc_init12]

end L.Ind
