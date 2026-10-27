import ConAgua.Arena.RecCheckSpec.TruncSl

/-!
# Tmn

`ctorsHaveName_spec`, `tmnK4`, `tmnK3`, `tmnK2`, `tmnK1`, `tmnW` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem ctorsHaveName_spec (p : Prog) (hp : p.lookup "ctors_have_name" = some ctorsHaveName) (n : Nat) :
    ∀ (s₀ : St) (co cl name : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ctors_have_name" [co, cl, name]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ chnW n s₀.mem co cl name = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ co cl name; rw [invoke_eq _ hp]; simp only [callFn, ctorsHaveName]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ co cl name
    rw [invoke_eq _ hp]
    simp only [callFn, ctorsHaveName]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)

end L.Ind

end

end

section

noncomputable section

/-!
# `RecCheck`: `targetMajorNfs` (lane `indproofs3`, helper `rec`)

The walk's recorded constructor normal forms of a class. L (D18): the loop became the twin's list
recursion (the tail first, so the class-match calls fire from the last entry to the first), each
kept entry `sl_cons`ed onto the kept tail (a copy, so the result is a pointer slice decoded below
the tops). Callees: `ctors_have_name` (helper `recb`'s `chnW`), `target_class_match`
(`RecCheckSpec12`), `sl_cons`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

def tmnK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m) => some ([rc.headD 0, rc.tail.headD 0], m)

def tmnK3 (_cR : CallM) (n : Nat) (rr : List Word) (e : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rk, m) =>
    if rk.headD 0 = 0 then some ([rr.headD 0, rr.tail.headD 0], m)
    else tmnK4 (consW n m e (rr.headD 0) (rr.tail.headD 0))

def tmnK2 (cR : CallM) (n : Nat) (vis q fto ftl pfo pfl us dso dsl : Word) (rr : List Word) (m : Mem) (e : Word) :
    Option Word → Option (List Word × Mem)
  | none => none
  | some hv =>
    if hv = 0 then some ([rr.headD 0, rr.tail.headD 0], m)
    else tmnK3 cR n rr e (tcmF cR n m vis q fto ftl pfo pfl us dso dsl (rdW (m.arr64 IW) (e + 1))
      (rdW (m.arr64 IW) (e + 2)) (rdW (m.arr64 IW) (e + 3)))

def tmnK1 (cR : CallM) (n : Nat) (vis q fto ftl pfo pfl us dso dsl cto ctl nfo : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m) => tmnK2 cR n vis q fto ftl pfo pfl us dso dsl rr m (rdW (m.arr64 IW) nfo)
      (chnW n m cto ctl (rdW (m.arr64 IW) (rdW (m.arr64 IW) nfo)))

/-- **The model of `target_major_nfs`** (exec fuel). -/
def tmnW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl =>
    if nfl = 0 then some ([0, 0], m)
    else tmnK1 cR n vis q fto ftl pfo pfl us dso dsl cto ctl nfo
      (tmnW cR n m vis q fto ftl pfo pfl us dso dsl cto ctl (nfo + 1) (nfl - 1))

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl e hv : Word) (rr rk rc : List Word)
theorem tmnK4_some : tmnK4 (some (rc, m)) = some ([rc.headD 0, rc.tail.headD 0], m) := rfl
theorem tmnK3_drop (h : rk.headD 0 = 0) : tmnK3 cR n rr e (some (rk, m)) = some ([rr.headD 0, rr.tail.headD 0], m) := by
  simp only [tmnK3]; rw [ite_eq_left h]
theorem tmnK3_keep (h : ¬ rk.headD 0 = 0) : tmnK3 cR n rr e (some (rk, m)) =
    tmnK4 (consW n m e (rr.headD 0) (rr.tail.headD 0)) := by simp only [tmnK3]; rw [ite_eq_right h]
theorem tmnK2_no (h : hv = 0) : tmnK2 cR n vis q fto ftl pfo pfl us dso dsl rr m e (some hv) =
    some ([rr.headD 0, rr.tail.headD 0], m) := by simp only [tmnK2]; rw [ite_eq_left h]
theorem tmnK2_yes (h : ¬ hv = 0) : tmnK2 cR n vis q fto ftl pfo pfl us dso dsl rr m e (some hv) =
    tmnK3 cR n rr e (tcmF cR n m vis q fto ftl pfo pfl us dso dsl (rdW (m.arr64 IW) (e + 1))
      (rdW (m.arr64 IW) (e + 2)) (rdW (m.arr64 IW) (e + 3))) := by simp only [tmnK2]; rw [ite_eq_right h]
theorem tmnK1_some : tmnK1 cR n vis q fto ftl pfo pfl us dso dsl cto ctl nfo (some (rr, m)) =
    tmnK2 cR n vis q fto ftl pfo pfl us dso dsl rr m (rdW (m.arr64 IW) nfo)
      (chnW n m cto ctl (rdW (m.arr64 IW) (rdW (m.arr64 IW) nfo))) := rfl
theorem tmnW_nil (h : nfl = 0) : tmnW cR (n + 1) m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl = some ([0, 0], m) := by
  simp [tmnW, h]
theorem tmnW_cons (h : ¬ nfl = 0) : tmnW cR (n + 1) m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl =
    tmnK1 cR n vis q fto ftl pfo pfl us dso dsl cto ctl nfo
      (tmnW cR n m vis q fto ftl pfo pfl us dso dsl cto ctl (nfo + 1) (nfl - 1)) := by simp [tmnW, h]
end arms
attribute [ind_grind] tmnK4_some tmnK3_drop tmnK3_keep tmnK2_no tmnK2_yes tmnK1_some tmnW_nil tmnW_cons

theorem tmn_spec (p : Prog) (L : TmnLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) :
    ∀ (s₀ : St) (vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_nfs"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl]
    ⦃fun r s' => LocEq s' s₀ ∧
      tmnW cR n s₀.mem vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl
    rw [invoke_eq _ L.tmn]; simp only [callFn, targetMajorNfs]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl
    rw [invoke_eq _ L.tmn]
    simp only [callFn, targetMajorNfs]
    sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        ctorsHaveName_spec p L.chn n, tcmF_spec p L.tcm cR hcR n,
        slCons_specW p L.tcm.ha L.tcm.ic L.tcm.sc n] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8,
        loc_init9, loc_init10, loc_init11, loc_init12]

end L.Ind

end
end

end
