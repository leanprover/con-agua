import ConAgua.Arena.RecClassSpecE

/-!
# `RecClass`: `classReadSlot`, `classReadSlots` (lane `indproofs2`, helper `rec`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Models -/

section models
variable (n : Nat) (p vis : Word)

def sK6 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => some ([1, r6.headD 0], m6)

def sK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => sK6 (recW m5 2 [0, r5.headD 0])

def sK4 (iName us ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => sK5 (recW m4 4 [iName, us, ao, if r4.headD 0 < al then r4.headD 0 else al])

def sK3 (iName us : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => sK4 iName us (r3.headD 0) (r3.tail.headD 0) (npcW n m3 p vis iName)

def sK2 (mdom : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 >>> 28 ≠ 3 then some ([0, 0], m2)
    else if eViewW m2 (r2.headD 0) = [] then none
    else sK3 n p vis ((eViewW m2 (r2.headD 0)).tail.headD 0)
      ((eViewW m2 (r2.headD 0)).tail.tail.headD 0) (stubM "get_app_args" m2 [CWF, mdom])

def sK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.tail.headD 0 = 0 then some ([0, 0], m1)
    else sK2 n p vis (rdW (m1.arr64 IW) (r1.headD 0 + r1.tail.headD 0 - 1))
      (stubM "get_app_fn" m1 [CWF, rdW (m1.arr64 IW) (r1.headD 0 + r1.tail.headD 0 - 1)])

end models

/-- **The model of `class_read_slot_motive`.** -/
def slotMotW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, p, vis, dom => sK1 n p vis (piBW n m CWF dom)

def slK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

def slK1 (n : Nat) (p vis np mo ml d dom : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 >>> 28 = 2 then slK2 (slotMotW n m1 p vis dom)
    else slK2 (minorW n m1 np mo ml d dom)

/-- **The model of `class_read_slot`.** -/
def slotW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, p, vis, np, mo, ml, d, dom => slK1 n p vis np mo ml d dom (stubM "pi_result" m [CWF, dom])

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (p vis np mo ml d dom mdom iName us ao al : Word)
  (r r1 r2 r3 r4 r5 r6 : List Word)
theorem slotMotW_eq : slotMotW (n + 1) m p vis dom = sK1 n p vis (piBW n m CWF dom) := rfl
theorem sK1_nil (h : r1.tail.headD 0 = 0) : sK1 n p vis (some (r1, m1)) = some ([0, 0], m1) := by
  rw [sK1, if_pos h]
theorem sK1_ok (h : r1.tail.headD 0 ≠ 0) : sK1 n p vis (some (r1, m1)) =
    sK2 n p vis (rdW (m1.arr64 IW) (r1.headD 0 + r1.tail.headD 0 - 1))
      (stubM "get_app_fn" m1 [CWF, rdW (m1.arr64 IW) (r1.headD 0 + r1.tail.headD 0 - 1)]) := by
  rw [sK1, if_neg h]
theorem sK2_tag (h : r2.headD 0 >>> 28 ≠ 3) : sK2 n p vis mdom (some (r2, m2)) = some ([0, 0], m2) := by
  rw [sK2, if_pos h]
theorem sK2_nil (h : ¬ r2.headD 0 >>> 28 ≠ 3) (h2 : eViewW m2 (r2.headD 0) = []) :
    sK2 n p vis mdom (some (r2, m2)) = none := by rw [sK2, if_neg h, if_pos h2]
theorem sK2_ok (h : ¬ r2.headD 0 >>> 28 ≠ 3) (h2 : eViewW m2 (r2.headD 0) ≠ []) :
    sK2 n p vis mdom (some (r2, m2)) = sK3 n p vis ((eViewW m2 (r2.headD 0)).tail.headD 0)
      ((eViewW m2 (r2.headD 0)).tail.tail.headD 0) (stubM "get_app_args" m2 [CWF, mdom]) := by
  rw [sK2, if_neg h, if_neg h2]
theorem sK3_some : sK3 n p vis iName us (some (r3, m3)) =
    sK4 iName us (r3.headD 0) (r3.tail.headD 0) (npcW n m3 p vis iName) := rfl
theorem sK4_some : sK4 iName us ao al (some (r4, m4)) =
    sK5 (recW m4 4 [iName, us, ao, if r4.headD 0 < al then r4.headD 0 else al]) := rfl
theorem sK5_some : sK5 (some (r5, m5)) = sK6 (recW m5 2 [0, r5.headD 0]) := rfl
theorem sK6_some : sK6 (some (r6, m6)) = some ([1, r6.headD 0], m6) := rfl
theorem slotW_eq : slotW (n + 1) m p vis np mo ml d dom =
    slK1 n p vis np mo ml d dom (stubM "pi_result" m [CWF, dom]) := rfl
theorem slK1_mot (h : r1.headD 0 >>> 28 = 2) : slK1 n p vis np mo ml d dom (some (r1, m1)) =
    slK2 (slotMotW n m1 p vis dom) := by rw [slK1, if_pos h]
theorem slK1_min (h : ¬ r1.headD 0 >>> 28 = 2) : slK1 n p vis np mo ml d dom (some (r1, m1)) =
    slK2 (minorW n m1 np mo ml d dom) := by rw [slK1, if_neg h]
theorem slK2_some : slK2 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] slotMotW_eq => slotMotW (n + 1) m p vis dom
grind_pattern [ind_grind] sK1_nil => sK1 n p vis (some (r1, m1))
grind_pattern [ind_grind] sK1_ok => sK1 n p vis (some (r1, m1))
grind_pattern [ind_grind] sK2_tag => sK2 n p vis mdom (some (r2, m2))
grind_pattern [ind_grind] sK2_nil => sK2 n p vis mdom (some (r2, m2))
grind_pattern [ind_grind] sK2_ok => sK2 n p vis mdom (some (r2, m2))
grind_pattern [ind_grind] sK3_some => sK3 n p vis iName us (some (r3, m3))
grind_pattern [ind_grind] sK4_some => sK4 iName us ao al (some (r4, m4))
grind_pattern [ind_grind] sK5_some => sK5 (some (r5, m5))
grind_pattern [ind_grind] sK6_some => sK6 (some (r6, m6))
grind_pattern [ind_grind] slotW_eq => slotW (n + 1) m p vis np mo ml d dom
grind_pattern [ind_grind] slK1_mot => slK1 n p vis np mo ml d dom (some (r1, m1))
grind_pattern [ind_grind] slK1_min => slK1 n p vis np mo ml d dom (some (r1, m1))
grind_pattern [ind_grind] slK2_some => slK2 (some (r, m))

/-- The lookups `class_read_slot` needs. -/
structure SlotProg (p : Prog) : Prop where
  fh : p.lookup "fvar_head" = some fvarHead
  v : p.lookup "e_view" = some eView
  f : p.lookup "sl_find" = some slFind
  cm : p.lookup "class_of_motive_var" = some classOfMotiveVar
  c : p.lookup "iw_copy" = some iwCopy
  a : p.lookup "iw_alloc" = some iwAlloc
  sc : p.lookup "sl_cons" = some slCons
  r2 : p.lookup "rec2" = some rec2
  r4 : p.lookup "rec4" = some rec4
  r5 : p.lookup "rec5" = some rec5
  i1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1
  is : p.lookup "class_read_minor_ihs" = some classReadMinorIhs
  fin : p.lookup "class_read_minor_finish" = some classReadMinorFinish
  pb : p.lookup "pi_binders" = some piBinders
  min : p.lookup "class_read_minor" = some classReadMinor
  tl : p.lookup "class_read_minor_tail" = some classReadMinorTail
  mc : p.lookup "member_names_copy" = some memberNamesCopy
  mn : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  ct : p.lookup "sl_contains" = some slContains
  x : p.lookup "env_ix" = some envIxL
  g : p.lookup "env_row_get" = some envRowGetL
  ef : p.lookup "env_find" = some envFindL
  npc : p.lookup "class_n_pc_of" = some classNPcOf
  smot : p.lookup "class_read_slot_motive" = some classReadSlotMotive
  slot : p.lookup "class_read_slot" = some classReadSlot

theorem classReadSlotMotive_spec (p : Prog) (hP : SlotProg p) (n : Nat) (s₀ : St) (q vis dom : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_slot_motive" [q, vis, dom]
    ⦃fun r s' => LocEq s' s₀ ∧ slotMotW n s₀.mem q vis dom = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.smot]; simp only [callFn, classReadSlotMotive]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        piBinders_spec' p hP.a hP.c hP.v hP.sc hP.pb n, stubM_spec p "get_app_fn" n,
        stubM_spec p "get_app_args" n, eView_spec p hP.v n,
        classNPcOf_spec p hP.a hP.mc hP.mn hP.ct hP.x hP.g hP.ef hP.npc n,
        rec4_specW p hP.a n hP.r4, rec2_specW p hP.a n hP.r2] <;>
      finish (gen := 20) [rdW_eq]

theorem classReadSlot_spec (p : Prog) (hP : SlotProg p) (n : Nat) (s₀ : St)
    (q vis np mo ml d dom : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_slot" [q, vis, np, mo, ml, d, dom]
    ⦃fun r s' => LocEq s' s₀ ∧ slotW n s₀.mem q vis np mo ml d dom = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.slot]; simp only [callFn, classReadSlot]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "pi_result" n, classReadSlotMotive_spec p hP n,
        classReadMinor_spec p hP.fh hP.v hP.f hP.cm hP.c hP.a hP.sc hP.r2 hP.r5 hP.i1 hP.is hP.fin
          hP.pb hP.min hP.tl n] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6]

end L.Ind
