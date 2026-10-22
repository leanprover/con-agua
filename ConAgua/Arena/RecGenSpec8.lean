import ConAgua.Arena.RecGenSpec7

/-!
# `RecGen`: `classRecTysOk` (lane `indproofs2`, helper `rec2`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The model -/

def rtsK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([r3.headD 0, r3.tail.headD 0], m3)

def rtsK2 (n : Nat) (x : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => rtsK3 (consW n m2 x (r2.headD 0) (r2.tail.headD 0))

mutual
/-- **The model of `class_rec_tys_ok`.** -/
def rtsW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, g, k, ro, rl, vo, vl, co, cl =>
    if rl = 0 then some ([0, 0], m)
    else if vl = 0 ∨ cl = 0 then none
    else rtsK1 n vis g k ro rl vo vl co cl
      (rtoW n m vis g k (rdW (m.arr64 IW) ro) (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co))
def rtsK1 (n : Nat) (vis g k ro rl vo vl co cl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    rtsK2 n (r1.headD 0) (rtsW n m1 vis g k (ro + 1) (rl - 1) (vo + 1) (vl - 1) (co + 1) (cl - 1))
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (vis g k ro rl vo vl co cl x : Word) (r1 r2 r3 : List Word)
theorem rtsW_nil (h : rl = 0) : rtsW (n + 1) m vis g k ro rl vo vl co cl = some ([0, 0], m) := by
  simp [rtsW, h]
theorem rtsW_short (h : ¬ rl = 0) (h2 : vl = 0 ∨ cl = 0) : rtsW (n + 1) m vis g k ro rl vo vl co cl = none := by
  simp only [rtsW]; rw [if_neg h, if_pos h2]
theorem rtsW_cons (h : ¬ rl = 0) (h2 : ¬ (vl = 0 ∨ cl = 0)) : rtsW (n + 1) m vis g k ro rl vo vl co cl =
    rtsK1 n vis g k ro rl vo vl co cl
      (rtoW n m vis g k (rdW (m.arr64 IW) ro) (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co)) := by
  simp only [rtsW]; rw [if_neg h, if_neg h2]
theorem rtsK1_some : rtsK1 n vis g k ro rl vo vl co cl (some (r1, m1)) =
    rtsK2 n (r1.headD 0) (rtsW n m1 vis g k (ro + 1) (rl - 1) (vo + 1) (vl - 1) (co + 1) (cl - 1)) := by
  rw [rtsK1]
theorem rtsK2_some : rtsK2 n x (some (r2, m2)) = rtsK3 (consW n m2 x (r2.headD 0) (r2.tail.headD 0)) := rfl
theorem rtsK3_some : rtsK3 (some (r3, m3)) = some ([r3.headD 0, r3.tail.headD 0], m3) := rfl
end arms

grind_pattern [ind_grind] rtsW_nil => rtsW (n + 1) m vis g k ro rl vo vl co cl
grind_pattern [ind_grind] rtsW_short => rtsW (n + 1) m vis g k ro rl vo vl co cl
grind_pattern [ind_grind] rtsW_cons => rtsW (n + 1) m vis g k ro rl vo vl co cl
grind_pattern [ind_grind] rtsK1_some => rtsK1 n vis g k ro rl vo vl co cl (some (r1, m1))
grind_pattern [ind_grind] rtsK2_some => rtsK2 n x (some (r2, m2))
grind_pattern [ind_grind] rtsK3_some => rtsK3 (some (r3, m3))

/-- The lookups `class_rec_tys_ok` needs. -/
structure RtsProg (p : Prog) extends RtoProg p : Prop where
  cons : p.lookup "sl_cons" = some slCons
  rts : p.lookup "class_rec_tys_ok" = some classRecTysOkL

theorem classRecTysOk_spec (p : Prog) (h : RtsProg p) (n : Nat) :
    ∀ (s₀ : St) (vis g k ro rl vo vl co cl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_tys_ok" [vis, g, k, ro, rl, vo, vl, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ rtsW n s₀.mem vis g k ro rl vo vl co cl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis g k ro rl vo vl co cl
    rw [invoke_eq _ h.rts]; simp only [callFn, classRecTysOkL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis g k ro rl vo vl co cl
    rw [invoke_eq _ h.rts]
    simp only [callFn, classRecTysOkL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classRecTyOk_spec p h.toRtoProg n, slCons_specW p h.alloc h.copy h.cons n, ih] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8]

end L.Ind
