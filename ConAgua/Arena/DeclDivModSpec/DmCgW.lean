import ConAgua.Arena.IndRealApdT

/-!
# DmCgW

`SubstC0`, `applied_specW`, `appliedW`, `iw_rd_grow`, `word_add_one`, `craW` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section subst
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- **`subst_const0` refines `substConst0`** at the walk fuel `4000000000` (helper `decls3-nat`'s). -/
def SubstC0 : Prop := ∀ nm r h : Word, H nm → H r → H h →
  CallRef p "subst_const0" [nm, r, 4000000000, h] (StageR dn vis fe)
    (substConst0 (decI nm) (decE r) coreWalkFuel (decE h)) (KeepPost dn vis fe decW0E)

end subst

section applied
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-! ## `div_mod_cert_applied` -/

/-- **`div_mod_cert_applied` is its model `appliedW`** (generated). -/
l_model applied_specW (p : Prog) (hp : p.lookup "div_mod_cert_applied" = some divModCertAppliedL)
  fns [hp ↦ appliedW list]
  specs [callW_spec p n "nat_var", callW_spec p n "mk_app", callW_spec p n "intern_fvar"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem iw_rd_grow {m m' : Mem} (hg : IWGrow m m') {i : Word} (hi : i.toNat < iwTop m) :
    rdW (m'.arr64 IW) i = rdW (m.arr64 IW) i := by
  simp only [rdW]; rw [hg.2.2.1 i.toNat hi]

theorem word_add_one {w : Word} (h : w.toNat + 1 < 2 ^ 64) : (w + 1).toNat = w.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

/-! ## `consts_resolve_all` -/

def craW (p : Prog) (cl : CallM) (n : Nat) (m : Mem) (vs o l : Word) : Option (List Word × Mem) :=
  if l = 0 then some ([1], m) else
  ntBW (cl n "consts_resolve_ffast" [vs, rdW (m.arr64 IW) o] m) fun r1 m1 =>
  if r1.headD 0 = 0 then some ([0], m1) else
  ntBW (callW p n "consts_resolve_all" [vs, o + 1, l - 1] m1) fun r2 m2 => some ([r2.headD 0], m2)

/-! ## `div_mod_cert_guard` -/

def dmCgW (p : Prog) (cl : CallM) (n : Nat) (m : Mem) (vs c annVal ho hl eqE proof : Word) :
    Option (List Word × Mem) :=
  ntBW (callW p n "subst_const_all" [c, annVal, 4000000000, proof] m) fun r1 m1 =>
  ntBW (lbbF m1 [4000000000, 0, r1.headD 0]) fun r2 m2 =>
  if r2.headD 0 = 0 then some ([0], m2) else
  ntBW (hffF m2 [4000000000, r1.headD 0]) fun r3 m3 =>
  if r3.headD 0 ≠ 0 then some ([0], m3) else
  ntBW (cl n "all_level_params_defined" [0, 0, r1.headD 0] m3) fun r4 m4 =>
  if r4.headD 0 = 0 then some ([0], m4) else
  ntBW (cl n "consts_resolve_ffast" [vs, r1.headD 0] m4) fun r5 m5 =>
  if r5.headD 0 = 0 then some ([0], m5) else
  ntBW (callW p n "subst_const0_list" [c, annVal, ho, hl] m5) fun r6 m6 =>
  ntBW (callW p n "consts_resolve_all" [vs, r6.headD 0, r6.tail.headD 0] m6) fun r7 m7 =>
  if r7.headD 0 = 0 then some ([0], m7) else
  ntBW (callW p n "subst_const0" [c, annVal, 4000000000, eqE] m7) fun r8 m8 =>
  ntBW (cl n "consts_resolve_ffast" [vs, r8.headD 0] m8) fun r9 m9 => some ([r9.headD 0], m9)

theorem decW0B_false {m : Mem} {r : List Word} {b : Bool} (h : decW0B m r b) (hz : r.headD 0 = 0) :
    b = false := by
  have := h.1; rw [hz] at this; simpa using this.symm

theorem decW0B_true {m : Mem} {r : List Word} {b : Bool} (h : decW0B m r b) (hz : ¬ r.headD 0 = 0) :
    b = true := by
  have := h.1
  have e : (r.headD 0 != 0) = true := by simpa using hz
  rw [e] at this; exact this.symm

theorem decW0B_of_false (m : Mem) : decW0B m [0] false := by simp [decW0B]

end applied

end L.Ind

end
