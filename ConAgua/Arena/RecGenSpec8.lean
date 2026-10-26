import ConAgua.Arena.RecGenSpec7

/-!
# `RecGen`: `classRecTysOk` (lane `indproofs2`, helper `rec2`)
-/

noncomputable section

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
def rtsW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, g, k, ro, rl, vo, vl, co, cl =>
    if rl = 0 then some ([0, 0], m)
    else if vl = 0 ∨ cl = 0 then none
    else rtsK1 cR n vis g k ro rl vo vl co cl
      (rtoW cR n m vis g k (rdW (m.arr64 IW) ro) (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co))
def rtsK1 (cR : CallM) (n : Nat) (vis g k ro rl vo vl co cl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    rtsK2 n (r1.headD 0) (rtsW cR n m1 vis g k (ro + 1) (rl - 1) (vo + 1) (vl - 1) (co + 1) (cl - 1))
end

section arms
variable (cR : CallM) (n : Nat) (m m1 m2 m3 : Mem) (vis g k ro rl vo vl co cl x : Word) (r1 r2 r3 : List Word)
theorem rtsW_nil (h : rl = 0) : rtsW cR (n + 1) m vis g k ro rl vo vl co cl = some ([0, 0], m) := by
  simp [rtsW, h]
theorem rtsW_short (h : ¬ rl = 0) (h2 : vl = 0 ∨ cl = 0) : rtsW cR (n + 1) m vis g k ro rl vo vl co cl = none := by
  simp only [rtsW]; rw [ite_eq_right h, ite_eq_left h2]
theorem rtsW_cons (h : ¬ rl = 0) (h2 : ¬ (vl = 0 ∨ cl = 0)) : rtsW cR (n + 1) m vis g k ro rl vo vl co cl =
    rtsK1 cR n vis g k ro rl vo vl co cl
      (rtoW cR n m vis g k (rdW (m.arr64 IW) ro) (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co)) := by
  simp only [rtsW]; rw [ite_eq_right h, ite_eq_right h2]
theorem rtsK1_some : rtsK1 cR n vis g k ro rl vo vl co cl (some (r1, m1)) =
    rtsK2 n (r1.headD 0) (rtsW cR n m1 vis g k (ro + 1) (rl - 1) (vo + 1) (vl - 1) (co + 1) (cl - 1)) := by
  rw [rtsK1]
theorem rtsK2_some : rtsK2 n x (some (r2, m2)) = rtsK3 (consW n m2 x (r2.headD 0) (r2.tail.headD 0)) := rfl
theorem rtsK3_some : rtsK3 (some (r3, m3)) = some ([r3.headD 0, r3.tail.headD 0], m3) := rfl
end arms

grind_pattern [ind_grind] rtsW_nil => rtsW cR (n + 1) m vis g k ro rl vo vl co cl
grind_pattern [ind_grind] rtsW_short => rtsW cR (n + 1) m vis g k ro rl vo vl co cl
grind_pattern [ind_grind] rtsW_cons => rtsW cR (n + 1) m vis g k ro rl vo vl co cl
grind_pattern [ind_grind] rtsK1_some => rtsK1 cR n vis g k ro rl vo vl co cl (some (r1, m1))
grind_pattern [ind_grind] rtsK2_some => rtsK2 n x (some (r2, m2))
grind_pattern [ind_grind] rtsK3_some => rtsK3 (some (r3, m3))

/-- The lookups `class_rec_tys_ok` needs. -/
structure RtsProg (p : Prog) extends RtoProg p : Prop where
  cons : p.lookup "sl_cons" = some slCons
  rts : p.lookup "class_rec_tys_ok" = some classRecTysOkL

theorem classRecTysOk_spec (p : Prog) (h : RtsProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) :
    ∀ (s₀ : St) (vis g k ro rl vo vl co cl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_tys_ok" [vis, g, k, ro, rl, vo, vl, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ rtsW cR n s₀.mem vis g k ro rl vo vl co cl = some (r, s'.mem); ⊤⦄ := by
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
        classRecTyOk_spec p h.toRtoProg cR hcR n, slCons_specW p h.alloc h.copy h.cons n, ih] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8]

/-! ## Relational lemma -/

open Classical in
/-- A constant record below the record top, decoded. -/
noncomputable def decCVX (m : Mem) (p : Nat) : Option IConstantVal :=
  if CVExt m p then decCVp m p else none

theorem decCVX_stab {m : Mem} {p : Nat} {cv : IConstantVal} (h1 : decCVp m p = some cv)
    (h2 : CVExt m p) : StabD (fun m => decCVX m p) m cv := by
  intro m'' hg
  simp only [decCVX, ite_eq_left (CVExt_grow hg h2)]
  rw [decCVp_grow_r hg h2, h1]

theorem RecsOK_tail {m : Mem} {ro rl : Nat} {cv : IConstantVal} {cvs : List IConstantVal}
    (h : RecsOK m ro (rl + 1) (cv :: cvs)) : RecsOK m (ro + 1) rl cvs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by simpa using h2, fun j hj => ?_⟩
  obtain ⟨p0, q, cv', hp0, hp1, hq, hcv, hext, hcvs⟩ := h3 (j + 1) (by omega)
  exact ⟨p0, q, cv', by rw [show ro + 1 + j = ro + (j + 1) by omega]; exact hp0, hp1, hq, hcv, hext,
    by simpa using hcvs⟩

/-- `class_rec_tys_ok`'s result: a stable slice of constant records below the record top. -/
def decCVS (m' : Mem) (r : List Word) (xs : List IConstantVal) : Prop :=
  SPL decCVX m' (r.headD 0).toNat (r.tail.headD 0).toNat xs

theorem rec2ToNat_succ {o : Word} {i : Nat} (h : o.toNat ≤ i) (hi : i < 2 ^ 64 - 1) :
    (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega

theorem rec2ToNat_pred {l : Word} (h : l ≠ 0) : (l - 1).toNat = l.toNat - 1 := by
  have : l.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp

end L.Ind
