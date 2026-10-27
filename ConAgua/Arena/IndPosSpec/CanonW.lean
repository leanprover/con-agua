import ConAgua.Arena.IndPosSpec.FindIdxDecIP
import ConAgua.Arena.IndPosSpec.MatesW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# CanonW

`canonW_ne`, `canonW_eq`, `canonK0_miss`, `canonK0_hit`, `canonK1_ok`, `canonK2_big` and the lemmas only they use.
-/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (n : Nat) (m m1 m2 : Mem) (no nl us nn c v mi r s z : Word) (fr : List Word)
theorem canonW_ne (h : v ≠ us) : canonW (n + 1) m no nl us nn c v = some ([0, 0], m) := by simp [canonW, h]
theorem canonW_eq (h : ¬ v ≠ us) : canonW (n + 1) m no nl us nn c v = canonK0 nn m (findW n m no nl c) := by
  simp only [canonW]; rw [ite_eq_right h]
theorem canonK0_miss (h : fr.headD 0 = 0) : canonK0 nn m (some fr) = some ([0, 0], m) := by
  simp only [canonK0]; rw [ite_eq_left h]
theorem canonK0_hit (h : ¬ fr.headD 0 = 0) :
    canonK0 nn m (some fr) = canonK1 nn (fr.tail.headD 0) m (pinWordV m 53) := by
  simp only [canonK0]; rw [ite_eq_right h]
theorem canonK1_ok (h : ¬ 4294967296 ≤ z) : canonK1 nn mi m (some z) = canonK2 nn mi (sointernW m z) := by
  simp only [canonK1]; rw [ite_eq_right h]
theorem canonK2_big (h : 4294967296 ≤ s) : canonK2 nn mi (some (s, m1)) = none := by simp [canonK2, h]
theorem canonK2_ok (h : ¬ 4294967296 ≤ s) :
    canonK2 nn mi (some (s, m1)) = canonK3 (fvinternW m1 (nn + mi) s) := by
  simp only [canonK2]; rw [ite_eq_right h]
theorem canonK3_big (h : 4294967296 ≤ r) : canonK3 (some (r, m2)) = none := by simp [canonK3, h]
theorem canonK3_ok (h : ¬ 4294967296 ≤ r) : canonK3 (some (r, m2)) = some ([1, r], m2) := by
  simp only [canonK3]; rw [ite_eq_right h]
end arms
grind_pattern [ind_grind] canonW_ne => canonW (n + 1) m no nl us nn c v
grind_pattern [ind_grind] canonW_eq => canonW (n + 1) m no nl us nn c v
grind_pattern [ind_grind] canonK0_miss => canonK0 nn m (some fr)
grind_pattern [ind_grind] canonK0_hit => canonK0 nn m (some fr)
grind_pattern [ind_grind] canonK1_ok => canonK1 nn mi m (some z)
grind_pattern [ind_grind] canonK2_big => canonK2 nn mi (some (s, m1))
grind_pattern [ind_grind] canonK2_ok => canonK2 nn mi (some (s, m1))
grind_pattern [ind_grind] canonK3_big => canonK3 (some (r, m2))
grind_pattern [ind_grind] canonK3_ok => canonK3 (some (r, m2))

section spec
variable (p : Prog) (hf : p.lookup "sl_find" = some slFind) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hp : p.lookup "nest_canon_sub" = some nestCanonSub)
include hf hpw hsf hsp his hff hfp hif hp

theorem nestCanonSub_spec (n : Nat) (s₀ : St) (no nl us nn c v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_canon_sub" [no, nl, us, nn, c, v]
    ⦃fun r s' => LocEq s' s₀ ∧ canonW n s₀.mem no nl us nn c v = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCanonSub]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slFind_spec p hf n, pinWord_specV p hpw n, internSort_spec p hsf hsp his n,
        internFVar_spec p hff hfp hif n] <;> finish (gen := 20) [canonW]

end spec

theorem notbig_of_lt {z : Word} (h : z.toNat < 2 ^ 32) : ¬ 4294967296 ≤ z := by
  intro hh
  have := UInt64.le_iff_toNat_le.mp hh
  have e : (4294967296 : Word).toNat = 4294967296 := by decide
  omega

theorem canonW_ok (n : Nat) : ∀ (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl us nn c v : Word) (names : List NIdx) (r : List Word),
    canonW n m no nl us nn c v = some (r, m') → StageR dn vis fe m a → H c → H us → H v →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat < 2 ^ 64 →
    nn.toNat + names.length < 2 ^ 64 →
    ∃ x a', (ConRon.Arena.nestCanonSub names (decI us) nn.toNat (decI c) (decI v)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decOE m' r x := by
  intro dn fe vis m m' a no nl us nn c v names r h hS hc hus hv hdec hb hnn
  cases n with
  | zero => simp [canonW] at h
  | succ n =>
  by_cases hvu : v ≠ us
  · rw [canonW_ne n m no nl us nn c v hvu] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
    have : ¬ ((decI v : LsIdx) == decI us) = true := by
      rw [decI_beq' v us hv hus]; simpa using hvu
    simp only [ConRon.Arena.nestCanonSub, this]; rfl
  · rw [canonW_eq n m no nl us nn c v hvu] at h
    have hvu' : v = us := by simpa using hvu
    subst hvu'
    have hbeq : ((decI v : LsIdx) == decI v) = true := by simp
    obtain ⟨ws, hws, rfl, hwlt⟩ := slR_of_decHL m _ _ names hdec hb
    simp only [UInt64.ofNat_toNat] at hws
    have hlen : ws.length < 2 ^ 64 := by
      have := decHL_length m hdec; simp at this; omega
    rcases hfw : findW n m no nl c with _ | fr <;> rw [hfw] at h; · simp [canonK0] at h
    have hfr := findW_ok n _ _ _ _ _ _ hws hfw hlen
    have hfi := findIdx_decIP ws c hwlt hc
    cases hwi : ws.findIdx? (· == c) with
    | none =>
      rw [hwi] at hfr
      subst hfr
      rw [canonK0_miss _ _ _ rfl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
      simp only [ConRon.Arena.nestCanonSub, hbeq, ite_true, hfi, hwi]; rfl
    | some i =>
      rw [hwi] at hfr
      subst hfr
      rw [canonK0_hit _ _ _ (by simp)] at h
      simp only [List.tail_cons, List.headD_cons] at h
      rcases hpw : pinWordV m 53 with _ | z <;> rw [hpw] at h; · simp [canonK1] at h
      have hpne : rdW (m.arr64 PINS) 0 ≠ 0 := by
        intro h0; simp [pinWordV, h0] at hpw
      have hz : z = pinW m 53 := by
        simp only [pinWordV, hpne, ite_false, Option.some.injEq] at hpw
        rw [← hpw]; simp [pinW, rdW]
      have hpin0 : pinW m 0 ≠ 0 := by simpa [pinW, rdW] using hpne
      have hfull := hS.1.pins.full hpin0
      have hzlt : z.toNat < 2 ^ 32 := by rw [hz]; exact hfull.lv_lt.2.1
      rw [canonK1_ok _ _ _ _ (notbig_of_lt hzlt)] at h
      rcases hso : sointernW m z with _ | ⟨s1, m1⟩ <;> rw [hso] at h; · simp [canonK2] at h
      by_cases hsb : 4294967296 ≤ s1
      · rw [canonK2_big _ _ _ _ hsb] at h; simp at h
      rw [canonK2_ok _ _ _ _ hsb] at h
      obtain ⟨a1, hrun1, hS1, hg1⟩ := internSort_stage hS z hzlt hso
      have hs1lt : s1.toNat < 2 ^ 32 := lt_of_notbig hsb
      rcases hfv : fvinternW m1 (nn + UInt64.ofNat i) s1 with _ | ⟨rr, m2⟩ <;> rw [hfv] at h; · simp [canonK3] at h
      by_cases hrb : 4294967296 ≤ rr
      · rw [canonK3_big _ _ hrb] at h; simp at h
      rw [canonK3_ok _ _ hrb] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 (nn + UInt64.ofNat i) s1 hs1lt hfv
      have hilt : i < ws.length := by
        have := List.findIdx?_eq_some_iff_findIdx_eq.mp hwi
        exact this.1
      have hnn' : nn.toNat + ws.length < 2 ^ 64 := by simpa using hnn
      have hsz : UInt64.size = 2 ^ 64 := rfl
      have hnn2 : (nn + UInt64.ofNat i).toNat = nn.toNat + i := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      refine ⟨some (decE rr), a2, ?_, hS2, (hg1.trans hg2), ?_⟩
      · have hzl : (zeroLevel).run a = .ok (decI z, a) := by
          rw [hz]; exact pinZeroLevel_run hfull
        simp only [ConRon.Arena.nestCanonSub, hbeq, ite_true, hfi, hwi, StateT.run_bind, hzl, except_ok_bind, ConRon.Arena.internSortE, ConRon.Arena.internFVarE, hrun1]
        rw [hnn2] at hrun2
        rw [hrun2]
        rfl
      · exact ⟨rfl, lt_of_notbig hrb, rfl⟩

section arms
variable (n : Nat) (m m1 m2 : Mem) (c off l oO oL b : Word) (r r2 : List Word)
theorem matesW_nil (h : l = 0) : matesW (n + 1) m c off l oO oL = some ([oO, oL], m) := by simp [matesW, h]
theorem matesW_cons (h : l ≠ 0) : matesW (n + 1) m c off l oO oL =
    matesK1 n m c off l oO oL (containsW n m oO oL (rdW (m.arr64 EREC) off)) := by simp [matesW, h]
theorem matesK1_skip (h : rdW (m.arr64 EREC) off = c ∨ b ≠ 0) : matesK1 n m c off l oO oL (some b) =
    matesK3 (matesW n m c (off + 1) (l - 1) oO oL) := by simp only [matesK1]; rw [ite_eq_left h]
theorem matesK1_add (h : ¬ (rdW (m.arr64 EREC) off = c ∨ b ≠ 0)) : matesK1 n m c off l oO oL (some b) =
    matesK2 n c off l (snocW n m oO oL (rdW (m.arr64 EREC) off)) := by simp only [matesK1]; rw [ite_eq_right h]
theorem matesK2_some : matesK2 n c off l (some (r2, m2)) =
    matesK3 (matesW n m2 c (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0)) := by rw [matesK2]
theorem matesK3_some : matesK3 (some (r, m2)) = some ([r.headD 0, r.tail.headD 0], m2) := by rw [matesK3]
end arms
grind_pattern [ind_grind] matesW_nil => matesW (n + 1) m c off l oO oL
grind_pattern [ind_grind] matesW_cons => matesW (n + 1) m c off l oO oL
grind_pattern [ind_grind] matesK1_skip => matesK1 n m c off l oO oL (some b)
grind_pattern [ind_grind] matesK1_add => matesK1 n m c off l oO oL (some b)
grind_pattern [ind_grind] matesK2_some => matesK2 n c off l (some (r2, m2))
grind_pattern [ind_grind] matesK3_some => matesK3 (some (r, m2))

section spec
variable (p : Prog) (hc : p.lookup "sl_contains" = some slContains) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hcp : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
  (hp : p.lookup "nest_frame_mates_go" = some nestFrameMatesGoL)
include hc ha hcp hsn hp

theorem nestFrameMatesGo_spec (n : Nat) : ∀ (s₀ : St) (c off l oO oL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_mates_go" [c, off, l, oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧ matesW n s₀.mem c off l oO oL = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ c off l oO oL
    rw [invoke_eq _ hp]; simp only [callFn, nestFrameMatesGoL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ c off l oO oL
    simp only [invoke_eq _ hp, callFn, nestFrameMatesGoL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slContains_spec p hc n, slSnoc_specW p ha hcp hsn n, ih] <;> finish (gen := 20)

end spec

/-- **`sl_snoc`'s pool**: the new slice at the old top, the source's words then `x`. -/
theorem snocW_core {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word}
    (h : snocW n m o l x = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m) :
    r = [rdW (m.arr64 CTL) 200, l + 1] ∧ (l + 1).toNat = l.toNat + 1 ∧ (rdW (m.arr64 CTL) 200).toNat = iwTop m ∧
    MemFrame [IW] [200] m m' ∧ IWGrow m m' ∧ iwTop m' = iwTop m + (l.toNat + 1) ∧
    ∀ i, (m'.arr64 IW)[i]? = if i = iwTop m + l.toNat then some x
      else if iwTop m ≤ i ∧ i < iwTop m + l.toNat then (m.arr64 IW)[o.toNat + (i - iwTop m)]?
      else (m.arr64 IW)[i]? := by
  simp only [snocW] at h
  by_cases h0 : l + 1 = 0
  · simp [h0] at h
  simp only [h0, ite_false] at h
  rcases hal : allocW m (l + 1) with _ | ⟨q, m1⟩; · simp [hal] at h
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  rcases hcp : copyW (n - 1) m1 q o l with _ | m2; · simp [hcp] at h
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq hm1
  have hqt : (rdW (m.arr64 CTL) 200).toNat = iwTop m := rfl
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hl1 : (l + 1).toNat = l.toNat + 1 := by
    have hlm : l.toNat ≠ 2 ^ 64 - 1 := fun e => h0 (by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp [e])
    rw [UInt64.toNat_add]; simp; have := l.toNat_lt; omega
  rw [hl1] at hroom
  have hql : (q + l).toNat = q.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hIW := allocMem_IW m (l + 1)
  obtain ⟨hA, hS, hW, hG⟩ := copyW_get (n - 1) _ _ _ _ _ hcp (by omega)
    (by rw [hIW]; omega) (by rw [hIW]; exact hsz)
  rw [hIW] at hS hG
  have hfr : MemFrame [IW] [200] m (m2.set64 IW (q + l) x) :=
    ((allocMem_frame m (l + 1)).trans (copy_frame hA (by rw [hS, hIW]) (by first | (rw [hW]) | (rw [hW]; simp [allocMem])))).trans
      (set64IW_frame m2 (q + l) x)
  have hget : ∀ i, ((m2.set64 IW (q + l) x).arr64 IW)[i]? =
      if i = q.toNat + l.toNat then some x
      else if q.toNat ≤ i ∧ i < q.toNat + l.toNat then (m.arr64 IW)[o.toNat + (i - q.toNat)]?
      else (m.arr64 IW)[i]? := by
    intro i
    rw [set64IW_get, hql, hS, hG i]
    by_cases h1 : i = q.toNat + l.toNat
    · rw [ite_eq_left ⟨h1, by omega⟩, ite_eq_left h1]
    · rw [ite_eq_right (by omega), ite_eq_right h1]
  have htop : rdW ((m2.set64 IW (q + l) x).arr64 CTL) 200 = q + (l + 1) := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + (l + 1)).toNat = q.toNat + (l.toNat + 1) := by
    rw [UInt64.toNat_add, hl1]; simp; omega
  have htop' : iwTop (m2.set64 IW (q + l) x) = iwTop m + (l.toNat + 1) := by
    simp only [iwTop, htop, hsum, hqt]
  refine ⟨rfl, hl1, hqt, hfr, ?_, htop', by rw [← hqt]; exact hget⟩
  refine iwGrow_of_frame hfr (N := l + 1) ?_ ?_ hsz ?_
  · rw [htop, hqq]
  · omega
  · intro i hi
    simp only [iwTop, hqq] at hi
    rw [hget, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem contains_decI (ws : List Word) (x : Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hx : x.toNat < 2 ^ 32) :
    (ws.map (fun w => (decI w : NIdx))).contains (decI x) = ws.contains x := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.contains_cons, decI_beq' x w hx (hws w (by simp))]
    have := ih (fun y hy => hws y (by simp [hy]))
    rw [this]
    by_cases h : x = w <;> simp [h]

/-! ## `mentions_any_go`, `mentions_any_node`: word models -/

mutual
def maGoW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, no, nl, f, h =>
    if f = 0 then none else maG1 n m no nl f h (eViewW m h)
def maG1 (n : Nat) (m : Mem) (no nl f h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 then some (0, m)
  else if v.headD 0 = 3 then maC m (containsW n m no nl (v.tail.headD 0))
  else maG3 n m no nl f h v (mfindG maSch m h 0)
def maG3 (n : Nat) (m : Mem) (no nl f h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 MAM) (fr.tail.headD 0 * 4 + 3), m)
  else maG4 h (maNodeW n m no nl (f - 1) (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def maG4 (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => maG5 r (msetG maSch m1 h 0 r)
def maG5 (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 => some (r, m2)
def maC (m : Mem) : Option Word → Option (Word × Mem)
  | none => none
  | some r => some (r, m)
def maNodeW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, f1, g, x, y, z =>
    if g = 1 then maGoW n m no nl f1 y
    else if g = 4 ∨ g = 5 ∨ g = 6 then maB1 n no nl f1 y (maGoW n m no nl f1 x)
    else if g = 7 then maL1 n no nl f1 y z (maGoW n m no nl f1 x)
    else maP1 n no nl x (maGoW n m no nl f1 z)
def maB1 (n : Nat) (no nl f1 y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => maB2 b1 (maGoW n m1 no nl f1 y)
def maB2 (b1 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b2, m2) => some (if b1 ≠ 0 ∨ b2 ≠ 0 then 1 else 0, m2)
def maL1 (n : Nat) (no nl f1 y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => maL2 n no nl f1 z b1 (maGoW n m1 no nl f1 y)
def maL2 (n : Nat) (no nl f1 z b1 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b2, m2) => maL3 b1 b2 (maGoW n m2 no nl f1 z)
def maL3 (b1 b2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b3, m3) => some (if b1 ≠ 0 ∨ b2 ≠ 0 ∨ b3 ≠ 0 then 1 else 0, m3)
def maP1 (n : Nat) (no nl x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => maP2 b1 m1 (containsW n m1 no nl x)
def maP2 (b1 : Word) (m1 : Mem) : Option Word → Option (Word × Mem)
  | none => none
  | some b2 => some (if b1 ≠ 0 ∨ b2 ≠ 0 then 1 else 0, m1)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (no nl f f1 h g x y z b1 b2 b3 r : Word) (v fr : List Word)
theorem maGoW_view (hf : f ≠ 0) : maGoW (n + 1) m no nl f h = maG1 n m no nl f h (eViewW m h) := by
  simp [maGoW, hf]
theorem maG1_leaf (hv : v ≠ []) (hg : v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8) :
    maG1 n m no nl f h v = some (0, m) := by simp only [maG1]; rw [ite_eq_right hv, ite_eq_left hg]
theorem maG1_const (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : v.headD 0 = 3) : maG1 n m no nl f h v = maC m (containsW n m no nl (v.tail.headD 0)) := by
  simp only [maG1]; rw [ite_eq_right hv, ite_eq_right hg, ite_eq_left h3]
theorem maG1_node (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : ¬ v.headD 0 = 3) : maG1 n m no nl f h v = maG3 n m no nl f h v (mfindG maSch m h 0) := by
  simp only [maG1]; rw [ite_eq_right hv, ite_eq_right hg, ite_eq_right h3]
theorem maG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    maG3 n m no nl f h v fr = some (rdW (m.arr64 MAM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [maG3]; rw [ite_eq_right hr, ite_eq_left hh]
theorem maG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    maG3 n m no nl f h v fr = maG4 h (maNodeW n m no nl (f - 1) (v.headD 0) (v.tail.headD 0)
      (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [maG3]; rw [ite_eq_right hr, ite_eq_right hh]
theorem maG4_some : maG4 h (some (r, m1)) = maG5 r (msetG maSch m1 h 0 r) := by rw [maG4]
theorem maG5_some : maG5 r (some m2) = some (r, m2) := by rw [maG5]
theorem maC_some : maC m (some r) = some (r, m) := by rw [maC]
theorem maNodeW_fvar (hg : g = 1) : maNodeW (n + 1) m no nl f1 g x y z = maGoW n m no nl f1 y := by
  simp [maNodeW, hg]
theorem maNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) : maNodeW (n + 1) m no nl f1 g x y z =
    maB1 n no nl f1 y (maGoW n m no nl f1 x) := by
  have : ¬ g = 1 := by
    intro e; rcases hg with h | h | h <;> (rw [e] at h; exact absurd h (by decide))
  simp only [maNodeW]; rw [ite_eq_right this, ite_eq_left hg]
theorem maNodeW_let (hg : g = 7) : maNodeW (n + 1) m no nl f1 g x y z =
    maL1 n no nl f1 y z (maGoW n m no nl f1 x) := by
  simp [maNodeW, hg]
theorem maNodeW_proj (hg1 : g ≠ 1) (hg2 : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (hg3 : g ≠ 7) :
    maNodeW (n + 1) m no nl f1 g x y z = maP1 n no nl x (maGoW n m no nl f1 z) := by
  simp only [maNodeW]; rw [ite_eq_right hg1, ite_eq_right hg2, ite_eq_right hg3]
theorem maB1_some : maB1 n no nl f1 y (some (b1, m1)) = maB2 b1 (maGoW n m1 no nl f1 y) := by rw [maB1]
theorem maB2_some : maB2 b1 (some (b2, m2)) = some (if b1 ≠ 0 ∨ b2 ≠ 0 then 1 else 0, m2) := by rw [maB2]
theorem maL1_some : maL1 n no nl f1 y z (some (b1, m1)) = maL2 n no nl f1 z b1 (maGoW n m1 no nl f1 y) := by rw [maL1]
theorem maL2_some : maL2 n no nl f1 z b1 (some (b2, m2)) = maL3 b1 b2 (maGoW n m2 no nl f1 z) := by rw [maL2]
theorem maL3_some : maL3 b1 b2 (some (b3, m3)) =
    some (if b1 ≠ 0 ∨ b2 ≠ 0 ∨ b3 ≠ 0 then 1 else 0, m3) := by rw [maL3]
theorem maP1_some : maP1 n no nl x (some (b1, m1)) = maP2 b1 m1 (containsW n m1 no nl x) := by rw [maP1]
theorem maP2_some : maP2 b1 m1 (some b2) = some (if b1 ≠ 0 ∨ b2 ≠ 0 then 1 else 0, m1) := by rw [maP2]
end arms

attribute [ind_grind] maGoW_view maG1_leaf maG1_const maG1_node maG3_hit maG3_miss maG4_some maG5_some maC_some maNodeW_fvar maNodeW_bin maNodeW_let maNodeW_proj maB1_some maB2_some maL1_some maL2_some maL3_some maP1_some maP2_some

section spec
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hc : p.lookup "sl_contains" = some slContains)
  (hf : p.lookup "ma_find" = some (memoFindG maSch)) (hput : p.lookup "ma_put" = some (memoPutG maSch))
  (hgo : p.lookup "mentions_any_go" = some mentionsAnyGo)
  (hnode : p.lookup "mentions_any_node" = some mentionsAnyNode)

def MaGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mentions_any_go" [no, nl, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ maGoW n s₀.mem no nl f h = some (r.headD 0, s'.mem); ⊤⦄

def MaNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl f1 g x y z : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mentions_any_node" [no, nl, f1, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ maNodeW n s₀.mem no nl f1 g x y z = some (r.headD 0, s'.mem); ⊤⦄

include hv hc hf hput hgo in
theorem maGo_step (n : Nat) (ih : MaNodeSpec p n) : MaGoSpec p (n + 1) := by
  unfold MaNodeSpec at ih
  intro s₀ no nl f h
  simp only [invoke_eq _ hgo, callFn, mentionsAnyGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p hv n, slContains_spec p hc n, memoFindG_spec maSch p _ hf n,
      memoPutG_spec maSch p _ hput n, ih] <;> finish (gen := 20)

include hc hnode in
theorem maNode_step (n : Nat) (ih : MaGoSpec p n) : MaNodeSpec p (n + 1) := by
  unfold MaGoSpec at ih
  intro s₀ no nl f1 g x y z
  simp only [invoke_eq _ hnode, callFn, mentionsAnyNode]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      slContains_spec p hc n, ih] <;> finish (gen := 20)

include hv hc hf hput hgo hnode in
theorem maGo_spec (n : Nat) : MaGoSpec p n ∧ MaNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ no nl f h; rw [invoke_eq _ hgo]; simp only [callFn, mentionsAnyGo]; vcgen [exec] <;> grind
    · intro s₀ no nl f1 g x y z; rw [invoke_eq _ hnode]; simp only [callFn, mentionsAnyNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨maGo_step p hv hc hf hput hgo n ih.2, maNode_step p hc hgo hnode n ih.1⟩

end spec

def maArm (names : List NIdx) (memo : Std.HashMap EIdx Bool) (fuel : Nat) :
    ENodeView → AM (Bool × Std.HashMap EIdx Bool)
  | .fvar _ ty => ConRon.Arena.mentionsAnyGo names memo fuel ty
  | .app f a => do
    let (b1, m) ← ConRon.Arena.mentionsAnyGo names memo fuel f
    let (b2, m2) ← ConRon.Arena.mentionsAnyGo names m fuel a
    pure (b1 || b2, m2)
  | .lam ty body => do
    let (b1, m) ← ConRon.Arena.mentionsAnyGo names memo fuel ty
    let (b2, m2) ← ConRon.Arena.mentionsAnyGo names m fuel body
    pure (b1 || b2, m2)
  | .forallE ty body => do
    let (b1, m) ← ConRon.Arena.mentionsAnyGo names memo fuel ty
    let (b2, m2) ← ConRon.Arena.mentionsAnyGo names m fuel body
    pure (b1 || b2, m2)
  | .letE ty val body => do
    let (b1, m) ← ConRon.Arena.mentionsAnyGo names memo fuel ty
    let (b2, m2) ← ConRon.Arena.mentionsAnyGo names m fuel val
    let (b3, m3) ← ConRon.Arena.mentionsAnyGo names m2 fuel body
    pure (b1 || b2 || b3, m3)
  | .proj s _ sub => do
    let (b, m) ← ConRon.Arena.mentionsAnyGo names memo fuel sub
    pure (names.contains s || b, m)
  | _ => pure (false, memo)

theorem maFrame_arena {m m' : Mem} {a : AState} (hf : MemFrame [MAM] [203] m m') (hR : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame (fun b hb => by simp at hb; subst hb; simp [arenaArrs, storeArrs, memoArrs, MAM])
    (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf hR

theorem maFrame_iw {m m' : Mem} (hf : MemFrame [MAM] [203] m m') : m'.arr64 IW = m.arr64 IW :=
  hf.1 IW (by decide) (by decide)

def MaGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (no nl f h r : Word) (ws : List Word) (mp : Std.HashMap EIdx Bool),
    maGoW n m no nl f h = some (r, m') → ArenaR m a → H h → SlR m no nl ws →
    (∀ w ∈ ws, w.toNat < 2 ^ 32) → maMR m mp →
    ∃ b mp', (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f.toNat (decE h)).run a =
        .ok ((b, mp'), a) ∧ (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m'

end L.Ind

end
