import ConAgua.Arena.IndPos2SpecA

/-! Continued from `IndPos2SpecA.lean` (split by size; lane `indproofs`). -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `pin_word` as a word model -/

def pinWordV (m : Mem) (k : Word) : Option Word :=
  if rdW (m.arr64 PINS) 0 = 0 then none else some (rdW (m.arr64 PINS) k)

theorem pinWord_specV (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (n : Nat) (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_word" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ pinWordV s₀.mem k = some (r.headD 0); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, pinWordL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;> finish [pinWordV]

/-! ## `nest_canon_sub` -/

def canonK3 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => if 4294967296 ≤ r then none else some ([1, r], m2)
def canonK2 (nn mi : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (s, m1) => if 4294967296 ≤ s then none else canonK3 (fvinternW m1 (nn + mi) s)
def canonK1 (nn mi : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some z => if 4294967296 ≤ z then none else canonK2 nn mi (sointernW m z)
def canonK0 (nn : Word) (m : Mem) : Option (List Word) → Option (List Word × Mem)
  | none => none
  | some fr => if fr.headD 0 = 0 then some ([0, 0], m)
      else canonK1 nn (fr.tail.headD 0) m (pinWordV m 53)
def canonW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, us, nn, c, v =>
    if v ≠ us then some ([0, 0], m) else canonK0 nn m (findW n m no nl c)

section arms
variable (n : Nat) (m m1 m2 : Mem) (no nl us nn c v mi r s z : Word) (fr : List Word)
theorem canonW_ne (h : v ≠ us) : canonW (n + 1) m no nl us nn c v = some ([0, 0], m) := by simp [canonW, h]
theorem canonW_eq (h : ¬ v ≠ us) : canonW (n + 1) m no nl us nn c v = canonK0 nn m (findW n m no nl c) := by
  simp only [canonW]; rw [if_neg h]
theorem canonK0_miss (h : fr.headD 0 = 0) : canonK0 nn m (some fr) = some ([0, 0], m) := by
  simp only [canonK0]; rw [if_pos h]
theorem canonK0_hit (h : ¬ fr.headD 0 = 0) :
    canonK0 nn m (some fr) = canonK1 nn (fr.tail.headD 0) m (pinWordV m 53) := by
  simp only [canonK0]; rw [if_neg h]
theorem canonK1_big (h : 4294967296 ≤ z) : canonK1 nn mi m (some z) = none := by simp [canonK1, h]
theorem canonK1_ok (h : ¬ 4294967296 ≤ z) : canonK1 nn mi m (some z) = canonK2 nn mi (sointernW m z) := by
  simp only [canonK1]; rw [if_neg h]
theorem canonK2_big (h : 4294967296 ≤ s) : canonK2 nn mi (some (s, m1)) = none := by simp [canonK2, h]
theorem canonK2_ok (h : ¬ 4294967296 ≤ s) :
    canonK2 nn mi (some (s, m1)) = canonK3 (fvinternW m1 (nn + mi) s) := by
  simp only [canonK2]; rw [if_neg h]
theorem canonK3_big (h : 4294967296 ≤ r) : canonK3 (some (r, m2)) = none := by simp [canonK3, h]
theorem canonK3_ok (h : ¬ 4294967296 ≤ r) : canonK3 (some (r, m2)) = some ([1, r], m2) := by
  simp only [canonK3]; rw [if_neg h]
end arms
grind_pattern [ind_grind] canonW_ne => canonW (n + 1) m no nl us nn c v
grind_pattern [ind_grind] canonW_eq => canonW (n + 1) m no nl us nn c v
grind_pattern [ind_grind] canonK0_miss => canonK0 nn m (some fr)
grind_pattern [ind_grind] canonK0_hit => canonK0 nn m (some fr)
grind_pattern [ind_grind] canonK1_big => canonK1 nn mi m (some z)
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

theorem findIdx_decIP (ws : List Word) (c : Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hc : c.toNat < 2 ^ 32) :
    (ws.map (fun w => (decI w : NIdx))).findIdx? (· == (decI c : NIdx)) = ws.findIdx? (· == c) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.findIdx?_cons, decI_beq' w c (hws w (by simp)) hc]
    by_cases h : w = c
    · simp [h]
    · simp [h]
      have := ih (fun x hx => hws x (by simp [hx]))
      simp only [List.findIdx?_map] at this
      rw [this]

theorem notbig_of_lt {z : Word} (h : z.toNat < 2 ^ 32) : ¬ 4294967296 ≤ z := by
  intro hh
  have := UInt64.le_iff_toNat_le.mp hh
  have e : (4294967296 : Word).toNat = 4294967296 := by decide
  omega

theorem lt_of_notbig {z : Word} (h : ¬ 4294967296 ≤ z) : z.toNat < 2 ^ 32 := by
  have : ¬ (4294967296 : Word).toNat ≤ z.toNat := fun hh => h (UInt64.le_iff_toNat_le.mpr hh)
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
    simp only [ConRon.Arena.nestCanonSub, this, if_false]; rfl
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
        simp only [pinWordV, hpne, if_false, Option.some.injEq] at hpw
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

section census
variable (p : Prog) (hf : p.lookup "sl_find" = some slFind) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hp : p.lookup "nest_canon_sub" = some nestCanonSub)
include hf hpw hsf hsp his hff hfp hif hp

/-- **`nest_canon_sub` refines `nestCanonSub`**. -/
@[refines ConRon.Arena.nestCanonSub]
theorem nestCanonSub_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl us nn c v : Word) (names : List NIdx) (hc : H c) (hus : H us) (hv : H v)
    (hS : StageR dn vis fe s₀.mem a₀) (hdec : decHL s₀.mem no.toNat nl.toNat = some names)
    (hb : no.toNat + nl.toNat < 2 ^ 64) (hnn : nn.toNat + names.length < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_canon_sub" [no, nl, us, nn, c, v]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.nestCanonSub names (decI us) nn.toNat (decI c) (decI v)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestCanonSub names (decI us) nn.toNat (decI c) (decI v)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decOE s'.mem r (AM.res (ConRon.Arena.nestCanonSub names (decI us) nn.toNat (decI c) (decI v)) a₀); ⊤⦄ := by
  refine triple_post (nestCanonSub_spec p hf hpw hsf hsp his hff hfp hif hp n s₀ no nl us nn c v) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := canonW_ok n dn fe vis _ _ a₀ no nl us nn c v names r hm hS hc hus hv hdec hb hnn
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

/-! ## `nest_frame_mates_go` -/

mutual
def matesW : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, c, off, l, oO, oL =>
    if l = 0 then some ([oO, oL], m)
    else matesK1 n m c off l oO oL (containsW n m oO oL (rdW (m.arr64 EREC) off))
def matesK1 (n : Nat) (m : Mem) (c off l oO oL : Word) : Option Word → Option (List Word × Mem)
  | none => none
  | some b =>
    if rdW (m.arr64 EREC) off = c ∨ b ≠ 0 then matesK3 (matesW n m c (off + 1) (l - 1) oO oL)
    else matesK2 n c off l (snocW n m oO oL (rdW (m.arr64 EREC) off))
def matesK2 (n : Nat) (c off l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => matesK3 (matesW n m2 c (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0))
def matesK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([r.headD 0, r.tail.headD 0], m3)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (c off l oO oL b : Word) (r r2 : List Word)
theorem matesW_nil (h : l = 0) : matesW (n + 1) m c off l oO oL = some ([oO, oL], m) := by simp [matesW, h]
theorem matesW_cons (h : l ≠ 0) : matesW (n + 1) m c off l oO oL =
    matesK1 n m c off l oO oL (containsW n m oO oL (rdW (m.arr64 EREC) off)) := by simp [matesW, h]
theorem matesK1_skip (h : rdW (m.arr64 EREC) off = c ∨ b ≠ 0) : matesK1 n m c off l oO oL (some b) =
    matesK3 (matesW n m c (off + 1) (l - 1) oO oL) := by simp only [matesK1]; rw [if_pos h]
theorem matesK1_add (h : ¬ (rdW (m.arr64 EREC) off = c ∨ b ≠ 0)) : matesK1 n m c off l oO oL (some b) =
    matesK2 n c off l (snocW n m oO oL (rdW (m.arr64 EREC) off)) := by simp only [matesK1]; rw [if_neg h]
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
  simp only [h0, if_false] at h
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
    · rw [if_pos ⟨h1, by omega⟩, if_pos h1]
    · rw [if_neg (by omega), if_neg h1]
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
    rw [hget, if_neg (by omega), if_neg (by omega)]

theorem snocW_decK {k : IdxKind} {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} {xs : List (Idx k)}
    (h : snocW n m o l x = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hx : x.toNat < 2 ^ 32) (hxs : decHL m o.toNat l.toNat = some xs) :
    r = [rdW (m.arr64 CTL) 200, l + 1] ∧
    decHL m' (rdW (m.arr64 CTL) 200).toNat (l + 1).toNat = some (xs ++ [decI x]) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ (l + 1).toNat = l.toNat + 1 ∧
    (rdW (m.arr64 CTL) 200).toNat + (l + 1).toNat = iwTop m' := by
  obtain ⟨hr, hl1, hqt, hfr, hg, htop, hget⟩ := snocW_core h hsz hc hsrc
  refine ⟨hr, ?_, hg, hfr, hl1, by omega⟩
  simp only [decHL]
  rw [hl1, hslice?_add, hqt]
  have h1 : (hslice? (iwA m') (iwTop m) l.toNat : Option (List (Idx k))) = some xs := by
    rw [← hxs]; simp only [decHL]
    apply hslice?_congr
    intro j hj
    simp only [iwA, hget]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 1; omega
  have h2 : (hslice? (iwA m') (iwTop m + l.toNat) 1 : Option (List (Idx k))) = some [decI x] := by
    rw [hslice?_succ]
    have : (hd? (iwA m') (iwTop m + l.toNat) : Option (Idx k)) = some (decI x) := by simp [hd?, iwA, hget, hx]
    rw [this]; simp [hslice?]
  rw [h1, h2]; simp

theorem contains_decI (ws : List Word) (x : Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hx : x.toNat < 2 ^ 32) :
    (ws.map (fun w => (decI w : NIdx))).contains (decI x) = ws.contains x := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.contains_cons, decI_beq' x w hx (hws w (by simp))]
    have := ih (fun y hy => hws y (by simp [hy]))
    rw [this]
    by_cases h : x = w <;> simp [h]

theorem matesW_ok (n : Nat) : ∀ (m m' : Mem) (c off l oO oL : Word) (block out : List NIdx) (r : List Word),
    matesW n m c off l oO oL = some (r, m') → (m.arr64 IW).size < 2 ^ 64 → 200 < (m.arr64 CTL).size →
    (m.arr64 EREC).size < 2 ^ 64 →
    H c → hslice? (erA m) off.toNat l.toNat = some block → decHL m oO.toNat oL.toNat = some out →
    oO.toNat + oL.toNat ≤ iwTop m → oO.toNat + oL.toNat < 2 ^ 64 →
    decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (ConRon.Arena.nestFrameMates.go (decI c) block out) ∧
    IWGrow m m' ∧ m'.arr64 EREC = m.arr64 EREC ∧
    (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  induction n with
  | zero => intro m m' c off l oO oL block out r h; simp [matesW] at h
  | succ n ih =>
    intro m m' c off l oO oL block out r h hsz hc200 hEs hc hblock hout hit hb
    by_cases hl : l = 0
    · rw [matesW_nil n m c off l oO oL hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : block = [] := by
        have h0 : l.toNat = 0 := by rw [hl]; rfl
        rw [h0] at hblock; simpa [hslice?] using hblock.symm
      subst this
      exact ⟨by simpa [ConRon.Arena.nestFrameMates.go] using hout, IWGrow.refl _, rfl, hit⟩
    · have hl1 : l.toNat = (l.toNat - 1) + 1 := by have := toNat_ne_zero' hl; omega
      rw [hl1, hslice?_succ] at hblock
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hblock
      obtain ⟨x, hx, rest, hrest, rfl⟩ := hblock
      obtain ⟨w0, hw0, hw0lt, hw0d⟩ := hd?_some hx
      have hrd : rdW (m.arr64 EREC) off = w0 := by
        have : (m.arr64 EREC)[off.toNat]? = some w0 := hw0
        simp only [rdW, this, Option.getD_some]
      obtain ⟨ws, hws, rfl, hwlt⟩ := slR_of_decHL m _ _ out hout hb
      simp only [UInt64.ofNat_toNat] at hws
      rw [matesW_cons n m c off l oO oL hl, hrd] at h
      rcases hcn : containsW n m oO oL w0 with _ | b <;> rw [hcn] at h; · simp [matesK1] at h
      have hbv := containsW_ok n _ _ _ _ _ _ hws hcn
      have hlt : off.toNat < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp hw0).1
      have hoff1 : (off + 1).toNat = off.toNat + 1 := toNat_add_one' (by omega)
      have hl1' : (l - 1).toNat = l.toNat - 1 := toNat_sub_one' hl
      have hcond : ((decI w0 : NIdx) == decI c || (ws.map (fun w => (decI w : NIdx))).contains (decI w0)) =
          decide (w0 = c ∨ b ≠ 0) := by
        rw [decI_beq' w0 c hw0lt hc, contains_decI ws w0 hwlt hw0lt, hbv]
        by_cases h1 : w0 = c <;> by_cases h2 : ws.contains w0 = true <;> simp [h1, h2]
      have hblock' : hslice? (erA m) (off + 1).toNat (l - 1).toNat = some rest := by
        rw [hoff1, hl1']; exact hrest
      subst hw0d
      by_cases hskip : (w0 = c ∨ b ≠ 0)
      · have hskip' : rdW (m.arr64 EREC) off = c ∨ b ≠ 0 := by rw [hrd]; exact hskip
        rw [matesK1_skip n m c off l oO oL b hskip'] at h
        rcases hrec : matesW n m c (off + 1) (l - 1) oO oL with _ | ⟨r3, m3⟩ <;> rw [hrec] at h; · simp [matesK3] at h
        rw [matesK3_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hd, hg, hE', htop⟩ := ih m m3 c (off + 1) (l - 1) oO oL rest _ r3 hrec hsz hc200 hEs hc
          hblock' hout hit hb
        refine ⟨?_, hg, hE', by simpa using htop⟩
        rw [ConRon.Arena.nestFrameMates.go.eq_2, if_pos (by rw [hcond]; simpa using hskip)]
        simpa using hd
      · have hskip' : ¬ (rdW (m.arr64 EREC) off = c ∨ b ≠ 0) := by rw [hrd]; exact hskip
        rw [matesK1_add n m c off l oO oL b hskip', hrd] at h
        rcases hsn : snocW n m oO oL w0 with _ | ⟨r2, m2⟩ <;> rw [hsn] at h; · simp [matesK2] at h
        rw [matesK2_some] at h
        obtain ⟨hr2, hdec2, hg2, hfr2, hl2, htop2⟩ := snocW_decK hsn hsz hc200 hit hw0lt hout
        subst hr2
        simp only [List.headD_cons, List.tail_cons] at h
        rcases hrec : matesW n m2 c (off + 1) (l - 1) (rdW (m.arr64 CTL) 200) (oL + 1) with _ | ⟨r3, m3⟩ <;> rw [hrec] at h; · simp [matesK3] at h
        rw [matesK3_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hE2 : m2.arr64 EREC = m.arr64 EREC := hfr2.1 EREC (by decide) (by decide)
        have hsz2 : (m2.arr64 IW).size < 2 ^ 64 := by rw [hfr2.2.2.1 IW]; exact hsz
        have hc2 : 200 < (m2.arr64 CTL).size := by rw [hfr2.2.2.1 CTL]; exact hc200
        obtain ⟨hd, hg, hE', htop⟩ := ih m2 m3 c (off + 1) (l - 1) _ (oL + 1) rest _ r3 hrec hsz2 hc2
          (by rw [hE2]; exact hEs) hc (by simp only [erA]; rw [hE2]; exact hblock') (by simpa using hdec2)
          (Nat.le_of_eq htop2) (by have : iwTop m2 < 2 ^ 64 := (rdW (m2.arr64 CTL) 200).toNat_lt; omega)
        refine ⟨?_, hg2.trans hg, hE'.trans hE2, by simpa using htop⟩
        rw [ConRon.Arena.nestFrameMates.go.eq_2, if_neg (by rw [hcond]; simpa using hskip)]
        simpa using hd

section census
variable (p : Prog) (hc : p.lookup "sl_contains" = some slContains) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hcp : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
  (hp : p.lookup "nest_frame_mates_go" = some nestFrameMatesGoL)
include hc ha hcp hsn hp

/-- **`nest_frame_mates_go` refines `nestFrameMates.go`**: the block is an `EREC` slice, the
accumulator an `IW` slice. -/
@[refines ConRon.Arena.nestFrameMates.go]
theorem nestFrameMatesGo_refines (n : Nat) (s₀ : St) (c off l oO oL : Word) (block out : List NIdx)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hc200 : 200 < (s₀.mem.arr64 CTL).size)
    (hEs : (s₀.mem.arr64 EREC).size < 2 ^ 64) (hcH : H c)
    (hblock : hslice? (erA s₀.mem) off.toNat l.toNat = some block)
    (hout : decHL s₀.mem oO.toNat oL.toNat = some out)
    (hit : oO.toNat + oL.toNat ≤ iwTop s₀.mem) (hb : oO.toNat + oL.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_mates_go" [c, off, l, oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (ConRon.Arena.nestFrameMates.go (decI c) block out) ∧ IWGrow s₀.mem s'.mem ∧
      s'.mem.arr64 EREC = s₀.mem.arr64 EREC ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  refine triple_post (nestFrameMatesGo_spec p hc ha hcp hsn hp n s₀ c off l oO oL) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨h1, h2, h3, h4⟩ := matesW_ok n _ _ c off l oO oL block out r hm hsz hc200 hEs hcH hblock hout hit hb
  exact ⟨hl, h1, h2, h3, h4⟩

end census

theorem decHL_zero_zero {k : IdxKind} (m : Mem) : (decHL m 0 0 : Option (List (Idx k))) = some [] := by
  simp [decHL, hslice?]

section census2
variable (p : Prog) (hc : p.lookup "sl_contains" = some slContains) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hcp : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
  (hgo : p.lookup "nest_frame_mates_go" = some nestFrameMatesGoL)
  (hx : p.lookup "env_ix" = some envIxL) (hg : p.lookup "env_row_get" = some envRowGetL)
  (hf : p.lookup "env_find" = some envFindL) (hbo : p.lookup "nest_block_of" = some nestBlockOfL)
  (hp : p.lookup "nest_frame_mates" = some nestFrameMatesL)
include hc ha hcp hsn hgo hx hg hf hbo hp

/-- **`nest_frame_mates` refines `nestFrameMates`**. -/
@[refines ConRon.Arena.nestFrameMates]
theorem nestFrameMates_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis c : Word) (hcH : H c) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_frame_mates" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (ConRon.Arena.nestFrameMates fe (decI c)) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  obtain ⟨hOK1, hOK2, hOK3, hOK4, hOK5⟩ := hS.2
  have hE := hS.1.env
  simp only [invoke_eq _ hp, callFn, nestFrameMatesL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      nestBlockOf_refines p hx hg hf hbo n (dn := dn) (fe := fe),
      nestFrameMatesGo_refines p hc ha hcp hsn hgo n (block := ConRon.Arena.nestBlockOf fe (decI c)) (out := [])] <;> finish (gen := 20) [ConRon.Arena.nestFrameMates, decHL_zero_zero]

end census2

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
theorem maGoW_abort (hf : f = 0) : maGoW (n + 1) m no nl f h = none := by simp [maGoW, hf]
theorem maGoW_view (hf : f ≠ 0) : maGoW (n + 1) m no nl f h = maG1 n m no nl f h (eViewW m h) := by
  simp [maGoW, hf]
theorem maG1_leaf (hv : v ≠ []) (hg : v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8) :
    maG1 n m no nl f h v = some (0, m) := by simp only [maG1]; rw [if_neg hv, if_pos hg]
theorem maG1_const (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : v.headD 0 = 3) : maG1 n m no nl f h v = maC m (containsW n m no nl (v.tail.headD 0)) := by
  simp only [maG1]; rw [if_neg hv, if_neg hg, if_pos h3]
theorem maG1_node (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : ¬ v.headD 0 = 3) : maG1 n m no nl f h v = maG3 n m no nl f h v (mfindG maSch m h 0) := by
  simp only [maG1]; rw [if_neg hv, if_neg hg, if_neg h3]
theorem maG3_abort (hr : fr = []) : maG3 n m no nl f h v fr = none := by simp [maG3, hr]
theorem maG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    maG3 n m no nl f h v fr = some (rdW (m.arr64 MAM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [maG3]; rw [if_neg hr, if_pos hh]
theorem maG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    maG3 n m no nl f h v fr = maG4 h (maNodeW n m no nl (f - 1) (v.headD 0) (v.tail.headD 0)
      (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [maG3]; rw [if_neg hr, if_neg hh]
theorem maG4_some : maG4 h (some (r, m1)) = maG5 r (msetG maSch m1 h 0 r) := by rw [maG4]
theorem maG5_some : maG5 r (some m2) = some (r, m2) := by rw [maG5]
theorem maC_some : maC m (some r) = some (r, m) := by rw [maC]
theorem maNodeW_fvar (hg : g = 1) : maNodeW (n + 1) m no nl f1 g x y z = maGoW n m no nl f1 y := by
  simp [maNodeW, hg]
theorem maNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) : maNodeW (n + 1) m no nl f1 g x y z =
    maB1 n no nl f1 y (maGoW n m no nl f1 x) := by
  have : ¬ g = 1 := by
    intro e; rcases hg with h | h | h <;> (rw [e] at h; exact absurd h (by decide))
  simp only [maNodeW]; rw [if_neg this, if_pos hg]
theorem maNodeW_let (hg : g = 7) : maNodeW (n + 1) m no nl f1 g x y z =
    maL1 n no nl f1 y z (maGoW n m no nl f1 x) := by
  simp [maNodeW, hg]
theorem maNodeW_proj (hg1 : g ≠ 1) (hg2 : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (hg3 : g ≠ 7) :
    maNodeW (n + 1) m no nl f1 g x y z = maP1 n no nl x (maGoW n m no nl f1 z) := by
  simp only [maNodeW]; rw [if_neg hg1, if_neg hg2, if_neg hg3]
theorem maB1_some : maB1 n no nl f1 y (some (b1, m1)) = maB2 b1 (maGoW n m1 no nl f1 y) := by rw [maB1]
theorem maB2_some : maB2 b1 (some (b2, m2)) = some (if b1 ≠ 0 ∨ b2 ≠ 0 then 1 else 0, m2) := by rw [maB2]
theorem maL1_some : maL1 n no nl f1 y z (some (b1, m1)) = maL2 n no nl f1 z b1 (maGoW n m1 no nl f1 y) := by rw [maL1]
theorem maL2_some : maL2 n no nl f1 z b1 (some (b2, m2)) = maL3 b1 b2 (maGoW n m2 no nl f1 z) := by rw [maL2]
theorem maL3_some : maL3 b1 b2 (some (b3, m3)) =
    some (if b1 ≠ 0 ∨ b2 ≠ 0 ∨ b3 ≠ 0 then 1 else 0, m3) := by rw [maL3]
theorem maP1_some : maP1 n no nl x (some (b1, m1)) = maP2 b1 m1 (containsW n m1 no nl x) := by rw [maP1]
theorem maP2_some : maP2 b1 m1 (some b2) = some (if b1 ≠ 0 ∨ b2 ≠ 0 then 1 else 0, m1) := by rw [maP2]
end arms

attribute [ind_grind] maGoW_abort maGoW_view maG1_leaf maG1_const maG1_node maG3_abort maG3_hit
  maG3_miss maG4_some maG5_some maC_some maNodeW_fvar maNodeW_bin maNodeW_let maNodeW_proj maB1_some
  maB2_some maL1_some maL2_some maL3_some maP1_some maP2_some

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

include hc hgo hnode in
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

theorem mentionsAnyGo_succ' (names : List NIdx) (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx) :
    ConRon.Arena.mentionsAnyGo names memo (fuel + 1) h = (do
      let v ← view h
      match v with
      | .bvar _ => pure (false, memo)
      | .sort _ => pure (false, memo)
      | .lit _ => pure (false, memo)
      | .const n _ => pure (names.contains n, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← maArm names memo fuel v
          pure (r, m.insert h r)) := by
  rw [ConRon.Arena.mentionsAnyGo.eq_2]
  congr 1
  funext v
  cases v <;> first | rfl | (simp only [maArm, bind_assoc, pure_bind]; rfl)

theorem getD2_eq (vl : List Word) : vl.getD 2 0 = vl.tail.tail.headD 0 := by
  rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> rfl
theorem getD3_eq (vl : List Word) : vl.getD 3 0 = vl.tail.tail.tail.headD 0 := by
  rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩ <;> rfl
theorem getD1_eq' (vl : List Word) : vl.getD 1 0 = vl.tail.headD 0 := by
  rcases vl with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> rfl

theorem maFrame_arena {m m' : Mem} {a : AState} (hf : MemFrame [MAM] [203] m m') (hR : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame (fun b hb => by simp at hb; subst hb; simp [arenaArrs, storeArrs, memoArrs, MAM])
    (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf hR

theorem maFrame_iw {m m' : Mem} (hf : MemFrame [MAM] [203] m m') : m'.arr64 IW = m.arr64 IW :=
  hf.1 IW (by decide) (by decide)

theorem slR_congr {m m' : Mem} (hI : m'.arr64 IW = m.arr64 IW) {o l : Word} {ws : List Word}
    (h : SlR m o l ws) : SlR m' o l ws := by
  induction h with
  | nil => exact SlR.nil
  | @cons o l ws hl _ ih =>
    have := SlR.cons (m := m') (o := o) hl ih
    simpa [rdW, hI] using this

/-- The word-valued memo relation of the mentions walk. -/
abbrev maMR (m : Mem) (mp : Std.HashMap EIdx Bool) : Prop :=
  MemoRG maSch bmKey (fun w : Word => w != 0) m mp

def MaGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (no nl f h r : Word) (ws : List Word) (mp : Std.HashMap EIdx Bool),
    maGoW n m no nl f h = some (r, m') → ArenaR m a → H h → SlR m no nl ws →
    (∀ w ∈ ws, w.toNat < 2 ^ 32) → maMR m mp →
    ∃ b mp', (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f.toNat (decE h)).run a =
        .ok ((b, mp'), a) ∧ (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m'

theorem maNodeBin_ok (n : Nat) (ih : MaGoOK n) (m m' : Mem) (a : AState) (no nl f1 g x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hg : g = 4 ∨ g = 5 ∨ g = 6) (hx : H x) (hy : H y)
    (hn : maNodeW (n + 1) m no nl f1 g x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp) :
    ∃ b mp', (do
        let (b1, m) ← ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f1.toNat (decE x)
        let (b2, m2) ← ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) m f1.toNat (decE y)
        pure (b1 || b2, m2) : AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m' := by
  rw [maNodeW_bin n m no nl f1 g x y z hg] at hn
  rcases h1 : maGoW n m no nl f1 x with _ | ⟨b1w, m1⟩ <;> rw [h1] at hn; · simp [maB1] at hn
  rw [maB1_some] at hn
  rcases h2 : maGoW n m1 no nl f1 y with _ | ⟨b2w, m2⟩ <;> rw [h2] at hn; · simp [maB2] at hn
  rw [maB2_some] at hn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
  obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a no nl f1 x b1w ws mp h1 hA hx hws hwlt hM
  obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m2 a no nl f1 y b2w ws mp1 h2 (maFrame_arena hf1 hA) hy
    (slR_congr (maFrame_iw hf1) hws) hwlt hM1
  refine ⟨c1 || c2, mp2, ?_, ?_, hM2, hf1.trans hf2⟩
  · simp only [StateT.run_bind]
    simp only [hr1, except_ok_bind, StateT.run_bind, hr2]
    rfl
  · rw [← hb1, ← hb2]
    by_cases e1 : b1w = 0 <;> by_cases e2 : b2w = 0 <;> simp [e1, e2]

theorem maNodeLet_ok (n : Nat) (ih : MaGoOK n) (m m' : Mem) (a : AState) (no nl f1 x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hx : H x) (hy : H y) (hz : H z)
    (hn : maNodeW (n + 1) m no nl f1 7 x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp) :
    ∃ b mp', (do
        let (b1, m) ← ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f1.toNat (decE x)
        let (b2, m2) ← ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) m f1.toNat (decE y)
        let (b3, m3) ← ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) m2 f1.toNat (decE z)
        pure (b1 || b2 || b3, m3) : AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m' := by
  rw [maNodeW_let n m no nl f1 7 x y z rfl] at hn
  rcases h1 : maGoW n m no nl f1 x with _ | ⟨b1w, m1⟩ <;> rw [h1] at hn; · simp [maL1] at hn
  rw [maL1_some] at hn
  rcases h2 : maGoW n m1 no nl f1 y with _ | ⟨b2w, m2⟩ <;> rw [h2] at hn; · simp [maL2] at hn
  rw [maL2_some] at hn
  rcases h3 : maGoW n m2 no nl f1 z with _ | ⟨b3w, m3⟩ <;> rw [h3] at hn; · simp [maL3] at hn
  rw [maL3_some] at hn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
  obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a no nl f1 x b1w ws mp h1 hA hx hws hwlt hM
  obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m2 a no nl f1 y b2w ws mp1 h2 (maFrame_arena hf1 hA) hy
    (slR_congr (maFrame_iw hf1) hws) hwlt hM1
  obtain ⟨c3, mp3, hr3, hb3, hM3, hf3⟩ := ih m2 m3 a no nl f1 z b3w ws mp2 h3
    (maFrame_arena (hf1.trans hf2) hA) hz (slR_congr (maFrame_iw (hf1.trans hf2)) hws) hwlt hM2
  refine ⟨c1 || c2 || c3, mp3, ?_, ?_, hM3, (hf1.trans hf2).trans hf3⟩
  · simp only [StateT.run_bind]
    simp only [hr1, except_ok_bind, StateT.run_bind, hr2, hr3]
    rfl
  · rw [← hb1, ← hb2, ← hb3]
    by_cases e1 : b1w = 0 <;> by_cases e2 : b2w = 0 <;> by_cases e3 : b3w = 0 <;> simp [e1, e2, e3]

theorem maNodeProj_ok (n : Nat) (ih : MaGoOK n) (m m' : Mem) (a : AState) (no nl f1 x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hx : H x) (hz : H z)
    (hn : maNodeW (n + 1) m no nl f1 9 x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp) :
    ∃ b mp', (do
        let (b, m) ← ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f1.toNat (decE z)
        pure ((ws.map (fun w => (decI w : NIdx))).contains (decI x) || b, m) :
          AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m' := by
  rw [maNodeW_proj n m no nl f1 9 x y z (by decide) (by decide) (by decide)] at hn
  rcases h1 : maGoW n m no nl f1 z with _ | ⟨b1w, m1⟩ <;> rw [h1] at hn; · simp [maP1] at hn
  rw [maP1_some] at hn
  rcases h2 : containsW n m1 no nl x with _ | b2w <;> rw [h2] at hn; · simp [maP2] at hn
  rw [maP2_some] at hn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
  obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a no nl f1 z b1w ws mp h1 hA hz hws hwlt hM
  have hws1 := slR_congr (maFrame_iw hf1) hws
  have hcont := containsW_ok n _ _ _ _ _ _ hws1 h2
  refine ⟨(ws.map (fun w => (decI w : NIdx))).contains (decI x) || c1, mp1, ?_, ?_, hM1, hf1⟩
  · simp only [StateT.run_bind]
    simp only [hr1, except_ok_bind]
    rfl
  · rw [← hb1, contains_decI ws x hwlt hx, hcont]
    generalize ws.contains x = bc
    by_cases e1 : b1w = 0 <;> cases bc <;> simp [e1]

theorem maNodeFVar_ok (n : Nat) (ih : MaGoOK n) (m m' : Mem) (a : AState) (no nl f1 x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hy : H y)
    (hn : maNodeW (n + 1) m no nl f1 1 x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp) :
    ∃ b mp', (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f1.toNat (decE y)).run a =
        .ok ((b, mp'), a) ∧ (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m' := by
  rw [maNodeW_fvar n m no nl f1 1 x y z rfl] at hn
  exact ih m m' a no nl f1 y r ws mp hn hA hy hws hwlt hM

/-- The non-leaf, non-`const` views: the ones whose walk goes through `mentions_any_node`. -/
def NodeV : ENodeView → Prop
  | .fvar .. | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => True
  | _ => False

theorem maNode_arm (k : Nat) (ih : MaGoOK k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeV v) (m m' : Mem) (a : AState) (no nl f1 r : Word) (ws : List Word)
    (mp : Std.HashMap EIdx Bool)
    (hn : maNodeW (k + 1) m no nl f1 (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0) = some (r, m'))
    (hA : ArenaR m a) (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp) :
    ∃ b mp', (maArm (ws.map (fun w => (decI w : NIdx))) mp f1.toNat v).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m' := by
  cases v with
  | fvar i ty =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, -, hy, hdy⟩ := hvr
    rw [hg] at hn
    have := maNodeFVar_ok k ih m m' a no nl f1 _ _ _ r ws mp hy hn hA hws hwlt hM
    rw [← hdy] at *
    simp only [maArm]; exact this
  | app f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := maNodeBin_ok k ih m m' a no nl f1 _ _ _ _ r ws mp (Or.inl hg) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [maArm]; exact this
  | lam f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := maNodeBin_ok k ih m m' a no nl f1 _ _ _ _ r ws mp (Or.inr (Or.inl hg)) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [maArm]; exact this
  | forallE f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := maNodeBin_ok k ih m m' a no nl f1 _ _ _ _ r ws mp (Or.inr (Or.inr hg)) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [maArm]; exact this
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := maNodeLet_ok k ih m m' a no nl f1 _ _ _ r ws mp hx hy hz hn hA hws hwlt hM
    rw [hdx, hdy, hdz] at this
    simp only [maArm]; exact this
  | proj s i e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, -, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := maNodeProj_ok k ih m m' a no nl f1 _ _ _ r ws mp hx hz hn hA hws hwlt hM
    rw [hdz, hdx] at this
    simp only [maArm]; exact this
  | bvar _ => exact False.elim hnv
  | sort _ => exact False.elim hnv
  | const _ _ => exact False.elim hnv
  | lit _ => exact False.elim hnv

theorem maSch_wf : maSch.WF := ⟨by decide, by decide⟩

theorem maTwin_node (names : List NIdx) (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx)
    (a : AState) (v : ENodeView) (hv : a.store.view h = some v) (hnv : NodeV v) :
    (ConRon.Arena.mentionsAnyGo names memo (fuel + 1) h).run a =
      ((match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← maArm names memo fuel v
          pure (r, m.insert h r) : AM (Bool × Std.HashMap EIdx Bool)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | rw [mentionsAnyGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]

theorem maGo_nodeCase (j : Nat) (ih : ∀ k, k + 1 < j + 1 → MaGoOK k) (m m' : Mem) (a : AState)
    (no nl f h r : Word) (ws : List Word) (mp : Std.HashMap EIdx Bool) (F : Nat)
    (hF : f.toNat = F + 1) (hf0 : f ≠ 0) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v) (hnv : NodeV v)
    (hv : a.store.view (decE h) = some v) (hvl : vl ≠ [])
    (hgs : vl.headD 0 = 1 ∨ vl.headD 0 = 4 ∨ vl.headD 0 = 5 ∨ vl.headD 0 = 6 ∨ vl.headD 0 = 7 ∨ vl.headD 0 = 9)
    (hb : maG1 j m no nl f h vl = some (r, m')) (hA : ArenaR m a) (hh : H h)
    (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp) :
    ∃ b mp', (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp (F + 1) (decE h)).run a =
        .ok ((b, mp'), a) ∧ (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m' := by
  have hnl : ¬ (vl.headD 0 = 0 ∨ vl.headD 0 = 2 ∨ vl.headD 0 = 8) := by
    rcases hgs with e | e | e | e | e | e <;> rw [e] <;> decide
  have hn3 : ¬ vl.headD 0 = 3 := by
    rcases hgs with e | e | e | e | e | e <;> rw [e] <;> decide
  rw [maG1_node j m no nl f h vl hvl hnl hn3] at hb
  rw [maTwin_node _ _ _ _ a v hv hnv]
  by_cases hfr : mfindG maSch m h 0 = []
  · rw [maG3_abort j m no nl f h vl _ hfr] at hb; simp at hb
  by_cases hhit : (mfindG maSch m h 0).headD 0 ≠ 0
  · rw [maG3_hit j m no nl f h vl _ hfr hhit] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    have hmem := memoRG_hit maSch bmKey (fun w : Word => w != 0) m mp hM h 0 hfr hhit ⟨hh, rfl⟩
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmem
    refine ⟨_, mp, ?_, rfl, hM, MemFrame.refl _ _ _⟩
    simp only [hmem]; rfl
  · rw [maG3_miss j m no nl f h vl _ hfr hhit] at hb
    have hmiss := memoRG_miss maSch bmKey (fun w : Word => w != 0) m mp hM h 0 ⟨hh, rfl⟩ hfr (by simpa using hhit)
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmiss
    cases j with
    | zero => simp [maNodeW, maG4] at hb
    | succ k =>
      rcases hnode : maNodeW (k + 1) m no nl (f - 1) (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
          (vl.tail.tail.tail.headD 0) with _ | ⟨rn, m1⟩; · rw [hnode] at hb; simp [maG4] at hb
      rw [hnode, maG4_some] at hb
      rcases hset : msetG maSch m1 h 0 rn with _ | m2 <;> rw [hset] at hb; · simp [maG5] at hb
      rw [maG5_some] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have hf1 : f - 1 = f - 1 := rfl
      have hF1 : (f - 1).toNat = F := by rw [toNat_sub_one' hf0, hF]; rfl
      obtain ⟨bb, mp1, hr1, hbb, hM1, hfr1⟩ := maNode_arm k (ih k (by omega)) vl v hvr hnv m m1 a no nl (f - 1) rn
        ws mp hnode hA hws hwlt hM
      rw [hF1] at hr1
      have hset' := memoRG_set maSch maSch_wf bmKey (fun w : Word => w != 0) m1 mp1 hM1 h 0 rn ⟨hh, rfl⟩ m2 hset
      have hfs : MemFrame [MAM] [203] m1 m2 := msetG_frame maSch maSch_wf m1 m2 h 0 rn hset
      refine ⟨bb, mp1.insert (decE h) bb, ?_, hbb, ?_, hfr1.trans hfs⟩
      · rw [hmiss]
        simp only [StateT.run_bind, hr1, except_ok_bind]
        rfl
      · rw [← hbb]; exact hset'

theorem maGo_step_ok (j : Nat) (ih : ∀ k, k + 1 < j + 1 → MaGoOK k) : MaGoOK (j + 1) := by
  intro m m' a no nl f h r ws mp hb hA hh hws hwlt hM
  by_cases hf0 : f = 0
  · rw [maGoW_abort j m no nl f h hf0] at hb; simp at hb
  rw [maGoW_view j m no nl f h hf0] at hb
  obtain ⟨F, hF⟩ : ∃ F, f.toNat = F + 1 := ⟨f.toNat - 1, by have := toNat_ne_zero' hf0; omega⟩
  cases hvl : eViewW m h with
  | nil => rw [hvl] at hb; simp [maG1] at hb
  | cons g vt =>
    have hne : eViewW m h ≠ [] := by rw [hvl]; simp
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA h hne
    rw [hvl] at hvr hb
    cases v with
    | bvar i =>
      rw [hF, mentionsAnyGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 0 := by simpa [ViewR] using hvr.1
      rw [maG1_leaf j m no nl f h _ (by simp) (Or.inl hg0)] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | sort u =>
      rw [hF, mentionsAnyGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 2 := by simpa [ViewR] using hvr.1
      rw [maG1_leaf j m no nl f h _ (by simp) (Or.inr (Or.inl hg0))] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | lit l =>
      rw [hF, mentionsAnyGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 8 := by simpa [ViewR] using hvr
      rw [maG1_leaf j m no nl f h _ (by simp) (Or.inr (Or.inr hg0))] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | const nn us =>
      rw [hF, mentionsAnyGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      simp only [ViewR, getD1_eq'] at hvr
      obtain ⟨hg3, hx, hdx, -⟩ := hvr
      have hg3' : (g :: vt).headD 0 = 3 := hg3
      rw [maG1_const j m no nl f h _ (by simp) (by rw [hg3']; decide) hg3'] at hb
      rcases hc : containsW j m no nl ((g :: vt).tail.headD 0) with _ | rc <;> rw [hc] at hb; · simp [maC] at hb
      rw [maC_some] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have hcv := containsW_ok j _ _ _ _ _ _ hws hc
      refine ⟨(ws.map (fun w => (decI w : NIdx))).contains nn, mp, ?_, ?_, hM, MemFrame.refl _ _ _⟩
      · rfl
      · rw [hcv, ← hdx, contains_decI ws _ hwlt hx]
        generalize ws.contains _ = bc
        cases bc <;> simp
    | fvar i ty => rw [hF]; exact maGo_nodeCase j ih m m' a no nl f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inl hvr.1) hb hA hh hws hwlt hM
    | app f' x' => rw [hF]; exact maGo_nodeCase j ih m m' a no nl f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inl hvr.1)) hb hA hh hws hwlt hM
    | lam f' x' => rw [hF]; exact maGo_nodeCase j ih m m' a no nl f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inl hvr.1))) hb hA hh hws hwlt hM
    | forallE f' x' => rw [hF]; exact maGo_nodeCase j ih m m' a no nl f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inr (Or.inl hvr.1)))) hb hA hh hws hwlt hM
    | letE t v' b' => rw [hF]; exact maGo_nodeCase j ih m m' a no nl f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvr.1))))) hb hA hh hws hwlt hM
    | proj s i e => rw [hF]; exact maGo_nodeCase j ih m m' a no nl f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hvr.1))))) hb hA hh hws hwlt hM

theorem maGoOK (n : Nat) : MaGoOK n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro m m' a no nl f h r ws mp hb; simp [maGoW] at hb
    | succ j => exact maGo_step_ok j (fun k hk => ih k (by omega))

/-- **The stage relation across a writer above array 136 and `CTL[129]`** (the per-call memos). -/
theorem StageR.frame_hi {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {A : List ArrId} {C : List Word} (hS : StageR dn vis fe m a) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, 137 ≤ b ∧ b < 256 ∧ (b < 140 ∨ 144 ≤ b)) (hC : ∀ x ∈ C, 130 ≤ x.toNat ∧ x.toNat ≠ 133) (hA2 : IW ∉ A) (hC2 : (200 : Word) ∉ C) :
    StageR dn vis fe m' a ∧ IWGrow m m' := by
  have hI : m'.arr64 IW = m.arr64 IW := hf.1 IW hA2 (by decide)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (fun h => by have := hA _ h; simp [EREC] at this)
    (by decide)
  have h200 : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hf.2.1 200 hC2
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 :=
    hf.2.1 129 (fun h => by have := (hC _ h).1; simp at this)
  refine ⟨⟨CheckR.frame_hi hA hC hf hS.1, ?_⟩, ?_⟩
  · simp only [IWOK, iwTop, erTop, hI, hE, h200, h129, hf.2.2.1 CTL]; exact hS.2
  · refine ⟨?_, ?_, fun i _ => by rw [hI], fun i _ => by rw [hE]⟩
    · simp only [iwTop, h200]; exact Nat.le_refl _
    · simp only [erTop, h129]; exact Nat.le_refl _

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hc : p.lookup "sl_contains" = some slContains)
  (hf : p.lookup "ma_find" = some (memoFindG maSch)) (hput : p.lookup "ma_put" = some (memoPutG maSch))
  (hgo : p.lookup "mentions_any_go" = some mentionsAnyGo)
  (hnode : p.lookup "mentions_any_node" = some mentionsAnyNode)
include hv hc hf hput hgo hnode

/-- **`mentions_any_go` (with `mentions_any_node`) refines `mentionsAnyGo`**, from a memo related to
the twin's. -/
@[refines ConRon.Arena.mentionsAnyGo]
theorem mentionsAnyGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl f h : Word) (ws : List Word) (mp : Std.HashMap EIdx Bool) (hh : H h)
    (hS : StageR dn vis fe s₀.mem a₀) (hws : SlR s₀.mem no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hM : maMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mentions_any_go" [no, nl, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f.toNat (decE h)) a₀ ∧
      AM.st (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f.toNat (decE h)) a₀ = a₀ ∧
      (r.headD 0 != 0) =
        (AM.res (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f.toNat (decE h)) a₀).1 ∧
      maMR s'.mem
        (AM.res (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f.toNat (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post ((maGo_spec p hv hc hf hput hgo hnode n).1 s₀ no nl f h) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, mp', hrun, hb, hM', hfr⟩ := maGoOK n _ _ a₀ no nl f h _ ws mp hm hS.1.arena.1 hh hws hwlt hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  obtain ⟨hS', hg⟩ := StageR.frame_hi hS hfr (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp at hx; subst hx; decide) (by decide) (by decide)
  refine ⟨hl, hok, hst, by rw [hres]; exact hb, by rw [hres]; exact hM', hS', hg⟩

end census

end L.Ind
