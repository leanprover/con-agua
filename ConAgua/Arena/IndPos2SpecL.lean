import ConAgua.Arena.IndPos2SpecK
import ConAgua.Arena.IndRealWalk
import ConAgua.Arena.IndSumSpec7
import ConAgua.Arena.IndPosSpec7

/-! # `IndPos2`, the `nestPos` block's leaves (lane `indproofs2`, helper `pos2`): word models and
specs of the block's non-recursive helpers (`nest_frame_mates` with the stage relation,
`sl_new1`, `nest_frame_grp`, `nest_frame_holes`, `nest_cont_new_active`, `nest_cont_params_closed`,
…). Every model takes the exec fuel first and is `none` at `0`. -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_block_of`, `nest_frame_mates` -/

/-- **`nest_block_of(vis, c)` is its model `nboW`** (generated). -/
l_model nestBlockOf_specW (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hf : p.lookup "env_find" = some envFindL)
    (hp : p.lookup "nest_block_of" = some nestBlockOfL)
  fns [hp ↦ nboW]
  specs [envFind_specW p hx hg hf n]
  grind [ind_grind] finish [rdW_eq] gen 20

def nfmK (n : Nat) (c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => matesK3 (matesW n m1 c (r.headD 0) (r.tail.headD 0) 0 0)

/-- The model of `nest_frame_mates(vis, c)`. -/
def nfmW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, c => nfmK n c (nboW m vis c)

theorem nfmK_some (n : Nat) (c : Word) (r : List Word) (m1 : Mem) :
    nfmK n c (some (r, m1)) = matesK3 (matesW n m1 c (r.headD 0) (r.tail.headD 0) 0 0) := rfl
attribute [ind_grind] nfmK_some

/-- The lookups of `nest_frame_mates`. -/
structure FmLook (p : Prog) : Prop where
  hc : p.lookup "sl_contains" = some slContains
  ha : p.lookup "iw_alloc" = some iwAlloc
  hcp : p.lookup "iw_copy" = some iwCopy
  hsn : p.lookup "sl_snoc" = some slSnoc
  hgo : p.lookup "nest_frame_mates_go" = some nestFrameMatesGoL
  hx : p.lookup "env_ix" = some envIxL
  hg : p.lookup "env_row_get" = some envRowGetL
  hf : p.lookup "env_find" = some envFindL
  hbo : p.lookup "nest_block_of" = some nestBlockOfL
  hp : p.lookup "nest_frame_mates" = some nestFrameMatesL

theorem nestFrameMates_specW (p : Prog) (L : FmLook p) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_mates" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ nfmW n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ L.hp, callFn, nestFrameMatesL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        nestBlockOf_specW p L.hx L.hg L.hf L.hbo n,
        nestFrameMatesGo_spec p L.hc L.ha L.hcp L.hsn L.hgo n] <;>
      finish (gen := 20) [nfmW]

/-- `nest_frame_mates_go` keeps the stage relation (it writes `IW` by `sl_snoc` only). -/
theorem matesW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} (n : Nat) :
    ∀ (m m' : Mem) (c off l oO oL : Word) (r : List Word),
    matesW n m c off l oO oL = some (r, m') → StageR dn vis fe m a → StageR dn vis fe m' a := by
  induction n with
  | zero => intro m m' c off l oO oL r h; simp [matesW] at h
  | succ n ih =>
    intro m m' c off l oO oL r h hS
    by_cases hl : l = 0
    · rw [matesW_nil n m c off l oO oL hl] at h; cases h; exact hS
    rw [matesW_cons n m c off l oO oL hl] at h
    rcases hb : containsW n m oO oL (rdW (m.arr64 EREC) off) with _ | b <;> rw [hb] at h; · simp [matesK1] at h
    simp only [matesK1] at h
    split at h
    · cases hr : matesW n m c (off + 1) (l - 1) oO oL with
      | none => rw [hr] at h; simp [matesK3] at h
      | some pr => rw [hr, matesK3_some] at h; cases h; exact ih _ _ _ _ _ _ _ _ hr hS
    · cases hs : snocW n m oO oL (rdW (m.arr64 EREC) off) with
      | none => rw [hs] at h; simp [matesK2] at h
      | some pr =>
        obtain ⟨r2, m2⟩ := pr
        simp only [hs, matesK2] at h
        cases hr : matesW n m2 c (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0) with
        | none => rw [hr] at h; simp [matesK3] at h
        | some pr => rw [hr, matesK3_some] at h; cases h; exact ih _ _ _ _ _ _ _ _ hr (snocW_stage hs hS)

/-- **`nest_frame_mates`, under the stage relation**: the mates as a handle slice below the top. -/
theorem nfmW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {c : Word} {r : List Word} (h : nfmW n m vis c = some (r, m')) (hS : StageR dn vis fe m a)
    (hc : H c) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (nestFrameMates fe (decI c)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  cases n with
  | zero => simp [nfmW] at h
  | succ n =>
  simp only [nfmW, nboW] at h
  have hE := hS.1.env
  obtain ⟨hI1, hE1, hsz, hEs, hc200⟩ := hS.2
  rcases hef : envFindW m c vis with _ | ⟨r1, m1⟩; · rw [hef] at h; simp [nboW.k_env_find.none, nfmK] at h
  have hm1 := envFindW_mem hef
  subst m1
  rw [hef] at h
  -- the block slice
  have hblk : ∃ o l : Word, nboW.k_env_find (some (r1, m)) = some ([o, l], m) ∧
      hslice? (erA m) o.toNat l.toNat = some (nestBlockOf fe (decI c)) := by
    rw [nboW.k_env_find.eq_2]
    by_cases h0 : r1.headD 0 = 0
    · rw [ite_eq_left h0]
      obtain ⟨-, hn⟩ := envFindW_miss hef hE hc h0
      exact ⟨0, 0, rfl, by simp [nestBlockOf, hn, hslice?]⟩
    rw [ite_eq_right h0]
    obtain ⟨-, hfind, hex⟩ := envFindW_hit hef hE hc h0
    have hfound : fe.find? (decI c) = decFound dn m (r1.headD 0) (r1.tail.headD 0) := by
      rw [hfind]; simp only [decFound, ite_eq_right h0]
    by_cases h3 : rdW (m.arr64 EREC) (r1.tail.headD 0) ≠ 3
    · rw [ite_eq_left h3]; exact ⟨0, 0, rfl, blk_nok3 _ _ hfound h0 h3⟩
    rw [ite_eq_right h3]
    exact ⟨_, _, rfl, blk_k3 _ _ hfound h0 hex (by simpa using h3)⟩
  obtain ⟨o, l, ho, hsl⟩ := hblk
  simp only [ho, nfmK_some, List.headD_cons, List.tail_cons] at h
  rcases hmt : matesW n m c o l 0 0 with _ | ⟨r2, m2⟩ <;> rw [hmt] at h; · simp [matesK3] at h
  rw [matesK3_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨h1, h2, -, h4⟩ := matesW_ok n _ _ c o l 0 0 _ [] r2 hmt hsz hc200 hEs hc hsl
    (by simp [decHL, hslice?]) (by simp) (by simp)
  exact ⟨matesW_stage n _ _ _ _ _ _ _ _ hmt ⟨hS.1, hI1, hE1, hsz, hEs, hc200⟩, h2, by simpa [nestFrameMates] using h1,
    by simpa using h4⟩

/-! ## `sl_new1` -/

/-- The model of `sl_new1(x)`. -/
def new1W (m : Mem) (x : Word) : Option (List Word × Mem) :=
  match allocW m 1 with
  | none => none
  | some (q, _) => some ([q, 1], (allocMem m 1).set64 IW (rdW (m.arr64 CTL) 200) x)

theorem new1W_rec {m m' : Mem} {x : Word} {r : List Word} (h : new1W m x = some (r, m')) :
    posRecW m [x] = some (r.headD 0, m') ∧ r = [r.headD 0, 1] := by
  rw [posRecW_eq m [x] 1 rfl]
  simp only [new1W] at h
  rcases ha : allocW m 1 with _ | ⟨q, m1⟩ <;> rw [ha] at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  simp [wrIW]

theorem slNew1_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "sl_new1" = some slNew1) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sl_new1" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ new1W s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, slNew1]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, iwAlloc_specW p ha n] <;>
      finish [new1W, allocMem, allocW]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Hole slices grown -/

/-- A hole slice grown by one record (`sl_snoc`). -/
theorem pos2_hsl_snoc {m m' : Mem} {o l q : Nat} {hs : List NestHole} {h : NestHole} {w : Word}
    (hH : HSl m o l hs) (hg : IWGrow m m') (hq : q + l + 1 ≤ iwTop m')
    (hw : ∀ i < l, (m'.arr64 IW)[q + i]? = (m.arr64 IW)[o + i]?) (hx : (m'.arr64 IW)[q + l]? = some w)
    (hd : decNH m' w.toNat = some h) (hin : NHIn m' w.toNat (· < iwTop m')) :
    HSl m' q (l + 1) (hs ++ [h]) := by
  obtain ⟨h1, h2, h3⟩ := hH
  refine ⟨by simp [h1], by omega, fun i hi => ?_⟩
  by_cases hil : i < l
  · obtain ⟨w', hw', hd', hn'⟩ := h3 i hil
    obtain ⟨e, hn''⟩ := hn'.grow hg
    refine ⟨w', by rw [hw i hil]; exact hw', ?_, hn''⟩
    rw [e, hd', List.getElem?_append_left (by omega)]
  · have : i = l := by omega
    subst this
    refine ⟨w, hx, ?_, hin⟩
    rw [hd, List.getElem?_append_right (by omega)]; simp [h1]

/-- A hole record `[key, base]` (`rec2`). -/
theorem pos2_hole_rec {m' : Mem} {p key hi : Word} {K : NestKey}
    (hp : p.toNat + 2 ≤ iwTop m')
    (hget : ∀ j < [key, hi].length, (m'.arr64 IW)[p.toNat + j]? = [key, hi][j]?)
    (hK : decNK m' key.toNat = some K) (hKin : NKIn m' key.toNat (· < iwTop m')) :
    decNH m' p.toNat = some ⟨K, hi.toNat⟩ ∧ NHIn m' p.toNat (· < iwTop m') := by
  have g0 : (m'.arr64 IW)[p.toNat]? = some key := by simpa using hget 0 (by simp)
  have g1 : (m'.arr64 IW)[p.toNat + 1]? = some hi := by simpa using hget 1 (by simp)
  have e0 : iwN m' p.toNat = some key.toNat := by simp [iwN, nat?, iwA, g0]
  have e1 : iwN m' (p.toNat + 1) = some hi.toNat := by simp [iwN, nat?, iwA, g1]
  refine ⟨by simp [decNH, e0, e1, hK], by omega, by omega, fun k hk => ?_⟩
  rw [e0] at hk; cases hk; exact hKin

/-! ## `nest_frame_grp`: the stack grown by the group's holes, and the group's names -/

mutual
def fgW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, hi, us, dO, dL, gO, gL, pO, pL, nO, nL =>
    if gL = 0 then some ([pO, pL, nO, nL], m)
    else fgK1 n hi us dO dL gO gL pO pL nO nL (rdW (m.arr64 IW) (rdW (m.arr64 IW) gO))
      (posRecW m [rdW (m.arr64 IW) (rdW (m.arr64 IW) gO), us, dO, dL])
def fgK1 (n : Nat) (hi us dO dL gO gL pO pL nO nL c : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (key, m1) => fgK2 n hi us dO dL gO gL pO pL nO nL c (posRecW m1 [key, hi])
def fgK2 (n : Nat) (hi us dO dL gO gL pO pL nO nL c : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hole, m2) => fgK3 n hi us dO dL gO gL nO nL c (snocW n m2 pO pL hole)
def fgK3 (n : Nat) (hi us dO dL gO gL nO nL c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => fgK4 n hi us dO dL gO gL (r.headD 0) (r.tail.headD 0) (snocW n m3 nO nL c)
def fgK4 (n : Nat) (hi us dO dL gO gL pO pL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m4) => fgW n m4 hi us dO dL (gO + 1) (gL - 1) pO pL (r.headD 0) (r.tail.headD 0)
end

section arms
variable (n : Nat) (m m1 : Mem) (hi us dO dL gO gL pO pL nO nL c key : Word) (r : List Word)
theorem fgW_nil (h : gL = 0) : fgW (n + 1) m hi us dO dL gO gL pO pL nO nL = some ([pO, pL, nO, nL], m) := by
  simp [fgW, h]
theorem fgW_cons (h : ¬ gL = 0) : fgW (n + 1) m hi us dO dL gO gL pO pL nO nL =
    fgK1 n hi us dO dL gO gL pO pL nO nL (rdW (m.arr64 IW) (rdW (m.arr64 IW) gO))
      (posRecW m [rdW (m.arr64 IW) (rdW (m.arr64 IW) gO), us, dO, dL]) := by simp [fgW, h]
theorem fgK1_some : fgK1 n hi us dO dL gO gL pO pL nO nL c (some (key, m1)) =
    fgK2 n hi us dO dL gO gL pO pL nO nL c (posRecW m1 [key, hi]) := by rw [fgK1]
theorem fgK2_some : fgK2 n hi us dO dL gO gL pO pL nO nL c (some (key, m1)) =
    fgK3 n hi us dO dL gO gL nO nL c (snocW n m1 pO pL key) := by rw [fgK2]
theorem fgK3_some : fgK3 n hi us dO dL gO gL nO nL c (some (r, m1)) =
    fgK4 n hi us dO dL gO gL (r.headD 0) (r.tail.headD 0) (snocW n m1 nO nL c) := by rw [fgK3]
theorem fgK4_some : fgK4 n hi us dO dL gO gL pO pL (some (r, m1)) =
    fgW n m1 hi us dO dL (gO + 1) (gL - 1) pO pL (r.headD 0) (r.tail.headD 0) := by rw [fgK4]
end arms
attribute [ind_grind] fgW_nil fgW_cons fgK1_some fgK2_some fgK3_some fgK4_some

theorem nestFrameGrp_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc2 : p.lookup "iw_copy" = some iwCopy) (h2 : p.lookup "rec2" = some rec2)
    (h4 : p.lookup "rec4" = some rec4) (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hp : p.lookup "nest_frame_grp" = some nestFrameGrpL) (n : Nat) :
    ∀ (s₀ : St) (hi us dO dL gO gL pO pL nO nL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_grp" [hi, us, dO, dL, gO, gL, pO, pL, nO, nL]
    ⦃fun r s' => LocEq s' s₀ ∧ fgW n s₀.mem hi us dO dL gO gL pO pL nO nL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ hi us dO dL gO gL pO pL nO nL
    rw [invoke_eq _ hp]; simp only [callFn, nestFrameGrpL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ hi us dO dL gO gL pO pL nO nL
    simp only [invoke_eq _ hp, callFn, nestFrameGrpL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        posRec4_specW p ha h4 n, posRec2_specW p ha h2 n, slSnoc_specW p ha hc2 hsn n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, Locals.init_cons_zero]

end L.Ind

namespace L.Ind

open L.Arena

/-- A group's tail, from the next pointer on. -/
theorem GrpAt.tail {m : Mem} {o : Nat} {x : NIdx × EIdx} {grp : List (NIdx × EIdx)} (h : GrpAt m o (x :: grp)) :
    GrpAt m (o + 1) grp := fun i hi => by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h (i + 1) (by simp; omega)
  exact ⟨a1, a2, a3, by rw [show o + 1 + i = o + (i + 1) by omega]; exact a4, a5, a6, a7, by simpa using a8, a9,
    a10, by simpa using a11⟩

/-- A group's head pointer and its words. -/
theorem GrpAt.head {m : Mem} {o : Nat} {x : NIdx × EIdx} {grp : List (NIdx × EIdx)} (h : GrpAt m o (x :: grp))
    (ho : o < 2 ^ 64) (htop : iwTop m < 2 ^ 64) :
    ∃ w c t : Word, rdW (m.arr64 IW) (UInt64.ofNat o) = w ∧ w.toNat + 1 < iwTop m ∧ rdW (m.arr64 IW) w = c ∧
      H c ∧ decI c = x.1 ∧ rdW (m.arr64 IW) (w + 1) = t ∧ H t ∧ decI t = x.2 := by
  obtain ⟨w, c, t, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h 0 (by simp)
  have e1 : (w + 1).toNat = w.toNat + 1 := word_add_toNat (by simp; omega)
  refine ⟨w, c, t, ?_, h2, by simp [rdW, h3], h4, by simpa using h5, by simp [rdW, e1, h6], h7, by simpa using h8⟩
  simp only [Nat.add_zero] at h1
  simp [rdW, UInt64.toNat_ofNat_of_lt' ho, h1]

/-- **`nest_frame_grp`**: the stack grown by the group's holes (base `hi`), the group's names. -/
theorem fgW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (hi us dO dL : Word)
    (ds : List EIdx) (hus : H us) : ∀ (n : Nat) (m m' : Mem) (a : AState) (gO gL pO pL nO nL : Word)
    (grp : List (NIdx × EIdx)) (accP : List NestHole) (accN : List NIdx) (r : List Word),
    fgW n m hi us dO dL gO gL pO pL nO nL = some (r, m') → StageR dn vis fe m a →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp →
    HSl m pO.toNat pL.toNat accP → decHL m nO.toNat nL.toNat = some accN → nO.toNat + nL.toNat ≤ iwTop m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      HSl m' (r.headD 0).toNat (r.tail.headD 0).toNat
        (accP ++ grp.map fun x => (⟨⟨x.1, decI us, ds⟩, hi.toNat⟩ : NestHole)) ∧
      decHL m' (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat = some (accN ++ grp.map (·.1)) ∧
      (r.tail.tail.headD 0).toNat + (r.tail.tail.tail.headD 0).toNat ≤ iwTop m' := by
  intro n
  induction n with
  | zero => intro m m' a gO gL pO pL nO nL grp accP accN r h; simp [fgW] at h
  | succ n ih =>
    intro m m' a gO gL pO pL nO nL grp accP accN r h hS hds hgl hgb hgrp hP hN hNb
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    by_cases hg0 : gL = 0
    · rw [fgW_nil (h := hg0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hg0
      have : grp = [] := List.eq_nil_of_length_eq_zero (by simpa using hgl.symm)
      subst this
      exact ⟨hS, IWGrow.refl _, by simpa using hP, by simpa using hN, by simpa using hNb⟩
    rw [fgW_cons (h := hg0)] at h
    obtain ⟨⟨c, t⟩, grp', rfl⟩ : ∃ x grp', grp = x :: grp' := by
      cases grp with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hgl)) hg0
      | cons x grp' => exact ⟨x, grp', rfl⟩
    simp only [List.length_cons] at hgl hgb
    obtain ⟨w, cw, tw, hrw, hw1, hrc, hcH, hcd, -, -, -⟩ := hgrp.head (by omega) htop
    rw [UInt64.ofNat_toNat] at hrw
    rw [hrw, hrc] at h
    -- the key
    rcases hk : posRecW m [cw, us, dO, dL] with _ | ⟨key, m1⟩ <;> rw [hk] at h; · simp [fgK1] at h
    rw [fgK1_some] at h
    obtain ⟨hS1, hg1, hkq, ht1, hget1⟩ := posRecW_stage hk hS (by simp)
    simp only [List.length_cons, List.length_nil] at ht1
    have hds1 := DecB.grow (OMono.decHL _ _) hg1 hds
    have hK : DecB (fun m => decNK m key.toNat) m1 ⟨decI cw, decI us, ds⟩ :=
      pos2_key_rec hcH hus (by omega) hget1 hds1
    -- the hole
    rcases hh : posRecW m1 [key, hi] with _ | ⟨hole, m2⟩ <;> rw [hh] at h; · simp [fgK2] at h
    rw [fgK2_some] at h
    obtain ⟨hS2, hg2, hhq, ht2, hget2⟩ := posRecW_stage hh hS1 (by simp)
    simp only [List.length_cons, List.length_nil] at ht2
    obtain ⟨hKd, hKin⟩ := pos2_nk_in (DecB.grow (decNK_mono _) hg2 hK)
    obtain ⟨hHd, hHin⟩ := pos2_hole_rec (by omega) hget2 hKd hKin
    have hg12 := hg1.trans hg2
    -- the two snocs
    rcases hs1 : snocW n m2 pO pL hole with _ | ⟨r3, m3⟩ <;> rw [hs1] at h; · simp [fgK3] at h
    rw [fgK3_some] at h
    obtain ⟨hS3, hg3, h30, h31, ht3, hw3, hx3⟩ := snocW_words hs1 hS2 (by have := hg12.1; have := hP.2.1; omega)
    have hP3 : HSl m3 (r3.headD 0).toNat (r3.tail.headD 0).toNat (accP ++ [⟨⟨decI cw, decI us, ds⟩, hi.toNat⟩]) := by
      rw [h30, h31]
      exact pos2_hsl_snoc (hP.grow hg12) hg3 (by omega) hw3 hx3
        (by rw [(hHin.grow hg3).1]; exact hHd) (hHin.grow hg3).2
    rcases hs2 : snocW n m3 nO nL cw with _ | ⟨r4, m4⟩ <;> rw [hs2] at h; · simp [fgK4] at h
    rw [fgK4_some] at h
    have hg13 := hg12.trans hg3
    obtain ⟨hr4, hN4, hg4, -, hl4, ht4⟩ := snocW_decK hs2 hS3.2.2.2.1 hS3.2.2.2.2.2 (by have := hg13.1; omega)
      hcH (by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by omega)]; exact hN)
    have hS4 := snocW_stage hs2 hS3
    have hgO1 : (gO + 1).toNat = gO.toNat + 1 := word_add_toNat (by simp; omega)
    have hgL1 : (gL - 1).toNat = grp'.length := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hg14 := hg13.trans hg4
    obtain ⟨hS', hg', hP', hN', hNb'⟩ := ih m4 m' a (gO + 1) (gL - 1) _ _ _ _ grp' _ _ r h hS4
      (DecB.grow (OMono.decHL _ _) (hg2.trans (hg3.trans hg4)) hds1) hgL1
      (by rw [hgO1]; have := hg14.1; omega) (by rw [hgO1]; exact (hgrp.grow (by simpa using hgb) hg14).tail)
      (hP3.grow hg4) (by rw [hr4]; simpa using hN4) (by rw [hr4]; simp; omega)
    refine ⟨hS', hg14.trans hg', ?_, ?_, hNb'⟩
    · simpa [hcd] using hP'
    · simpa [hcd] using hN'

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_frame_holes`: the group's holes, interned in order -/

mutual
def fhW : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, hi, gO, gL, aO, aL =>
    if gL = 0 then some ([aO, aL], m)
    else if hi + 1 = 0 then none
    else fhK1 n hi gO gL aO aL (fvinternW m hi (rdW (m.arr64 IW) (rdW (m.arr64 IW) gO + 1)))
def fhK1 (n : Nat) (hi gO gL aO aL : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (v, m1) => if 4294967296 ≤ v then none else fhK2 n hi gO gL (snocW n m1 aO aL v)
def fhK2 (n : Nat) (hi gO gL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => fhW n m2 (hi + 1) (gO + 1) (gL - 1) (r.headD 0) (r.tail.headD 0)
end

section arms
variable (n : Nat) (m m1 : Mem) (hi gO gL aO aL v : Word) (r : List Word)
theorem fhW_nil (h : gL = 0) : fhW (n + 1) m hi gO gL aO aL = some ([aO, aL], m) := by simp [fhW, h]
theorem fhW_ovf (h : ¬ gL = 0) (h1 : hi + 1 = 0) : fhW (n + 1) m hi gO gL aO aL = none := by simp [fhW, h, h1]
theorem fhW_cons (h : ¬ gL = 0) (h1 : ¬ hi + 1 = 0) : fhW (n + 1) m hi gO gL aO aL =
    fhK1 n hi gO gL aO aL (fvinternW m hi (rdW (m.arr64 IW) (rdW (m.arr64 IW) gO + 1))) := by simp [fhW, h, h1]
theorem fhK1_big (h : 4294967296 ≤ v) : fhK1 n hi gO gL aO aL (some (v, m1)) = none := by simp [fhK1, h]
theorem fhK1_ok (h : ¬ 4294967296 ≤ v) : fhK1 n hi gO gL aO aL (some (v, m1)) =
    fhK2 n hi gO gL (snocW n m1 aO aL v) := by simp [fhK1, h]
theorem fhK2_some : fhK2 n hi gO gL (some (r, m1)) =
    fhW n m1 (hi + 1) (gO + 1) (gL - 1) (r.headD 0) (r.tail.headD 0) := by rw [fhK2]
end arms
attribute [ind_grind] fhW_nil fhW_ovf fhW_cons fhK1_big fhK1_ok fhK2_some

theorem nestFrameHoles_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc2 : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hp : p.lookup "nest_frame_holes" = some nestFrameHolesL) (n : Nat) :
    ∀ (s₀ : St) (hi gO gL aO aL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_holes" [hi, gO, gL, aO, aL]
    ⦃fun r s' => LocEq s' s₀ ∧ fhW n s₀.mem hi gO gL aO aL = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ hi gO gL aO aL
    rw [invoke_eq _ hp]; simp only [callFn, nestFrameHolesL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ hi gO gL aO aL
    simp only [invoke_eq _ hp, callFn, nestFrameHolesL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        internFVar_spec p hff hfp hif n, slSnoc_specW p ha hc2 hsn n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, Locals.init_cons_zero]

end L.Ind

namespace L.Ind

open L.Arena

/-- The twin's holes of a group from `hi` on, one by one. -/
def pos2FhT (hi : Nat) : List (NIdx × EIdx) → AM (List EIdx)
  | [] => pure []
  | x :: g => do
    let v ← internFVarE hi x.2
    let vs ← pos2FhT (hi + 1) g
    pure (v :: vs)

theorem pos2_zipIdx_holes (hi : Nat) : ∀ (grp : List (NIdx × EIdx)) (k : Nat),
    (grp.zipIdx k).mapM (fun (x : (NIdx × EIdx) × Nat) => internFVarE (hi + x.2) x.1.2) =
      pos2FhT (hi + k) grp
  | [], k => rfl
  | x :: g, k => by
    simp only [List.zipIdx_cons, List.mapM_cons, pos2FhT, pos2_zipIdx_holes hi g (k + 1), Nat.add_assoc]

/-- **`nest_frame_holes`**: the group's holes from `hi` on, appended to the accumulator. -/
theorem fhW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) : ∀ (n : Nat) (m m' : Mem)
    (a : AState) (hi gO gL aO aL : Word) (grp : List (NIdx × EIdx)) (acc : List EIdx) (r : List Word),
    fhW n m hi gO gL aO aL = some (r, m') → StageR dn vis fe m a →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp →
    decHL m aO.toNat aL.toNat = some acc → aO.toNat + aL.toNat ≤ iwTop m →
    ∃ vs a', (pos2FhT hi.toNat grp).run a = .ok (vs, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (acc ++ vs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  intro n
  induction n with
  | zero => intro m m' a hi gO gL aO aL grp acc r h; simp [fhW] at h
  | succ n ih =>
    intro m m' a hi gO gL aO aL grp acc r h hS hgl hgb hgrp hA hAb
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    by_cases hg0 : gL = 0
    · rw [fhW_nil (h := hg0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hg0
      have : grp = [] := List.eq_nil_of_length_eq_zero (by simpa using hgl.symm)
      subst this
      exact ⟨[], a, rfl, hS, IWGrow.refl _, by simpa using hA, by simpa using hAb⟩
    by_cases hov : hi + 1 = 0
    · rw [fhW_ovf (h := hg0) (h1 := hov)] at h; cases h
    rw [fhW_cons (h := hg0) (h1 := hov)] at h
    obtain ⟨⟨c, t⟩, grp', rfl⟩ : ∃ x grp', grp = x :: grp' := by
      cases grp with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hgl)) hg0
      | cons x grp' => exact ⟨x, grp', rfl⟩
    simp only [List.length_cons] at hgl hgb
    obtain ⟨w, cw, tw, hrw, hw1, -, -, -, hrt, htH, htd⟩ := hgrp.head (by omega) htop
    rw [UInt64.ofNat_toNat] at hrw
    rw [hrw, hrt] at h
    rcases hf : fvinternW m hi tw with _ | ⟨v, m1⟩ <;> rw [hf] at h; · simp [fhK1] at h
    by_cases hvb : 4294967296 ≤ v
    · rw [fhK1_big (h := hvb)] at h; cases h
    rw [fhK1_ok (h := hvb)] at h
    obtain ⟨a1, hrun1, hS1, hg1⟩ := internFVar_stage hS hi tw htH hf
    rcases hs : snocW n m1 aO aL v with _ | ⟨r2, m2⟩ <;> rw [hs] at h; · simp [fhK2] at h
    rw [fhK2_some] at h
    have hvH : H v := by
      have : ¬ (4294967296 : Word).toNat ≤ v.toNat := fun h' => hvb (UInt64.le_iff_toNat_le.mpr h')
      simp only [H]; simpa using this
    obtain ⟨hr2, hA2, hg2, -, -, ht2⟩ := snocW_decK hs hS1.2.2.2.1 hS1.2.2.2.2.2 (by have := hg1.1; omega)
      hvH (by rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hA)
    have hS2 := snocW_stage hs hS1
    have hgO1 : (gO + 1).toNat = gO.toNat + 1 := word_add_toNat (by simp; omega)
    have hgL1 : (gL - 1).toNat = grp'.length := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hhi1 : (hi + 1).toNat = hi.toNat + 1 := by
      rcases Nat.lt_or_ge (hi.toNat + 1) (2 ^ 64) with hl | hl
      · exact word_add_toNat (by simpa using hl)
      · exfalso; apply hov; apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; have := hi.toNat_lt; simp; omega
    have hg12 := hg1.trans hg2
    have hb2 : (gO + 1).toNat + grp'.length ≤ iwTop m2 := by
      rw [hgO1]; have := hg12.1; omega
    have hgr2 : GrpAt m2 (gO + 1).toNat grp' := by
      rw [hgO1]; exact (hgrp.grow (by simpa using hgb) hg12).tail
    have hA2' : decHL m2 (r2.headD 0).toNat (r2.tail.headD 0).toNat = some (acc ++ [decI v]) := by
      rw [hr2]; simpa using hA2
    have hAb2 : (r2.headD 0).toNat + (r2.tail.headD 0).toNat ≤ iwTop m2 := by
      rw [hr2]; simp only [List.headD_cons, List.tail_cons]; omega
    obtain ⟨vs, a', hrun, hS', hg', hA', hAb'⟩ := ih m2 m' a1 (hi + 1) (gO + 1) (gL - 1) _ _ grp' _ r h hS2
      hgL1 hb2 hgr2 hA2' hAb2
    refine ⟨decI v :: vs, a', ?_, hS', hg12.trans hg', by simpa using hA', hAb'⟩
    rw [hhi1] at hrun
    have htd' : t = decE tw := by simpa [decE_eq] using htd.symm
    subst htd'
    simp only [pos2FhT, internFVarE, StateT.run_bind, hrun1, except_ok_bind, hrun]
    rfl

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_cont_new_active`: the group's keys -/

mutual
def caW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, us, dO, dL, gO, gL, aO, aL =>
    if gL = 0 then some ([aO, aL], m)
    else caK1 n us dO dL gO gL aO aL (posRecW m [rdW (m.arr64 IW) (rdW (m.arr64 IW) gO), us, dO, dL])
def caK1 (n : Nat) (us dO dL gO gL aO aL : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (key, m1) => caK2 n us dO dL gO gL (snocW n m1 aO aL key)
def caK2 (n : Nat) (us dO dL gO gL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => caW n m2 us dO dL (gO + 1) (gL - 1) (r.headD 0) (r.tail.headD 0)
end

section arms
variable (n : Nat) (m m1 : Mem) (us dO dL gO gL aO aL key : Word) (r : List Word)
theorem caW_nil (h : gL = 0) : caW (n + 1) m us dO dL gO gL aO aL = some ([aO, aL], m) := by simp [caW, h]
theorem caW_cons (h : ¬ gL = 0) : caW (n + 1) m us dO dL gO gL aO aL =
    caK1 n us dO dL gO gL aO aL (posRecW m [rdW (m.arr64 IW) (rdW (m.arr64 IW) gO), us, dO, dL]) := by
  simp [caW, h]
theorem caK1_some : caK1 n us dO dL gO gL aO aL (some (key, m1)) = caK2 n us dO dL gO gL (snocW n m1 aO aL key) := by
  rw [caK1]
theorem caK2_some : caK2 n us dO dL gO gL (some (r, m1)) =
    caW n m1 us dO dL (gO + 1) (gL - 1) (r.headD 0) (r.tail.headD 0) := by rw [caK2]
end arms
attribute [ind_grind] caW_nil caW_cons caK1_some caK2_some

theorem nestContNewActive_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc2 : p.lookup "iw_copy" = some iwCopy) (h4 : p.lookup "rec4" = some rec4)
    (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hp : p.lookup "nest_cont_new_active" = some nestContNewActiveL) (n : Nat) :
    ∀ (s₀ : St) (us dO dL gO gL aO aL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_new_active" [us, dO, dL, gO, gL, aO, aL]
    ⦃fun r s' => LocEq s' s₀ ∧ caW n s₀.mem us dO dL gO gL aO aL = some ([r.headD 0, r.tail.headD 0], s'.mem);
      ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ us dO dL gO gL aO aL
    rw [invoke_eq _ hp]; simp only [callFn, nestContNewActiveL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ us dO dL gO gL aO aL
    simp only [invoke_eq _ hp, callFn, nestContNewActiveL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        posRec4_specW p ha h4 n, slSnoc_specW p ha hc2 hsn n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, Locals.init_cons_zero]

/-- **`nest_cont_new_active`**: the group's keys at `(us, ds)`, appended to the accumulator. -/
theorem caW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (us dO dL : Word)
    (ds : List EIdx) (hus : H us) : ∀ (n : Nat) (m m' : Mem) (a : AState) (gO gL aO aL : Word)
    (grp : List (NIdx × EIdx)) (acc : List NestKey) (r : List Word),
    caW n m us dO dL gO gL aO aL = some (r, m') → StageR dn vis fe m a →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp →
    KsB m aO.toNat aL.toNat acc → aO.toNat + aL.toNat ≤ iwTop m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      KsB m' (r.headD 0).toNat (r.tail.headD 0).toNat
        (acc ++ grp.map fun x => (⟨x.1, decI us, ds⟩ : NestKey)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  intro n
  induction n with
  | zero => intro m m' a gO gL aO aL grp acc r h; simp [caW] at h
  | succ n ih =>
    intro m m' a gO gL aO aL grp acc r h hS hds hgl hgb hgrp hA hAb
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    by_cases hg0 : gL = 0
    · rw [caW_nil (h := hg0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hg0
      have : grp = [] := List.eq_nil_of_length_eq_zero (by simpa using hgl.symm)
      subst this
      exact ⟨hS, IWGrow.refl _, by simpa using hA, by simpa using hAb⟩
    rw [caW_cons (h := hg0)] at h
    obtain ⟨⟨c, t⟩, grp', rfl⟩ : ∃ x grp', grp = x :: grp' := by
      cases grp with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hgl)) hg0
      | cons x grp' => exact ⟨x, grp', rfl⟩
    simp only [List.length_cons] at hgl hgb
    obtain ⟨w, cw, tw, hrw, hw1, hrc, hcH, hcd, -, -, -⟩ := hgrp.head (by omega) htop
    rw [UInt64.ofNat_toNat] at hrw
    rw [hrw, hrc] at h
    rcases hk : posRecW m [cw, us, dO, dL] with _ | ⟨key, m1⟩ <;> rw [hk] at h; · simp [caK1] at h
    rw [caK1_some] at h
    obtain ⟨hS1, hg1, hkq, ht1, hget1⟩ := posRecW_stage hk hS (by simp)
    simp only [List.length_cons, List.length_nil] at ht1
    have hds1 := DecB.grow (OMono.decHL _ _) hg1 hds
    have hK : DecB (fun m => decNK m key.toNat) m1 ⟨decI cw, decI us, ds⟩ :=
      pos2_key_rec hcH hus (by omega) hget1 hds1
    rcases hs : snocW n m1 aO aL key with _ | ⟨r2, m2⟩ <;> rw [hs] at h; · simp [caK2] at h
    rw [caK2_some] at h
    obtain ⟨hS2, hg2, h20, h21, ht2, hw2, hx2⟩ := snocW_words hs hS1 (by have := hg1.1; omega)
    have hA2 : KsB m2 (r2.headD 0).toNat (r2.tail.headD 0).toNat (acc ++ [⟨decI cw, decI us, ds⟩]) := by
      rw [h20, h21]
      exact pos2_decB_snoc decNK_mono (hA.grow hg1) hg2 (by omega) hw2 hx2 (DecB.grow (decNK_mono _) hg2 hK)
    have hgO1 : (gO + 1).toNat = gO.toNat + 1 := word_add_toNat (by simp; omega)
    have hgL1 : (gL - 1).toNat = grp'.length := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hg12 := hg1.trans hg2
    have hb2 : (gO + 1).toNat + grp'.length ≤ iwTop m2 := by rw [hgO1]; have := hg12.1; omega
    have hgr2 : GrpAt m2 (gO + 1).toNat grp' := by
      rw [hgO1]; exact (hgrp.grow (by simpa using hgb) hg12).tail
    have hAb2 : (r2.headD 0).toNat + (r2.tail.headD 0).toNat ≤ iwTop m2 := by rw [h20, h21]; omega
    obtain ⟨hS', hg', hA', hAb'⟩ := ih m2 m' a (gO + 1) (gL - 1) _ _ grp' _ r h hS2
      (DecB.grow (OMono.decHL _ _) hg2 hds1) hgL1 hb2 hgr2 hA2 hAb2
    refine ⟨hS', hg12.trans hg', ?_, hAb'⟩
    simpa [hcd] using hA'

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_cont_params_closed`: the parameters have no local variables -/

mutual
def cpW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, hp, dO, dL =>
    if dL = 0 then some ([1], m) else cpK1 n hp dO dL (bvbW n m (rdW (m.arr64 IW) dO) CWF)
def cpK1 (n : Nat) (hp dO dL : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (bb, m1) =>
    if bb ≠ 0 then some ([0], m1) else cpK2 n hp dO dL (fvbF m1 [CWF, rdW (m1.arr64 IW) dO])
def cpK2 (n : Nat) (hp dO dL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => if hp < r.headD 0 then some ([0], m2) else cpW n m2 hp (dO + 1) (dL - 1)
end

section arms
variable (n : Nat) (m m1 : Mem) (hp dO dL bb : Word) (r : List Word)
theorem cpW_nil (h : dL = 0) : cpW (n + 1) m hp dO dL = some ([1], m) := by simp [cpW, h]
theorem cpW_cons (h : ¬ dL = 0) : cpW (n + 1) m hp dO dL = cpK1 n hp dO dL (bvbW n m (rdW (m.arr64 IW) dO) CWF) := by
  simp [cpW, h]
theorem cpK1_b (h : bb ≠ 0) : cpK1 n hp dO dL (some (bb, m1)) = some ([0], m1) := by simp [cpK1, h]
theorem cpK1_ok (h : ¬ bb ≠ 0) : cpK1 n hp dO dL (some (bb, m1)) =
    cpK2 n hp dO dL (fvbF m1 [CWF, rdW (m1.arr64 IW) dO]) := by simp [cpK1, h]
theorem cpK2_out (h : hp < r.headD 0) : cpK2 n hp dO dL (some (r, m1)) = some ([0], m1) := by
  rw [cpK2, ite_eq_left h]
theorem cpK2_in (h : ¬ hp < r.headD 0) : cpK2 n hp dO dL (some (r, m1)) = cpW n m1 hp (dO + 1) (dL - 1) := by
  rw [cpK2, ite_eq_right h]
end arms
attribute [ind_grind] cpW_nil cpW_cons cpK1_b cpK1_ok cpK2_out cpK2_in

theorem nestContParamsClosed_spec (p : Prog) (hb : BvbProg p) (hf : HfF p)
    (hp : p.lookup "nest_cont_params_closed" = some nestContParamsClosedL) (n : Nat) :
    ∀ (s₀ : St) (hpw dO dL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_params_closed" [hpw, dO, dL]
    ⦃fun r s' => LocEq s' s₀ ∧ cpW n s₀.mem hpw dO dL = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ hpw dO dL
    rw [invoke_eq _ hp]; simp only [callFn, nestContParamsClosedL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ hpw dO dL
    simp only [invoke_eq _ hp, callFn, nestContParamsClosedL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        bvarBL_spec p hb n, fvbF_spec p hf n, ih] <;>
      finish (gen := 20) [rdW_eq]

/-- The twin's per-parameter test of `nestCont`. -/
def pcF (hp : Nat) (x : EIdx) : AM Bool := do
  let bb ← bvarB coreWalkFuel x
  if bb != 0 then pure false
  else do
    let fb ← fvarB coreWalkFuel x
    pure (decide (fb ≤ hp))

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `pin_at` (a copy of lane `decls3`'s model, `DeclBasisSpec.lean`, which this chain does not
import) -/

def pos2PinW (m : Mem) (i : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else if 51 ≤ i then none else some ([rdW (m.arr64 PINS) (1 + i)], m)

theorem pos2Pin_spec (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_at" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ pos2PinW s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, pinAtL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [pos2PinW, pinW_eq, rdW_eq]

theorem pos2PinW_ok {m m' : Mem} {a : AState} {i : Word} {r : List Word}
    (h : pos2PinW m i = some (r, m')) (hP : PinsR m a.pins) :
    m' = m ∧ H (r.headD 0) ∧ (pinAt i.toNat).run a = .ok (decI (r.headD 0), a) := by
  unfold pos2PinW at h
  by_cases h0 : pinW m 0 = 0
  · simp [h0] at h
  rw [ite_eq_right h0] at h
  by_cases hi : 51 ≤ i
  · simp [hi] at h
  rw [ite_eq_right hi] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hF := hP.full h0
  have hi' : i.toNat < 51 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hi); simpa using this
  have e : rdW (m.arr64 PINS) (1 + i) = pinW m (1 + i.toNat) := by
    simp only [rdW, pinW]
    congr 2
    rw [UInt64.toNat_add]; simp; omega
  refine ⟨rfl, ?_, ?_⟩ <;> simp only [List.headD_cons] <;> rw [e]
  · exact hF.names_lt i.toNat hi'
  · exact pinAt_run hF i.toNat hi'

/-! ## `nest_cont_checks`: hole-free indices, not `Quot`, parameters without local variables -/

def p2ccK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => if r.headD 0 = 0 then none else some ([0], m2)
def p2ccK1 (k : Nat) (hp nn dO dL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 ≠ 0 then none
    else match pos2PinW m1 47 with
      | none => none
      | some (q, m2) => if nn = q.headD 0 then none else p2ccK2 (cpW k m2 hp dO dL)
/-- The model of `nest_cont_checks(ctx, hp, n, dsOff, dsLen, idxOff, idxLen)`. -/
def p2ccW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | k + 1, m, ctx, hp, nn, dO, dL, iO, iL =>
    p2ccK1 k hp nn dO dL (noaW k m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1))
      (rdW (m.arr64 IW) (ctx + 4)) hp iO iL)

section arms
variable (k : Nat) (m1 m2 : Mem) (hp nn dO dL : Word) (r : List Word)
theorem p2ccK2_z (h : r.headD 0 = 0) : p2ccK2 (some (r, m2)) = none := by rw [p2ccK2, ite_eq_left h]
theorem p2ccK2_nz (h : ¬ r.headD 0 = 0) : p2ccK2 (some (r, m2)) = some ([0], m2) := by rw [p2ccK2, ite_eq_right h]
theorem p2ccK1_eq : p2ccK1 k hp nn dO dL (some (r, m1)) =
    if r.headD 0 ≠ 0 then none
    else match pos2PinW m1 47 with
      | none => none
      | some (q, m2) => if nn = q.headD 0 then none else p2ccK2 (cpW k m2 hp dO dL) := rfl
end arms
attribute [ind_grind] p2ccK2_z p2ccK2_nz

theorem nestContChecks_spec (p : Prog) (hl : NoLook p) (hoa : p.lookup "nest_occ_any" = some nestOccAnyL)
    (hpa : p.lookup "pin_at" = some pinAtL) (hb : BvbProg p) (hf : HfF p)
    (hpc : p.lookup "nest_cont_params_closed" = some nestContParamsClosedL)
    (hp : p.lookup "nest_cont_checks" = some nestContChecksL) (n : Nat) (s₀ : St)
    (ctx hpw nn dO dL iO iL : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_checks" [ctx, hpw, nn, dO, dL, iO, iL]
    ⦃fun r s' => LocEq s' s₀ ∧ p2ccW n s₀.mem ctx hpw nn dO dL iO iL = some ([r.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestContChecksL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestOccAny_spec p hl hoa n, pos2Pin_spec p hpa n, nestContParamsClosed_spec p hb hf hpc n] <;>
      finish (gen := 20) [p2ccW, p2ccK1, rdW_eq]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Memo frames of the `IndPos2` pieces (helper `posmemo`) -/

theorem nagW_mfr : ∀ (n : Nat) (m m' : Mem) (us dO dL gO gL kO kL : Word) (r : List Word),
    nagW n m us dO dL gO gL kO kL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [nagW] at h
  | n + 1, m, m', us, dO, dL, gO, gL, kO, kL, r, h => by
    unfold nagW nagK1 nagK2 nagK3 at h
    mfr_auto h [posRecW_mfr, snocW_mfr, nagW_mfr n _ _ _ _ _ _ _ _ _ _]

theorem matesW_mfr : ∀ (n : Nat) (m m' : Mem) (c off l oO oL : Word) (r : List Word),
    matesW n m c off l oO oL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, h => by simp [matesW] at h
  | n + 1, m, m', c, off, l, oO, oL, r, h => by
    unfold matesW matesK1 matesK2 matesK3 at h
    mfr_auto h [snocW_mfr, matesW_mfr n _ _ _ _ _ _ _ _]

theorem nboW_mfr {m m' : Mem} {vis c : Word} {r : List Word} (h : nboW m vis c = some (r, m')) :
    MFr [] [] m m' := by
  simp only [nboW] at h
  unfold nboW.k_env_find at h
  mfr_auto h [envFindW_mfr]

theorem nfmW_mfr {n : Nat} {m m' : Mem} {vis c : Word} {r : List Word} (h : nfmW n m vis c = some (r, m')) :
    MFr [] [] m m' := by
  cases n with
  | zero => simp [nfmW] at h
  | succ n =>
  simp only [nfmW] at h
  unfold nfmK matesK3 at h
  mfr_auto h [nboW_mfr, matesW_mfr _ _ _ _ _ _ _ _ _]

theorem fgW_mfr : ∀ (n : Nat) (m m' : Mem) (hi us dO dL gO gL pO pL nO nL : Word) (r : List Word),
    fgW n m hi us dO dL gO gL pO pL nO nL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [fgW] at h
  | n + 1, m, m', hi, us, dO, dL, gO, gL, pO, pL, nO, nL, r, h => by
    unfold fgW fgK1 fgK2 fgK3 fgK4 at h
    mfr_auto h [posRecW_mfr, snocW_mfr, fgW_mfr n _ _ _ _ _ _ _ _ _ _ _ _ _]

theorem fhW_mfr : ∀ (n : Nat) (m m' : Mem) (hi gO gL aO aL : Word) (r : List Word),
    fhW n m hi gO gL aO aL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, h => by simp [fhW] at h
  | n + 1, m, m', hi, gO, gL, aO, aL, r, h => by
    unfold fhW fhK1 fhK2 at h
    mfr_auto h [fvinternW_mfr, snocW_mfr, fhW_mfr n _ _ _ _ _ _ _ _]

theorem caW_mfr : ∀ (n : Nat) (m m' : Mem) (us dO dL gO gL aO aL : Word) (r : List Word),
    caW n m us dO dL gO gL aO aL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [caW] at h
  | n + 1, m, m', us, dO, dL, gO, gL, aO, aL, r, h => by
    unfold caW caK1 caK2 at h
    mfr_auto h [posRecW_mfr, snocW_mfr, caW_mfr n _ _ _ _ _ _ _ _ _ _]

theorem new1W_mfr {m m' : Mem} {x : Word} {r : List Word} (h : new1W m x = some (r, m')) : MFr [] [] m m' :=
  posRecW_mfr (new1W_rec h).1

theorem cpW_mfr : ∀ (n : Nat) (m m' : Mem) (hp dO dL : Word) (r : List Word),
    cpW n m hp dO dL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [cpW] at h
  | n + 1, m, m', hp, dO, dL, r, h => by
    unfold cpW cpK1 cpK2 at h
    mfr_auto h [bvbW_mfr, MFr.ofFvbF, cpW_mfr n _ _ _ _ _ _]

theorem ustW_mfr {n : Nat} {m m' : Mem} {cty nP j r : Word} (h : ustW n m cty nP j = some (r, m')) : HbFr m m' := by
  unfold ustW ustK1 at h
  mfr_auto h [MFr.ofStripF, hbFastW_mfr]

end L.Ind
