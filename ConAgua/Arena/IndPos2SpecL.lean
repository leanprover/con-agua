import ConAgua.Arena.IndPos2SpecK

/-! # `IndPos2`, the `nestPos` block's leaves (lane `indproofs2`, helper `pos2`): word models and
specs of the block's non-recursive helpers (`nest_frame_mates` with the stage relation,
`sl_new1`, `nest_frame_grp`, `nest_frame_holes`, `nest_cont_new_active`, `nest_cont_params_closed`,
…). Every model takes the exec fuel first and is `none` at `0`. -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_block_of`, `nest_frame_mates` -/

def nboK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0], m1)
    else if rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3 then some ([0, 0], m1)
    else some ([rdW (m1.arr64 EREC) (r.tail.headD 0 + 15), rdW (m1.arr64 EREC) (r.tail.headD 0 + 16)], m1)

/-- The model of `nest_block_of(vis, c)`. -/
def nboW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | _ + 1, m, vis, c => nboK (envFindW m c vis)

theorem nboK_eq (m1 : Mem) (r : List Word) : nboK (some (r, m1)) =
    if r.headD 0 = 0 then some ([0, 0], m1)
    else if rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3 then some ([0, 0], m1)
    else some ([rdW (m1.arr64 EREC) (r.tail.headD 0 + 15), rdW (m1.arr64 EREC) (r.tail.headD 0 + 16)], m1) := rfl
attribute [ind_grind] nboK_eq

theorem nestBlockOf_specW (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hf : p.lookup "env_find" = some envFindL)
    (hp : p.lookup "nest_block_of" = some nestBlockOfL) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_block_of" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ nboW n s₀.mem vis c = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nestBlockOfL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, envFind_specW p hx hg hf n] <;>
      finish (gen := 20) [nboW, rdW_eq]

def nfmK (n : Nat) (c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => matesK3 (matesW n m1 c (r.headD 0) (r.tail.headD 0) 0 0)

/-- The model of `nest_frame_mates(vis, c)`. -/
def nfmW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, c => nfmK n c (nboW n m vis c)

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
  rw [invoke_eq _ L.hp]
  simp only [callFn, nestFrameMatesL]
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
    cases hb : containsW n m oO oL (rdW (m.arr64 EREC) off) with
    | none => rw [hb] at h; simp [matesK1] at h
    | some b =>
    rw [hb] at h
    simp only [matesK1] at h
    split at h
    · cases hr : matesW n m c (off + 1) (l - 1) oO oL with
      | none => rw [hr] at h; simp [matesK3] at h
      | some pr => rw [hr, matesK3_some] at h; cases h; exact ih _ _ _ _ _ _ _ _ hr hS
    · cases hs : snocW n m oO oL (rdW (m.arr64 EREC) off) with
      | none => rw [hs] at h; simp [matesK2] at h
      | some pr =>
        obtain ⟨r2, m2⟩ := pr
        rw [hs] at h
        simp only [matesK2] at h
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
  cases n with
  | zero => simp [nfmW, nboW, nfmK] at h
  | succ n =>
  simp only [nfmW, nboW] at h
  have hE := hS.1.env
  obtain ⟨hI1, hE1, hsz, hEs, hc200⟩ := hS.2
  cases hef : envFindW m c vis with
  | none => rw [hef] at h; simp [nboK, nfmK] at h
  | some pr =>
  obtain ⟨r1, m1⟩ := pr
  have hm1 := envFindW_mem hef
  subst m1
  rw [hef] at h
  -- the block slice
  have hblk : ∃ o l : Word, nboK (some (r1, m)) = some ([o, l], m) ∧
      hslice? (erA m) o.toNat l.toNat = some (nestBlockOf fe (decI c)) := by
    rw [nboK_eq]
    by_cases h0 : r1.headD 0 = 0
    · rw [if_pos h0]
      obtain ⟨-, hn⟩ := envFindW_miss hef hE hc h0
      exact ⟨0, 0, rfl, by simp [nestBlockOf, hn, hslice?]⟩
    rw [if_neg h0]
    obtain ⟨-, hfind, hex⟩ := envFindW_hit hef hE hc h0
    have hfound : fe.find? (decI c) = decFound dn m (r1.headD 0) (r1.tail.headD 0) := by
      rw [hfind]; simp only [decFound, if_neg h0]
    by_cases h3 : rdW (m.arr64 EREC) (r1.tail.headD 0) ≠ 3
    · rw [if_pos h3]; exact ⟨0, 0, rfl, blk_nok3 _ _ hfound h0 h3⟩
    rw [if_neg h3]
    exact ⟨_, _, rfl, blk_k3 _ _ hfound h0 hex (by simpa using h3)⟩
  obtain ⟨o, l, ho, hsl⟩ := hblk
  rw [ho, nfmK_some] at h
  simp only [List.headD_cons, List.tail_cons] at h
  cases hmt : matesW (n + 1) m c o l 0 0 with
  | none => rw [hmt] at h; simp [matesK3] at h
  | some pr =>
  obtain ⟨r2, m2⟩ := pr
  rw [hmt, matesK3_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨h1, h2, -, h4⟩ := matesW_ok (n + 1) _ _ c o l 0 0 _ [] r2 hmt hsz hc200 hEs hc hsl
    (by simp [decHL, hslice?]) (by simp) (by simp)
  exact ⟨matesW_stage (n + 1) _ _ _ _ _ _ _ _ hmt ⟨hS.1, hI1, hE1, hsz, hEs, hc200⟩, h2, by simpa [nestFrameMates] using h1,
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
  cases ha : allocW m 1 with
  | none => rw [ha] at h; simp at h
  | some pr =>
    obtain ⟨q, m1⟩ := pr
    rw [ha] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [wrIW]

theorem slNew1_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "sl_new1" = some slNew1) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sl_new1" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ new1W s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, slNew1]
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
    rw [invoke_eq _ hp]
    simp only [callFn, nestFrameGrpL]
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
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
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
    cases hk : posRecW m [cw, us, dO, dL] with
    | none => rw [hk] at h; simp [fgK1] at h
    | some pr =>
    obtain ⟨key, m1⟩ := pr
    rw [hk, fgK1_some] at h
    obtain ⟨hS1, hg1, hkq, ht1, hget1⟩ := posRecW_stage hk hS (by simp)
    simp only [List.length_cons, List.length_nil] at ht1
    have hds1 := DecB.grow (OMono.decHL _ _) hg1 hds
    have hK : DecB (fun m => decNK m key.toNat) m1 ⟨decI cw, decI us, ds⟩ :=
      pos2_key_rec hcH hus (by omega) hget1 hds1
    -- the hole
    cases hh : posRecW m1 [key, hi] with
    | none => rw [hh] at h; simp [fgK2] at h
    | some pr2 =>
    obtain ⟨hole, m2⟩ := pr2
    rw [hh, fgK2_some] at h
    obtain ⟨hS2, hg2, hhq, ht2, hget2⟩ := posRecW_stage hh hS1 (by simp)
    simp only [List.length_cons, List.length_nil] at ht2
    obtain ⟨hKd, hKin⟩ := pos2_nk_in (DecB.grow (decNK_mono _) hg2 hK)
    obtain ⟨hHd, hHin⟩ := pos2_hole_rec (by omega) hget2 hKd hKin
    have hg12 := hg1.trans hg2
    -- the two snocs
    cases hs1 : snocW n m2 pO pL hole with
    | none => rw [hs1] at h; simp [fgK3] at h
    | some pr3 =>
    obtain ⟨r3, m3⟩ := pr3
    rw [hs1, fgK3_some] at h
    obtain ⟨hS3, hg3, h30, h31, ht3, hw3, hx3⟩ := snocW_words hs1 hS2 (by have := hg12.1; have := hP.2.1; omega)
    have hP3 : HSl m3 (r3.headD 0).toNat (r3.tail.headD 0).toNat (accP ++ [⟨⟨decI cw, decI us, ds⟩, hi.toNat⟩]) := by
      rw [h30, h31]
      exact pos2_hsl_snoc (hP.grow hg12) hg3 (by omega) hw3 hx3
        (by rw [(hHin.grow hg3).1]; exact hHd) (hHin.grow hg3).2
    cases hs2 : snocW n m3 nO nL cw with
    | none => rw [hs2] at h; simp [fgK4] at h
    | some pr4 =>
    obtain ⟨r4, m4⟩ := pr4
    rw [hs2, fgK4_some] at h
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
