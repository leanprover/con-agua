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
