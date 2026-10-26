import ConAgua.Arena.IndPos2SpecC
import ConAgua.Arena.StageInst1

/-! Continued from `IndPos2SpecC.lean` (split by size; lane `indproofs`). -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `app_hole` -/

/-- **`app_hole` is its model `ahWf`** (generated). -/
l_model appHole_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hph : p.lookup "ph_app" = some phApp)
    (hf : p.lookup "sl_find" = some slFind) (hpw : p.lookup "pin_word" = some pinWordL)
    (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
    (his : p.lookup "intern_sort" = some internSort)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hcs : p.lookup "nest_canon_sub" = some nestCanonSub)
    (hp : p.lookup "app_hole" = some appHole)
  fns [hp ↦ ahWf]
  specs [phApp_spec p hv hph n, nestCanonSub_spec p hf hpw hsf hsp his hff hfp hif hcs n]
  grind [ind_grind] simp [St.setLocs_mem']

theorem ahW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl us b nn e : Word) (N : Nat) (names : List NIdx) (r : List Word)
    (hh : ahWf (n + 1) m no nl us b nn e = some (r, m')) (hS : StageR dn vis fe m a) (hN : nn.toNat = N)
    (he : H e) (hus : H us) (hb : b.toNat + N < 2 ^ 64)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hnn : nn.toNat + names.length < 2 ^ 64) :
    ∃ x a', (ConRon.Arena.appHole? names (decI us) b.toNat N (decI e)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decOE m' r x := by
  rw [ahWf.arm1] at hh
  rcases hph : phW n m b e nn with _ | r0 <;> rw [hph] at hh; · simp [ahWf.k_ph_app.none] at hh
  obtain ⟨o, hrun, hpo⟩ := phW_ok n m a b e nn N r0 hN hph hS.1.arena.1 he hb
  by_cases hz : r0.headD 0 = 0
  · rw [ahWf.k_ph_app.arm1 n no nl us nn m r0 hz] at hh
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
    refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
    cases o with
    | none =>
      simp only [ConRon.Arena.appHole?, StateT.run_bind]
      rw [hrun]; rfl
    | some pr =>
      obtain ⟨c, us0⟩ := pr
      obtain ⟨w1, w2, hr0, -⟩ := hpo
      rw [hr0] at hz; simp at hz
  · rw [ahWf.k_ph_app.arm2 n no nl us nn m r0 hz] at hh
    cases o with
    | none => exact absurd hpo hz
    | some pr =>
      obtain ⟨c, us0⟩ := pr
      obtain ⟨w1, w2, hr0, hw1, hd1, hw2, hd2⟩ := hpo
      subst hr0
      cases hcw : canonW n m no nl us nn w1 w2 with
      | none =>
        simp only [List.tail_cons, List.headD_cons] at hh
        rw [hcw] at hh; simp [ahWf.k_nest_canon_sub.none] at hh
      | some pc =>
        obtain ⟨rc, m1⟩ := pc
        simp only [List.tail_cons, List.headD_cons, hcw, ahWf.k_nest_canon_sub.arm1] at hh
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
        obtain ⟨x, a', hrun', hS', hg, hout⟩ := canonW_ok n dn fe vis m m1 a no nl us nn w1 w2 names rc hcw hS
          hw1 hus hw2 hdec hno hnn
        refine ⟨x, a', ?_, hS', hg, ?_⟩
        · simp only [ConRon.Arena.appHole?, StateT.run_bind]
          simp only [hrun, except_ok_bind]
          rw [hN, hd1, hd2] at hrun'
          exact hrun'
        · cases x with
          | none => simpa [decOE] using hout
          | some e3 =>
            simp only [decOE, decW0E] at hout ⊢
            obtain ⟨h1, h2, h3⟩ := hout
            exact ⟨h1, by simpa using h2, by simpa using h3⟩

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hph : p.lookup "ph_app" = some phApp)
  (hf : p.lookup "sl_find" = some slFind) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hcs : p.lookup "nest_canon_sub" = some nestCanonSub)
  (hp : p.lookup "app_hole" = some appHole)
include hv hph hf hpw hsf hsp his hff hfp hif hcs hp

/-- **`app_hole` refines `appHole?`**. -/
@[refines ConRon.Arena.appHole?]
theorem appHole_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl us b nn e : Word) (N : Nat) (names : List NIdx) (hN : nn.toNat = N)
    (he : H e) (hus : H us) (hb : b.toNat + N < 2 ^ 64) (hS : StageR dn vis fe s₀.mem a₀)
    (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hnn : nn.toNat + names.length < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "app_hole" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.appHole? names (decI us) b.toNat N (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.appHole? names (decI us) b.toNat N (decI e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decOE s'.mem r (AM.res (ConRon.Arena.appHole? names (decI us) b.toNat N (decI e)) a₀); ⊤⦄ := by
  refine triple_post (appHole_spec p hv hph hf hpw hsf hsp his hff hfp hif hcs hp (n + 1) s₀ no nl us b nn e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := ahW_ok n dn fe vis _ _ a₀ no nl us b nn e N names r hm hS hN he hus hb
    hdec hno hnn
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

/-! ## Low frames: writers of the store tiers (arrays and `CTL` words below 64) -/

def LowFr (m m' : Mem) : Prop :=
  ∃ (A : List ArrId) (C : List Word), MemFrame A C m m' ∧ (∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) ∧ (∀ x ∈ C, x.toNat < 64)

theorem LowFr.refl (m : Mem) : LowFr m m := ⟨[], [], MemFrame.refl _ _ _, by simp, by simp⟩

theorem LowFr.trans {m₁ m₂ m₃ : Mem} (h₁ : LowFr m₁ m₂) (h₂ : LowFr m₂ m₃) : LowFr m₁ m₃ := by
  obtain ⟨A₁, C₁, f₁, a₁, c₁⟩ := h₁
  obtain ⟨A₂, C₂, f₂, a₂, c₂⟩ := h₂
  refine ⟨A₁ ++ A₂, C₁ ++ C₂, (f₁.mono (fun b hb => List.mem_append_left _ hb) (fun x hx => List.mem_append_left _ hx)).trans
    (f₂.mono (fun b hb => List.mem_append_right _ hb) (fun x hx => List.mem_append_right _ hx)), ?_, ?_⟩
  · intro b hb; rcases List.mem_append.mp hb with h | h; exact a₁ b h; exact a₂ b h
  · intro x hx; rcases List.mem_append.mp hx with h | h; exact c₁ x h; exact c₂ x h

theorem sointernW_low {m m' : Mem} {u r : Word} (h : sointernW m u = some (r, m')) : LowFr m m' := by
  exact ⟨_, _, (sointernW_frame (hI := h)), by simp [SOREC, SOSLOT, SOLP], by simp⟩

theorem fvinternW_low {m m' : Mem} {u ty r : Word} (h : fvinternW m u ty = some (r, m')) : LowFr m m' := by
  exact ⟨_, _, (fvinternW_frame (hI := h)), by simp [FVREC, FVSLOT, FVLP], by simp⟩

theorem mkAppW_low {m m' : Mem} {f x r : Word} (hI : mkAppW m f x = some (r, m')) : LowFr m m' := by
  have hf : MemFrame (ADER :: (ADER + 256) :: appCS.wset) [appCS.ca, appCS.ca + 1] m m' := by
    unfold mkAppW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame appCS_wf hx) hI
  exact ⟨_, _, hf, by simp [ConsSch.wset, appCS, ADER, AREC, ASLOT], by simp [appCS]⟩

theorem mkLamW_low {m m' : Mem} {t b r : Word} (hI : mkLamW m t b = some (r, m')) : LowFr m m' := by
  have hf : MemFrame (LADER :: (LADER + 256) :: lamCS.wset) [lamCS.ca, lamCS.ca + 1] m m' := by
    unfold mkLamW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame lamCS_wf hx) hI
  exact ⟨_, _, hf, by simp [ConsSch.wset, lamCS, LADER, LAREC, LASLOT], by simp [lamCS]⟩

theorem mkForallW_low {m m' : Mem} {t b r : Word} (hI : mkForallW m t b = some (r, m')) : LowFr m m' := by
  have hf : MemFrame (FADER :: (FADER + 256) :: forallCS.wset) [forallCS.ca, forallCS.ca + 1] m m' := by
    unfold mkForallW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame forallCS_wf hx) hI
  exact ⟨_, _, hf, by simp [ConsSch.wset, forallCS, FADER, FAREC, FASLOT], by simp [forallCS]⟩

theorem mkLetW_low {m m' : Mem} {t v b r : Word} (hI : mkLetW m t v b = some (r, m')) : LowFr m m' := by
  have hf : MemFrame (LEDER :: (LEDER + 256) :: letCS.wset) [letCS.ca, letCS.ca + 1] m m' := by
    unfold mkLetW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame letCS_wf hx) hI
  exact ⟨_, _, hf, by simp [ConsSch.wset, letCS, LEDER, LEREC, LESLOT], by simp [letCS]⟩

theorem mkProjW_low {m m' : Mem} {n i e r : Word} (hI : mkProjW m n i e = some (r, m')) : LowFr m m' := by
  have hf : MemFrame (PJDER :: (PJDER + 256) :: projCS.wset) [projCS.ca, projCS.ca + 1] m m' := by
    unfold mkProjW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame projCS_wf hx) hI
  exact ⟨_, _, hf, by simp [ConsSch.wset, projCS, PJDER, PJREC, PJSLOT], by simp [projCS]⟩

theorem canonW_low (n : Nat) {m m' : Mem} {no nl us nn c v : Word} {r : List Word}
    (h : canonW n m no nl us nn c v = some (r, m')) : LowFr m m' := by
  cases n with
  | zero => simp [canonW] at h
  | succ n =>
  simp only [canonW, canonK0.eq_def, canonK1.eq_def, canonK2.eq_def, canonK3.eq_def] at h
  repeat' (first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact LowFr.refl _)
    | (simp only [reduceCtorEq] at h; done)
    | refine LowFr.trans (sointernW_low (by assumption)) ?_
    | refine LowFr.trans (fvinternW_low (by assumption)) ?_
    | split at h)

/-! ## `replace_apps_go` / `replace_apps_node` -/

structure MkLook (p : Prog) : Prop where
  hd : p.lookup "der_b" = some derB
  appF : p.lookup "app_find" = some appFind
  appP : p.lookup "app_push" = some appPush
  appI : p.lookup "intern_app" = some internApp
  appM : p.lookup "mk_app" = some mkApp
  lamF : p.lookup "lam_find" = some lamFind
  lamP : p.lookup "lam_push" = some lamPush
  lamI : p.lookup "intern_lam" = some internLamL
  lamM : p.lookup "mk_lam" = some mkLam
  forF : p.lookup "forall_find" = some forallFind
  forP : p.lookup "forall_push" = some forallPush
  forI : p.lookup "intern_forall" = some internForallL
  forM : p.lookup "mk_forall" = some mkForall
  ltF : p.lookup "letE_find" = some letFind
  ltP : p.lookup "letE_push" = some letPush
  ltI : p.lookup "intern_letE" = some internLet
  ltM : p.lookup "mk_let" = some mkLet
  prjF : p.lookup "proj_find" = some projFind
  prjP : p.lookup "proj_push" = some projPush
  prjI : p.lookup "intern_proj" = some internProj
  prjM : p.lookup "mk_proj" = some mkProj

structure AhLook (p : Prog) : Prop where
  hi1 : I1Prog p
  hv : p.lookup "e_view" = some eView
  hph : p.lookup "ph_app" = some phApp
  hf : p.lookup "sl_find" = some slFind
  hpw : p.lookup "pin_word" = some pinWordL
  hsf : p.lookup "sort_find" = some sortFind
  hsp : p.lookup "sort_push" = some sortPush
  his : p.lookup "intern_sort" = some internSort
  hff : p.lookup "fvar_find" = some fvarFind
  hfp : p.lookup "fvar_push" = some fvarPush
  hif : p.lookup "intern_fvar" = some internFVar
  hcs : p.lookup "nest_canon_sub" = some nestCanonSub
  hp : p.lookup "app_hole" = some appHole

theorem appHole_spec' (p : Prog) (hl : AhLook p) (k : Nat) (s₀ : St) (no nl us b nn e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "app_hole" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧ ahWf k s₀.mem no nl us b nn e = some (r, s'.mem); ⊤⦄ :=
  appHole_spec p hl.hv hl.hph hl.hf hl.hpw hl.hsf hl.hsp hl.his hl.hff hl.hfp hl.hif hl.hcs hl.hp k s₀ no nl us b nn e

def rpMkW (m : Mem) (g a2 x2 c2 y : Word) (x : Word) : Option (Word × Mem) :=
  if g = 4 then mkAppW m a2 x2
  else if g = 5 then mkLamW m a2 x2
  else if g = 6 then mkForallW m a2 x2
  else if g = 7 then mkLetW m a2 x2 c2
  else mkProjW m x y a2

mutual
def rpGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, us, b, nn, f, h =>
    if f = 0 then none else rpG1 n m no nl us b nn f h (eViewW m h)
def rpG1 (n : Nat) (m : Mem) (no nl us b nn f h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 then some (h, m)
  else if v.headD 0 = 3 then rpH h (ahWf n m no nl us b nn h)
  else rpG3 n m no nl us b nn f h v (mfindG raSch m h 0)
def rpH (h : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (rr, m1) => some ((if rr.headD 0 ≠ 0 then rr.tail.headD 0 else h), m1)
def rpG3 (n : Nat) (m : Mem) (no nl us b nn f h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 RAM) (fr.tail.headD 0 * 4 + 3), m)
  else rpG4 h (rpNodeW n m no nl us b nn (f - 1) h (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def rpG4 (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => rpG5 r (msetG raSch m1 h 0 r)
def rpG5 (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 => some (r, m2)
def rpNodeW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, us, b, nn, f1, h, g, x, y, z =>
    if g = 4 then rpA1 n m no nl us b nn f1 h x y (ahWf n m no nl us b nn h)
    else if g = 5 ∨ g = 6 then rpB1 n no nl us b nn f1 g x y (rpGoW n m no nl us b nn f1 x)
    else if g = 7 then rpL1 n no nl us b nn f1 x y z (rpGoW n m no nl us b nn f1 x)
    else rpP1 n m no nl us b nn f1 x y z (rpGoW n m no nl us b nn f1 z)
def rpA1 (n : Nat) (_m : Mem) (no nl us b nn f1 _h x y : Word) :
    Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (rr, m1) =>
    if rr.headD 0 ≠ 0 then some (rr.tail.headD 0, m1)
    else rpB1 n no nl us b nn f1 4 x y (rpGoW n m1 no nl us b nn f1 x)
def rpB1 (n : Nat) (no nl us b nn f1 g x y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (a2, m1) => rpB2 g a2 x (rpGoW n m1 no nl us b nn f1 y)
def rpB2 (g a2 _x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x2, m2) => rpMkW m2 g a2 x2 0 0 0
def rpL1 (n : Nat) (no nl us b nn f1 _x y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (a2, m1) => rpL2 n no nl us b nn f1 z a2 (rpGoW n m1 no nl us b nn f1 y)
def rpL2 (n : Nat) (no nl us b nn f1 z a2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x2, m2) => rpL3 a2 x2 (rpGoW n m2 no nl us b nn f1 z)
def rpL3 (a2 x2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (c2, m3) => rpMkW m3 7 a2 x2 c2 0 0
def rpP1 (_n : Nat) (_m : Mem) (_no _nl _us _b _nn _f1 x y _z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (a2, m1) => rpMkW m1 9 a2 0 0 y x
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (no nl us b nn f f1 h g x y z a2 x2 c2 r : Word) (v fr rr : List Word)
theorem rpGoW_abort (hf : f = 0) : rpGoW (n + 1) m no nl us b nn f h = none := by simp [rpGoW, hf]
theorem rpGoW_view (hf : f ≠ 0) :
    rpGoW (n + 1) m no nl us b nn f h = rpG1 n m no nl us b nn f h (eViewW m h) := by simp [rpGoW, hf]
theorem rpG1_leaf (hv : v ≠ []) (hg : v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8) :
    rpG1 n m no nl us b nn f h v = some (h, m) := by simp only [rpG1]; rw [ite_eq_right hv, ite_eq_left hg]
theorem rpG1_const (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : v.headD 0 = 3) : rpG1 n m no nl us b nn f h v = rpH h (ahWf n m no nl us b nn h) := by
  simp only [rpG1]; rw [ite_eq_right hv, ite_eq_right hg, ite_eq_left h3]
theorem rpG1_node (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : ¬ v.headD 0 = 3) :
    rpG1 n m no nl us b nn f h v = rpG3 n m no nl us b nn f h v (mfindG raSch m h 0) := by
  simp only [rpG1]; rw [ite_eq_right hv, ite_eq_right hg, ite_eq_right h3]
theorem rpH_some : rpH h (some (rr, m1)) = some ((if rr.headD 0 ≠ 0 then rr.tail.headD 0 else h), m1) := by rw [rpH]
theorem rpG3_abort (hr : fr = []) : rpG3 n m no nl us b nn f h v fr = none := by simp [rpG3, hr]
theorem rpG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    rpG3 n m no nl us b nn f h v fr = some (rdW (m.arr64 RAM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [rpG3]; rw [ite_eq_right hr, ite_eq_left hh]
theorem rpG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    rpG3 n m no nl us b nn f h v fr = rpG4 h (rpNodeW n m no nl us b nn (f - 1) h (v.headD 0)
      (v.tail.headD 0) (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [rpG3]; rw [ite_eq_right hr, ite_eq_right hh]
theorem rpG4_some : rpG4 h (some (r, m1)) = rpG5 r (msetG raSch m1 h 0 r) := by rw [rpG4]
theorem rpG5_some : rpG5 r (some m2) = some (r, m2) := by rw [rpG5]
theorem rpNodeW_app : rpNodeW (n + 1) m no nl us b nn f1 h 4 x y z =
    rpA1 n m no nl us b nn f1 h x y (ahWf n m no nl us b nn h) := by simp [rpNodeW]
theorem rpNodeW_bin (hg : g = 5 ∨ g = 6) : rpNodeW (n + 1) m no nl us b nn f1 h g x y z =
    rpB1 n no nl us b nn f1 g x y (rpGoW n m no nl us b nn f1 x) := by
  have : ¬ g = 4 := by intro e; rcases hg with e' | e' <;> (rw [e] at e'; exact absurd e' (by decide))
  simp only [rpNodeW]; rw [ite_eq_right this, ite_eq_left hg]
theorem rpNodeW_let : rpNodeW (n + 1) m no nl us b nn f1 h 7 x y z =
    rpL1 n no nl us b nn f1 x y z (rpGoW n m no nl us b nn f1 x) := by simp [rpNodeW]
theorem rpNodeW_proj (hg4 : ¬ g = 4) (hg5 : ¬ (g = 5 ∨ g = 6)) (hg7 : ¬ g = 7) :
    rpNodeW (n + 1) m no nl us b nn f1 h g x y z =
    rpP1 n m no nl us b nn f1 x y z (rpGoW n m no nl us b nn f1 z) := by
  simp only [rpNodeW]; rw [ite_eq_right hg4, ite_eq_right hg5, ite_eq_right hg7]
theorem rpA1_hit (hh : rr.headD 0 ≠ 0) : rpA1 n m no nl us b nn f1 h x y (some (rr, m1)) =
    some (rr.tail.headD 0, m1) := by simp only [rpA1]; rw [ite_eq_left hh]
theorem rpA1_miss (hh : ¬ rr.headD 0 ≠ 0) : rpA1 n m no nl us b nn f1 h x y (some (rr, m1)) =
    rpB1 n no nl us b nn f1 4 x y (rpGoW n m1 no nl us b nn f1 x) := by simp only [rpA1]; rw [ite_eq_right hh]
theorem rpB1_some : rpB1 n no nl us b nn f1 g x y (some (a2, m1)) =
    rpB2 g a2 x (rpGoW n m1 no nl us b nn f1 y) := by rw [rpB1]
theorem rpB2_some : rpB2 g a2 x (some (x2, m2)) = rpMkW m2 g a2 x2 0 0 0 := by rw [rpB2]
theorem rpL1_some : rpL1 n no nl us b nn f1 x y z (some (a2, m1)) =
    rpL2 n no nl us b nn f1 z a2 (rpGoW n m1 no nl us b nn f1 y) := by rw [rpL1]
theorem rpL2_some : rpL2 n no nl us b nn f1 z a2 (some (x2, m2)) =
    rpL3 a2 x2 (rpGoW n m2 no nl us b nn f1 z) := by rw [rpL2]
theorem rpL3_some : rpL3 a2 x2 (some (c2, m3)) = rpMkW m3 7 a2 x2 c2 0 0 := by rw [rpL3]
theorem rpP1_some : rpP1 n m no nl us b nn f1 x y z (some (a2, m1)) = rpMkW m1 9 a2 0 0 y x := by rw [rpP1]
theorem rpMkW_app : rpMkW m 4 a2 x2 c2 y x = mkAppW m a2 x2 := by simp [rpMkW]
theorem rpMkW_lam : rpMkW m 5 a2 x2 c2 y x = mkLamW m a2 x2 := by simp [rpMkW]
theorem rpMkW_forall : rpMkW m 6 a2 x2 c2 y x = mkForallW m a2 x2 := by simp [rpMkW]
theorem rpMkW_let : rpMkW m 7 a2 x2 c2 y x = mkLetW m a2 x2 c2 := by simp [rpMkW]
theorem rpMkW_proj : rpMkW m 9 a2 x2 c2 y x = mkProjW m x y a2 := by simp [rpMkW]
end arms
attribute [ind_grind] rpGoW_abort rpGoW_view rpG1_leaf rpG1_const rpG1_node rpH_some rpG3_abort
  rpG3_hit rpG3_miss rpG4_some rpG5_some rpNodeW_app rpNodeW_bin rpNodeW_let rpNodeW_proj rpA1_hit
  rpA1_miss rpB1_some rpB2_some rpL1_some rpL2_some rpL3_some rpP1_some rpMkW_app rpMkW_lam rpMkW_forall
  rpMkW_let rpMkW_proj

section spec
variable (p : Prog) (hl : AhLook p) (hk : MkLook p)
  (hf : p.lookup "ra_find" = some (memoFindG raSch)) (hput : p.lookup "ra_put" = some (memoPutG raSch))
  (hgo : p.lookup "replace_apps_go" = some replaceAppsGo)
  (hnode : p.lookup "replace_apps_node" = some replaceAppsNode)

def RpGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl us b nn f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "replace_apps_go" [no, nl, us, b, nn, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ rpGoW n s₀.mem no nl us b nn f h = some (r.headD 0, s'.mem); ⊤⦄

def RpNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl us b nn f1 h g x y z : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "replace_apps_node" [no, nl, us, b, nn, f1, h, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ rpNodeW n s₀.mem no nl us b nn f1 h g x y z = some (r.headD 0, s'.mem); ⊤⦄

include hl hf hput hgo in
theorem rpGo_step (n : Nat) (ih : RpNodeSpec p n) : RpGoSpec p (n + 1) := by
  unfold RpNodeSpec at ih
  intro s₀ no nl us b nn f h
  simp only [invoke_eq _ hgo, callFn, replaceAppsGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p hl.hv n, appHole_spec' p hl n, memoFindG_spec raSch p _ hf n,
      memoPutG_spec raSch p _ hput n, ih] <;> finish (gen := 20) [St.setLocs_mem']

include hl hk hgo hnode in
theorem rpNode_step (n : Nat) (ih : RpGoSpec p n) : RpNodeSpec p (n + 1) := by
  unfold RpGoSpec at ih
  intro s₀ no nl us b nn f1 h g x y z
  simp only [invoke_eq _ hnode, callFn, replaceAppsNode]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      appHole_spec' p hl n, ih,
      mkApp_spec p hk.hd hk.appF hk.appP hk.appI hk.appM n,
      mkLam_spec p hk.hd hk.lamF hk.lamP hk.lamI hk.lamM n,
      mkForall_spec p hk.hd hk.forF hk.forP hk.forI hk.forM n,
      mkLet_spec p hk.hd hk.ltF hk.ltP hk.ltI hk.ltM n,
      mkProj_spec p hk.hd hk.prjF hk.prjP hk.prjI hk.prjM n] <;> finish (gen := 20) [St.setLocs_mem']

include hl hk hf hput hgo hnode in
theorem rpGo_spec (n : Nat) : RpGoSpec p n ∧ RpNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ no nl us b nn f h; rw [invoke_eq _ hgo]; simp only [callFn, replaceAppsGo]; vcgen [exec] <;> grind
    · intro s₀ no nl us b nn f1 h g x y z; rw [invoke_eq _ hnode]; simp only [callFn, replaceAppsNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨rpGo_step p hl hf hput hgo n ih.2, rpNode_step p hl hk hgo hnode n ih.1⟩

end spec

def rpClrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => if rdW (m1.arr64 CTL) raSch.cs + 2 = 0 then none else some (r, mclearG raSch m1)

def rpConstW (n : Nat) (m : Mem) (no nl us b nn e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) raSch.cs + 2 = 0 then none
  else rpClrK (rpGoW n (mclearG raSch m) no nl us b nn CWF e)

theorem rpConstW_eq (n : Nat) (m : Mem) (no nl us b nn e : Word) (h0 : rdW (m.arr64 CTL) raSch.cs + 2 ≠ 0) :
    rpConstW n m no nl us b nn e = rpClrK (rpGoW n (mclearG raSch m) no nl us b nn CWF e) := by
  simp [rpConstW, h0]
theorem rpClrK_some (r : Word) (m1 : Mem) (h0 : rdW (m1.arr64 CTL) raSch.cs + 2 ≠ 0) :
    rpClrK (some (r, m1)) = some (r, mclearG raSch m1) := by simp [rpClrK, h0]
attribute [ind_grind] rpConstW_eq rpClrK_some

theorem replaceApps_spec (p : Prog) (hl : AhLook p) (hk : MkLook p)
    (hf : p.lookup "ra_find" = some (memoFindG raSch)) (hput : p.lookup "ra_put" = some (memoPutG raSch))
    (hgo : p.lookup "replace_apps_go" = some replaceAppsGo)
    (hnode : p.lookup "replace_apps_node" = some replaceAppsNode)
    (hcl : p.lookup "ra_clear" = some (memoClearG raSch))
    (hp : p.lookup "replace_apps" = some replaceApps) (n : Nat) (s₀ : St) (no nl us b nn e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "replace_apps" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧ rpConstW n s₀.mem no nl us b nn e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (rpGo_spec p hl hk hf hput hgo hnode n).1
  unfold RpGoSpec at ih
  simp only [invoke_eq _ hp, callFn, replaceApps]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec raSch p _ hcl n, ih] <;>
    finish

/-! ### The relational side -/

def rpArm (names : List NIdx) (us : LsIdx) (b n : Nat) (memo : Std.HashMap EIdx EIdx) (fuel : Nat)
    (h : EIdx) : ENodeView → AM (EIdx × Std.HashMap EIdx EIdx)
  | .app a x => do
    match ← ConRon.Arena.appHole? names us b n h with
    | some r => pure (r, memo)
    | none => do
      let (a2, m) ← ConRon.Arena.replaceAppsGo names us b n memo fuel a
      let (x2, m2) ← ConRon.Arena.replaceAppsGo names us b n m fuel x
      let r ← internAppE a2 x2
      pure (r, m2)
  | .lam t body => do
    let (t2, m) ← ConRon.Arena.replaceAppsGo names us b n memo fuel t
    let (b2, m2) ← ConRon.Arena.replaceAppsGo names us b n m fuel body
    let r ← internLamE t2 b2
    pure (r, m2)
  | .forallE t body => do
    let (t2, m) ← ConRon.Arena.replaceAppsGo names us b n memo fuel t
    let (b2, m2) ← ConRon.Arena.replaceAppsGo names us b n m fuel body
    let r ← internForallEE t2 b2
    pure (r, m2)
  | .letE t val body => do
    let (t2, m) ← ConRon.Arena.replaceAppsGo names us b n memo fuel t
    let (v2, m2) ← ConRon.Arena.replaceAppsGo names us b n m fuel val
    let (b2, m3) ← ConRon.Arena.replaceAppsGo names us b n m2 fuel body
    let r ← internLetEE t2 v2 b2
    pure (r, m3)
  | .proj s i x => do
    let (x2, m) ← ConRon.Arena.replaceAppsGo names us b n memo fuel x
    let r ← internProjE s i x2
    pure (r, m)
  | _ => pure (h, memo)

def NodeVr : ENodeView → Prop
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => True
  | _ => False

theorem replaceAppsGo_succ' (names : List NIdx) (us : LsIdx) (b n : Nat) (memo : Std.HashMap EIdx EIdx)
    (fuel : Nat) (h : EIdx) :
    ConRon.Arena.replaceAppsGo names us b n memo (fuel + 1) h = (do
      let v ← view h
      match v with
      | .bvar _ => pure (h, memo)
      | .sort _ => pure (h, memo)
      | .lit _ => pure (h, memo)
      | .fvar _ _ => pure (h, memo)
      | .const _ _ =>
        match ← ConRon.Arena.appHole? names us b n h with
        | some r => pure (r, memo)
        | none => pure (h, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← rpArm names us b n memo fuel h v
          pure (r, m.insert h r)) := by
  rw [ConRon.Arena.replaceAppsGo.eq_2]
  congr 1
  funext v
  cases v with
  | app a' x' =>
    simp only [rpArm, bind_assoc, pure_bind]
    cases hm : memo[h]? with
    | some r => rfl
    | none =>
      refine congrArg (ConRon.Arena.appHole? names us b n h >>= ·) (funext fun x => ?_)
      cases x <;> simp
  | lam t body => simp only [rpArm, bind_assoc, pure_bind]; rfl
  | forallE t body => simp only [rpArm, bind_assoc, pure_bind]; rfl
  | letE t v' body => simp only [rpArm, bind_assoc, pure_bind]; rfl
  | proj s i x => simp only [rpArm, bind_assoc, pure_bind]; rfl
  | bvar _ => rfl
  | sort _ => rfl
  | lit _ => rfl
  | fvar _ _ => rfl
  | const _ _ => rfl

theorem raSch_wf : raSch.WF := ⟨by decide, by decide⟩

abbrev rpMR (m : Mem) (mp : Std.HashMap EIdx EIdx) : Prop :=
  MemoRG raSch bmKey (fun w : Word => decE w) m mp

theorem rpMR_low {m m' : Mem} (hf : LowFr m m') {mp : Std.HashMap EIdx EIdx} (h : rpMR m mp) :
    rpMR m' mp := by
  obtain ⟨A, C, hf, hA, hC⟩ := hf
  exact memoRG_frame raSch raSch_wf bmKey (fun w : Word => decE w) A C
    (fun hmem => by have := hA _ hmem; simp [raSch, RAM] at this)
    (fun hmem => by have := hC _ hmem; simp [raSch] at this) m m' hf mp h

theorem MFr.of_low {m m' : Mem} (h : LowFr m m') : MFr [] [] m m' := by
  obtain ⟨A, C, hf, hA, hC⟩ := h
  refine MFr.of_frame hf (fun b hb => ?_) (fun x hx => ?_)
  · have := hA b hb; simp only [ArrId] at this ⊢; omega
  · have := hC x hx; left; omega

theorem rpMR_mfr {S0 : List ArrId} {T0 : List Word} {m m' : Mem} (hf : MFr S0 T0 m m') (hS : RAM ∉ S0)
    (hT : (210 : Word) ∉ T0) {mp : Std.HashMap EIdx EIdx} (h : rpMR m mp) : rpMR m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := hf.memo RAM 210 (by decide) (by decide) hS hT
  exact memoRG_frame raSch raSch_wf bmKey (fun w : Word => decE w) A C hA hC m m' f mp h

theorem noMR_mfr {S0 : List ArrId} {T0 : List Word} {m m' : Mem} (hf : MFr S0 T0 m m') (hS : NOM ∉ S0)
    (hT : (204 : Word) ∉ T0) {mp : Std.HashMap EIdx Bool} (h : noMR m mp) : noMR m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := hf.memo NOM 204 (by decide) (by decide) hS hT
  exact memoRG_frame noSch noSch_wf bmKey (fun w : Word => w != 0) A C hA hC m m' f mp h

theorem ahW_low {n : Nat} {m m' : Mem} {no nl us b nn e : Word} {r : List Word}
    (h : ahWf (n + 1) m no nl us b nn e = some (r, m')) : LowFr m m' := by
  simp only [ahWf, ahWf.k_ph_app.eq_def, ahWf.k_nest_canon_sub.eq_def] at h
  repeat' (first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact LowFr.refl _)
    | (simp only [reduceCtorEq] at h; done)
    | refine LowFr.trans (canonW_low n (by assumption)) ?_
    | split at h)

def RpGoOK (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (no nl us b nn f h r : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx),
    rpGoW n m no nl us b nn f h = some (r, m') → StageR dn vis fe m a → H h → H us →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat < 2 ^ 64 →
    no.toNat + nl.toNat ≤ iwTop m → nn.toNat = N → nn.toNat + names.length < 2 ^ 64 →
    b.toNat + N < 2 ^ 64 → rpMR m mp →
    ∃ a' mp', (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)).run a =
        .ok ((decE r, mp'), a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp'

/-- Two children and an interning: the shared shape of `lam` and `forallE`. -/
theorem rpBin_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : RpGoOK dn fe vis k) (g : Word)
    (mkW : Mem → Word → Word → Option (Word × Mem)) (iop : EIdx → EIdx → AM EIdx)
    (hmk : ∀ m a2 x2, rpMkW m g a2 x2 0 0 0 = mkW m a2 x2)
    (hst : ∀ (m m' : Mem) (a : AState) (u v r : Word), StageR dn vis fe m a → mkW m u v = some (r, m') →
      ∃ a', (iop (decE u) (decE v)).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m')
    (hlow : ∀ (m m' : Mem) (u v r : Word), mkW m u v = some (r, m') → LowFr m m')
    (m m' : Mem) (a : AState) (no nl us b nn f1 x y r : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx)
    (hn : rpB1 k no nl us b nn f1 g x y (rpGoW k m no nl us b nn f1 x) = some (r, m'))
    (hS : StageR dn vis fe m a) (hx : H x) (hy : H y) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hb : b.toNat + N < 2 ^ 64) (hM : rpMR m mp) :
    ∃ a' mp', (do
        let (t2, mm) ← ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f1.toNat (decE x)
        let (b2, m2) ← ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mm f1.toNat (decE y)
        let r ← iop t2 b2
        pure (r, m2) : AM (EIdx × Std.HashMap EIdx EIdx)).run a = .ok ((decE r, mp'), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
  rcases h1 : rpGoW k m no nl us b nn f1 x with _ | ⟨a2, m1⟩ <;> rw [h1] at hn; · simp [rpB1] at hn
  rw [rpB1_some] at hn
  rcases h2 : rpGoW k m1 no nl us b nn f1 y with _ | ⟨x2, m2⟩ <;> rw [h2] at hn; · simp [rpB2] at hn
  rw [rpB2_some, hmk] at hn
  obtain ⟨a1, mp1, hr1, hS1, hg1, hM1⟩ := ih m m1 a no nl us b nn f1 x a2 N names mp h1 hS hx hus hdec hno hit hN hnn hb hM
  have hdec1 : decHL m1 no.toNat nl.toNat = some names := by rw [decHL_grow hg1 hit]; exact hdec
  obtain ⟨a2', mp2, hr2, hS2, hg2, hM2⟩ := ih m1 m2 a1 no nl us b nn f1 y x2 N names mp1 h2 hS1 hy hus hdec1 hno
    (by have := hg1.1; omega) hN hnn hb hM1
  obtain ⟨a3, hr3, hS3, hg3⟩ := hst m2 m' a2' a2 x2 r hS2 hn
  refine ⟨a3, mp2, ?_, hS3, (hg1.trans hg2).trans hg3, rpMR_low (hlow m2 m' a2 x2 r hn) hM2⟩
  simp only [StateT.run_bind, hr1, except_ok_bind, hr2, hr3]
  rfl

theorem rpLet_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : RpGoOK dn fe vis k)
    (m m' : Mem) (a : AState) (no nl us b nn f1 x y z r : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx)
    (hn : rpL1 k no nl us b nn f1 x y z (rpGoW k m no nl us b nn f1 x) = some (r, m'))
    (hS : StageR dn vis fe m a) (hx : H x) (hy : H y) (hz : H z) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hb : b.toNat + N < 2 ^ 64) (hM : rpMR m mp) :
    ∃ a' mp', (do
        let (t2, mm) ← ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f1.toNat (decE x)
        let (v2, m2) ← ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mm f1.toNat (decE y)
        let (b2, m3) ← ConRon.Arena.replaceAppsGo names (decI us) b.toNat N m2 f1.toNat (decE z)
        let r ← internLetEE t2 v2 b2
        pure (r, m3) : AM (EIdx × Std.HashMap EIdx EIdx)).run a = .ok ((decE r, mp'), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
  rcases h1 : rpGoW k m no nl us b nn f1 x with _ | ⟨a2, m1⟩ <;> rw [h1] at hn; · simp [rpL1] at hn
  rw [rpL1_some] at hn
  rcases h2 : rpGoW k m1 no nl us b nn f1 y with _ | ⟨x2, m2⟩ <;> rw [h2] at hn; · simp [rpL2] at hn
  rw [rpL2_some] at hn
  rcases h3 : rpGoW k m2 no nl us b nn f1 z with _ | ⟨c2, m3⟩ <;> rw [h3] at hn; · simp [rpL3] at hn
  rw [rpL3_some, rpMkW_let] at hn
  obtain ⟨a1, mp1, hr1, hS1, hg1, hM1⟩ := ih m m1 a no nl us b nn f1 x a2 N names mp h1 hS hx hus hdec hno hit hN hnn hb hM
  have hdec1 : decHL m1 no.toNat nl.toNat = some names := by rw [decHL_grow hg1 hit]; exact hdec
  obtain ⟨a2', mp2, hr2, hS2, hg2, hM2⟩ := ih m1 m2 a1 no nl us b nn f1 y x2 N names mp1 h2 hS1 hy hus hdec1 hno
    (by have := hg1.1; omega) hN hnn hb hM1
  have hg12 := hg1.trans hg2
  have hdec2 : decHL m2 no.toNat nl.toNat = some names := by rw [decHL_grow hg12 hit]; exact hdec
  obtain ⟨a3', mp3, hr3, hS3, hg3, hM3⟩ := ih m2 m3 a2' no nl us b nn f1 z c2 N names mp2 h3 hS2 hz hus hdec2 hno
    (by have := hg12.1; omega) hN hnn hb hM2
  obtain ⟨a4, hr4, hS4, hg4⟩ := mkLet_stage hS3 a2 x2 c2 hn
  refine ⟨a4, mp3, ?_, hS4, (hg12.trans hg3).trans hg4, rpMR_low (mkLetW_low hn) hM3⟩
  simp only [StateT.run_bind, hr1, except_ok_bind, hr2, hr3]
  have hr4' : (internLetEE (decE a2) (decE x2) (decE c2)).run a3' = .ok (decE r, a4) := hr4
  rw [hr4']
  rfl

theorem rpProj_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : RpGoOK dn fe vis k)
    (m m' : Mem) (a : AState) (no nl us b nn f1 x y z r : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx)
    (hn : rpP1 k m no nl us b nn f1 x y z (rpGoW k m no nl us b nn f1 z) = some (r, m'))
    (hS : StageR dn vis fe m a) (hz : H z) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hb : b.toNat + N < 2 ^ 64) (hM : rpMR m mp) :
    ∃ a' mp', (do
        let (x2, mm) ← ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f1.toNat (decE z)
        let r ← internProjE (decI x) y.toNat x2
        pure (r, mm) : AM (EIdx × Std.HashMap EIdx EIdx)).run a = .ok ((decE r, mp'), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
  rcases h1 : rpGoW k m no nl us b nn f1 z with _ | ⟨a2, m1⟩ <;> rw [h1] at hn; · simp [rpP1] at hn
  rw [rpP1_some, rpMkW_proj] at hn
  obtain ⟨a1, mp1, hr1, hS1, hg1, hM1⟩ := ih m m1 a no nl us b nn f1 z a2 N names mp h1 hS hz hus hdec hno hit hN hnn hb hM
  obtain ⟨a3, hr3, hS3, hg3⟩ := mkProj_stage hS1 x y a2 hn
  refine ⟨a3, mp1, ?_, hS3, hg1.trans hg3, rpMR_low (mkProjW_low hn) hM1⟩
  simp only [StateT.run_bind, hr1, except_ok_bind]
  have hr3' : (internProjE (decI x) y.toNat (decE a2)).run a1 = .ok (decE r, a3) := hr3
  rw [hr3']
  rfl

theorem rpApp_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : RpGoOK dn fe vis k)
    (m m' : Mem) (a : AState) (no nl us b nn f1 h x y r : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx)
    (hn : rpA1 k m no nl us b nn f1 h x y (ahWf k m no nl us b nn h) = some (r, m'))
    (hS : StageR dn vis fe m a) (hh : H h) (hx : H x) (hy : H y) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hb : b.toNat + N < 2 ^ 64) (hM : rpMR m mp) :
    ∃ a' mp', (rpArm names (decI us) b.toNat N mp f1.toNat (decE h) (.app (decE x) (decE y))).run a =
        .ok ((decE r, mp'), a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
  cases k with
  | zero => simp [ahWf, rpA1] at hn
  | succ j =>
    rcases hah : ahWf (j + 1) m no nl us b nn h with _ | ⟨rr, m1⟩; · rw [hah] at hn; simp [rpA1] at hn
    rw [hah] at hn
    obtain ⟨xo, a1, hrun1, hS1, hg1, hout⟩ := ahW_ok j dn fe vis m m1 a no nl us b nn h N names rr hah hS hN hh hus hb
      hdec hno hnn
    rw [show (decI h : EIdx) = decE h from rfl] at hrun1
    by_cases hh0 : rr.headD 0 ≠ 0
    · rw [rpA1_hit _ _ _ _ _ _ _ _ _ _ _ _ _ hh0] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      cases xo with
      | none => exact absurd hout hh0
      | some e' =>
        simp only [decOE, decW0E] at hout
        obtain ⟨-, -, hd⟩ := hout
        refine ⟨a1, mp, ?_, hS1, hg1, rpMR_low (ahW_low hah) hM⟩
        simp only [rpArm, StateT.run_bind, hrun1, except_ok_bind, show decE (rr.tail.headD 0) = e' from hd]
        rfl
    · rw [rpA1_miss _ _ _ _ _ _ _ _ _ _ _ _ _ hh0] at hn
      have hz : rr.headD 0 = 0 := by simpa using hh0
      have hxo : xo = none := by
        cases xo with
        | none => rfl
        | some e' => simp only [decOE] at hout; rw [hout.1] at hz; simp at hz
      subst hxo
      have hdec1 : decHL m1 no.toNat nl.toNat = some names := by rw [decHL_grow hg1 hit]; exact hdec
      obtain ⟨a', mp', hr, hS', hg', hM'⟩ := rpBin_ok dn fe vis (j + 1) ih 4 (fun m a b => mkAppW m a b) internAppE
        (fun m a2 x2 => by simp [rpMkW])
        (fun m m' a u v r hS hI => mkApp_stage hS u v hI) (fun m m' u v r hI => mkAppW_low hI)
        m1 m' a1 no nl us b nn f1 x y r N names mp hn hS1 hx hy hus hdec1 hno
        (by have := hg1.1; omega) hN hnn hb (rpMR_low (ahW_low hah) hM)
      refine ⟨a', mp', ?_, hS', hg1.trans hg', hM'⟩
      simp only [rpArm, StateT.run_bind, hrun1, except_ok_bind]
      exact hr

theorem rpNode_arm (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : RpGoOK dn fe vis k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v) (hnv : NodeVr v)
    (m m' : Mem) (a : AState) (no nl us b nn f1 h r : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx)
    (hn : rpNodeW (k + 1) m no nl us b nn f1 h (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0) = some (r, m'))
    (hS : StageR dn vis fe m a) (hh : H h) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hb : b.toNat + N < 2 ^ 64) (hM : rpMR m mp) :
    ∃ a' mp', (rpArm names (decI us) b.toNat N mp f1.toNat (decE h) v).run a = .ok ((decE r, mp'), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
  cases v with
  | app f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    rw [hg, rpNodeW_app] at hn
    have := rpApp_ok dn fe vis k ih m m' a no nl us b nn f1 h _ _ r N names mp hn hS hh hx hy hus hdec hno hit hN hnn hb hM
    rw [hdx, hdy] at this
    exact this
  | lam f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    rw [hg, rpNodeW_bin k m no nl us b nn f1 h 5 _ _ _ (Or.inl rfl)] at hn
    obtain ⟨a', mp', hr, hS', hg', hM'⟩ := rpBin_ok dn fe vis k ih 5 (fun m a b => mkLamW m a b) internLamE
      (fun m a2 x2 => by simp [rpMkW])
      (fun m m' a u v r hS hI => mkLam_stage hS u v hI) (fun m m' u v r hI => mkLamW_low hI)
      m m' a no nl us b nn f1 _ _ r N names mp hn hS hx hy hus hdec hno hit hN hnn hb hM
    rw [hdx, hdy] at hr
    exact ⟨a', mp', hr, hS', hg', hM'⟩
  | forallE f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    rw [hg, rpNodeW_bin k m no nl us b nn f1 h 6 _ _ _ (Or.inr rfl)] at hn
    obtain ⟨a', mp', hr, hS', hg', hM'⟩ := rpBin_ok dn fe vis k ih 6 (fun m a b => mkForallW m a b) internForallEE
      (fun m a2 x2 => by simp [rpMkW])
      (fun m m' a u v r hS hI => mkForall_stage hS u v hI) (fun m m' u v r hI => mkForallW_low hI)
      m m' a no nl us b nn f1 _ _ r N names mp hn hS hx hy hus hdec hno hit hN hnn hb hM
    rw [hdx, hdy] at hr
    exact ⟨a', mp', hr, hS', hg', hM'⟩
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
    rw [hg, rpNodeW_let] at hn
    have := rpLet_ok dn fe vis k ih m m' a no nl us b nn f1 _ _ _ r N names mp hn hS hx hy hz hus hdec hno hit hN hnn hb hM
    rw [hdx, hdy, hdz] at this
    exact this
  | proj s i e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hi, hz, hdz⟩ := hvr
    rw [hg, rpNodeW_proj k m no nl us b nn f1 h 9 _ _ _ (by decide) (by decide) (by decide)] at hn
    have := rpProj_ok dn fe vis k ih m m' a no nl us b nn f1 _ _ _ r N names mp hn hS hz hus hdec hno hit hN hnn hb hM
    rw [hdz, hdx, hi] at this
    exact this
  | bvar _ => exact False.elim hnv
  | sort _ => exact False.elim hnv
  | const _ _ => exact False.elim hnv
  | lit _ => exact False.elim hnv
  | fvar _ _ => exact False.elim hnv

theorem rpTwin_node (names : List NIdx) (us : LsIdx) (b n : Nat) (memo : Std.HashMap EIdx EIdx)
    (fuel : Nat) (h : EIdx) (a : AState) (v : ENodeView) (hv : a.store.view h = some v) (hnv : NodeVr v) :
    (ConRon.Arena.replaceAppsGo names us b n memo (fuel + 1) h).run a =
      ((match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← rpArm names us b n memo fuel h v
          pure (r, m.insert h r) : AM (EIdx × Std.HashMap EIdx EIdx)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | (rw [replaceAppsGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind])

theorem rpGo_nodeCase (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (j : Nat)
    (ih : ∀ k, k + 1 < j + 1 → RpGoOK dn fe vis k) (m m' : Mem) (a : AState)
    (no nl us b nn f h r : Word) (N : Nat) (names : List NIdx) (mp : Std.HashMap EIdx EIdx) (F : Nat)
    (hF : f.toNat = F + 1) (hf0 : f ≠ 0) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVr v) (hv : a.store.view (decE h) = some v) (hvl : vl ≠ [])
    (hgs : vl.headD 0 = 4 ∨ vl.headD 0 = 5 ∨ vl.headD 0 = 6 ∨ vl.headD 0 = 7 ∨ vl.headD 0 = 9)
    (hb : rpG1 j m no nl us b nn f h vl = some (r, m')) (hS : StageR dn vis fe m a) (hh : H h) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hbN : b.toNat + N < 2 ^ 64) (hM : rpMR m mp) :
    ∃ a' mp', (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp (F + 1) (decE h)).run a =
        .ok ((decE r, mp'), a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
  have hnl : ¬ (vl.headD 0 = 0 ∨ vl.headD 0 = 1 ∨ vl.headD 0 = 2 ∨ vl.headD 0 = 8) := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  have hn3 : ¬ vl.headD 0 = 3 := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  rw [rpG1_node j m no nl us b nn f h vl hvl hnl hn3] at hb
  rw [rpTwin_node _ _ _ _ _ _ _ a v hv hnv]
  by_cases hfr : mfindG raSch m h 0 = []
  · rw [rpG3_abort j m no nl us b nn f h vl _ hfr] at hb; simp at hb
  by_cases hhit : (mfindG raSch m h 0).headD 0 ≠ 0
  · rw [rpG3_hit j m no nl us b nn f h vl _ hfr hhit] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    have hmem := memoRG_hit raSch bmKey (fun w : Word => decE w) m mp hM h 0 hfr hhit ⟨hh, rfl⟩
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmem
    refine ⟨a, mp, ?_, hS, IWGrow.refl _, hM⟩
    simp only [hmem]; rfl
  · rw [rpG3_miss j m no nl us b nn f h vl _ hfr hhit] at hb
    have hmiss := memoRG_miss raSch bmKey (fun w : Word => decE w) m mp hM h 0 ⟨hh, rfl⟩ hfr (by simpa using hhit)
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmiss
    cases j with
    | zero => simp [rpNodeW, rpG4] at hb
    | succ k =>
      rcases hnode : rpNodeW (k + 1) m no nl us b nn (f - 1) h (vl.headD 0) (vl.tail.headD 0)
          (vl.tail.tail.headD 0) (vl.tail.tail.tail.headD 0) with _ | ⟨rn, m1⟩; · rw [hnode] at hb; simp [rpG4] at hb
      rw [hnode, rpG4_some] at hb
      rcases hset : msetG raSch m1 h 0 rn with _ | m2 <;> rw [hset] at hb; · simp [rpG5] at hb
      rw [rpG5_some] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have hF1 : (f - 1).toNat = F := by rw [toNat_sub_one' hf0, hF]; rfl
      obtain ⟨a1, mp1, hr1, hS1, hg1, hM1⟩ := rpNode_arm dn fe vis k (ih k (by omega)) vl v hvr hnv m m1 a no nl us b
        nn (f - 1) h rn N names mp hnode hS hh hus hdec hno hit hN hnn hbN hM
      rw [hF1] at hr1
      have hset' := memoRG_set raSch raSch_wf bmKey (fun w : Word => decE w) m1 mp1 hM1 h 0 rn ⟨hh, rfl⟩ m2 hset
      have hfs : MemFrame [RAM] [raSch.cs + 1] m1 m2 := msetG_frame raSch raSch_wf m1 m2 h 0 rn hset
      obtain ⟨hS2, hg2⟩ := StageR.frame_hi hS1 hfs (by intro b hb; simp at hb; subst hb; decide)
        (by intro x hx; simp [raSch] at hx; subst hx; decide) (by decide) (by simp [raSch])
      refine ⟨a1, mp1.insert (decE h) (decE rn), ?_, hS2, hg1.trans hg2, hset'⟩
      simp only [hmiss, StateT.run_bind, hr1, except_ok_bind]
      rfl

theorem rpGo_step_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (j : Nat)
    (ih : ∀ k, k + 1 < j + 1 → RpGoOK dn fe vis k) : RpGoOK dn fe vis (j + 1) := by
  intro m m' a no nl us b nn f h r N names mp hb hS hh hus hdec hno hit hN hnn hbN hM
  by_cases hf0 : f = 0
  · rw [rpGoW_abort j m no nl us b nn f h hf0] at hb; simp at hb
  rw [rpGoW_view j m no nl us b nn f h hf0] at hb
  obtain ⟨F, hF⟩ : ∃ F, f.toNat = F + 1 := ⟨f.toNat - 1, by have := toNat_ne_zero' hf0; omega⟩
  cases hvl : eViewW m h with
  | nil => rw [hvl] at hb; simp [rpG1] at hb
  | cons g vt =>
    have hne : eViewW m h ≠ [] := by rw [hvl]; simp
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hS.1.arena.1 h hne
    rw [hvl] at hvr hb
    have leaf : ∀ (hg : (g :: vt).headD 0 = 0 ∨ (g :: vt).headD 0 = 1 ∨ (g :: vt).headD 0 = 2 ∨ (g :: vt).headD 0 = 8),
        (match v with | .bvar _ | .sort _ | .lit _ | .fvar _ _ => True | _ => False) →
        ∃ a' mp', (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)).run a =
          .ok ((decE r, mp'), a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
      intro hg hv'
      rw [rpG1_leaf j m no nl us b nn f h _ (by simp) hg] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      refine ⟨a, mp, ?_, hS, IWGrow.refl _, hM⟩
      rw [hF, replaceAppsGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      cases v <;> first | rfl | exact False.elim hv'
    cases v with
    | bvar i =>
      have hg0 : (g :: vt).headD 0 = 0 := by simpa [ViewR] using hvr.1
      exact leaf (Or.inl hg0) trivial
    | sort u =>
      have hg0 : (g :: vt).headD 0 = 2 := by simpa [ViewR] using hvr.1
      exact leaf (Or.inr (Or.inr (Or.inl hg0))) trivial
    | lit l =>
      have hg0 : (g :: vt).headD 0 = 8 := by simpa [ViewR] using hvr
      exact leaf (Or.inr (Or.inr (Or.inr hg0))) trivial
    | fvar i ty =>
      have hg0 : (g :: vt).headD 0 = 1 := hvr.1
      exact leaf (Or.inr (Or.inl hg0)) trivial
    | const nn' us' =>
      have hg3 : (g :: vt).headD 0 = 3 := hvr.1
      rw [rpG1_const j m no nl us b nn f h _ (by simp) (by rw [hg3]; decide) hg3] at hb
      cases j with
      | zero => simp [ahWf, rpH] at hb
      | succ i =>
        rcases hah : ahWf (i + 1) m no nl us b nn h with _ | ⟨rr, m1⟩; · rw [hah] at hb; simp [rpH] at hb
        simp only [hah, rpH_some] at hb
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
        obtain ⟨xo, a1, hrun1, hS1, hg1, hout⟩ := ahW_ok i dn fe vis m m1 a no nl us b nn h N names rr hah hS hN hh hus
          hbN hdec hno hnn
        rw [show (decI h : EIdx) = decE h from rfl] at hrun1
        refine ⟨a1, mp, ?_, hS1, hg1, rpMR_low (ahW_low hah) hM⟩
        simp only [hF, replaceAppsGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind, hrun1]
        cases xo with
        | none =>
          simp only [decOE] at hout
          simp only [hout, ne_eq, not_true_eq_false, ite_false]; rfl
        | some e' =>
          simp only [decOE, decW0E] at hout
          obtain ⟨h1, -, hd⟩ := hout
          have hne : ¬ rr.headD 0 = 0 := by rw [h1]; decide
          rw [ite_eq_left (show rr.headD 0 ≠ 0 from hne)]
          show (pure (e', mp) : AM _).run a1 = _
          rw [show decE (rr.tail.headD 0) = e' from hd]; rfl
    | app f' x' =>
      rw [hF]
      exact rpGo_nodeCase dn fe vis j ih m m' a no nl us b nn f h r N names mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inl hvr.1) hb hS hh hus hdec hno hit hN hnn hbN hM
    | lam f' x' =>
      rw [hF]
      exact rpGo_nodeCase dn fe vis j ih m m' a no nl us b nn f h r N names mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inl hvr.1)) hb hS hh hus hdec hno hit hN hnn hbN hM
    | forallE f' x' =>
      rw [hF]
      exact rpGo_nodeCase dn fe vis j ih m m' a no nl us b nn f h r N names mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inr (Or.inl hvr.1))) hb hS hh hus hdec hno hit hN hnn hbN hM
    | letE t v' b' =>
      rw [hF]
      exact rpGo_nodeCase dn fe vis j ih m m' a no nl us b nn f h r N names mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inr (Or.inr (Or.inl hvr.1)))) hb hS hh hus hdec hno hit hN hnn hbN hM
    | proj s i e =>
      rw [hF]
      exact rpGo_nodeCase dn fe vis j ih m m' a no nl us b nn f h r N names mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inr (Or.inr (Or.inr hvr.1)))) hb hS hh hus hdec hno hit hN hnn hbN hM

theorem rpGoOK (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) :
    RpGoOK dn fe vis n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro m m' a no nl us b nn f h r N names mp hb; simp [rpGoW] at hb
    | succ j => exact rpGo_step_ok dn fe vis j (fun k hk => ih k (by omega))

theorem rpConstW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl us b nn e r : Word) (N : Nat) (names : List NIdx)
    (mp0 : Std.HashMap EIdx EIdx)
    (hb : rpConstW n m no nl us b nn e = some (r, m')) (hS : StageR dn vis fe m a) (he : H e) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hbN : b.toNat + N < 2 ^ 64) (hM : rpMR m mp0) :
    ∃ a', (ConRon.Arena.replaceApps names (decI us) b.toNat N (decE e)).run a = .ok (decE r, a') ∧
      rpMR m' ∅ ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  by_cases h0 : rdW (m.arr64 CTL) raSch.cs + 2 = 0
  · simp [rpConstW, h0] at hb
  rw [rpConstW_eq n m no nl us b nn e h0] at hb
  have hf0 := mclearG_frame raSch m
  have hM0 := memoRG_clear raSch raSch_wf bmKey (fun w : Word => decE w) m mp0 hM h0
  obtain ⟨hS0, hg0⟩ := StageR.frame_hi hS hf0 (by intro b hb; simp at hb) (by intro x hx; simp [raSch] at hx; rcases hx with rfl | rfl <;> decide)
    (by simp) (by simp [raSch])
  have hdec0 : decHL (mclearG raSch m) no.toNat nl.toNat = some names := by rw [decHL_grow hg0 hit]; exact hdec
  rcases hg : rpGoW n (mclearG raSch m) no nl us b nn CWF e with _ | ⟨r1, m1⟩ <;> rw [hg] at hb; · simp [rpClrK] at hb
  by_cases h1 : rdW (m1.arr64 CTL) raSch.cs + 2 = 0
  · simp [rpClrK, h1] at hb
  rw [rpClrK_some r1 m1 h1] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  obtain ⟨a1, mp1, hrun, hS1, hg1, hM1⟩ := rpGoOK dn fe vis n _ _ a no nl us b nn CWF e r1 N names ∅ hg hS0 he hus hdec0
    hno (by have := hg0.1; omega) hN hnn hbN hM0
  rw [CWF_eq] at hrun
  have hM2 := memoRG_clear raSch raSch_wf bmKey (fun w : Word => decE w) m1 mp1 hM1 h1
  have hf2 := mclearG_frame raSch m1
  obtain ⟨hS2, hg2⟩ := StageR.frame_hi hS1 hf2 (by intro b hb; simp at hb) (by intro x hx; simp [raSch] at hx; rcases hx with rfl | rfl <;> decide)
    (by simp) (by simp [raSch])
  refine ⟨a1, ?_, hM2, hS2, (hg0.trans hg1).trans hg2⟩
  simp only [ConRon.Arena.replaceApps, StateT.run_bind, hrun]
  rfl

section census
variable (p : Prog) (hl : AhLook p) (hk : MkLook p)
  (hf : p.lookup "ra_find" = some (memoFindG raSch)) (hput : p.lookup "ra_put" = some (memoPutG raSch))
  (hgo : p.lookup "replace_apps_go" = some replaceAppsGo)
  (hnode : p.lookup "replace_apps_node" = some replaceAppsNode)
include hl hk hf hput hgo hnode

/-- **`replace_apps_go` (with `replace_apps_node`) refines `replaceAppsGo`**, from a memo related to
the twin's. -/
@[refines ConRon.Arena.replaceAppsGo]
theorem replaceAppsGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl us b nn f h : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx) (hh : H h) (hus : H us) (hS : StageR dn vis fe s₀.mem a₀)
    (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem) (hN : nn.toNat = N)
    (hnn : nn.toNat + names.length < 2 ^ 64) (hbN : b.toNat + N < 2 ^ 64) (hM : rpMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "replace_apps_go" [no, nl, us, b, nn, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)) a₀ ∧
      decE (r.headD 0) =
        (AM.res (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)) a₀).1 ∧
      rpMR s'.mem
        (AM.res (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem
        (AM.st (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post ((rpGo_spec p hl hk hf hput hgo hnode n).1 s₀ no nl us b nn f h) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨a', mp', hrun, hS', hg, hM'⟩ := rpGoOK dn fe vis n _ _ a₀ no nl us b nn f h _ N names mp hm hS hh hus hdec
    hno hit hN hnn hbN hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hres], by rw [hres]; exact hM', by rw [hst]; exact hS', hg⟩

end census

section census2
variable (p : Prog) (hl : AhLook p) (hk : MkLook p)
  (hf : p.lookup "ra_find" = some (memoFindG raSch)) (hput : p.lookup "ra_put" = some (memoPutG raSch))
  (hgo : p.lookup "replace_apps_go" = some replaceAppsGo)
  (hnode : p.lookup "replace_apps_node" = some replaceAppsNode)
  (hcl : p.lookup "ra_clear" = some (memoClearG raSch))
  (hp : p.lookup "replace_apps" = some replaceApps)
include hl hk hf hput hgo hnode hcl hp

/-- **`replace_apps` refines `replaceApps`**: one memoised DAG walk between two clears. -/
@[refines ConRon.Arena.replaceApps]
theorem replaceApps_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl us b nn e : Word) (N : Nat) (names : List NIdx)
    (mp0 : Std.HashMap EIdx EIdx) (he : H e) (hus : H us) (hS : StageR dn vis fe s₀.mem a₀)
    (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem) (hN : nn.toNat = N)
    (hnn : nn.toNat + names.length < 2 ^ 64) (hbN : b.toNat + N < 2 ^ 64) (hM : rpMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "replace_apps" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.replaceApps names (decI us) b.toNat N (decE e)) a₀ ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.replaceApps names (decI us) b.toNat N (decE e)) a₀ ∧
      rpMR s'.mem ∅ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.replaceApps names (decI us) b.toNat N (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (replaceApps_spec p hl hk hf hput hgo hnode hcl hp n s₀ no nl us b nn e) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨a', hrun, hM', hS', hg⟩ := rpConstW_ok n dn fe vis _ _ a₀ no nl us b nn e _ N names mp0 hm hS he hus hdec hno
    hit hN hnn hbN hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hres], hM', by rw [hst]; exact hS', hg⟩

end census2

end L.Ind
