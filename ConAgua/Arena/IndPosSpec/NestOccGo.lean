import ConAgua.Arena.IndPosSpec.MentionsAnyGo
import ConAgua.Arena.IndPosSpec.NoGoStep
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# NestOccGo: `ConRon.Arena.memberIdxAt`, `ConRon.Arena.mentionsAnyConst`, `ConRon.Arena.nestOccGo`, `ConRon.Arena.nestOcc`, `ConRon.Arena.phApp`

The refinement theorems `mentionsAnyConst_refines`, `nestOccGo_refines`, `nestOcc_refines`, `memberIdxAt_refines`, `phApp_refines` and the lemmas only they use.
-/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem mentionsAnyConst_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hc : p.lookup "sl_contains" = some slContains)
    (hf : p.lookup "ma_find" = some (memoFindG maSch)) (hput : p.lookup "ma_put" = some (memoPutG maSch))
    (hgo : p.lookup "mentions_any_go" = some mentionsAnyGo)
    (hnode : p.lookup "mentions_any_node" = some mentionsAnyNode)
    (hcl : p.lookup "ma_clear" = some (memoClearG maSch))
    (hp : p.lookup "mentions_any_const" = some mentionsAnyConst) (n : Nat) (s₀ : St) (no nl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "mentions_any_const" [no, nl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ maConstW n s₀.mem no nl e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (maGo_spec p hv hc hf hput hgo hnode n).1
  unfold MaGoSpec at ih
  simp only [invoke_eq _ hp, callFn, mentionsAnyConst]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec maSch p _ hcl n, ih] <;>
    finish

theorem maConstW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl e r : Word) (ws : List Word) (mp0 : Std.HashMap EIdx Bool)
    (hb : maConstW n m no nl e = some (r, m')) (hS : StageR dn vis fe m a) (hh : H e)
    (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp0) :
    ∃ b, (ConRon.Arena.mentionsAnyConst (ws.map (fun w => (decI w : NIdx))) (decE e)).run a =
        .ok (b, a) ∧ (r != 0) = b ∧ maMR m' ∅ ∧ StageR dn vis fe m' a ∧ IWGrow m m' := by
  by_cases h0 : rdW (m.arr64 CTL) maSch.cs + 2 = 0
  · simp [maConstW, h0] at hb
  rw [maConstW_eq n m no nl e h0] at hb
  have hf0 := mclearG_frame maSch m
  have hM0 := memoRG_clear maSch maSch_wf bmKey (fun w : Word => w != 0) m mp0 hM h0
  have hA0 : ArenaR (mclearG maSch m) a :=
    ArenaR.frame (A := []) (C := [maSch.cs, maSch.cs + 1]) (fun b hb => by simp at hb)
      (fun x hx => by simp [maSch] at hx; rcases hx with rfl | rfl <;> exact not_mem_arenaCtl _ (by decide)) hf0
      hS.1.arena.1
  have hws0 : SlR (mclearG maSch m) no nl ws := slR_congr (hf0.1 IW (by simp) (by decide)) hws
  rcases hg : maGoW n (mclearG maSch m) no nl CWF e with _ | ⟨r1, m1⟩ <;> rw [hg] at hb; · simp [maClrK] at hb
  by_cases h1 : rdW (m1.arr64 CTL) maSch.cs + 2 = 0
  · simp [maClrK, h1] at hb
  rw [maClrK_some r1 m1 h1] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  obtain ⟨c, mp1, hrun, hbb, hM1, hfr1⟩ := maGoOK n _ _ a no nl CWF e r1 ws ∅ hg hA0 hh hws0 hwlt hM0
  rw [CWF_eq] at hrun
  have hM2 := memoRG_clear maSch maSch_wf bmKey (fun w : Word => w != 0) m1 mp1 hM1 h1
  have hf2 := mclearG_frame maSch m1
  have hfall : MemFrame [MAM] [maSch.cs, maSch.cs + 1] m (mclearG maSch m1) :=
    ((hf0.mono (by simp) (by simp)).trans (hfr1.mono (by simp) (by simp [maSch]))).trans
      (hf2.mono (by simp) (by simp))
  obtain ⟨hS', hg'⟩ := StageR.frame_hi hS hfall (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp [maSch] at hx; rcases hx with rfl | rfl <;> decide) (by decide)
    (by simp [maSch])
  refine ⟨c, ?_, hbb, hM2, hS', hg'⟩
  simp only [ConRon.Arena.mentionsAnyConst, StateT.run_bind, hrun]
  rfl

section census3
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hc : p.lookup "sl_contains" = some slContains)
  (hf : p.lookup "ma_find" = some (memoFindG maSch)) (hput : p.lookup "ma_put" = some (memoPutG maSch))
  (hgo : p.lookup "mentions_any_go" = some mentionsAnyGo)
  (hnode : p.lookup "mentions_any_node" = some mentionsAnyNode)
  (hcl : p.lookup "ma_clear" = some (memoClearG maSch))
  (hp : p.lookup "mentions_any_const" = some mentionsAnyConst)
include hv hc hf hput hgo hnode hcl hp

/-- **`mentions_any_const` refines `mentionsAnyConst`**: one memoised DAG walk between two clears;
the per-call memo is any well-formed one on entry (`mp0`) and empty after. -/
@[refines ConRon.Arena.mentionsAnyConst]
theorem mentionsAnyConst_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl e : Word) (ws : List Word) (mp0 : Std.HashMap EIdx Bool) (hh : H e)
    (hS : StageR dn vis fe s₀.mem a₀) (hws : SlR s₀.mem no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hM : maMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "mentions_any_const" [no, nl, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.mentionsAnyConst (ws.map (fun w => (decI w : NIdx))) (decE e)) a₀ ∧
      AM.st (ConRon.Arena.mentionsAnyConst (ws.map (fun w => (decI w : NIdx))) (decE e)) a₀ = a₀ ∧
      (r.headD 0 != 0) =
        AM.res (ConRon.Arena.mentionsAnyConst (ws.map (fun w => (decI w : NIdx))) (decE e)) a₀ ∧
      maMR s'.mem ∅ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (mentionsAnyConst_spec p hv hc hf hput hgo hnode hcl hp n s₀ no nl e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, hrun, hb, hM', hS', hg⟩ := maConstW_ok n dn fe vis _ _ a₀ no nl e _ ws mp0 hm hS hh hws hwlt hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hst, by rw [hres]; exact hb, hM', hS', hg⟩

end census3

/-- A memo-free frame is one for any memo sets. -/
theorem MFr.up {S : List ArrId} {T : List Word} {m m' : Mem} (h : MFr [] [] m m') : MFr S T m m' :=
  h.mono (by simp) (by simp)

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hc : p.lookup "sl_contains" = some slContains)
  (hf : p.lookup "no_find" = some (memoFindG noSch)) (hput : p.lookup "no_put" = some (memoPutG noSch))
  (hgo : p.lookup "nest_occ_go" = some nestOccGo)
  (hnode : p.lookup "nest_occ_node" = some nestOccNode)
include hv hc hf hput hgo hnode

/-- **`nest_occ_go` (with `nest_occ_node`) refines `nestOccGo`**, from a memo related to
the twin's. -/
@[refines ConRon.Arena.nestOccGo]
theorem nestOccGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl lo hi f h : Word) (ws : List Word) (mp : Std.HashMap EIdx Bool) (hh : H h)
    (hS : StageR dn vis fe s₀.mem a₀) (hws : SlR s₀.mem no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hM : noMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_occ_go" [no, nl, lo, hi, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f.toNat (decE h)) a₀ ∧
      AM.st (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f.toNat (decE h)) a₀ = a₀ ∧
      (r.headD 0 != 0) =
        (AM.res (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f.toNat (decE h)) a₀).1 ∧
      noMR s'.mem
        (AM.res (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f.toNat (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post ((noGo_spec p hv hc hf hput hgo hnode n).1 s₀ no nl lo hi f h) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, mp', hrun, hb, hM', hfr⟩ := noGoOK n _ _ a₀ no nl lo hi f h _ ws mp hm hS.1.arena.1 hh hws hwlt hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  obtain ⟨hS', hg⟩ := StageR.frame_hi hS hfr (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp at hx; subst hx; decide) (by decide) (by decide)
  refine ⟨hl, hok, hst, by rw [hres]; exact hb, by rw [hres]; exact hM', hS', hg⟩

end census

theorem nestOcc_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hc : p.lookup "sl_contains" = some slContains)
    (hf : p.lookup "no_find" = some (memoFindG noSch)) (hput : p.lookup "no_put" = some (memoPutG noSch))
    (hgo : p.lookup "nest_occ_go" = some nestOccGo)
    (hnode : p.lookup "nest_occ_node" = some nestOccNode)
    (hcl : p.lookup "no_clear" = some (memoClearG noSch))
    (hp : p.lookup "nest_occ" = some nestOcc) (n : Nat) (s₀ : St) (no nl lo hi e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_occ" [no, nl, lo, hi, e]
    ⦃fun r s' => LocEq s' s₀ ∧ noConstW n s₀.mem no nl lo hi e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (noGo_spec p hv hc hf hput hgo hnode n).1
  unfold NoGoSpec at ih
  simp only [invoke_eq _ hp, callFn, nestOcc]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec noSch p _ hcl n, ih] <;>
    finish

theorem noConstW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl lo hi e r : Word) (ws : List Word) (mp0 : Std.HashMap EIdx Bool)
    (hb : noConstW n m no nl lo hi e = some (r, m')) (hS : StageR dn vis fe m a) (hh : H e)
    (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : noMR m mp0) :
    ∃ b, (ConRon.Arena.nestOcc (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat (decE e)).run a =
        .ok (b, a) ∧ (r != 0) = b ∧ noMR m' ∅ ∧ StageR dn vis fe m' a ∧ IWGrow m m' ∧
        MFr [NOM] [204, 205] m m' := by
  by_cases h0 : rdW (m.arr64 CTL) noSch.cs + 2 = 0
  · simp [noConstW, h0] at hb
  rw [noConstW_eq n m no nl lo hi e h0] at hb
  have hf0 := mclearG_frame noSch m
  have hM0 := memoRG_clear noSch noSch_wf bmKey (fun w : Word => w != 0) m mp0 hM h0
  have hA0 : ArenaR (mclearG noSch m) a :=
    ArenaR.frame (A := []) (C := [noSch.cs, noSch.cs + 1]) (fun b hb => by simp at hb)
      (fun x hx => by simp [noSch] at hx; rcases hx with rfl | rfl <;> exact not_mem_arenaCtl _ (by decide)) hf0
      hS.1.arena.1
  have hws0 : SlR (mclearG noSch m) no nl ws := slR_congr (hf0.1 IW (by simp) (by decide)) hws
  rcases hg : noGoW n (mclearG noSch m) no nl lo hi CWF e with _ | ⟨r1, m1⟩ <;> rw [hg] at hb; · simp [noClrK] at hb
  by_cases h1 : rdW (m1.arr64 CTL) noSch.cs + 2 = 0
  · simp [noClrK, h1] at hb
  rw [noClrK_some r1 m1 h1] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  obtain ⟨c, mp1, hrun, hbb, hM1, hfr1⟩ := noGoOK n _ _ a no nl lo hi CWF e r1 ws ∅ hg hA0 hh hws0 hwlt hM0
  rw [CWF_eq] at hrun
  have hM2 := memoRG_clear noSch noSch_wf bmKey (fun w : Word => w != 0) m1 mp1 hM1 h1
  have hf2 := mclearG_frame noSch m1
  have hfall : MemFrame [NOM] [noSch.cs, noSch.cs + 1] m (mclearG noSch m1) :=
    ((hf0.mono (by simp) (by simp)).trans (hfr1.mono (by simp) (by simp [noSch]))).trans
      (hf2.mono (by simp) (by simp))
  obtain ⟨hS', hg'⟩ := StageR.frame_hi hS hfall (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp [noSch] at hx; rcases hx with rfl | rfl <;> decide) (by decide)
    (by simp [noSch])
  refine ⟨c, ?_, hbb, hM2, hS', hg', ⟨_, _, hfall, by simp, fun x hx => .inr (.inr (by simpa [noSch] using hx))⟩⟩
  simp only [ConRon.Arena.nestOcc, StateT.run_bind, hrun]
  rfl

section census3
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hc : p.lookup "sl_contains" = some slContains)
  (hf : p.lookup "no_find" = some (memoFindG noSch)) (hput : p.lookup "no_put" = some (memoPutG noSch))
  (hgo : p.lookup "nest_occ_go" = some nestOccGo)
  (hnode : p.lookup "nest_occ_node" = some nestOccNode)
  (hcl : p.lookup "no_clear" = some (memoClearG noSch))
  (hp : p.lookup "nest_occ" = some nestOcc)
include hv hc hf hput hgo hnode hcl hp

/-- **`nest_occ` refines `nestOcc`**: one memoised DAG walk between two clears;
the per-call memo is any well-formed one on entry (`mp0`) and empty after. -/
@[refines ConRon.Arena.nestOcc]
theorem nestOcc_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl lo hi e : Word) (ws : List Word) (mp0 : Std.HashMap EIdx Bool) (hh : H e)
    (hS : StageR dn vis fe s₀.mem a₀) (hws : SlR s₀.mem no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hM : noMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_occ" [no, nl, lo, hi, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.nestOcc (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat (decE e)) a₀ ∧
      AM.st (ConRon.Arena.nestOcc (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat (decE e)) a₀ = a₀ ∧
      (r.headD 0 != 0) =
        AM.res (ConRon.Arena.nestOcc (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat (decE e)) a₀ ∧
      noMR s'.mem ∅ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (nestOcc_spec p hv hc hf hput hgo hnode hcl hp n s₀ no nl lo hi e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, hrun, hb, hM', hS', hg, -⟩ := noConstW_ok n dn fe vis _ _ a₀ no nl lo hi e _ ws mp0 hm hS hh hws hwlt hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hst, by rw [hres]; exact hb, hM', hS', hg⟩

end census3

def memW (n : Nat) (m : Mem) (no nl lvls e : Word) : Option (List Word × Mem) :=
  if e >>> 28 ≠ 3 then some ([0, 0], m) else memK n m no nl lvls (eViewW m e)

theorem memW_not (n : Nat) (m : Mem) (no nl lvls e : Word) (h : e >>> 28 ≠ 3) :
    memW n m no nl lvls e = some ([0, 0], m) := by simp [memW, h]
theorem memW_const (n : Nat) (m : Mem) (no nl lvls e : Word) (h : ¬ e >>> 28 ≠ 3) :
    memW n m no nl lvls e = memK n m no nl lvls (eViewW m e) := by simp only [memW]; rw [ite_eq_right h]
attribute [ind_grind] memW_not memW_const

theorem memberIdxAt_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hp : p.lookup "member_idx_at" = some memberIdxAt)
    (n : Nat) (s₀ : St) (no nl lvls e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "member_idx_at" [no, nl, lvls, e]
    ⦃fun r s' => LocEq s' s₀ ∧ memW n s₀.mem no nl lvls e = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, memberIdxAt]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, eView_spec p hv n,
      slFind_spec p hf n] <;> finish (gen := 20)

theorem memW_ok (n : Nat) (m m' : Mem) (a : AState) (no nl lvls e : Word) (r : List Word)
    (ws : List Word) (hA : ArenaR m a) (he : H e)
    (hlv : H lvls) (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hlen : ws.length < 2 ^ 64) (h : memW n m no nl lvls e = some (r, m')) :
    m' = m ∧ ∃ o, (ConRon.Arena.memberIdxAt? (ws.map (fun w => (decI w : NIdx))) (decI lvls)
      (decI e)).run a = .ok (o, a) ∧ MemIdxOut r o := by
  have htag := tag_const_iff e he
  by_cases hd : e >>> 28 ≠ 3
  · rw [memW_not n m no nl lvls e hd] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨rfl, none, ?_, rfl⟩
    have : ¬ ((decI e : EIdx).tag == ETag.const) = true := by rw [htag]; simpa using hd
    simp only [ConRon.Arena.memberIdxAt?, this]; rfl
  · rw [memW_const n m no nl lvls e hd] at h
    have he3 : e >>> 28 = 3 := by simpa using hd
    cases hvl : eViewW m e with
    | nil => rw [hvl] at h; simp [memK] at h
    | cons g vt =>
      have hne : eViewW m e ≠ [] := by rw [hvl]; simp
      obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA e hne
      rw [hvl] at hvr h
      have ht : (decE e).tag = ETag.const := by
        have h1 : ((decI e : EIdx).tag == ETag.const) = true := by rw [htag, he3]; decide
        exact beq_iff_eq.mp h1
      obtain ⟨nn, us0, rfl⟩ := EStore.view_const a.store (decE e) ht v hv
      simp only [ViewR, getD1_eq', getD2_eq] at hvr
      obtain ⟨-, hx, hdx, hy, hdy⟩ := hvr
      have hview : a.store.viewConst (decE e) = some (nn, us0) :=
        EStore.viewConst_of_view _ _ ht nn us0 hv
      have hbeq : (us0 == decI lvls) = decide ((g :: vt).tail.tail.headD 0 = lvls) := by
        rw [← hdy]; exact decI_beq' _ _ hy hlv
      by_cases hl : (g :: vt).tail.tail.headD 0 ≠ lvls
      · rw [memK_miss n m no nl lvls _ (by simp) hl] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        refine ⟨rfl, none, ?_, rfl⟩
        have : ¬ (us0 == decI lvls) = true := by rw [hbeq]; simpa using hl
        have htg : ((decI e : EIdx).tag == ETag.const) = true := by rw [htag, he3]; decide
        simp only [ConRon.Arena.memberIdxAt?, htg, ite_true, StateT.run_bind]
        rw [show (decI e : EIdx) = decE e from rfl, viewConst_run, except_ok_bind, hview]
        simp only [this]; rfl
      · rw [memK_find n m no nl lvls _ (by simp) hl] at h
        rcases hfw : findW n m no nl ((g :: vt).tail.headD 0) with _ | fr <;> rw [hfw] at h; · simp at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hfr := findW_ok n _ _ _ _ _ _ hws hfw hlen
        have hl' : (g :: vt).tail.tail.headD 0 = lvls := by simpa using hl
        have htg : ((decI e : EIdx).tag == ETag.const) = true := by rw [htag, he3]; decide
        have hfi := findIdx_decIP ws ((g :: vt).tail.headD 0) hwlt hx
        refine ⟨rfl, (ws.map (fun w => (decI w : NIdx))).findIdx? (· == nn), ?_, ?_⟩
        · simp only [ConRon.Arena.memberIdxAt?, htg, ite_true, StateT.run_bind]
          rw [show (decI e : EIdx) = decE e from rfl, viewConst_run, except_ok_bind, hview]
          have : (us0 == decI lvls) = true := by rw [hbeq]; simpa using hl'
          simp only [this, ite_true]; rfl
        · rw [← hdx, hfi, hfr]
          cases hwi : ws.findIdx? (· == (g :: vt).tail.headD 0) <;> simp [MemIdxOut]

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
  (hp : p.lookup "member_idx_at" = some memberIdxAt)
include hv hf hp

/-- **`member_idx_at` refines `memberIdxAt?`**. -/
@[refines ConRon.Arena.memberIdxAt?]
theorem memberIdxAt_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl lvls e : Word) (ws : List Word) (he : H e) (hlv : H lvls)
    (hS : StageR dn vis fe s₀.mem a₀) (hws : SlR s₀.mem no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hlen : ws.length < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "member_idx_at" [no, nl, lvls, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.memberIdxAt? (ws.map (fun w => (decI w : NIdx))) (decI lvls) (decI e)) a₀ ∧
      AM.st (ConRon.Arena.memberIdxAt? (ws.map (fun w => (decI w : NIdx))) (decI lvls) (decI e)) a₀ = a₀ ∧
      MemIdxOut r
        (AM.res (ConRon.Arena.memberIdxAt? (ws.map (fun w => (decI w : NIdx))) (decI lvls) (decI e)) a₀) ∧
      s'.mem = s₀.mem; ⊤⦄ := by
  refine triple_post (memberIdxAt_spec p hv hf hp n s₀ no nl lvls e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hmem, o, hrun, hout⟩ := memW_ok n _ _ a₀ no nl lvls e r ws hS.1.arena.1 he hlv hws hwlt hlen hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hst, by rw [hres]; exact hout, hmem⟩

end census

/-! ## `ph_app` -/

theorem ETables.get_app (t : ETables) (i : EIdx) (ht : i.tag = ETag.app) (v : ENodeView)
    (h : t.get i = some v) : ∃ f x, v = .app f x := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app] at h
  cases hn : t.apps.node? i.idxNat with
  | none => simp [hn] at h
  | some x => simp [hn] at h; exact ⟨_, _, h.symm⟩

theorem EStore.view_app (st : EStore) (i : EIdx) (ht : i.tag = ETag.app) (v : ENodeView)
    (h : st.view i = some v) : ∃ f x, v = .app f x := by
  unfold EStore.view at h
  split at h
  · exact ETables.get_app _ _ ht v h
  · split at h
    · exact ETables.get_app _ _ ht v h
    · simp at h

theorem ETables.get_fvar (t : ETables) (i : EIdx) (ht : i.tag = ETag.fvar) (v : ENodeView)
    (h : t.get i = some v) : ∃ k ty, v = .fvar k ty := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar] at h
  cases hn : t.fvars.node? i.idxNat with
  | none => simp [hn] at h
  | some x => simp [hn] at h; exact ⟨_, _, h.symm⟩

theorem EStore.view_fvar (st : EStore) (i : EIdx) (ht : i.tag = ETag.fvar) (v : ENodeView)
    (h : st.view i = some v) : ∃ k ty, v = .fvar k ty := by
  unfold EStore.view at h
  split at h
  · exact ETables.get_fvar _ _ ht v h
  · split at h
    · exact ETables.get_fvar _ _ ht v h
    · simp at h

theorem ETables.getApp_of_get (t : ETables) (i : EIdx) (ht : i.tag = ETag.app) (f x : EIdx)
    (h : t.get i = some (.app f x)) : t.getApp i = some (f, x) := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app] at h
  simp only [ETables.getApp]
  cases hn : t.apps.node? i.idxNat with
  | none => simp [hn] at h
  | some y => simp [hn] at h ⊢; exact h

theorem EStore.viewApp_of_view (st : EStore) (i : EIdx) (ht : i.tag = ETag.app) (f x : EIdx)
    (h : st.view i = some (.app f x)) : st.viewApp i = some (f, x) := by
  unfold EStore.view at h
  unfold EStore.viewApp EStore.persGetApp
  split at h
  · rename_i hp; rw [ite_eq_left hp]; exact ETables.getApp_of_get _ _ ht f x h
  · rename_i hp; rw [ite_eq_right hp]
    split at h
    · rename_i hs; rw [ite_eq_left hs]; exact ETables.getApp_of_get _ _ ht f x h
    · simp at h

theorem viewApp_run' (h : EIdx) (a : AState) :
    (ConRon.Arena.viewApp h).run a = .ok (a.store.viewApp h, a) := rfl

theorem ETables.getFVarIdx_of_get' (t : ETables) (i : EIdx) (ht : i.tag = ETag.fvar) (k : Nat) (ty : EIdx)
    (h : t.get i = some (.fvar k ty)) : t.getFVarIdx i = some k := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar] at h
  simp only [ETables.getFVarIdx]
  cases hn : t.fvars.node? i.idxNat with
  | none => simp [hn] at h
  | some y => simp [hn] at h ⊢; exact h.1

theorem EStore.viewFVarIdx_of_view' (st : EStore) (i : EIdx) (ht : i.tag = ETag.fvar) (k : Nat) (ty : EIdx)
    (h : st.view i = some (.fvar k ty)) : st.viewFVarIdx i = some k := by
  unfold EStore.view at h
  unfold EStore.viewFVarIdx EStore.persGetFVarIdx
  split at h
  · rename_i hp; rw [ite_eq_left hp]; exact ETables.getFVarIdx_of_get' _ _ ht k ty h
  · rename_i hp; rw [ite_eq_right hp]
    split at h
    · rename_i hs; rw [ite_eq_left hs]; exact ETables.getFVarIdx_of_get' _ _ ht k ty h
    · simp at h

theorem viewFVarIdx_run'' (h : EIdx) (a : AState) :
    (ConRon.Arena.viewFVarIdx h).run a = .ok (a.store.viewFVarIdx h, a) := rfl

/-- **`ph_app` is its model `phW`** (generated). -/
l_model phApp_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "ph_app" = some phApp)
  fns [hp ↦ phW ro]
  specs [eView_spec p hv n]
  grind [ind_grind] simp [St.setLocs_mem']

theorem tag_app_iff (w : Word) (hw : w.toNat < 2 ^ 32) :
    ((decI w : EIdx).tag == ETag.app) = decide (w >>> 28 = 4) := by
  have := decE_tag_eq w hw 4 (by decide)
  have e1 : (ETag.app : UInt32) = UInt32.ofNat 4 := rfl
  show ((decE w).tag == ETag.app) = _
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e1, this]
  exact Iff.rfl

theorem tag_fvar_iff (w : Word) (hw : w.toNat < 2 ^ 32) :
    ((decI w : EIdx).tag == ETag.fvar) = decide (w >>> 28 = 1) := by
  have := decE_tag_eq w hw 1 (by decide)
  have e1 : (ETag.fvar : UInt32) = UInt32.ofNat 1 := rfl
  show ((decE w).tag == ETag.fvar) = _
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e1, this]
  exact Iff.rfl

def PhOut (r : List Word) : Option (NIdx × LsIdx) → Prop
  | none => r.headD 0 = 0
  | some (c, us) => ∃ w1 w2, r = [1, w1, w2] ∧ w1.toNat < 2 ^ 32 ∧ decI w1 = c ∧
      w2.toNat < 2 ^ 32 ∧ decI w2 = us

theorem phW_ok (k : Nat) : ∀ (m : Mem) (a : AState) (b e n : Word) (N : Nat) (r : List Word),
    n.toNat = N → phW k m b e n = some r → ArenaR m a → H e → b.toNat + N < 2 ^ 64 →
    ∃ o, (ConRon.Arena.phApp? b.toNat (decI e) N).run a = .ok (o, a) ∧ PhOut r o := by
  induction k with
  | zero => intro m a b e n N r _ h; simp [phW] at h
  | succ k ih =>
    intro m a b e n N r hN h hA he hb
    by_cases hn0 : n = 0
    · have hN0 : N = 0 := by rw [← hN, hn0]; rfl
      subst hN0
      by_cases hd : e >>> 28 ≠ 3
      · rw [phW.arm1 k m b e n hn0 hd] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨none, ?_, rfl⟩
        have : ¬ ((decI e : EIdx).tag == ETag.const) = true := by rw [tag_const_iff e he]; simpa using hd
        simp only [ConRon.Arena.phApp?, this]; rfl
      · have he3 : e >>> 28 = 3 := by simpa using hd
        cases hvl : eViewW m e with
        | nil => rw [phW.abort1 k m b e n hn0 he3 hvl] at h; cases h
        | cons g vt =>
          have hne : eViewW m e ≠ [] := by rw [hvl]; simp
          obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA e hne
          rw [phW.arm2 k m b e n hn0 he3 hne, hvl] at h
          rw [hvl] at hvr
          simp only [Option.some.injEq] at h
          subst h
          have ht : (decE e).tag = ETag.const := by
            have h1 : ((decI e : EIdx).tag == ETag.const) = true := by rw [tag_const_iff e he, he3]; decide
            exact beq_iff_eq.mp h1
          obtain ⟨nn, us0, rfl⟩ := EStore.view_const a.store (decE e) ht v hv
          simp only [ViewR, getD1_eq', getD2_eq] at hvr
          obtain ⟨-, hx, hdx, hy, hdy⟩ := hvr
          have hview : a.store.viewConst (decE e) = some (nn, us0) :=
            EStore.viewConst_of_view _ _ ht nn us0 hv
          have htg : ((decI e : EIdx).tag == ETag.const) = true := by rw [tag_const_iff e he, he3]; decide
          refine ⟨some (nn, us0), ?_, ?_⟩
          · simp only [ConRon.Arena.phApp?, htg, ite_true, StateT.run_bind]
            rw [show (decI e : EIdx) = decE e from rfl, viewConst_run, except_ok_bind, hview]
            rfl
          · exact ⟨_, _, rfl, hx, hdx, hy, hdy⟩
    · obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by have := toNat_ne_zero' hn0; omega⟩
      by_cases hd : e >>> 28 ≠ 4
      · rw [phW.arm3 k m b e n hn0 hd] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨none, ?_, rfl⟩
        have : ¬ ((decI e : EIdx).tag == ETag.app) = true := by rw [tag_app_iff e he]; simpa using hd
        simp only [ConRon.Arena.phApp?, this]; rfl
      · have he4 : e >>> 28 = 4 := by simpa using hd
        cases hvl : eViewW m e with
        | nil => rw [phW.abort2 k m b e n hn0 he4 hvl] at h; cases h
        | cons g vt =>
          have hne : eViewW m e ≠ [] := by rw [hvl]; simp
          obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA e hne
          rw [hvl] at hvr
          have ht : (decE e).tag = ETag.app := by
            have h1 : ((decI e : EIdx).tag == ETag.app) = true := by rw [tag_app_iff e he, he4]; decide
            exact beq_iff_eq.mp h1
          obtain ⟨f', a', rfl⟩ := EStore.view_app a.store (decE e) ht v hv
          simp only [ViewR, getD1_eq', getD2_eq] at hvr
          obtain ⟨-, hx, hdx, hy, hdy⟩ := hvr
          have hview : a.store.viewApp (decE e) = some (f', a') :=
            EStore.viewApp_of_view _ _ ht f' a' hv
          have htg : ((decI e : EIdx).tag == ETag.app) = true := by rw [tag_app_iff e he, he4]; decide
          by_cases hy1 : (g :: vt).tail.tail.headD 0 >>> 28 ≠ 1
          · rw [phW.arm4 k m b e n hn0 he4 hne (by rw [hvl]; exact hy1)] at h
            simp only [Option.some.injEq] at h
            subst h
            refine ⟨none, ?_, rfl⟩
            have : ¬ (a'.tag == ETag.fvar) = true := by
              rw [← hdy]
              show ¬ ((decI ((g :: vt).tail.tail.headD 0) : EIdx).tag == ETag.fvar) = true
              rw [tag_fvar_iff _ hy]; simpa using hy1
            simp only [ConRon.Arena.phApp?, htg, ite_true, StateT.run_bind]
            rw [show (decI e : EIdx) = decE e from rfl, viewApp_run', except_ok_bind, hview]
            simp only [this]; rfl
          · have hy1' : (g :: vt).tail.tail.headD 0 >>> 28 = 1 := by simpa using hy1
            cases hvl2 : eViewW m ((g :: vt).tail.tail.headD 0) with
            | nil => rw [phW.abort3 k m b e n hn0 he4 hne (by rw [hvl]; exact hy1') (by rw [hvl]; exact hvl2)] at h; cases h
            | cons g2 vt2 =>
              have hne2 : eViewW m ((g :: vt).tail.tail.headD 0) ≠ [] := by rw [hvl2]; simp
              obtain ⟨v2, hv2, hvr2⟩ := eViewW_ok m a hA _ hne2
              rw [hvl2] at hvr2
              have hyd : decE ((g :: vt).tail.tail.headD 0) = a' := hdy
              rw [hyd] at hv2
              have ht2 : a'.tag = ETag.fvar := by
                have h1 : ((decI ((g :: vt).tail.tail.headD 0) : EIdx).tag == ETag.fvar) = true := by
                  rw [tag_fvar_iff _ hy, hy1']; decide
                rw [← hyd]; exact beq_iff_eq.mp h1
              obtain ⟨j, ty, rfl⟩ := EStore.view_fvar a.store a' ht2 v2 hv2
              simp only [ViewR, getD1_eq'] at hvr2
              obtain ⟨-, hj, -⟩ := hvr2
              have hfi : a.store.viewFVarIdx a' = some j := EStore.viewFVarIdx_of_view' _ _ ht2 j ty hv2
              have hnn : (n - 1).toNat = N' := by rw [toNat_sub_one' hn0, hN]; rfl
              have hbn : (b + (n - 1)).toNat = b.toNat + N' := by
                rw [UInt64.toNat_add, hnn]; exact Nat.mod_eq_of_lt (by omega)
              by_cases hm : (g2 :: vt2).tail.headD 0 ≠ b + (n - 1)
              · rw [phW.arm5 k m b e n hn0 he4 hne (by rw [hvl]; exact hy1') (by rw [hvl]; exact hne2)
                  (by rw [hvl, hvl2]; exact hm)] at h
                simp only [Option.some.injEq] at h
                subst h
                refine ⟨none, ?_, rfl⟩
                have htfv : (a'.tag == ETag.fvar) = true := by
                  rw [← hyd]
                  show ((decI ((g :: vt).tail.tail.headD 0) : EIdx).tag == ETag.fvar) = true
                  rw [tag_fvar_iff _ hy, hy1']; decide
                have hjne : ¬ (j == b.toNat + N') = true := by
                  intro hc
                  have : j = b.toNat + N' := beq_iff_eq.mp hc
                  apply hm
                  apply UInt64.toNat_inj.mp
                  rw [hbn, ← this, ← hj]
                simp only [ConRon.Arena.phApp?, htg, ite_true, StateT.run_bind]
                rw [show (decI e : EIdx) = decE e from rfl, viewApp_run', except_ok_bind, hview]
                simp only [htfv, ite_true, StateT.run_bind]
                rw [viewFVarIdx_run'', except_ok_bind, hfi]
                simp only [hjne]; rfl
              · rw [phW.arm6 k m b e n hn0 he4 hne (by rw [hvl]; exact hy1') (by rw [hvl]; exact hne2)
                  (by rw [hvl, hvl2]; exact Decidable.of_not_not hm), hvl] at h
                cases hrec : phW k m b ((g :: vt).tail.headD 0) (n - 1) with
                | none => rw [hrec, phW.k_ph_app.none] at h; cases h
                | some r' =>
                  rw [hrec, phW.k_ph_app.arm1] at h
                  simp only [Option.some.injEq] at h
                  obtain ⟨o, hro, hpo⟩ := ih m a b _ (n - 1) N' r' hnn hrec hA hx (by omega)
                  subst h
                  have hm' : (g2 :: vt2).tail.headD 0 = b + (n - 1) := by simpa using hm
                  have hjeq : j = b.toNat + N' := by rw [← hbn, ← hm', ← hj]
                  have htfv : (a'.tag == ETag.fvar) = true := by
                    rw [← hyd]
                    show ((decI ((g :: vt).tail.tail.headD 0) : EIdx).tag == ETag.fvar) = true
                    rw [tag_fvar_iff _ hy, hy1']; decide
                  refine ⟨o, ?_, ?_⟩
                  · simp only [ConRon.Arena.phApp?, htg, ite_true, StateT.run_bind]
                    rw [show (decI e : EIdx) = decE e from rfl, viewApp_run', except_ok_bind, hview]
                    simp only [htfv, ite_true, StateT.run_bind]
                    rw [viewFVarIdx_run'', except_ok_bind, hfi]
                    have : (j == b.toNat + N') = true := by rw [hjeq]; simp
                    simp only [this, ite_true]
                    rw [← hdx]
                    exact hro
                  · cases o with
                    | none => simpa [PhOut] using hpo
                    | some pr =>
                      obtain ⟨c, us⟩ := pr
                      obtain ⟨w1, w2, hr, h1, h2, h3, h4⟩ := hpo
                      subst hr
                      exact ⟨w1, w2, rfl, h1, h2, h3, h4⟩

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hp : p.lookup "ph_app" = some phApp)
include hv hp

/-- **`ph_app` refines `phApp?`**: the constant applied to exactly the placeholders. -/
@[refines ConRon.Arena.phApp?]
theorem phApp_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis b e n : Word) (N : Nat) (hN : n.toNat = N) (he : H e)
    (hb : b.toNat + N < 2 ^ 64) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "ph_app" [b, e, n]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      AM.ok (ConRon.Arena.phApp? b.toNat (decI e) N) a₀ ∧
      AM.st (ConRon.Arena.phApp? b.toNat (decI e) N) a₀ = a₀ ∧
      PhOut r (AM.res (ConRon.Arena.phApp? b.toNat (decI e) N) a₀); ⊤⦄ := by
  refine triple_post (phApp_spec p hv hp k s₀ b e n) ?_
  rintro r s' ⟨hl, hmem, hm⟩
  obtain ⟨o, hrun, hout⟩ := phW_ok k _ a₀ b e n N r hN hm hS.1.arena.1 he hb
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hmem, hok, hst, by rw [hres]; exact hout⟩

end census

end L.Ind

end
