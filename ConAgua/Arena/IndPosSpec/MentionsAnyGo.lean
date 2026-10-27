import ConAgua.Arena.IndPosSpec.NodeV
import ConAgua.Arena.IndPosSpec.SlRCongr
import ConAgua.Arena.IndPosSpec.SnocWDecK

/-!
# MentionsAnyGo: `ConRon.Arena.mentionsAnyGo`, `ConRon.Arena.nestCanonSub`

The refinement theorems `nestCanonSub_refines`, `mentionsAnyGo_refines` and the lemmas only they use.
-/

set_option linter.unusedSectionVars false

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (n : Nat) (m m1 m2 : Mem) (no nl us nn c v mi r s z : Word) (fr : List Word)
theorem canonK1_big (h : 4294967296 ≤ z) : canonK1 nn mi m (some z) = none := by simp [canonK1, h]
end arms
grind_pattern [ind_grind] canonK1_big => canonK1 nn mi m (some z)
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
        by_cases h1 : w0 = c <;> by_cases h2 : ws.contains w0 = true <;> simp [h1]
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
        rw [ConRon.Arena.nestFrameMates.go.eq_2, ite_eq_left (by rw [hcond]; simpa using hskip)]
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
        rw [ConRon.Arena.nestFrameMates.go.eq_2, ite_eq_right (by rw [hcond]; simpa using hskip)]
        simpa using hd

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (no nl f f1 h g x y z b1 b2 b3 r : Word) (v fr : List Word)
theorem maGoW_abort (hf : f = 0) : maGoW (n + 1) m no nl f h = none := by simp [maGoW, hf]
theorem maG3_abort (hr : fr = []) : maG3 n m no nl f h v fr = none := by simp [maG3, hr]
end arms

attribute [ind_grind] maGoW_abort maG3_abort

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
    simp only [hr1, except_ok_bind, hr2]
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
    simp only [hr1, except_ok_bind, hr2, hr3]
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
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, -, hy, hdy⟩ := hvr
    rw [hg] at hn
    have := maNodeFVar_ok k ih m m' a no nl f1 _ _ _ r ws mp hy hn hA hws hwlt hM
    rw [← hdy] at *
    simp only [maArm]; exact this
  | app f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := maNodeBin_ok k ih m m' a no nl f1 _ _ _ _ r ws mp (Or.inl hg) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [maArm]; exact this
  | lam f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := maNodeBin_ok k ih m m' a no nl f1 _ _ _ _ r ws mp (Or.inr (Or.inl hg)) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [maArm]; exact this
  | forallE f x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
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

end
