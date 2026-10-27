import ConAgua.Arena.IndPosSpec.DecNHFields
import ConAgua.Arena.IndPosSpec.DepthGo
import ConAgua.Arena.IndPosSpec.RootHoles
import ConAgua.Arena.IndPosSpec.Rx
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndGrindAttr

/-!
# MapOKStep

`erK2_big`, `rtK1_big`, `frK4_big`, `rxW_big`, `rxK1_big`, `rxGoW_abort` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (m m1 m2 : Mem) (ctx i s v hd : Word) (z : Word) (r : List Word)
theorem erK2_big (h : 4294967296 ≤ s) : erK2 i (some (s, m1)) = none := by simp [erK2, h]
theorem rtK1_big (h : 4294967296 ≤ hd) : rtK1 ctx (some (hd, m1)) = none := by simp [rtK1, h]
end arms
attribute [ind_grind] erK2_big rtK1_big

end L.Ind

namespace L.Ind

open L.Arena

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (f i ctx po pl nn n1 k h kp q l o j r s e fu f1 g x y z a2 x2 c2 v0 hd ok : Word)
  (v fr rr : List Word)
theorem frK4_big (hb : 4294967296 ≤ hd) : frK4 q l (some (hd, m4)) = none := by simp [frK4, hb]
theorem rxW_big (hb : 4294967296 ≤ rdW (m.arr64 CTL) 218 + 1) : rxW (n + 1) m f e = none := by
  simp [rxW, hb]
theorem rxK1_big (hb : 4294967296 ≤ r) : rxK1 s (some (r, m1)) = none := by simp [rxK1, hb]
theorem rxGoW_abort (hf : fu = 0) : rxGoW (n + 1) m f fu h = none := by simp [rxGoW, hf]
theorem rxG3_abort (hr : fr = []) : rxG3 n m f fu h v fr = none := by simp [rxG3, hr]
end arms
attribute [ind_grind] frK4_big rxW_big rxK1_big rxGoW_abort rxG3_abort

end L.Ind

/-! ## The relational side: the banked memo's invariant -/

namespace L.Ind

open L.Arena

theorem RfFr.refl (m : Mem) : RfFr m m := ⟨[], [], MemFrame.refl _ _ _, by simp, by simp, by simp, by simp⟩

theorem RfFr.trans {m₁ m₂ m₃ : Mem} (h₁ : RfFr m₁ m₂) (h₂ : RfFr m₂ m₃) : RfFr m₁ m₃ := by
  obtain ⟨A₁, C₁, f₁, a₁, c₁, d₁, e₁⟩ := h₁
  obtain ⟨A₂, C₂, f₂, a₂, c₂, d₂, e₂⟩ := h₂
  exact ⟨A₁ ++ A₂, C₁ ++ C₂, (f₁.mono (fun b hb => List.mem_append_left _ hb) (fun x hx => List.mem_append_left _ hx)).trans
    (f₂.mono (fun b hb => List.mem_append_right _ hb) (fun x hx => List.mem_append_right _ hx)),
    by simp [a₁, a₂], by simp [c₁, c₂], by simp [d₁, d₂], by simp [e₁, e₂]⟩

theorem RfFr.of_low {m m' : Mem} (h : LowFr m m') : RfFr m m' := by
  obtain ⟨A, C, hf, hA, hC⟩ := h
  exact ⟨A, C, hf, fun hh => by have := hA _ hh; simp [RFM] at this,
    fun hh => by have := hC _ hh; simp at this, fun hh => by have := hC _ hh; simp at this,
    fun hh => by have := hC _ hh; simp at this⟩

theorem RfFr.set_iw (m : Mem) (x v : Word) : RfFr m (m.set64 IW x v) := RfFr.of_iw (set64IW_frame m x v)

theorem RfFr.ofMknF {m m' : Mem} {args r : List Word} (h : mknF m args = some (r, m')) : RfFr m m' :=
  ⟨_, _, mknF_frame h, by simp [tier1, tierOff, RFM, SPN, AREC, ASLOT, ADER], by simp, by simp, by simp⟩

theorem GKeep.refl (M : Std.HashMap (EIdx × Word) EIdx) (G : Word) : GKeep M M G := fun _ _ _ => rfl

theorem GKeep.bank {M M' : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (h : GKeep M M' G) (hg : g ≤ G)
    {mp : Std.HashMap EIdx EIdx} (hb : Bank M g mp) : Bank M' g mp :=
  fun k => (hb k).trans (h k g hg).symm

end L.Ind

namespace L.Ind

open L.Arena

theorem posIwN_grow {m m' : Mem} (hg : IWGrow m m') {i : Nat} (hi : i < iwTop m) : iwN m' i = iwN m i :=
  iwN_agree (RdS.of_grow hg) hi

theorem FMOk.grow {m m' : Mem} {f : Nat} {fm : FvMap} (h : FMOk m f fm) (hg : IWGrow m m') : FMOk m' f fm := by
  have ht := hg.1
  cases fm with
  | holeImg ctx prog n =>
    obtain ⟨h0, hb, ⟨c, hc, hdc, hci⟩, ⟨po, pl, hpo, hpl, hs⟩, hn, hlt⟩ := h
    obtain ⟨e, hci'⟩ := hci.grow hg
    exact ⟨by rw [posIwN_grow hg (by omega)]; exact h0, by omega,
      ⟨c, by rw [posIwN_grow hg (by omega)]; exact hc, by rw [e]; exact hdc, hci'⟩,
      ⟨po, pl, by rw [posIwN_grow hg (by omega)]; exact hpo, by rw [posIwN_grow hg (by omega)]; exact hpl, hs.grow hg⟩,
      by rw [posIwN_grow hg (by omega)]; exact hn, hlt⟩
  | keyMap ds holes =>
    obtain ⟨h0, hb, ⟨o, l, ho, hl, hd, hol⟩, ⟨o2, l2, ho2, hl2, hd2, hol2⟩⟩ := h
    exact ⟨by rw [posIwN_grow hg (by omega)]; exact h0, by omega,
      ⟨o, l, by rw [posIwN_grow hg (by omega)]; exact ho, by rw [posIwN_grow hg (by omega)]; exact hl,
        by rw [decHL_grow hg hol]; exact hd, by omega⟩,
      ⟨o2, l2, by rw [posIwN_grow hg (by omega)]; exact ho2, by rw [posIwN_grow hg (by omega)]; exact hl2,
        by rw [decHL_grow hg hol2]; exact hd2, by omega⟩⟩
  | erase =>
    obtain ⟨h0, hb⟩ := h
    exact ⟨by rw [posIwN_grow hg (by omega)]; exact h0, by omega⟩
  | canon pfvs =>
    obtain ⟨h0, hb, ⟨o, l, ho, hl, hd, hol⟩⟩ := h
    exact ⟨by rw [posIwN_grow hg (by omega)]; exact h0, by omega,
      ⟨o, l, by rw [posIwN_grow hg (by omega)]; exact ho, by rw [posIwN_grow hg (by omega)]; exact hl,
        by rw [decHL_grow hg hol]; exact hd, by omega⟩⟩

/-! ### The twin's node step, with its arms named -/

def rfArm (f : FvMap) (memo : Std.HashMap EIdx EIdx) (fuel : Nat) (h : EIdx) :
    ENodeView → AM (EIdx × Std.HashMap EIdx EIdx)
  | .app a x => do
    let (a2, m) ← ConRon.Arena.replaceFVarsGo f memo fuel a
    let (x2, m2) ← ConRon.Arena.replaceFVarsGo f m fuel x
    let r ← internAppE a2 x2
    pure (r, m2)
  | .lam t body => do
    let (t2, m) ← ConRon.Arena.replaceFVarsGo f memo fuel t
    let (b2, m2) ← ConRon.Arena.replaceFVarsGo f m fuel body
    let r ← internLamE t2 b2
    pure (r, m2)
  | .forallE t body => do
    let (t2, m) ← ConRon.Arena.replaceFVarsGo f memo fuel t
    let (b2, m2) ← ConRon.Arena.replaceFVarsGo f m fuel body
    let r ← internForallEE t2 b2
    pure (r, m2)
  | .letE t val body => do
    let (t2, m) ← ConRon.Arena.replaceFVarsGo f memo fuel t
    let (v2, m2) ← ConRon.Arena.replaceFVarsGo f m fuel val
    let (b2, m3) ← ConRon.Arena.replaceFVarsGo f m2 fuel body
    let r ← internLetEE t2 v2 b2
    pure (r, m3)
  | .proj s i x => do
    let (x2, m) ← ConRon.Arena.replaceFVarsGo f memo fuel x
    let r ← internProjE s i x2
    pure (r, m)
  | _ => pure (h, memo)

theorem replaceFVarsGo_succ' (f : FvMap) (memo : Std.HashMap EIdx EIdx) (fuel : Nat) (h : EIdx) :
    ConRon.Arena.replaceFVarsGo f memo (fuel + 1) h = (do
      let v ← view h
      match v with
      | .bvar _ => pure (h, memo)
      | .sort _ => pure (h, memo)
      | .lit _ => pure (h, memo)
      | .const _ _ => pure (h, memo)
      | .fvar i _ =>
        match ← ConRon.Arena.fvMapAt f i with
        | some r => pure (r, memo)
        | none => pure (h, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← rfArm f memo fuel h v
          pure (r, m.insert h r)) := by
  rw [ConRon.Arena.replaceFVarsGo.eq_2]
  congr 1
  funext v
  cases v with
  | app a' x' => simp only [rfArm, bind_assoc, pure_bind]; rfl
  | lam t body => simp only [rfArm, bind_assoc, pure_bind]; rfl
  | forallE t body => simp only [rfArm, bind_assoc, pure_bind]; rfl
  | letE t v' body => simp only [rfArm, bind_assoc, pure_bind]; rfl
  | proj s i x => simp only [rfArm, bind_assoc, pure_bind]; rfl
  | bvar _ => rfl
  | sort _ => rfl
  | lit _ => rfl
  | fvar _ _ => rfl
  | const _ _ => rfl

end L.Ind

namespace L.Ind

open L.Arena

/-! ### The statements, by exec fuel -/

section stmts
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem nestHoleImg_succ (c : NestCtx) (prog : List NestHole) (n1 i : Nat) :
    ConRon.Arena.nestHoleImg c prog (n1 + 1) i =
      if (i == c.hiAt n1) = true then frameTwin c prog n1 else ConRon.Arena.nestHoleImg c prog n1 i := by
  rw [ConRon.Arena.nestHoleImg.eq_2]; rfl

end stmts

end L.Ind

namespace L.Ind

open L.Arena

/-! ### Word reads and small facts -/

theorem rdIW0 {m : Mem} {f : Word} {v : Nat} (h : iwN m f.toNat = some v) : (rdW (m.arr64 IW) f).toNat = v := by
  simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  simp [rdW, hw]

theorem rdIW {m : Mem} {f : Word} {i v : Nat} (h : iwN m (f.toNat + i) = some v) (hb : f.toNat + i < 2 ^ 64)
    (hi : i < 2 ^ 64) : (rdW (m.arr64 IW) (f + UInt64.ofNat i)).toNat = v :=
  rd_iwN (by rwa [UInt64.toNat_ofNat_of_lt' hi]) (by rwa [UInt64.toNat_ofNat_of_lt' hi])

/-- `nest_key_map` decodes `nestKeyMap`. -/
theorem kmW_ok {m : Mem} {dO dL hO hL i : Word} {ds holes : List EIdx}
    (hds : decHL m dO.toNat dL.toNat = some ds) (hho : decHL m hO.toNat hL.toNat = some holes)
    (h1 : dO.toNat + dL.toNat < 2 ^ 64) (h2 : hO.toNat + hL.toNat < 2 ^ 64) :
    OptE (kmW m dO dL hO hL i).1 (kmW m dO dL hO hL i).2 (ConRon.Arena.nestKeyMap ds holes i.toNat) := by
  have hdl : ds.length = dL.toNat := decHL_length m hds
  have hhl : holes.length = hL.toNat := decHL_length m hho
  unfold kmW ConRon.Arena.nestKeyMap
  by_cases hc1 : i < dL
  · have hc1' : i.toNat < dL.toNat := UInt64.lt_iff_toNat_lt.mp hc1
    obtain ⟨hH, hd⟩ := rd_iwH (p := dO) (i := i) (decHL_getI hds i.toNat hc1') (by omega)
    simp only [hc1, hc1', hdl, ite_true, List.getElem?_eq_getElem (show i.toNat < ds.length by omega)]
    exact ⟨by simp, hd⟩
  · have hc1' : ¬ i.toNat < dL.toNat := fun e => hc1 (UInt64.lt_iff_toNat_lt.mpr e)
    have hsub : (i - dL).toNat = i.toNat - dL.toNat :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
    simp only [hc1, hc1', hdl, ite_false]
    by_cases hc2 : i - dL < hL
    · have hc2' : i.toNat - dL.toNat < hL.toNat := by rw [← hsub]; exact UInt64.lt_iff_toNat_lt.mp hc2
      obtain ⟨hH, hd⟩ := rd_iwH (p := hO) (i := i - dL) (by rw [hsub]; exact decHL_getI hho _ hc2')
        (by rw [hsub]; omega)
      simp only [hc2, ite_true, List.getElem?_eq_getElem (show i.toNat - dL.toNat < holes.length by omega)]
      exact ⟨by simp, by rw [decE_eq, hd]⟩
    · have hc2' : ¬ i.toNat - dL.toNat < hL.toNat := fun e => hc2 (by
        rw [UInt64.lt_iff_toNat_lt, hsub]; exact e)
      simp only [hc2, ite_false, List.getElem?_eq_none (show holes.length ≤ i.toNat - dL.toNat by omega)]
      rfl

theorem RfInv.post {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m' : Mem} {a' : AState}
    {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (hR : RfInv m M G g) (hS : StageR dn vis fe m' a')
    (hg : IWGrow m m') (hf : RfFr m m') : RxPost dn fe vis m m' a' M G g :=
  ⟨M, G, hS, hg, hR.frame hf, GKeep.refl _ _, UInt64.le_refl _⟩

section steps
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem mapOK_step (n : Nat) (hImg : ImgOK dn fe vis n) : MapOK dn fe vis (n + 1) := by
  intro m m' a f i fm r0 r1 M G g h hS hfm hR
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  cases fm with
  | holeImg ctx prog nn =>
    obtain ⟨h0, hb, ⟨c, hc, hdc, hci⟩, ⟨po, pl, hpo, hpl, hs⟩, hn, hlt⟩ := hfm
    have e0 : rdW (m.arr64 IW) f = 0 := UInt64.toNat_inj.mp (by rw [rdIW0 h0]; rfl)
    rw [rxMapW_img n m f i e0] at h
    have rc := rdIW (i := 1) (by simpa using hc) (by omega) (by decide)
    have rpo := rdIW (i := 2) (by simpa using hpo) (by omega) (by decide)
    have rpl := rdIW (i := 3) (by simpa using hpl) (by omega) (by decide)
    have rn := rdIW (i := 4) (by simpa using hn) (by omega) (by decide)
    simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
      show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at rc rpo rpl rn
    obtain ⟨x, a', hrun, hout, hpost⟩ := hImg m m' a _ _ _ _ i ctx prog r0 r1 M G g h hS
      (by rw [rc]; exact hdc) (by rw [rc]; exact hci) (by rw [rpo, rpl]; exact hs) (by rw [rn]; exact hlt) hR
    refine ⟨x, a', ?_, hout, hpost⟩
    rw [ConRon.Arena.fvMapAt.eq_1, ← rn]; exact hrun
  | keyMap ds holes =>
    obtain ⟨h0, hb, ⟨o, l, ho, hl, hd, hol⟩, ⟨o2, l2, ho2, hl2, hd2, hol2⟩⟩ := hfm
    have e1 : rdW (m.arr64 IW) f = 1 := UInt64.toNat_inj.mp (by rw [rdIW0 h0]; rfl)
    simp only [rxMapW_km n m f i e1, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have r1 := rdIW (i := 1) (by simpa using ho) (by omega) (by decide)
    have r2 := rdIW (i := 2) (by simpa using hl) (by omega) (by decide)
    have r3 := rdIW (i := 3) (by simpa using ho2) (by omega) (by decide)
    have r4 := rdIW (i := 4) (by simpa using hl2) (by omega) (by decide)
    simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
      show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at r1 r2 r3 r4
    refine ⟨_, a, ?_, kmW_ok (by rw [r1, r2]; exact hd) (by rw [r3, r4]; exact hd2) (by omega) (by omega),
      hR.post hS (IWGrow.refl _) (RfFr.refl _)⟩
    rw [ConRon.Arena.fvMapAt.eq_def]; rfl
  | erase =>
    obtain ⟨h0, hb⟩ := hfm
    have e2 : rdW (m.arr64 IW) f = 2 := UInt64.toNat_inj.mp (by rw [rdIW0 h0]; rfl)
    rw [rxMapW_er n m f i e2] at h
    rcases hpw : pinWordV m 53 with _ | z <;> rw [hpw] at h; · simp [erK1] at h
    rw [erK1_some] at h
    obtain ⟨hzl, hzH⟩ := pinZero_stage hS hpw
    rcases hso : sointernW m z with _ | ⟨s, m1⟩ <;> rw [hso] at h; · simp [erK2] at h
    by_cases hsb : 4294967296 ≤ s
    · rw [erK2_big (h := hsb)] at h; simp at h
    rw [erK2_ok (h := hsb)] at h
    obtain ⟨a1, hr1, hS1, hg1⟩ := internSort_stage hS z hzH hso
    rcases hfv : fvinternW m1 i s with _ | ⟨v, m2⟩ <;> rw [hfv] at h; · simp [erK3] at h
    simp only [erK3_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨a2, hr2, hS2, hg2⟩ := internFVar_stage hS1 i s (lt_of_notbig hsb) hfv
    refine ⟨some (decE v), a2, ?_, ⟨by simp, rfl⟩,
      hR.post hS2 (hg1.trans hg2) (RfFr.of_low ((sointernW_low hso).trans (fvinternW_low hfv)))⟩
    simp only [ConRon.Arena.fvMapAt.eq_def, StateT.run_bind, hzl, except_ok_bind, ConRon.Arena.internSortE, ConRon.Arena.internFVarE, hr1, hr2]
    rfl
  | canon pfvs =>
    obtain ⟨h0, hb, ⟨o, l, ho, hl, hd, hol⟩⟩ := hfm
    have hn0 : ¬ rdW (m.arr64 IW) f = 0 := fun e => by have := rdIW0 h0; rw [e] at this; simp at this
    have hn1 : ¬ rdW (m.arr64 IW) f = 1 := fun e => by have := rdIW0 h0; rw [e] at this; simp at this
    have hn2 : ¬ rdW (m.arr64 IW) f = 2 := fun e => by have := rdIW0 h0; rw [e] at this; simp at this
    have r1 := rdIW (i := 1) (by simpa using ho) (by omega) (by decide)
    have r2 := rdIW (i := 2) (by simpa using hl) (by omega) (by decide)
    simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl] at r1 r2
    have hpl := decHL_length m hd
    by_cases hi : i < rdW (m.arr64 IW) (f + 2)
    · rw [rxMapW_cin n m f i hn0 hn1 hn2 hi] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hi' : i.toNat < l := by rw [← r2]; exact UInt64.lt_iff_toNat_lt.mp hi
      obtain ⟨hH, hdd⟩ := rd_iwH (p := rdW (m.arr64 IW) (f + 1)) (i := i) (by rw [r1]; exact decHL_getI hd _ hi')
        (by rw [r1]; omega)
      refine ⟨pfvs[i.toNat]?, a, ?_, ?_, hR.post hS (IWGrow.refl _) (RfFr.refl _)⟩
      · rw [ConRon.Arena.fvMapAt.eq_def]; rfl
      · rw [List.getElem?_eq_getElem (by omega)]; exact ⟨by simp, hdd⟩
    · rw [rxMapW_cout n m f i hn0 hn1 hn2 hi] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hi' : ¬ i.toNat < l := fun e => hi (by rw [UInt64.lt_iff_toNat_lt, r2]; exact e)
      refine ⟨pfvs[i.toNat]?, a, ?_, ?_, hR.post hS (IWGrow.refl _) (RfFr.refl _)⟩
      · rw [ConRon.Arena.fvMapAt.eq_def]; rfl
      · rw [List.getElem?_eq_none (by omega)]; rfl

theorem rootOK (m m' : Mem) (a : AState) (ctx i : Word) (c : NestCtx) (prog : List NestHole) (r0 r1 : Word)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word) (h : rxRootW m ctx i = some (r0, r1, m'))
    (hS : StageR dn vis fe m a) (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m))
    (hb : c.nP + c.names.length < 2 ^ 64) (hR : RfInv m M G g) :
    ∃ x a', (ConRon.Arena.nestHoleImg c prog 0 i.toNat).run a = .ok (x, a') ∧ OptE r0 r1 x ∧
      RxPost dn fe vis m m' a' M G g := by
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hn, hn', hpa, hpa', hnP, hlvH, hlv, -, -, h11⟩ := ctx_fields hc hin htop
  have hlen := decHL_length m hn
  have hhi : (hiW m ctx 0).toNat = c.nP + c.names.length := by
    simp only [hiW]
    rw [word_add_toNat (by rw [word_add_toNat (by omega)]; simp; omega), word_add_toNat (by omega), hnP, hlen]
    simp
  rw [ConRon.Arena.nestHoleImg.eq_1]
  by_cases hin2 : rdW (m.arr64 IW) (ctx + 4) ≤ i ∧ i < hiW m ctx 0
  · have h1 : c.nP ≤ i.toNat := by rw [← hnP]; exact UInt64.le_iff_toNat_le.mp hin2.1
    have h2 : i.toNat < c.nP + c.names.length := by rw [← hhi]; exact UInt64.lt_iff_toNat_lt.mp hin2.2
    rw [ite_eq_left (by simp only [Bool.and_eq_true, decide_eq_true_eq, ConRon.Arena.NestCtx.hiAt, Nat.add_zero]; exact ⟨h1, decide_eq_true h2⟩)]
    rw [rxRootW_in m ctx i hin2] at h
    have hsub : (i - rdW (m.arr64 IW) (ctx + 4)).toNat = i.toNat - c.nP := by
      rw [UInt64.toNat_sub_of_le _ _ hin2.1, hnP]
    have hgd : getDW m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (i - rdW (m.arr64 IW) (ctx + 4)) 0 =
        rdW (m.arr64 IW) (rdW (m.arr64 IW) ctx + (i - rdW (m.arr64 IW) (ctx + 4))) := by
      simp only [getDW]; rw [ite_eq_right (fun e => by have := UInt64.le_iff_toNat_le.mp e; omega)]
    rw [hgd] at h
    obtain ⟨hnmH, hnmd⟩ := rd_iwH (p := rdW (m.arr64 IW) ctx) (i := i - rdW (m.arr64 IW) (ctx + 4))
      (by rw [hsub]; exact decHL_getI hn _ (by omega)) (by rw [hsub]; have := hn' (i.toNat - c.nP) (by omega); omega)
    generalize rdW (m.arr64 IW) (rdW (m.arr64 IW) ctx + (i - rdW (m.arr64 IW) (ctx + 4))) = nm at h hnmH hnmd
    rcases hci : ceinternW m nm (rdW (m.arr64 IW) (ctx + 10)) with _ | ⟨hd, m1⟩ <;> rw [hci] at h; · simp [rtK1] at h
    by_cases hdb : 4294967296 ≤ hd
    · rw [rtK1_big (h := hdb)] at h; simp at h
    rw [rtK1_ok (h := hdb)] at h
    obtain ⟨a1, hr1, hS1, hg1⟩ := internConst_stage hS nm _ hnmH hlvH hci
    have hiw : m1.arr64 IW = m.arr64 IW := lowFr_iw (ceinternW_low hci)
    rw [hiw] at h
    rcases hst : mknF m1 [hd, rdW (m.arr64 IW) (ctx + 7), rdW (m.arr64 IW) (ctx + 8)] with _ | ⟨rr, m2⟩ <;> rw [hst] at h; · simp [rtK2] at h
    simp only [rtK2_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨x, a2, hr2, hS2, hg2, hx1, hx2⟩ := mknF_ok dn vis fe hd _ _ (lt_of_notbig hdb) c.params m1 m2 a1 rr hst
      ⟨hS1, by simp only [decHL, iwA, hiw]; exact hpa⟩
    refine ⟨some x, a2, ?_, ⟨by simp, by rw [← hx2]; rfl⟩,
      hR.post hS2 (hg1.trans hg2) ((RfFr.of_low (ceinternW_low hci)).trans (RfFr.ofMknF hst))⟩
    have hnm' : c.names.getD (i.toNat - c.nP) default = decI nm := by
      rw [hnmd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    simp only [hnm', ConRon.Arena.internConstE, StateT.run_bind, ← hlv, hr1, except_ok_bind, show (decE hd : EIdx) = decI hd from rfl, hr2]
    rfl
  · rw [rxRootW_out m ctx i hin2] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have : ¬ (c.nP ≤ i.toNat ∧ i.toNat < c.nP + c.names.length) := fun ⟨e1, e2⟩ => hin2
      ⟨UInt64.le_iff_toNat_le.mpr (by rw [hnP]; exact e1), UInt64.lt_iff_toNat_lt.mpr (by rw [hhi]; exact e2)⟩
    rw [ite_eq_right (by simp only [Bool.and_eq_true, decide_eq_true_eq, ConRon.Arena.NestCtx.hiAt, Nat.add_zero]; exact fun ⟨e1, e2⟩ => this ⟨e1, of_decide_eq_true e2⟩)]
    exact ⟨none, a, rfl, rfl, hR.post hS (IWGrow.refl _) (RfFr.refl _)⟩

theorem imgOK_step (n : Nat) (hImg : ImgOK dn fe vis n) (hFr : FrOK dn fe vis n) : ImgOK dn fe vis (n + 1) := by
  intro m m' a ctx po pl nn i c prog r0 r1 M G g h hS hc hin hs hb hR
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hn, -, -, -, hnP, -, -, -, -, h11⟩ := ctx_fields hc hin htop
  have hlen := decHL_length m hn
  by_cases h0 : nn = 0
  · rw [rxImgW_root (h0 := h0)] at h
    subst h0
    exact rootOK dn fe vis m m' a ctx i c prog r0 r1 M G g h hS hc hin (by simpa using hb) hR
  have hnn : nn.toNat ≠ 0 := toNat_ne_zero' h0
  have hn1 : (nn - 1).toNat = nn.toNat - 1 := toNat_sub_one' h0
  have hhi : (hiW m ctx (nn - 1)).toNat = c.hiAt (nn.toNat - 1) := by
    simp only [hiW, ConRon.Arena.NestCtx.hiAt]
    rw [word_add_toNat (by rw [word_add_toNat (by omega)]; omega), word_add_toNat (by omega), hnP, hlen, hn1]
  obtain ⟨n1, hn1'⟩ : ∃ n1, nn.toNat = n1 + 1 := ⟨nn.toNat - 1, by omega⟩
  rw [hn1', nestHoleImg_succ]
  by_cases hh : i = hiW m ctx (nn - 1)
  · rw [rxImgW_frame (h0 := h0) (hh := hh)] at h
    have : (i.toNat == c.hiAt n1) = true := by
      rw [hh, hhi, hn1']; simp
    rw [ite_eq_left this]
    have := hFr m m' a ctx po pl (nn - 1) i c prog r0 r1 M G g h hS hc hin hs (by rw [hn1]; omega) hR
    rwa [hn1, hn1'] at this
  · rw [rxImgW_next (h0 := h0) (hh := hh)] at h
    have : ¬ (i.toNat == c.hiAt n1) = true := by
      intro e; apply hh; apply UInt64.toNat_inj.mp; rw [hhi, hn1', Nat.add_sub_cancel]; simp at e; exact e
    rw [ite_eq_right this]
    have := hImg m m' a ctx po pl (nn - 1) i c prog r0 r1 M G g h hS hc hin hs (by rw [hn1]; omega) hR
    rwa [hn1, hn1'] at this

end steps

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem decNK_fields {m : Mem} {k : Nat} {key : NestKey} (h : decNK m k = some key) :
    iwH m k = some key.cname ∧ iwH m (k + 1) = some key.lvls ∧ decAt m (decHL m) (k + 2) = some key.ds := by
  simp only [decNK, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, l, hl, ds, hds, h'⟩ := h
  obtain rfl := Option.some.inj h'
  exact ⟨hc, hl, hds⟩

theorem RxPost.of_fr {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m1 m2 : Mem}
    {a2 : AState} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (_hR : RfInv m M G g)
    (_hf : RfFr m m1) (hg : IWGrow m m1) (h : RxPost dn fe vis m1 m2 a2 M G g) : RxPost dn fe vis m m2 a2 M G g := by
  obtain ⟨M2, G2, hS2, hg2, hR2, hk2, hG2⟩ := h
  exact ⟨M2, G2, hS2, hg.trans hg2, hR2, hk2, hG2⟩

theorem RxPost.then {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m1 m2 : Mem}
    {a1 a2 : AState} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (h : RxPost dn fe vis m m1 a1 M G g)
    (hS : StageR dn vis fe m2 a2) (hg : IWGrow m1 m2) (hf : RfFr m1 m2) : RxPost dn fe vis m m2 a2 M G g := by
  obtain ⟨M1, G1, -, hg1, hR1, hk1, hG1⟩ := h
  exact ⟨M1, G1, hS, hg1.trans hg, hR1.frame hf, hk1, hG1⟩

/-! ### Entering and leaving a bank -/

theorem rfEnter {m : Mem} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (hR : RfInv m M G g)
    (hG : (G + 1).toNat < 2 ^ 32) :
    RfInv (benterG 218 m) M (G + 1) (G + 1) ∧ Bank M (G + 1) ∅ ∧ G.toNat < 2 ^ 32 ∧ g ≤ G := by
  obtain ⟨hMR, hB, hF⟩ := hR
  have hG1 : (G + 1).toNat = G.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl]; have := hB.2.2.2.1; omega
  -- `bank_enter` wants the caller's bank only for its last conjunct
  refine ⟨⟨?_, ?_, fresh_mono M G hF hG1⟩, bank_fresh M G hF hG1, hB.2.2.2.1, hB.2.2.1⟩
  · exact memoRV_frame rfSch rfSch_wf rfK rfV [] [218, 218 + 1] (by simp) (by simp [rfSch]) m _
      (benterG_frame 218 m) (fun _ _ h => h) M hMR
  · obtain ⟨hB1, hB2, hgG, hGl, hsz⟩ := hB
    have hf := benterG_frame 218 m
    have hne : (218 : Word) ≠ 218 + 1 := by decide
    refine ⟨?_, ?_, UInt64.le_refl _, hG, by rw [hf.2.2.1]; exact hsz⟩
    · have h218 : (218 : Word).toNat = 218 := rfl
      simp only [benterG, rdW_set64, size_set64, hB1]
      simp; omega
    · have h218 : (218 : Word).toNat = 218 := rfl
      simp only [benterG, rdW_set64, size_set64, hB1]
      simp; intro; omega

theorem rfLeave {m : Mem} {M : Std.HashMap (EIdx × Word) EIdx} {G g' g : Word} (hR : RfInv m M G g')
    (hg : g ≤ G) : RfInv (m.set64 CTL 219 g) M G g := by
  obtain ⟨hMR, ⟨hB1, hB2, hgG, hGl, hsz⟩, hF⟩ := hR
  have hf := MemFrame.setCtl m 219 g
  have h218 : (218 : Word).toNat = 218 := rfl
  refine ⟨memoRV_frame rfSch rfSch_wf rfK rfV [] [219] (by simp) (by simp [rfSch]) m _ hf (fun _ _ h => h) M hMR,
    ⟨by rw [hf.2.1 218 (by simp)]; exact hB1, ?_, hg, hGl, by rw [hf.2.2.1]; exact hsz⟩, hF⟩
  rw [show (218 : Word) + 1 = 219 from rfl, rdW_set64]
  have : (219 : Word).toNat < (m.arr64 CTL).size := by
    rw [show (219 : Word).toNat = 219 from rfl]; omega
  simp; intro; simp at this; omega

theorem uint_le_succ {G : Word} (h : G.toNat < 2 ^ 32) : G ≤ G + 1 := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl]; omega

section steps
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- **A frame's hole read back, from its hole record on**. -/
theorem frameTail (n : Nat) (hDs : DsOK dn fe vis n) (mh m' : Mem) (a : AState) (ctx po pl n1 h : Word)
    (c : NestCtx) (prog : List NestHole) (H0 : NestHole) (r0 r1 : Word)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word)
    (hk : pfrK2 n (rdW (mh.arr64 IW) h) (posRecW mh [0, ctx, po, pl, n1]) = some (r0, r1, m'))
    (hS : StageR dn vis fe mh a) (hc : decCtx mh ctx.toNat = some c) (hin : CtxIn mh ctx.toNat (· < iwTop mh))
    (hs : HSl mh po.toNat pl.toNat prog) (hb : c.nP + c.names.length + n1.toNat + 1 < 2 ^ 64)
    (hh : decNH mh h.toNat = some H0) (hhin : NHIn mh h.toNat (· < iwTop mh)) (hR : RfInv mh M G g) :
    ∃ x a', (do
        let ds ← H0.key.ds.mapM fun x => ConRon.Arena.replaceFVars (.holeImg c prog n1.toNat) x
        let hd ← internConstE H0.key.cname H0.key.lvls
        let r ← mkAppN hd ds
        pure (some r) : AM (Option EIdx)).run a = .ok (x, a') ∧ OptE r0 r1 x ∧
      RxPost dn fe vis mh m' a' M G g := by
  have htop : iwTop mh < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨k, hk0, hkey⟩ := decNH_fields hh
  have hrk : (rdW (mh.arr64 IW) h).toNat = k := rdIW0 hk0
  have hNK := hhin.2.2 k hk0
  rcases hrec : posRecW mh [0, ctx, po, pl, n1] with _ | ⟨f, m2⟩ <;> rw [hrec] at hk; · simp [pfrK2] at hk
  rw [pfrK2_some] at hk
  obtain ⟨hS2, hg2, hf2, ht2, hget2⟩ := posRecW_stage hrec hS (by simp)
  simp only [List.length_cons, List.length_nil] at ht2
  have hR2 := hR.frame (posRecW_fr hrec)
  -- the new map record
  have g0 := iwN_of_get (by simpa using hget2 0 (by simp))
  have g1 := iwN_of_get (by simpa using hget2 1 (by simp))
  have g2 := iwN_of_get (by simpa using hget2 2 (by simp))
  have g3 := iwN_of_get (by simpa using hget2 3 (by simp))
  have g4 := iwN_of_get (by simpa using hget2 4 (by simp))
  obtain ⟨ec, hci2⟩ := hin.grow hg2
  have hfm : FMOk m2 f.toNat (.holeImg c prog n1.toNat) :=
    ⟨by simpa using g0, by omega, ⟨ctx.toNat, g1, by rw [ec]; exact hc, hci2⟩,
      ⟨po.toNat, pl.toNat, g2, g3, hs.grow hg2⟩, g4, by omega⟩
  -- the key, in `m2`
  obtain ⟨ekey, hNK2⟩ := hNK.agree (RdS.of_grow hg2)
  rw [hkey] at ekey
  obtain ⟨hcn, hlv, hds⟩ := decNK_fields ekey
  obtain ⟨o, l, ho, hl, hdsl⟩ := decAt_some hds
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have hkb : k + 4 ≤ iwTop m2 := by have := hNK2.1 3 (by omega); have := hg2.1; omega
  have ro := rdIW (m := m2) (f := rdW (mh.arr64 IW) h) (i := 2) (by rw [hrk]; exact ho) (by omega) (by decide)
  have rl := rdIW (m := m2) (f := rdW (mh.arr64 IW) h) (i := 3) (by rw [hrk]; simpa using hl) (by omega) (by decide)
  simp only [show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl] at ro rl
  have hsl : ∀ j < l, o + j < iwTop m2 := fun j hj =>
    Nat.lt_of_lt_of_le (hNK2.2 o l ho (by simpa using hl) j hj) hg2.1
  rcases hdsr : rxDsW n m2 f (rdW (m2.arr64 IW) (rdW (mh.arr64 IW) h + 2)) (rdW (m2.arr64 IW) (rdW (mh.arr64 IW) h + 3)) with _ | ⟨q, l3, m3⟩ <;> rw [hdsr] at hk; · simp [pfrK3] at hk
  rw [pfrK3_some] at hk
  obtain ⟨ys, a3, hrun3, hdec3, hq3, hpost3⟩ := hDs m2 m3 a f _ _ q l3 _ H0.key.ds M G g hdsr hS2 hfm
    (by rw [ro, rl]; exact hdsl) (by rw [ro, rl]; exact hsl) hR2
  obtain ⟨M3, G3, hS3, hg3, hR3, hk3, hG3⟩ := hpost3
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  have := hg3.1
  -- the container's head, in `m3`
  have hg23 := hg3
  obtain ⟨hcnH, hcnd⟩ := rd_iwH (m := m3) (p := rdW (mh.arr64 IW) h) (i := 0)
    (by rw [hrk]; simp only [UInt64.toNat_zero, Nat.add_zero]; rw [iwH_agree (RdS.of_grow hg3) (by omega)]; exact hcn)
    (by simp; omega)
  obtain ⟨hlvH, hlvd⟩ := rd_iwH (m := m3) (p := rdW (mh.arr64 IW) h) (i := 1)
    (by rw [hrk]; rw [iwH_agree (RdS.of_grow hg3) (by simp; omega)]; simpa using hlv) (by simp; omega)
  simp only [UInt64.add_zero] at hcnH hcnd hlvH hlvd
  rcases hci : ceinternW m3 (rdW (m3.arr64 IW) (rdW (mh.arr64 IW) h)) (rdW (m3.arr64 IW) (rdW (mh.arr64 IW) h + 1)) with _ | ⟨hd, m4⟩ <;> rw [hci] at hk; · simp [frK4] at hk
  by_cases hdb : 4294967296 ≤ hd
  · rw [frK4_big (hb := hdb)] at hk; simp at hk
  rw [frK4_ok (hb := hdb)] at hk
  obtain ⟨a4, hr4, hS4, hg4⟩ := internConst_stage hS3 _ _ hcnH hlvH hci
  have hiw4 : m4.arr64 IW = m3.arr64 IW := lowFr_iw (ceinternW_low hci)
  rcases hst : mknF m4 [hd, q, l3] with _ | ⟨rr, m5⟩ <;> rw [hst] at hk; · simp [frK5] at hk
  simp only [frK5_some, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl, rfl⟩ := hk
  obtain ⟨x, a5, hr5, hS5, hg5, hx1, hx2⟩ := mknF_ok dn vis fe hd q l3 (lt_of_notbig hdb) ys m4 m5 a4 rr hst
    ⟨hS4, by simp only [decHL, iwA, hiw4]; exact hdec3⟩
  refine ⟨some x, a5, ?_, ⟨by simp, by rw [← hx2]; rfl⟩, ?_⟩
  · simp only [StateT.run_bind]
    simp only [hrun3, except_ok_bind, ConRon.Arena.internConstE, ← hcnd, ← hlvd, hr4, show (decE hd : EIdx) = decI hd from rfl, hr5]
    rfl
  · exact ⟨M3, G3, hS5, ((hg2.trans hg3).trans hg4).trans hg5,
      (hR3.frame (RfFr.of_low (ceinternW_low hci))).frame (RfFr.ofMknF hst), hk3, hG3⟩

theorem default_hole : (default : NestHole) = ⟨⟨decI 0, decI 0, []⟩, 0⟩ := rfl

theorem frOK_step (n : Nat) (hDs : DsOK dn fe vis n) : FrOK dn fe vis (n + 1) := by
  intro m m' a ctx po pl n1 i c prog r0 r1 M G g h hS hc hin hs hb hR
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hpl, hpb, hH⟩ := hs
  unfold frameTwin
  by_cases hn : n1 < pl
  · rw [rxFrameW_in (hn := hn), pfrK1_some] at h
    have hn' : n1.toNat < pl.toNat := UInt64.lt_iff_toNat_lt.mp hn
    obtain ⟨w, hw, hd, hni⟩ := hH n1.toNat hn'
    have hrw : rdW (m.arr64 IW) (po + n1) = w := by
      simp [rdW, word_add_toNat (show po.toNat + n1.toNat < 2 ^ 64 by omega), hw]
    rw [hrw] at h
    rw [List.getElem?_eq_getElem (by omega)] at hd
    have hgd : prog.getD n1.toNat default = prog[n1.toNat]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    simp only [hgd]
    exact frameTail dn fe vis n hDs m m' a ctx po pl n1 w c prog _ r0 r1 M G g h hS hc hin ⟨hpl, hpb, hH⟩ hb hd
      hni hR
  · rw [rxFrameW_def (hn := hn)] at h
    have hn' : ¬ n1.toNat < pl.toNat := fun e => hn (UInt64.lt_iff_toNat_lt.mpr e)
    have hgd : prog.getD n1.toNat default = default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    simp only [hgd]
    rcases hr1 : posRecW m [0, 0, 0, 0] with _ | ⟨k, m1⟩ <;> rw [hr1] at h; · simp [frK0] at h
    rw [frK0_some] at h
    obtain ⟨hS1, hg1, hk1, ht1, hget1⟩ := posRecW_stage hr1 hS (by simp)
    rcases hr2 : posRecW m1 [k, 0] with _ | ⟨hh, m2⟩ <;> rw [hr2] at h; · simp [pfrK1] at h
    rw [pfrK1_some] at h
    obtain ⟨hS2, hg2, hk2, ht2, hget2⟩ := posRecW_stage hr2 hS1 (by simp)
    simp only [List.length_cons, List.length_nil] at ht1 ht2
    have hkw : ∀ j < 4, (m2.arr64 IW)[k.toNat + j]? = some 0 := fun j hj => by
      rw [hg2.2.2.1 _ (by omega), hget1 j (by simpa using hj)]
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
    have hdk : decNK m2 k.toNat = some ⟨decI 0, decI 0, []⟩ := by
      have := decNK_of_words (m := m2) (k := k.toNat) (c := 0) (u := 0) (o := 0) (l := 0) (ds := [])
        (by simpa using hkw 0 (by decide)) (by decide) (hkw 1 (by decide)) (by decide) (hkw 2 (by decide))
        (hkw 3 (by decide)) (by simp [decHL, hslice?])
      exact this
    have hdh : decNH m2 hh.toNat = some default := by
      rw [default_hole]
      exact decNH_of_words (by simpa using hget2 0 (by simp)) (hget2 1 (by simp)) hdk
    have hin2 : NHIn m2 hh.toNat (· < iwTop m2) := by
      refine ⟨by omega, by omega, fun k' hk' => ?_⟩
      have : k' = k.toNat := by
        have h0 := iwN_of_get (m := m2) (by simpa using hget2 0 (by simp)); rw [h0] at hk'; exact (Option.some.inj hk').symm
      subst this
      refine ⟨fun j hj => by omega, fun o l ho hl j hj => ?_⟩
      have : l = 0 := by
        have := iwN_of_get (m := m2) (hkw 3 (by decide)); rw [this] at hl; exact (Option.some.inj hl).symm
      omega
    have hg12 := hg1.trans hg2
    obtain ⟨ec, hci2⟩ := hin.grow hg12
    obtain ⟨x, a', hrun, hout, hpost⟩ := frameTail dn fe vis n hDs m2 m' a ctx po pl n1 hh c prog default r0 r1 M G g h
      hS2 (by rw [ec]; exact hc) hci2 (HSl.grow ⟨hpl, hpb, hH⟩ hg12) hb hdh hin2
      ((hR.frame (posRecW_fr hr1)).frame (posRecW_fr hr2))
    exact ⟨x, a', hrun, hout, RxPost.of_fr hR ((posRecW_fr hr1).trans (posRecW_fr hr2)) hg12 hpost⟩

theorem dsOK_step (n : Nat) (hDg : DsGoOK dn fe vis n) : DsOK dn fe vis (n + 1) := by
  intro m m' a f o l q l' fm xs M G g h hS hfm hxs hsl hR
  rw [rxDsW_succ] at h
  rcases hal : allocW m l with _ | ⟨q1, m1⟩ <;> rw [hal] at h; · simp [dsA] at h
  rw [dsA_some] at h
  obtain ⟨hS1, hg1, hqd, hroom, htop1⟩ := hS.alloc hal
  have hqt : q1.toNat = iwTop m := by simp only [iwTop, hqd]
  rcases hgo : rxDsGoW n m1 f o l q1 0 with _ | m2 <;> rw [hgo] at h; · simp [dsB] at h
  simp only [dsB_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨ys, a', hrun, hdec, hS', hg', ht', M', G', hR', hk', hG'⟩ := hDg m m1 m2 a f o l q1 0 fm xs [] M G g hgo hS1
    hg1 (by omega) (by omega) hfm hxs hsl (by simp) (by simp [decHL, hslice?]) (hR.frame (allocW_fr hal))
  refine ⟨ys, a', by simpa using hrun, by simpa using hdec, by omega, M', G', hS', hg', hR', hk', hG'⟩

theorem dsGoOK_step (n : Nat) (hRf : RfOK dn fe vis n) (hDg : DsGoOK dn fe vis n) :
    DsGoOK dn fe vis (n + 1) := by
  intro m0 m m' a f o l q j fm xs acc M G g h hS hg0 hq0 hql hfm hxs hsl hj hacc hR
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hxl := decHL_length m0 hxs
  have hal := decHL_length m hacc
  by_cases hd : l ≤ j
  · rw [rxDsGoW_done (hj := hd)] at h
    cases h
    have hjl : j.toNat = l.toNat := by have := UInt64.le_iff_toNat_le.mp hd; omega
    refine ⟨[], a, ?_, by rw [← hjl]; simpa using hacc, hS, hg0, Nat.le_refl _, M, G, hR, GKeep.refl _ _,
      UInt64.le_refl _⟩
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  rw [rxDsGoW_step (hj := hd)] at h
  have hjl : j.toNat < l.toNat := by
    have : ¬ l.toNat ≤ j.toNat := fun e => hd (UInt64.le_iff_toNat_le.mpr e)
    omega
  have hoj := hsl j.toNat hjl
  obtain ⟨hxH, hxd⟩ := rd_iwH (m := m) (p := o) (i := j)
    (by rw [iwH_agree (RdS.of_grow hg0) hoj]; exact decHL_getI hxs _ hjl) (by omega)
  generalize rdW (m.arr64 IW) (o + j) = x at h hxH hxd
  rcases hrf : rxW n m f x with _ | ⟨r, m1⟩ <;> rw [hrf] at h; · simp [dgK] at h
  rw [dgK_some] at h
  obtain ⟨a1, hr1, hrH, M1, G1, hS1, hg1, hR1, hk1, hG1⟩ := hRf m m1 a f x fm r M G g hrf hS (hfm.grow hg0) hxH hR
  have hqj : (q + j).toNat = q.toNat + j.toNat := word_add_toNat (by omega)
  have hj1 : (j + 1).toNat = j.toNat + 1 := word_add_toNat (show j.toNat + 1 < 2 ^ 64 by have := l.toNat_lt; omega)
  have hacc1 : decHL m1 q.toNat j.toNat = some acc := by rw [decHL_grow hg1 (by omega)]; exact hacc
  have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := hS1.2.2.2.1
  have hdec2 := decHL_write m1 q j r acc hrH hsz1 (by have := hS1.2.1; have := hg1.1; omega) hacc1
  have hS2 := hS1.set_iw (q + j) r
  have hg02 : IWGrow m0 (m1.set64 IW (q + j) r) := (hg0.trans hg1).set_iw (q + j) r (by omega)
  have ht2 : iwTop (m1.set64 IW (q + j) r) = iwTop m1 := by
    simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  obtain ⟨ys, a', hrun, hdec', hS', hg', ht', M', G', hR', hk', hG'⟩ := hDg m0 _ m' a1 f o l q (j + 1) fm xs
    (acc ++ [decE r]) M1 G1 g h hS2 hg02 hq0 (by rw [ht2]; have := hg1.1; omega) hfm hxs hsl
    (by rw [hj1]; omega) (by rw [hj1]; exact hdec2) (hR1.frame (RfFr.set_iw _ _ _))
  refine ⟨decE r :: ys, a', ?_, by simpa using hdec', hS', hg', by have := hg1.1; omega, M', G', hR',
    hk1.trans hk' hG1, UInt64.le_trans hG1 hG'⟩
  simp only [List.drop_eq_getElem_cons (show j.toNat < xs.length by omega), List.mapM_cons, StateT.run_bind, ← hxd, show (decI x : EIdx) = decE x from rfl, hr1, except_ok_bind]
  rw [hj1] at hrun
  rw [hrun]
  rfl

theorem rfOK_step (n : Nat) (hGo : GoOK dn fe vis n) : RfOK dn fe vis (n + 1) := by
  intro m m' a f e fm r M G g h hS hfm he hR
  have hB1 : rdW (m.arr64 CTL) 218 = G := hR.2.1.1
  have hB2 : rdW (m.arr64 CTL) 219 = g := hR.2.1.2.1
  by_cases hb : 4294967296 ≤ rdW (m.arr64 CTL) 218 + 1
  · rw [rxW_big (hb := hb)] at h; simp at h
  rw [rxW_ok (hb := hb), hB2] at h
  have hG : (G + 1).toNat < 2 ^ 32 := by rw [← hB1]; exact lt_of_notbig hb
  obtain ⟨hR1, hbank, hGl, hgG⟩ := rfEnter hR hG
  obtain ⟨hS1, hg1⟩ := StageR.frame_hi hS (benterG_frame 218 m) (by simp) (by simp) (by simp) (by simp)
  rcases hgo : rxGoW n (benterG 218 m) f CWF e with _ | ⟨r1, m1⟩ <;> rw [hgo] at h; · simp [rxK1] at h
  by_cases hrb : 4294967296 ≤ r1
  · rw [rxK1_big (hb := hrb)] at h; simp at h
  rw [rxK1_ok (hb := hrb)] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨mp', a', M1, G1, hrun, hS2, hg2, hR2, -, hkx, hG1⟩ := hGo _ m1 a f CWF e fm ∅ _ M (G + 1) (G + 1) hgo hS1
    (hfm.grow hg1) he hR1 hbank
  have hGG : G ≤ G + 1 := uint_le_succ hGl
  obtain ⟨hS3, hg3⟩ := StageR.frame_hi hS2 (MemFrame.setCtl m1 219 g) (by simp) (by simp) (by simp) (by simp)
  refine ⟨a', ?_, lt_of_notbig hrb, M1, G1, hS3, (hg1.trans hg2).trans hg3,
    rfLeave hR2 (UInt64.le_trans hgG (UInt64.le_trans hGG hG1)), fun k gen hgen => hkx k gen
      (UInt64.le_trans hgen hGG) (fun e => by
        subst e; rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl] at hgen; omega),
    UInt64.le_trans hGG hG1⟩
  rw [ConRon.Arena.replaceFVars.eq_1, StateT.run_bind, ← CWF_eq, hrun]
  rfl

/-- The walk's post. -/
def GoPost (m m' : Mem) (a' : AState) (M : Std.HashMap (EIdx × Word) EIdx) (G gn : Word)
    (mp' : Std.HashMap EIdx EIdx) : Prop :=
  ∃ M' G', StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RfInv m' M' G' gn ∧ Bank M' gn mp' ∧ GKeepX M M' G gn ∧
    G ≤ G'

theorem GKeepX.trans {M₁ M₂ M₃ : Std.HashMap (EIdx × Word) EIdx} {G G' g : Word} (h₁ : GKeepX M₁ M₂ G g)
    (h₂ : GKeepX M₂ M₃ G' g) (hG : G ≤ G') : GKeepX M₁ M₃ G g :=
  fun k gen hg hne => (h₂ k gen (UInt64.le_trans hg hG) hne).trans (h₁ k gen hg hne)

theorem GKeepX.refl (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word) : GKeepX M M G g := fun _ _ _ _ => rfl

/-- One child walked, then the rest. -/
theorem goStep {k : Nat} (hGo : GoOK dn fe vis k) {m m1 : Mem} {a : AState} {f f1 x x2 : Word} {fm : FvMap}
    {mp : Std.HashMap EIdx EIdx} {M : Std.HashMap (EIdx × Word) EIdx} {G gn : Word}
    (h1 : rxGoW k m f f1 x = some (x2, m1)) (hS : StageR dn vis fe m a) (hfm : FMOk m f.toNat fm) (hx : H x)
    (hR : RfInv m M G gn) (hb : Bank M gn mp) :
    ∃ mp1 a1, (ConRon.Arena.replaceFVarsGo fm mp f1.toNat (decE x)).run a = .ok ((decE x2, mp1), a1) ∧
      GoPost dn fe vis m m1 a1 M G gn mp1 := by
  obtain ⟨mp1, a1, M1, G1, hr, hS1, hg1, hR1, hb1, hk1, hG1⟩ := hGo m m1 a f f1 x fm mp x2 M G gn h1 hS hfm hx hR hb
  exact ⟨mp1, a1, hr, M1, G1, hS1, hg1, hR1, hb1, hk1, hG1⟩

theorem GoPost.then {m m1 m2 : Mem} {a1 a2 : AState} {M : Std.HashMap (EIdx × Word) EIdx} {G gn : Word}
    {mp1 mp2 : Std.HashMap EIdx EIdx} (h : GoPost dn fe vis m m1 a1 M G gn mp1)
    (k : ∀ M1 G1, RfInv m1 M1 G1 gn → Bank M1 gn mp1 → G ≤ G1 → StageR dn vis fe m1 a1 →
      ∃ M2 G2, StageR dn vis fe m2 a2 ∧ IWGrow m1 m2 ∧ RfInv m2 M2 G2 gn ∧ Bank M2 gn mp2 ∧
        GKeepX M1 M2 G1 gn ∧ G1 ≤ G2) :
    GoPost dn fe vis m m2 a2 M G gn mp2 := by
  obtain ⟨M1, G1, hS1, hg1, hR1, hb1, hk1, hG1⟩ := h
  obtain ⟨M2, G2, hS2, hg2, hR2, hb2, hk2, hG2⟩ := k M1 G1 hR1 hb1 hG1 hS1
  exact ⟨M2, G2, hS2, hg1.trans hg2, hR2, hb2, hk1.trans hk2 hG1, UInt64.le_trans hG1 hG2⟩

theorem GoPost.mk {m m1 m2 : Mem} {a1 a2 : AState} {M : Std.HashMap (EIdx × Word) EIdx} {G gn : Word}
    {mp1 : Std.HashMap EIdx EIdx} (h : GoPost dn fe vis m m1 a1 M G gn mp1) (hS : StageR dn vis fe m2 a2)
    (hg : IWGrow m1 m2) (hf : LowFr m1 m2) : GoPost dn fe vis m m2 a2 M G gn mp1 :=
  h.then dn fe vis fun M1 G1 hR1 hb1 _ _ =>
    ⟨M1, G1, hS, hg, hR1.frame (RfFr.of_low hf), hb1, GKeepX.refl _ _ _, UInt64.le_refl _⟩

/-- Two children and an interning: `app`, `lam`, `forallE`. -/
theorem rxBin_ok (k : Nat) (hGo : GoOK dn fe vis k) (g : Word)
    (mkW : Mem → Word → Word → Option (Word × Mem)) (iop : EIdx → EIdx → AM EIdx)
    (hmk : ∀ m a2 x2, rpMkW m g a2 x2 0 0 0 = mkW m a2 x2)
    (hst : ∀ (m m' : Mem) (a : AState) (u v r : Word), StageR dn vis fe m a → mkW m u v = some (r, m') →
      ∃ a', (iop (decE u) (decE v)).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m')
    (hlow : ∀ (m m' : Mem) (u v r : Word), mkW m u v = some (r, m') → LowFr m m')
    (m m' : Mem) (a : AState) (f f1 x y r : Word) (fm : FvMap) (mp : Std.HashMap EIdx EIdx)
    (M : Std.HashMap (EIdx × Word) EIdx) (G gn : Word)
    (hn : rxB1 k f f1 g x y (rxGoW k m f f1 x) = some (r, m'))
    (hS : StageR dn vis fe m a) (hfm : FMOk m f.toNat fm) (hx : H x) (hy : H y) (hR : RfInv m M G gn)
    (hb : Bank M gn mp) :
    ∃ mp' a', (do
        let (t2, mm) ← ConRon.Arena.replaceFVarsGo fm mp f1.toNat (decE x)
        let (b2, m2) ← ConRon.Arena.replaceFVarsGo fm mm f1.toNat (decE y)
        let r ← iop t2 b2
        pure (r, m2) : AM (EIdx × Std.HashMap EIdx EIdx)).run a = .ok ((decE r, mp'), a') ∧
      GoPost dn fe vis m m' a' M G gn mp' := by
  rcases h1 : rxGoW k m f f1 x with _ | ⟨a2, m1⟩ <;> rw [h1] at hn; · simp [rxB1] at hn
  rw [rxB1_some] at hn
  rcases h2 : rxGoW k m1 f f1 y with _ | ⟨x2, m2⟩ <;> rw [h2] at hn; · simp [rxB2] at hn
  rw [rxB2_some, hmk] at hn
  obtain ⟨mp1, a1, hr1, hP1⟩ := goStep dn fe vis hGo h1 hS hfm hx hR hb
  obtain ⟨M1, G1, hS1, hg1, hR1, hb1, hk1, hG1⟩ := hP1
  obtain ⟨mp2, a2', hr2, hP2⟩ := goStep dn fe vis hGo h2 hS1 (hfm.grow hg1) hy hR1 hb1
  obtain ⟨M2, G2, hS2, hg2, hR2, hb2, hk2, hG2⟩ := hP2
  obtain ⟨a3, hr3, hS3, hg3⟩ := hst m2 m' a2' a2 x2 r hS2 hn
  refine ⟨mp2, a3, ?_, M2, G2, hS3, (hg1.trans hg2).trans hg3, hR2.frame (RfFr.of_low (hlow _ _ _ _ _ hn)), hb2,
    hk1.trans hk2 hG1, UInt64.le_trans hG1 hG2⟩
  simp only [StateT.run_bind, hr1, except_ok_bind, hr2, hr3]
  rfl

theorem rxLet_ok (k : Nat) (hGo : GoOK dn fe vis k)
    (m m' : Mem) (a : AState) (f f1 x y z r : Word) (fm : FvMap) (mp : Std.HashMap EIdx EIdx)
    (M : Std.HashMap (EIdx × Word) EIdx) (G gn : Word)
    (hn : rxL1 k f f1 x y z (rxGoW k m f f1 x) = some (r, m'))
    (hS : StageR dn vis fe m a) (hfm : FMOk m f.toNat fm) (hx : H x) (hy : H y) (hz : H z)
    (hR : RfInv m M G gn) (hb : Bank M gn mp) :
    ∃ mp' a', (do
        let (t2, mm) ← ConRon.Arena.replaceFVarsGo fm mp f1.toNat (decE x)
        let (v2, m2) ← ConRon.Arena.replaceFVarsGo fm mm f1.toNat (decE y)
        let (b2, m3) ← ConRon.Arena.replaceFVarsGo fm m2 f1.toNat (decE z)
        let r ← internLetEE t2 v2 b2
        pure (r, m3) : AM (EIdx × Std.HashMap EIdx EIdx)).run a = .ok ((decE r, mp'), a') ∧
      GoPost dn fe vis m m' a' M G gn mp' := by
  rcases h1 : rxGoW k m f f1 x with _ | ⟨a2, m1⟩ <;> rw [h1] at hn; · simp [rxL1] at hn
  rw [rxL1_some] at hn
  rcases h2 : rxGoW k m1 f f1 y with _ | ⟨x2, m2⟩ <;> rw [h2] at hn; · simp [rxL2] at hn
  rw [rxL2_some] at hn
  rcases h3 : rxGoW k m2 f f1 z with _ | ⟨c2, m3⟩ <;> rw [h3] at hn; · simp [rxL3] at hn
  rw [rxL3_some, rpMkW_let] at hn
  obtain ⟨mp1, a1, hr1, M1, G1, hS1, hg1, hR1, hb1, hk1, hG1⟩ := goStep dn fe vis hGo h1 hS hfm hx hR hb
  obtain ⟨mp2, a2', hr2, M2, G2, hS2, hg2, hR2, hb2, hk2, hG2⟩ :=
    goStep dn fe vis hGo h2 hS1 (hfm.grow hg1) hy hR1 hb1
  obtain ⟨mp3, a3', hr3, M3, G3, hS3, hg3, hR3, hb3, hk3, hG3⟩ :=
    goStep dn fe vis hGo h3 hS2 ((hfm.grow hg1).grow hg2) hz hR2 hb2
  obtain ⟨a4, hr4, hS4, hg4⟩ := mkLet_stage hS3 a2 x2 c2 hn
  refine ⟨mp3, a4, ?_, M3, G3, hS4, ((hg1.trans hg2).trans hg3).trans hg4,
    hR3.frame (RfFr.of_low (mkLetW_low hn)), hb3, (hk1.trans hk2 hG1).trans hk3 (UInt64.le_trans hG1 hG2),
    UInt64.le_trans (UInt64.le_trans hG1 hG2) hG3⟩
  simp only [StateT.run_bind, hr1, except_ok_bind, hr2, hr3]
  have hr4' : (internLetEE (decE a2) (decE x2) (decE c2)).run a3' = .ok (decE r, a4) := hr4
  rw [hr4']
  rfl

theorem rxProj_ok (k : Nat) (hGo : GoOK dn fe vis k)
    (m m' : Mem) (a : AState) (f f1 x y z r : Word) (fm : FvMap) (mp : Std.HashMap EIdx EIdx)
    (M : Std.HashMap (EIdx × Word) EIdx) (G gn : Word)
    (hn : rxP1 x y (rxGoW k m f f1 z) = some (r, m'))
    (hS : StageR dn vis fe m a) (hfm : FMOk m f.toNat fm) (hz : H z) (hR : RfInv m M G gn) (hb : Bank M gn mp) :
    ∃ mp' a', (do
        let (x2, mm) ← ConRon.Arena.replaceFVarsGo fm mp f1.toNat (decE z)
        let r ← internProjE (decI x) y.toNat x2
        pure (r, mm) : AM (EIdx × Std.HashMap EIdx EIdx)).run a = .ok ((decE r, mp'), a') ∧
      GoPost dn fe vis m m' a' M G gn mp' := by
  rcases h1 : rxGoW k m f f1 z with _ | ⟨a2, m1⟩ <;> rw [h1] at hn; · simp [rxP1] at hn
  rw [rxP1_some, rpMkW_proj] at hn
  obtain ⟨mp1, a1, hr1, hP1⟩ := goStep dn fe vis hGo h1 hS hfm hz hR hb
  obtain ⟨a3, hr3, hS3, hg3⟩ := mkProj_stage hP1.choose_spec.choose_spec.1 x y a2 hn
  refine ⟨mp1, a3, ?_, hP1.mk dn fe vis hS3 hg3 (mkProjW_low hn)⟩
  simp only [StateT.run_bind, hr1, except_ok_bind]
  have hr3' : (internProjE (decI x) y.toNat (decE a2)).run a1 = .ok (decE r, a3) := hr3
  rw [hr3']
  rfl

theorem rxNode_arm (k : Nat) (hGo : GoOK dn fe vis k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVr v) (m m' : Mem) (a : AState) (f f1 h r : Word) (fm : FvMap) (mp : Std.HashMap EIdx EIdx)
    (M : Std.HashMap (EIdx × Word) EIdx) (G gn : Word)
    (hn : rxNodeW (k + 1) m f f1 (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0) = some (r, m'))
    (hS : StageR dn vis fe m a) (hfm : FMOk m f.toNat fm) (hR : RfInv m M G gn) (hb : Bank M gn mp) :
    ∃ mp' a', (rfArm fm mp f1.toNat (decE h) v).run a = .ok ((decE r, mp'), a') ∧
      GoPost dn fe vis m m' a' M G gn mp' := by
  cases v with
  | app f' x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    rw [hg, rxNodeW_bin (hg := Or.inl rfl)] at hn
    have := rxBin_ok dn fe vis k hGo 4 (fun m a b => mkAppW m a b) internAppE (fun m a2 x2 => by simp [rpMkW])
      (fun m m' a u v r hS hI => mkApp_stage hS u v hI) (fun m m' u v r hI => mkAppW_low hI)
      m m' a f f1 _ _ r fm mp M G gn hn hS hfm hx hy hR hb
    rw [hdx, hdy] at this; exact this
  | lam f' x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    rw [hg, rxNodeW_bin (hg := Or.inr (Or.inl rfl))] at hn
    have := rxBin_ok dn fe vis k hGo 5 (fun m a b => mkLamW m a b) internLamE (fun m a2 x2 => by simp [rpMkW])
      (fun m m' a u v r hS hI => mkLam_stage hS u v hI) (fun m m' u v r hI => mkLamW_low hI)
      m m' a f f1 _ _ r fm mp M G gn hn hS hfm hx hy hR hb
    rw [hdx, hdy] at this; exact this
  | forallE f' x' =>
    simp only [ViewR, getD1_eq', getD2_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    rw [hg, rxNodeW_bin (hg := Or.inr (Or.inr rfl))] at hn
    have := rxBin_ok dn fe vis k hGo 6 (fun m a b => mkForallW m a b) internForallEE (fun m a2 x2 => by simp [rpMkW])
      (fun m m' a u v r hS hI => mkForall_stage hS u v hI) (fun m m' u v r hI => mkForallW_low hI)
      m m' a f f1 _ _ r fm mp M G gn hn hS hfm hx hy hR hb
    rw [hdx, hdy] at this; exact this
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
    rw [hg, rxNodeW_let (hg := by decide) (h7 := rfl)] at hn
    have := rxLet_ok dn fe vis k hGo m m' a f f1 _ _ _ r fm mp M G gn hn hS hfm hx hy hz hR hb
    rw [hdx, hdy, hdz] at this; exact this
  | proj s i e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hi, hz, hdz⟩ := hvr
    rw [hg, rxNodeW_proj (hg := by decide) (h7 := by decide)] at hn
    have := rxProj_ok dn fe vis k hGo m m' a f f1 _ _ _ r fm mp M G gn hn hS hfm hz hR hb
    rw [hdz, hdx, hi] at this; exact this
  | bvar _ => exact False.elim hnv
  | sort _ => exact False.elim hnv
  | const _ _ => exact False.elim hnv
  | lit _ => exact False.elim hnv
  | fvar _ _ => exact False.elim hnv

theorem rfTwin_node (fm : FvMap) (memo : Std.HashMap EIdx EIdx) (fuel : Nat) (h : EIdx) (a : AState)
    (v : ENodeView) (hv : a.store.view h = some v) (hnv : NodeVr v) :
    (ConRon.Arena.replaceFVarsGo fm memo (fuel + 1) h).run a =
      ((match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← rfArm fm memo fuel h v
          pure (r, m.insert h r) : AM (EIdx × Std.HashMap EIdx EIdx)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | (rw [replaceFVarsGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]; try rfl)

theorem genW_zero (g : Word) : genW 0 g = g <<< 32 := by simp [genW]

theorem rxGo_nodeCase (j : Nat) (ih : ∀ k, k + 1 < j + 1 → GoOK dn fe vis k) (m m' : Mem) (a : AState)
    (f fu h r : Word) (fm : FvMap) (mp : Std.HashMap EIdx EIdx) (M : Std.HashMap (EIdx × Word) EIdx) (G gn : Word)
    (F : Nat) (hF : fu.toNat = F + 1) (hf0 : fu ≠ 0) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVr v) (hv : a.store.view (decE h) = some v) (hvl : vl ≠ [])
    (hgs : vl.headD 0 = 4 ∨ vl.headD 0 = 5 ∨ vl.headD 0 = 6 ∨ vl.headD 0 = 7 ∨ vl.headD 0 = 9)
    (hgo : rxG1 j m f fu h vl = some (r, m')) (hS : StageR dn vis fe m a) (hfm : FMOk m f.toNat fm) (hh : H h)
    (hR : RfInv m M G gn) (hb : Bank M gn mp) :
    ∃ mp' a', (ConRon.Arena.replaceFVarsGo fm mp (F + 1) (decE h)).run a = .ok ((decE r, mp'), a') ∧
      GoPost dn fe vis m m' a' M G gn mp' := by
  have hnl : ¬ (vl.headD 0 = 0 ∨ vl.headD 0 = 2 ∨ vl.headD 0 = 8 ∨ vl.headD 0 = 3) := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  have hn1 : ¬ vl.headD 0 = 1 := by rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  rw [rxG1_node (hv := hvl) (hg := hnl) (h1 := hn1)] at hgo
  rw [rfTwin_node _ _ _ _ a v hv hnv]
  obtain ⟨hMR, ⟨hB1, hB2, hgG, hGl, hcsz⟩, hFr⟩ := hR
  have hB2' : rdW (m.arr64 CTL) 219 = gn := hB2
  have hgn : gn.toNat < 2 ^ 32 := by have := UInt64.le_iff_toNat_le.mp hgG; omega
  rw [hB2', ← genW_zero] at hgo
  by_cases hfr : mfindG rfSch m h (genW 0 gn) = []
  · rw [rxG3_abort (hr := hfr)] at hgo; simp at hgo
  obtain ⟨hhit, hmiss⟩ := bank_find rfSch bmKey rfK_h2 rfV m M hMR gn hgn mp hb h 0 (show bmKey.ok h 0 from ⟨hh, rfl⟩) hfr
  have hdk : bmKey.dk h 0 = decE h := rfl
  by_cases hk : (mfindG rfSch m h (genW 0 gn)).headD 0 ≠ 0
  · rw [rxG3_hit (hr := hfr) (hh := hk)] at hgo
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hgo)
    obtain ⟨w, hw, hwv⟩ := hhit hk
    rw [hdk] at hw
    refine ⟨mp, a, ?_, M, G, hS, IWGrow.refl _, ⟨hMR, ⟨hB1, hB2, hgG, hGl, hcsz⟩, hFr⟩, hb, GKeepX.refl _ _ _,
      UInt64.le_refl _⟩
    simp only [hw]
    rw [hwv]; rfl
  · rw [rxG3_miss (hr := hfr) (hh := hk)] at hgo
    have hm := hmiss (by simpa using hk)
    rw [hdk] at hm
    cases j with
    | zero => simp [rxNodeW, rxG4] at hgo
    | succ k =>
    rcases hnode : rxNodeW (k + 1) m f (fu - 1) (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
        (vl.tail.tail.tail.headD 0) with _ | ⟨rn, m1⟩; · rw [hnode] at hgo; simp [rxG4] at hgo
    rw [hnode, rxG4_some] at hgo
    have hF1 : (fu - 1).toNat = F := by rw [toNat_sub_one' hf0, hF]; rfl
    obtain ⟨mp1, a1, hr1, M1, G1, hS1, hg1, hR1, hb1, hk1, hG1⟩ := rxNode_arm dn fe vis k (ih k (by omega)) vl v hvr
      hnv m m1 a f (fu - 1) h rn fm mp M G gn hnode hS hfm ⟨hMR, ⟨hB1, hB2, hgG, hGl, hcsz⟩, hFr⟩ hb
    rw [hF1] at hr1
    have hB21 : rdW (m1.arr64 CTL) 219 = gn := hR1.2.1.2.1
    rw [hB21, ← genW_zero] at hgo
    rcases hset : msetG rfSch m1 h (genW 0 gn) rn with _ | m2 <;> rw [hset] at hgo; · simp [rxG5] at hgo
    rw [rxG5_some] at hgo
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hgo)
    obtain ⟨hR2, hbk2, hF2, hBW2⟩ := bank_put rfSch rfSch_wf bmKey rfK_h2 rfV (fun _ _ _ _ _ h => h) 218
      ⟨by decide, by decide⟩ m1 M1 hR1.1 G1 gn hR1.2.1 hR1.2.2 mp1 hb1 h 0 rn (show bmKey.ok h 0 from ⟨hh, rfl⟩) (decE rn) rfl _ hset
    rw [hdk] at hR2 hbk2 hF2
    have hfs : MemFrame [RFM] [rfSch.cs + 1] m1 _ := msetG_frame rfSch rfSch_wf m1 _ h _ rn hset
    obtain ⟨hS2, hg2⟩ := StageR.frame_hi hS1 hfs (by intro b hb; simp at hb; subst hb; decide)
      (by intro x hx; simp [rfSch] at hx; subst hx; decide) (by decide) (by simp [rfSch])
    refine ⟨mp1.insert (decE h) (decE rn), a1, ?_, M1.insert (decE h, gn) (decE rn), G1, hS2, hg1.trans hg2,
      ⟨hR2, hBW2, hF2⟩, hbk2, fun k' gen hgen hne => ?_, hG1⟩
    · rw [hm]
      simp only [StateT.run_bind, hr1]
      rfl
    · rw [Std.HashMap.getElem?_insert]
      have : ¬ ((decE h, gn) == (k', gen)) = true := by simp [Ne.symm hne]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact hk1 k' gen hgen hne

theorem goOK_step (j : Nat) (hMap : MapOK dn fe vis j) (ih : ∀ k, k + 1 < j + 1 → GoOK dn fe vis k) :
    GoOK dn fe vis (j + 1) := by
  intro m m' a f fu h fm mp r M G gn hgo hS hfm hh hR hb
  by_cases hf0 : fu = 0
  · rw [rxGoW_abort (hf := hf0)] at hgo; simp at hgo
  rw [rxGoW_view (hf := hf0)] at hgo
  obtain ⟨F, hF⟩ : ∃ F, fu.toNat = F + 1 := ⟨fu.toNat - 1, by have := toNat_ne_zero' hf0; omega⟩
  cases hvl : eViewW m h with
  | nil => rw [hvl] at hgo; simp [rxG1] at hgo
  | cons g vt =>
  have hne : eViewW m h ≠ [] := by rw [hvl]; simp
  obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hS.1.arena.1 h hne
  rw [hvl] at hvr hgo
  have leaf : ∀ (hg : (g :: vt).headD 0 = 0 ∨ (g :: vt).headD 0 = 2 ∨ (g :: vt).headD 0 = 8 ∨
      (g :: vt).headD 0 = 3),
      (match v with | .bvar _ | .sort _ | .lit _ | .const _ _ => True | _ => False) →
      ∃ mp' a' M' G', (ConRon.Arena.replaceFVarsGo fm mp fu.toNat (decE h)).run a = .ok ((decE r, mp'), a') ∧
        StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RfInv m' M' G' gn ∧ Bank M' gn mp' ∧ GKeepX M M' G gn ∧
        G ≤ G' := by
    intro hg hv'
    rw [rxG1_leaf (hv := by simp) (hg := hg)] at hgo
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hgo)
    refine ⟨mp, a, M, G, ?_, hS, IWGrow.refl _, hR, hb, GKeepX.refl _ _ _, UInt64.le_refl _⟩
    rw [hF, replaceFVarsGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
    cases v <;> first | rfl | exact False.elim hv'
  have node : ∀ (hgs : (g :: vt).headD 0 = 4 ∨ (g :: vt).headD 0 = 5 ∨ (g :: vt).headD 0 = 6 ∨
      (g :: vt).headD 0 = 7 ∨ (g :: vt).headD 0 = 9), NodeVr v →
      ∃ mp' a' M' G', (ConRon.Arena.replaceFVarsGo fm mp fu.toNat (decE h)).run a = .ok ((decE r, mp'), a') ∧
        StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RfInv m' M' G' gn ∧ Bank M' gn mp' ∧ GKeepX M M' G gn ∧
        G ≤ G' := by
    intro hgs hnv
    rw [hF]
    obtain ⟨mp', a', hrun, M', G', h1, h2, h3, h4, h5, h6⟩ := rxGo_nodeCase dn fe vis j ih m m' a f fu h r fm mp M G
      gn F hF hf0 _ _ hvr hnv hv (by simp) hgs hgo hS hfm hh hR hb
    exact ⟨mp', a', M', G', hrun, h1, h2, h3, h4, h5, h6⟩
  cases v with
  | bvar i => exact leaf (Or.inl (by simpa [ViewR] using hvr.1)) trivial
  | sort u => exact leaf (Or.inr (Or.inl (by simpa [ViewR] using hvr.1))) trivial
  | lit l => exact leaf (Or.inr (Or.inr (Or.inl (by simpa [ViewR] using hvr)))) trivial
  | const n us => exact leaf (Or.inr (Or.inr (Or.inr hvr.1))) trivial
  | fvar i ty =>
    obtain ⟨hg1, hi, -, -⟩ := hvr
    rw [rxG1_fvar (hv := by simp) (hg := by rw [hg1]; decide) (h1 := hg1)] at hgo
    rw [getD1_eq'] at hi
    rcases hmap : rxMapW j m f ((g :: vt).tail.headD 0) with _ | ⟨r0, r1, m1⟩ <;> rw [hmap] at hgo; · simp [rxH] at hgo
    rw [rxH_some] at hgo
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hgo)
    obtain ⟨xo, a1, hrun, hout, M1, G1, hS1, hg1', hR1, hk1, hG1⟩ := hMap m m1 a f _ fm r0 r1 M G gn hmap hS hfm hR
    refine ⟨mp, a1, M1, G1, ?_, hS1, hg1', hR1, hk1.bank hR.2.1.2.2.1 hb, fun k gen hg _ => hk1 k gen hg, hG1⟩
    simp only [hF, replaceFVarsGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind, ← hi, hrun]
    cases xo with
    | none =>
      simp only [OptE] at hout
      simp only [hout, ne_eq, not_true_eq_false, ite_false]; rfl
    | some e' =>
      obtain ⟨h0, hd⟩ := hout
      rw [ite_eq_left h0, hd]; rfl
  | app f' x' => exact node (Or.inl hvr.1) trivial
  | lam f' x' => exact node (Or.inr (Or.inl hvr.1)) trivial
  | forallE f' x' => exact node (Or.inr (Or.inr (Or.inl hvr.1))) trivial
  | letE t v' b' => exact node (Or.inr (Or.inr (Or.inr (Or.inl hvr.1)))) trivial
  | proj s i e => exact node (Or.inr (Or.inr (Or.inr (Or.inr hvr.1)))) trivial

theorem rxOK_all (n : Nat) : MapOK dn fe vis n ∧ ImgOK dn fe vis n ∧ FrOK dn fe vis n ∧ DsOK dn fe vis n ∧
    DsGoOK dn fe vis n ∧ GoOK dn fe vis n ∧ RfOK dn fe vis n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [MapOK, ImgOK, FrOK, DsOK, DsGoOK, GoOK, RfOK] <;> intros <;>
        simp_all [rxMapW, rxImgW, rxFrameW, rxDsW, rxDsGoW, rxGoW, rxW]
    | succ j =>
      obtain ⟨hMap, hImg, hFr, hDs, hDg, hGo, hRf⟩ := ih j (by omega)
      exact ⟨mapOK_step dn fe vis j hImg, imgOK_step dn fe vis j hImg hFr, frOK_step dn fe vis j hDs,
        dsOK_step dn fe vis j hDg, dsGoOK_step dn fe vis j hRf hDg,
        goOK_step dn fe vis j hMap (fun k hk => (ih k (by omega)).2.2.2.2.2.1), rfOK_step dn fe vis j hGo⟩

end steps

end L.Ind

end

end
