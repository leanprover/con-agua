module

import ConAgua.Arena.IndPosSpec.CtxFields
public import ConAgua.Arena.IndPosSpec.RpGoStep
import ConAgua.Arena.IndSim
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndInstallSpec.DomsW
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.RecCheck
import ConAgua.L.ModelGen
import ConAgua.L.WordOff
import ConAgua.Arena.IndSumSpec.McGoStep

@[expose] public section

/-!
# TaCW

`target_abs`' models (`taCW`, `taGoW`, `taNodeW`, `taAW`, generated), their refinement `taAW_ok` and the
lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Word models -/

/-- The lookups of the `target_abs` walk. -/
structure TaLook (p : Prog) : Prop where
  hk : MkLook p
  hv : p.lookup "e_view" = some eView
  hf : p.lookup "sl_find" = some slFind
  tf : p.lookup "ta_find" = some (memoFindG taSch)
  tp : p.lookup "ta_put" = some (memoPutG taSch)
  tc : p.lookup "ta_clear" = some (memoClearG taSch)
  cst : p.lookup "target_abs_const" = some targetAbsConst
  go : p.lookup "target_abs_go" = some targetAbsGo
  node : p.lookup "target_abs_node" = some targetAbsNode
  top : p.lookup "target_abs" = some targetAbs

/-- **`target_abs_const` is its model `taCW`** (generated). -/
l_model taConst_spec (p : Prog) (hL : TaLook p)
  fns [hL.cst ↦ taCW]
  specs [slFind_spec p hL.hf n]
  grind [arena_grind]

/-- **`target_abs_go` and `target_abs_node` are their models `taGoW`, `taNodeW`** (generated). -/
l_model taGo_spec (p : Prog) (hL : TaLook p)
  fns [hL.go ↦ taGoW, hL.node ↦ taNodeW]
  specs [eView_spec p hL.hv n, taConst_spec p hL n, memoFindG_spec taSch p _ hL.tf n,
    memoPutG_spec taSch p _ hL.tp n,
    mkApp_spec p hL.hk.hd hL.hk.appF hL.hk.appP hL.hk.appI hL.hk.appM n,
    mkLam_spec p hL.hk.hd hL.hk.lamF hL.hk.lamP hL.hk.lamI hL.hk.lamM n,
    mkForall_spec p hL.hk.hd hL.hk.forF hL.hk.forP hL.hk.forI hL.hk.forM n,
    mkLet_spec p hL.hk.hd hL.hk.ltF hL.hk.ltP hL.hk.ltI hL.hk.ltM n,
    mkProj_spec p hL.hk.hd hL.hk.prjF hL.hk.prjP hL.hk.prjI hL.hk.prjM n]
  grind [arena_grind]
/-- A leaf of `target_abs_go` (`bvar`, `sort`, `fvar`, `lit`): the handle itself. -/
theorem taGoW_leaf (n : Nat) (m : Mem) (no nl lvls ho hl f h : Word) (hf : f ≠ 0)
    (hv : eViewW m h ≠ [])
    (hg : (eViewW m h).headD 0 = 0 ∨ (eViewW m h).headD 0 = 1 ∨ (eViewW m h).headD 0 = 2 ∨
      (eViewW m h).headD 0 = 8) :
    taGoW (n + 1) m no nl lvls ho hl f h = some (h, m) := by
  rcases hg with e | e | e | e
  · exact taGoW.arm1 _ _ _ _ _ _ _ _ _ hf hv e
  · exact taGoW.arm2 _ _ _ _ _ _ _ _ _ hf hv (by rw [e]; decide) e
  · exact taGoW.arm3 _ _ _ _ _ _ _ _ _ hf hv (by rw [e]; decide) (by rw [e]; decide) e
  · exact taGoW.arm4 _ _ _ _ _ _ _ _ _ hf hv (by rw [e]; decide) (by rw [e]; decide) (by rw [e]; decide) e

/-- After `target_abs_node`: the memo insert, as `msetG`. -/
theorem taGoW_kNode (h r : Word) (m1 : Mem) :
    taGoW.k_target_abs_node h (some (r, m1)) = (msetG taSch m1 h 0 r).map (fun m2 => (r, m2)) := by
  simp only [taGoW.k_target_abs_node, msetG]
  split
  · rfl
  · cases mputG taSch m1 h 0 r _ _ <;> rfl

/-- **What a returning `target_abs_go` step did**: kept the memory (a leaf, a memo hit), the
`const` arm, or the node's walk and its memo insert. -/
theorem taGoW_some {n : Nat} {m m' : Mem} {no nl lvls ho hl f h r : Word}
    (hg : taGoW (n + 1) m no nl lvls ho hl f h = some (r, m')) :
    m' = m ∨ taCW n m no nl lvls ho hl h ((eViewW m h).tail.headD 0) ((eViewW m h).tail.tail.headD 0) =
      some (r, m') ∨
    ∃ rn m1, taNodeW n m no nl lvls ho hl (f - 1) ((eViewW m h).headD 0) ((eViewW m h).tail.headD 0)
      ((eViewW m h).tail.tail.headD 0) ((eViewW m h).tail.tail.tail.headD 0) = some (rn, m1) ∧
      msetG taSch m1 h 0 rn = some m' := by
  have keep : ∀ {x : Word} {mm : Mem}, some (x, mm) = some (r, m') → mm = m' := fun e => by
    cases e; rfl
  by_cases c : f = 0
  · rw [taGoW.abort1 _ _ _ _ _ _ _ _ _ c] at hg; cases hg
  by_cases cv : eViewW m h = []
  · rw [taGoW.abort2 _ _ _ _ _ _ _ _ _ c cv] at hg; cases hg
  by_cases c0 : (eViewW m h).headD 0 = 0
  · rw [taGoW.arm1 _ _ _ _ _ _ _ _ _ c cv c0] at hg; exact Or.inl (keep hg).symm
  by_cases c1 : (eViewW m h).headD 0 = 1
  · rw [taGoW.arm2 _ _ _ _ _ _ _ _ _ c cv c0 c1] at hg; exact Or.inl (keep hg).symm
  by_cases c2 : (eViewW m h).headD 0 = 2
  · rw [taGoW.arm3 _ _ _ _ _ _ _ _ _ c cv c0 c1 c2] at hg; exact Or.inl (keep hg).symm
  by_cases c8 : (eViewW m h).headD 0 = 8
  · rw [taGoW.arm4 _ _ _ _ _ _ _ _ _ c cv c0 c1 c2 c8] at hg; exact Or.inl (keep hg).symm
  by_cases c3 : (eViewW m h).headD 0 = 3
  · rw [taGoW.arm5 _ _ _ _ _ _ _ _ _ c cv c0 c1 c2 c8 c3] at hg; exact Or.inr (Or.inl hg)
  by_cases cf : mfindG taSch m h 0 = []
  · rw [taGoW.abort3 _ _ _ _ _ _ _ _ _ c cv c0 c1 c2 c8 c3 cf] at hg; cases hg
  by_cases ch : (mfindG taSch m h 0).headD 0 ≠ 0
  · rw [taGoW.arm6 _ _ _ _ _ _ _ _ _ c cv c0 c1 c2 c8 c3 cf ch] at hg; exact Or.inl (keep hg).symm
  rw [taGoW.arm7 _ _ _ _ _ _ _ _ _ c cv c0 c1 c2 c8 c3 cf (by simpa using ch)] at hg
  obtain ⟨⟨rn, m1⟩, hn, hg⟩ := of_K hg (taGoW.k_target_abs_node.none _)
  rw [taGoW_kNode] at hg
  rcases hs : msetG taSch m1 h 0 rn with _ | m2 <;>
    simp only [hs, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hg
  exact Or.inr (Or.inr ⟨rn, m1, hn, hg.2 ▸ hs⟩)

/-- `target_abs_go`'s half of `taGo_spec`, as a triple (`target_abs`' callee spec). -/
theorem taGo_specG (p : Prog) (L : TaLook p) (n : Nat) (s₀ : St) (no nl lvls ho hl f h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_abs_go" [no, nl, lvls, ho, hl, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ taGoW n s₀.mem no nl lvls ho hl f h = some (r.headD 0, s'.mem); ⊤⦄ :=
  (taGo_spec p L n).1 s₀ no nl lvls ho hl f h

/-- **`target_abs` is its model `taAW`** (generated): clear the memo, the walk at `⟪CWF⟫`. -/
l_model targetAbs_spec (p : Prog) (hL : TaLook p)
  fns [hL.top ↦ taAW]
  specs [memoClearG_spec taSch p _ hL.tc n, taGo_specG p hL n]
  grind [arena_grind] fold [CWF] pfuel

/-! ## The relational side -/

/-- The twin's `const` arm. -/
def taConstT (names : List NIdx) (lvls : LsIdx) (holes : List EIdx) (h : EIdx) (n : NIdx) (us : LsIdx) : EIdx :=
  if us == lvls then
    match names.findIdx? (· == n) with
    | some t => match holes[t]? with
      | some x => x
      | none => h
    | none => h
  else h

/-- The twin's memoised arms. -/
def taArm (names : List NIdx) (lvls : LsIdx) (holes : List EIdx) (memo : Std.HashMap EIdx EIdx)
    (fuel : Nat) (h : EIdx) : ENodeView → AM (EIdx × Std.HashMap EIdx EIdx)
  | .app a b => do
    let (a', m) ← ConRon.Arena.targetAbsGo names lvls holes memo fuel a
    let (b', m2) ← ConRon.Arena.targetAbsGo names lvls holes m fuel b
    let r ← internAppE a' b'
    pure (r, m2)
  | .lam ty body => do
    let (t', m) ← ConRon.Arena.targetAbsGo names lvls holes memo fuel ty
    let (b', m2) ← ConRon.Arena.targetAbsGo names lvls holes m fuel body
    let r ← internLamE t' b'
    pure (r, m2)
  | .forallE ty body => do
    let (t', m) ← ConRon.Arena.targetAbsGo names lvls holes memo fuel ty
    let (b', m2) ← ConRon.Arena.targetAbsGo names lvls holes m fuel body
    let r ← internForallEE t' b'
    pure (r, m2)
  | .letE ty val body => do
    let (t', m) ← ConRon.Arena.targetAbsGo names lvls holes memo fuel ty
    let (v', m2) ← ConRon.Arena.targetAbsGo names lvls holes m fuel val
    let (b', m3) ← ConRon.Arena.targetAbsGo names lvls holes m2 fuel body
    let r ← internLetEE t' v' b'
    pure (r, m3)
  | .proj s i sub => do
    let (u, m) ← ConRon.Arena.targetAbsGo names lvls holes memo fuel sub
    let r ← internProjE s i u
    pure (r, m)
  | _ => pure (h, memo)

theorem targetAbsGo_succ' (names : List NIdx) (lvls : LsIdx) (holes : List EIdx) (memo : Std.HashMap EIdx EIdx)
    (fuel : Nat) (h : EIdx) :
    ConRon.Arena.targetAbsGo names lvls holes memo (fuel + 1) h = (do
      let v ← view h
      match v with
      | .bvar _ => pure (h, memo)
      | .sort _ => pure (h, memo)
      | .lit _ => pure (h, memo)
      | .fvar _ _ => pure (h, memo)
      | .const n us => pure (taConstT names lvls holes h n us, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← taArm names lvls holes memo fuel h v
          pure (r, m.insert h r)) := by
  rw [ConRon.Arena.targetAbsGo.eq_2]
  congr 1
  funext v
  cases v with
  | app a' x' => simp only [taArm, bind_assoc, pure_bind]; rfl
  | lam t body => simp only [taArm, bind_assoc, pure_bind]; rfl
  | forallE t body => simp only [taArm, bind_assoc, pure_bind]; rfl
  | letE t v' body => simp only [taArm, bind_assoc, pure_bind]; rfl
  | proj s i x => simp only [taArm, bind_assoc, pure_bind]; rfl
  | bvar _ => rfl
  | sort _ => rfl
  | lit _ => rfl
  | fvar _ _ => rfl
  | const n us =>
    simp only [taConstT]
    by_cases hb : (us == lvls) = true
    · simp only [hb, ite_true]
      cases names.findIdx? (· == n) with
      | none => rfl
      | some t => dsimp only; cases holes[t]? <;> rfl
    · simp [hb]

theorem taSch_wf : taSch.WF := ⟨by decide, by decide⟩

/-- The `ta` memo against the twin's map. -/
abbrev taMR (m : Mem) (mp : Std.HashMap EIdx EIdx) : Prop :=
  MemoRG taSch bmKey (fun w : Word => decE w) m mp

theorem taMR_low {m m' : Mem} (hf : LowFr m m') {mp : Std.HashMap EIdx EIdx} (h : taMR m mp) : taMR m' mp := by
  obtain ⟨A, C, hf, hA, hC⟩ := hf
  exact memoRG_frame taSch taSch_wf bmKey (fun w : Word => decE w) A C
    (fun hmem => by have := hA _ hmem; simp [taSch, TAM] at this)
    (fun hmem => by have := hC _ hmem; simp [taSch] at this) m m' hf mp h

/-- **The `const` arm**: a read; the hole of a member at the walk's levels. -/
theorem taCW_ok (n : Nat) {m m' : Mem} {no nl lvls ho hl h nn vus r : Word} {names : List NIdx}
    {holes : List EIdx} (hc : taCW n m no nl lvls ho hl h nn vus = some (r, m'))
    (hlv : H lvls) (hn : H nn) (hvus : H vus)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hho : decHL m ho.toNat hl.toNat = some holes) (hhb : ho.toNat + hl.toNat < 2 ^ 64) :
    m' = m ∧ decE r = taConstT names (decI lvls) holes (decE h) (decI nn) (decI vus) := by
  obtain _ | n := n
  · simp [taCW] at hc
  by_cases hv : vus ≠ lvls
  · rw [taCW.arm1 (hc1 := hv)] at hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
    have : ¬ ((decI vus : LsIdx) == decI lvls) = true := by rw [decI_beq vus lvls hvus hlv]; simpa using hv
    refine ⟨rfl, ?_⟩
    simp only [taConstT, this]; rfl
  rw [taCW.arm2 (hc1 := by simpa using hv)] at hc
  have hbeq : ((decI vus : LsIdx) == decI lvls) = true := by rw [decI_beq vus lvls hvus hlv]; simpa using hv
  obtain ⟨ws, hws, rfl, hwlt⟩ := slR_of_decHL m _ _ names hdec hno
  simp only [UInt64.ofNat_toNat] at hws
  have hlen : ws.length < 2 ^ 64 := by have := decHL_length m hdec; simp at this; omega
  have hhl := decHL_length m hho
  rcases hfw : findW n m no nl nn with _ | fr <;> rw [hfw] at hc <;>
    try (simp only [taCW.k_sl_find, reduceCtorEq] at hc; done)
  have hfr := findW_ok n _ _ _ _ _ _ hws hfw hlen
  have hfi := findIdx_map_decI (k := .name) nn hn ws hwlt
  cases hwi : ws.findIdx? (· == nn) with
  | none =>
    rw [hwi] at hfr; subst hfr
    rw [taCW.k_sl_find.arm1 (hc1 := rfl)] at hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
    refine ⟨rfl, ?_⟩
    simp only [taConstT, hbeq, ite_true, hfi, hwi]
  | some i =>
    rw [hwi] at hfr; subst hfr
    obtain ⟨hil, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hwi
    have hi : (UInt64.ofNat i : Word).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
    by_cases hout : hl ≤ UInt64.ofNat i
    · rw [taCW.k_sl_find.arm2 (hc1 := by simp) (hc2 := by simpa using hout)] at hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
      have : holes.length ≤ i := by
        have h1 := UInt64.le_iff_toNat_le.mp hout; rw [hi] at h1; rw [hhl]; exact h1
      refine ⟨rfl, ?_⟩
      simp only [taConstT, hbeq, ite_true, hfi, hwi, List.getElem?_eq_none this]
    · rw [taCW.k_sl_find.arm3 (hc1 := by simp) (hc2 := by simpa using hout)] at hc
      simp only [Option.some.injEq, Prod.mk.injEq, List.tail_cons, List.headD_cons] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hih : i < hl.toNat := by
        have : ¬ hl.toNat ≤ i := fun x => hout (UInt64.le_iff_toNat_le.mpr (by rw [hi]; exact x))
        omega
      obtain ⟨-, hd⟩ := rd_iwH (p := ho) (i := UInt64.ofNat i) (by rw [hi]; exact decHL_getI hho i hih)
        (by rw [hi]; omega)
      refine ⟨rfl, ?_⟩
      simp only [taConstT, hbeq, ite_true, hfi, hwi, List.getElem?_eq_getElem (show i < holes.length by omega)]
      exact hd

/-- The inputs of the `ta` walk at `m`: the member names and the holes decode below the IW top. -/
def TaIn (m : Mem) (no nl ho hl : Word) (names : List NIdx) (holes : List EIdx) : Prop :=
  decHL m no.toNat nl.toNat = some names ∧ no.toNat + nl.toNat ≤ iwTop m ∧
    decHL m ho.toNat hl.toNat = some holes ∧ ho.toNat + hl.toNat ≤ iwTop m

theorem TaIn.grow {m m1 : Mem} {no nl ho hl : Word} {names : List NIdx} {holes : List EIdx}
    (h : TaIn m no nl ho hl names holes) (hg : IWGrow m m1) : TaIn m1 no nl ho hl names holes :=
  ⟨by rw [decHL_grow hg h.2.1]; exact h.1, by have := hg.iw; have := h.2.1; omega,
    by rw [decHL_grow hg h.2.2.2]; exact h.2.2.1, by have := hg.iw; have := h.2.2.2; omega⟩

/-- The post of the `ta` walk from `m`: the result decoded, the stage kept, the memo related. -/
abbrev TaQ (_dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m : Mem) (r : Word)
    (x : EIdx × Std.HashMap EIdx EIdx) (m' : Mem) (a' : AState) : Prop :=
  x.1 = decE r ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧ taMR m' x.2

def TaGoOK (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (no nl lvls ho hl f h : Word) (names : List NIdx) (holes : List EIdx)
    (mp : Std.HashMap EIdx EIdx), StageR vis fe m a → H h → H lvls →
    TaIn m no nl ho hl names holes → taMR m mp →
    Sim (taGoW n m no nl lvls ho hl f h)
      (ConRon.Arena.targetAbsGo names (decI lvls) holes mp f.toNat (decE h)) a (TaQ dn fe vis m)

/-- Two children and an interning: `app`, `lam`, `forallE` (`K1`, `K2`: the continuations after
the two walks). -/
theorem taBin_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : TaGoOK dn fe vis k)
    (mkW : Mem → Word → Word → Option (Word × Mem)) (iop : EIdx → EIdx → AM EIdx)
    (hst : ∀ (m m' : Mem) (a : AState) (u v r : Word), StageR vis fe m a → mkW m u v = some (r, m') →
      ∃ a', (iop (decE u) (decE v)).run a = .ok (decE r, a') ∧ StageR vis fe m' a' ∧ IWGrow m m')
    (hlow : ∀ (m m' : Mem) (u v r : Word), mkW m u v = some (r, m') → LowFr m m')
    (m : Mem) (a : AState) (no nl lvls ho hl f1 x y : Word)
    (K1 : Option (Word × Mem) → Option (Word × Mem)) (K2 : Word → Option (Word × Mem) → Option (Word × Mem))
    (h1n : K1 none = none) (h1s : ∀ a2 m1, K1 (some (a2, m1)) = K2 a2 (taGoW k m1 no nl lvls ho hl f1 y))
    (h2n : ∀ a2, K2 a2 none = none) (h2s : ∀ a2 x2 m2, K2 a2 (some (x2, m2)) = mkW m2 a2 x2)
    (names : List NIdx) (holes : List EIdx)
    (mp : Std.HashMap EIdx EIdx) (hS : StageR vis fe m a) (hx : H x) (hy : H y) (hlv : H lvls)
    (hI : TaIn m no nl ho hl names holes) (hM : taMR m mp) :
    Sim (K1 (taGoW k m no nl lvls ho hl f1 x)) (do
        let (t2, mm) ← ConRon.Arena.targetAbsGo names (decI lvls) holes mp f1.toNat (decE x)
        let (b2, m2) ← ConRon.Arena.targetAbsGo names (decI lvls) holes mm f1.toNat (decE y)
        let r ← iop t2 b2
        pure (r, m2) : AM (EIdx × Std.HashMap EIdx EIdx)) a (TaQ dn fe vis m) := by
  refine Sim.bindK h1n h1s (ih m a _ _ _ _ _ f1 x _ _ mp hS hx hlv hI hM) ?_
  rintro a2 ⟨t2, mp1⟩ m1 a1 ⟨rfl, hS1, hg1, hM1⟩
  refine Sim.bindK (h2n a2) (h2s a2) (ih m1 a1 _ _ _ _ _ f1 y _ _ mp1 hS1 hy hlv (hI.grow hg1) hM1) ?_
  rintro x2 ⟨b2, mp2⟩ m2 a2' ⟨rfl, hS2, hg2, hM2⟩
  intro r m' hn
  obtain ⟨a3, hr3, hS3, hg3⟩ := hst m2 m' a2' a2 x2 r hS2 hn
  exact ⟨(decE r, mp2), a3, by rw [StateT.run_bind, hr3]; rfl, rfl, hS3, (hg1.trans hg2).trans hg3,
    taMR_low (hlow m2 m' a2 x2 r hn) hM2⟩

theorem taLet_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : TaGoOK dn fe vis k)
    (m : Mem) (a : AState) (no nl lvls ho hl f1 x y z : Word) (names : List NIdx) (holes : List EIdx)
    (mp : Std.HashMap EIdx EIdx) (hS : StageR vis fe m a) (hx : H x) (hy : H y) (hz : H z) (hlv : H lvls)
    (hI : TaIn m no nl ho hl names holes) (hM : taMR m mp) :
    Sim (taNodeW.k_target_abs_go_7 k no nl lvls ho hl f1 y z (taGoW k m no nl lvls ho hl f1 x)) (do
        let (t2, mm) ← ConRon.Arena.targetAbsGo names (decI lvls) holes mp f1.toNat (decE x)
        let (v2, m2) ← ConRon.Arena.targetAbsGo names (decI lvls) holes mm f1.toNat (decE y)
        let (b2, m3) ← ConRon.Arena.targetAbsGo names (decI lvls) holes m2 f1.toNat (decE z)
        let r ← internLetEE t2 v2 b2
        pure (r, m3) : AM (EIdx × Std.HashMap EIdx EIdx)) a (TaQ dn fe vis m) := by
  refine Sim.bindK (taNodeW.k_target_abs_go_7.none ..) (fun _ _ => taNodeW.k_target_abs_go_7.arm1 ..)
    (ih m a _ _ _ _ _ f1 x _ _ mp hS hx hlv hI hM) ?_
  rintro a2 ⟨t2, mp1⟩ m1 a1 ⟨rfl, hS1, hg1, hM1⟩
  refine Sim.bindK (taNodeW.k_target_abs_go_8.none ..) (fun _ _ => taNodeW.k_target_abs_go_8.arm1 ..)
    (ih m1 a1 _ _ _ _ _ f1 y _ _ mp1 hS1 hy hlv (hI.grow hg1) hM1) ?_
  rintro x2 ⟨v2, mp2⟩ m2 a2' ⟨rfl, hS2, hg2, hM2⟩
  have hg12 := hg1.trans hg2
  refine Sim.bindK (taNodeW.k_target_abs_go_9.none ..) (fun _ _ => taNodeW.k_target_abs_go_9.arm1 ..)
    (ih m2 a2' _ _ _ _ _ f1 z _ _ mp2 hS2 hz hlv (hI.grow hg12) hM2) ?_
  rintro c2 ⟨b2, mp3⟩ m3 a3' ⟨rfl, hS3, hg3, hM3⟩
  intro r m' hn
  obtain ⟨a4, hr4, hS4, hg4⟩ := mkLet_stage hS3 a2 x2 c2 hn
  have hr4' : (internLetEE (decE a2) (decE x2) (decE c2)).run a3' = .ok (decE r, a4) := hr4
  exact ⟨(decE r, mp3), a4, by rw [StateT.run_bind, hr4']; rfl, rfl, hS4, (hg12.trans hg3).trans hg4,
    taMR_low (mkLetW_low hn) hM3⟩

theorem taProj_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : TaGoOK dn fe vis k)
    (m : Mem) (a : AState) (no nl lvls ho hl f1 x y z : Word) (names : List NIdx) (holes : List EIdx)
    (mp : Std.HashMap EIdx EIdx) (hS : StageR vis fe m a) (hz : H z) (hlv : H lvls)
    (hI : TaIn m no nl ho hl names holes) (hM : taMR m mp) :
    Sim (taNodeW.k_target_abs_go_10 x y (taGoW k m no nl lvls ho hl f1 z)) (do
        let (x2, mm) ← ConRon.Arena.targetAbsGo names (decI lvls) holes mp f1.toNat (decE z)
        let r ← internProjE (decI x) y.toNat x2
        pure (r, mm) : AM (EIdx × Std.HashMap EIdx EIdx)) a (TaQ dn fe vis m) := by
  refine Sim.bindK (taNodeW.k_target_abs_go_10.none ..) (fun _ _ => taNodeW.k_target_abs_go_10.arm1 ..)
    (ih m a _ _ _ _ _ f1 z _ _ mp hS hz hlv hI hM) ?_
  rintro a2 ⟨t2, mp1⟩ m1 a1 ⟨rfl, hS1, hg1, hM1⟩
  intro r m' hn
  obtain ⟨a3, hr3, hS3, hg3⟩ := mkProj_stage hS1 x y a2 hn
  have hr3' : (internProjE (decI x) y.toNat (decE a2)).run a1 = .ok (decE r, a3) := hr3
  exact ⟨(decE r, mp1), a3, by rw [StateT.run_bind, hr3']; rfl, rfl, hS3, hg1.trans hg3, taMR_low (mkProjW_low hn) hM1⟩

theorem taNode_arm (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : TaGoOK dn fe vis k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v) (hnv : NodeVr v)
    (m : Mem) (a : AState) (no nl lvls ho hl f1 h : Word) (names : List NIdx) (holes : List EIdx)
    (mp : Std.HashMap EIdx EIdx) (hS : StageR vis fe m a) (hlv : H lvls)
    (hI : TaIn m no nl ho hl names holes) (hM : taMR m mp) :
    Sim (taNodeW (k + 1) m no nl lvls ho hl f1 (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0)) (taArm names (decI lvls) holes mp f1.toNat (decE h) v) a
      (TaQ dn fe vis m) := by
  cases v with
  | app f x' =>
    simp only [ViewR, L.getD_one, L.getD_two] at hvr
    obtain ⟨hg, hx, rfl, hy, rfl⟩ := hvr
    rw [hg, taNodeW.arm1 k m no nl lvls ho hl f1 4 _ _ _ rfl]
    exact taBin_ok dn fe vis k ih (fun m a b => mkAppW m a b) internAppE
      (fun m m' a u v r hS hI => mkApp_stage hS u v hI) (fun m m' u v r hI => mkAppW_low hI)
      m a no nl lvls ho hl f1 _ _ _ _ (taNodeW.k_target_abs_go.none ..) (fun _ _ => taNodeW.k_target_abs_go.arm1 ..)
      (fun _ => taNodeW.k_target_abs_go_2.none ..) (fun _ _ _ => taNodeW.k_target_abs_go_2.arm1 ..) names holes mp hS hx hy hlv hI hM
  | lam f x' =>
    simp only [ViewR, L.getD_one, L.getD_two] at hvr
    obtain ⟨hg, hx, rfl, hy, rfl⟩ := hvr
    rw [hg, taNodeW.arm2 k m no nl lvls ho hl f1 5 _ _ _ (by decide) rfl]
    exact taBin_ok dn fe vis k ih (fun m a b => mkLamW m a b) internLamE
      (fun m m' a u v r hS hI => mkLam_stage hS u v hI) (fun m m' u v r hI => mkLamW_low hI)
      m a no nl lvls ho hl f1 _ _ _ _ (taNodeW.k_target_abs_go_3.none ..) (fun _ _ => taNodeW.k_target_abs_go_3.arm1 ..)
      (fun _ => taNodeW.k_target_abs_go_4.none ..) (fun _ _ _ => taNodeW.k_target_abs_go_4.arm1 ..) names holes mp hS hx hy hlv hI hM
  | forallE f x' =>
    simp only [ViewR, L.getD_one, L.getD_two] at hvr
    obtain ⟨hg, hx, rfl, hy, rfl⟩ := hvr
    rw [hg, taNodeW.arm3 k m no nl lvls ho hl f1 6 _ _ _ (by decide) (by decide) rfl]
    exact taBin_ok dn fe vis k ih (fun m a b => mkForallW m a b) internForallEE
      (fun m m' a u v r hS hI => mkForall_stage hS u v hI) (fun m m' u v r hI => mkForallW_low hI)
      m a no nl lvls ho hl f1 _ _ _ _ (taNodeW.k_target_abs_go_5.none ..) (fun _ _ => taNodeW.k_target_abs_go_5.arm1 ..)
      (fun _ => taNodeW.k_target_abs_go_6.none ..) (fun _ _ _ => taNodeW.k_target_abs_go_6.arm1 ..) names holes mp hS hx hy hlv hI hM
  | letE t v' b' =>
    simp only [ViewR, L.getD_one, L.getD_two, L.getD_three] at hvr
    obtain ⟨hg, hx, rfl, hy, rfl, hz, rfl⟩ := hvr
    rw [hg, taNodeW.arm4 k m no nl lvls ho hl f1 7 _ _ _ (by decide) (by decide) (by decide) rfl]
    exact taLet_ok dn fe vis k ih m a no nl lvls ho hl f1 _ _ _ names holes mp hS hx hy hz hlv hI hM
  | proj s i e =>
    simp only [ViewR, L.getD_one, L.getD_two, L.getD_three] at hvr
    obtain ⟨hg, hx, rfl, rfl, hz, rfl⟩ := hvr
    rw [hg, taNodeW.arm5 k m no nl lvls ho hl f1 9 _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact taProj_ok dn fe vis k ih m a no nl lvls ho hl f1 _ _ _ names holes mp hS hz hlv hI hM
  | bvar _ | sort _ | const _ _ | lit _ | fvar _ _ => exact False.elim hnv

theorem taTwin_node (names : List NIdx) (lvls : LsIdx) (holes : List EIdx) (memo : Std.HashMap EIdx EIdx)
    (fuel : Nat) (h : EIdx) (a : AState) (v : ENodeView) (hv : a.store.view h = some v) (hnv : NodeVr v) :
    (ConRon.Arena.targetAbsGo names lvls holes memo (fuel + 1) h).run a =
      ((match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← taArm names lvls holes memo fuel h v
          pure (r, m.insert h r) : AM (EIdx × Std.HashMap EIdx EIdx)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | (rw [targetAbsGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind])

theorem taGo_nodeCase (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (j : Nat)
    (ih : ∀ k, k + 1 < j + 1 → TaGoOK dn fe vis k) (m : Mem) (a : AState)
    (no nl lvls ho hl f h : Word) (names : List NIdx) (holes : List EIdx) (mp : Std.HashMap EIdx EIdx) (F : Nat)
    (hF : f.toNat = F + 1) (hf0 : f ≠ 0) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVr v) (hv : a.store.view (decE h) = some v) (hvle : eViewW m h = vl) (hvl : vl ≠ [])
    (hgs : vl.headD 0 = 4 ∨ vl.headD 0 = 5 ∨ vl.headD 0 = 6 ∨ vl.headD 0 = 7 ∨ vl.headD 0 = 9)
    (hS : StageR vis fe m a) (hh : H h) (hlv : H lvls)
    (hI : TaIn m no nl ho hl names holes) (hM : taMR m mp) :
    Sim (taGoW (j + 1) m no nl lvls ho hl f h)
      (ConRon.Arena.targetAbsGo names (decI lvls) holes mp (F + 1) (decE h)) a (TaQ dn fe vis m) := by
  have c0 : vl.headD 0 ≠ 0 := by rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  have c1 : vl.headD 0 ≠ 1 := by rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  have c2 : vl.headD 0 ≠ 2 := by rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  have c8 : vl.headD 0 ≠ 8 := by rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  have c3 : vl.headD 0 ≠ 3 := by rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  subst hvle
  refine L.Ind.Sim.ofRun (taTwin_node _ _ _ _ _ _ a v hv hnv) ?_
  by_cases hfr : mfindG taSch m h 0 = []
  · rw [taGoW.abort3 j m no nl lvls ho hl f h hf0 hvl c0 c1 c2 c8 c3 hfr]; exact Sim.of_none
  by_cases hhit : (mfindG taSch m h 0).headD 0 ≠ 0
  · rw [taGoW.arm6 j m no nl lvls ho hl f h hf0 hvl c0 c1 c2 c8 c3 hfr hhit]
    have hmem := memoRG_hit taSch bmKey (fun w : Word => decE w) m mp hM h 0 hfr hhit ⟨hh, rfl⟩
    change mp[decE h]? = _ at hmem
    simp only [hmem]
    exact Sim.ret ⟨rfl, hS, IWGrow.refl _, hM⟩
  rw [taGoW.arm7 j m no nl lvls ho hl f h hf0 hvl c0 c1 c2 c8 c3 hfr (by simpa using hhit)]
  have hmiss := memoRG_miss taSch bmKey (fun w : Word => decE w) m mp hM h 0 ⟨hh, rfl⟩ hfr (by simpa using hhit)
  change mp[decE h]? = _ at hmiss
  simp only [hmiss]
  cases j with
  | zero => rw [taNodeW.eq_1]; exact Sim.of_none
  | succ k =>
  have hF1 : (f - 1).toNat = F := by rw [L.toNat_sub_one_of_ne hf0, hF]; rfl
  rw [← hF1]
  refine Sim.bindK (taGoW.k_target_abs_node.none _) (fun _ _ => taGoW_kNode ..)
    (taNode_arm dn fe vis k (ih k (by omega)) _ v hvr hnv m a no nl lvls ho hl (f - 1) h names holes mp hS
      hlv hI hM) ?_
  rintro rn ⟨r1, mp1⟩ m1 a1 ⟨rfl, hS1, hg1, hM1⟩
  rcases hset : msetG taSch m1 h 0 rn with _ | m2 <;> simp only [Option.map_none, Option.map_some]
  · exact Sim.of_none
  obtain ⟨hS2, hg2⟩ := L.Ind.StageR.frame_hi hS1 (msetG_frame taSch taSch_wf m1 m2 h 0 rn hset)
    (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp [taSch] at hx; subst hx; decide) (by decide) (by simp [taSch])
  exact Sim.ret ⟨rfl, hS2, hg1.trans hg2,
    memoRG_set taSch taSch_wf bmKey (fun w : Word => decE w) m1 mp1 hM1 h 0 rn ⟨hh, rfl⟩ m2 hset⟩

theorem taGo_step_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (j : Nat)
    (ih : ∀ k, k + 1 < j + 1 → TaGoOK dn fe vis k) : TaGoOK dn fe vis (j + 1) := by
  intro m a no nl lvls ho hl f h names holes mp hS hh hlv hI hM
  by_cases hf0 : f = 0
  · rw [taGoW.abort1 j m no nl lvls ho hl f h hf0]; exact Sim.of_none
  obtain ⟨F, hF⟩ : ∃ F, f.toNat = F + 1 := ⟨f.toNat - 1, by have := L.toNat_ne_zero_of_ne _ hf0; omega⟩
  rw [hF]
  cases hvl : eViewW m h with
  | nil => rw [taGoW.abort2 j m no nl lvls ho hl f h hf0 hvl]; exact Sim.of_none
  | cons g vt =>
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hS.check.arena.base h (by rw [hvl]; simp)
    rw [hvl] at hvr
    cases v with
    | bvar _ | sort _ | lit _ | fvar _ _ =>
      rw [targetAbsGo_succ']
      refine Sim.bind_twin (view_run _ a _ hv) ?_
      simp only [ViewR] at hvr
      rw [taGoW_leaf j m no nl lvls ho hl f h hf0 (by rw [hvl]; simp) (by
        rw [hvl]
        first | exact Or.inl hvr.1 | exact Or.inr (Or.inl hvr.1) | exact Or.inr (Or.inr (Or.inl hvr.1)) | exact Or.inr (Or.inr (Or.inr hvr)))]
      exact Sim.ret ⟨rfl, hS, IWGrow.refl _, hM⟩
    | const nn' us' =>
      simp only [ViewR, L.getD_one, L.getD_two] at hvr
      obtain ⟨hg3, hx, hdx, hy, hdy⟩ := hvr
      rw [taGoW.arm5 j m no nl lvls ho hl f h hf0 (by rw [hvl]; simp) (by rw [hvl, hg3]; decide)
        (by rw [hvl, hg3]; decide) (by rw [hvl, hg3]; decide) (by rw [hvl, hg3]; decide) (by rw [hvl]; exact hg3),
        hvl, targetAbsGo_succ']
      refine Sim.bind_twin (view_run _ a _ hv) ?_
      intro r m' hb
      obtain ⟨rfl, hr⟩ := taCW_ok j hb hlv hx hy hI.1 (hS.lt64 hI.2.1) hI.2.2.1 (hS.lt64 hI.2.2.2)
      exact ⟨_, a, rfl, by rw [hr, ← hdx, ← hdy], hS, IWGrow.refl _, hM⟩
    | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ | proj _ _ _ =>
      exact taGo_nodeCase dn fe vis j ih m a no nl lvls ho hl f h names holes mp F hF hf0 _ _ hvr trivial hv
        hvl (by simp) (by have := hvr.1; simp only [List.headD_cons] at this ⊢; simp [this]) hS hh hlv hI hM

theorem taGoOK (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) : TaGoOK dn fe vis n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero =>
      intro m a no nl lvls ho hl f h names holes mp; rw [taGoW.eq_1]; exact fun _ _ _ _ _ => Sim.of_none
    | succ j => exact taGo_step_ok dn fe vis j (fun k hk => ih k (by omega))

theorem taAW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl lvls ho hl e r : Word) (names : List NIdx) (holes : List EIdx)
    (mp0 : Std.HashMap EIdx EIdx)
    (hb : taAW n m no nl lvls ho hl e = some (r, m')) (hS : StageR vis fe m a) (he : H e) (hlv : H lvls)
    (hdec : decHL m no.toNat nl.toNat = some names) (hit : no.toNat + nl.toNat ≤ iwTop m)
    (hho : decHL m ho.toNat hl.toNat = some holes) (hht : ho.toNat + hl.toNat ≤ iwTop m) (hM : taMR m mp0) :
    ∃ a' mp1, (ConRon.Arena.targetAbs names (decI lvls) holes (decE e)).run a = .ok (decE r, a') ∧
      taMR m' mp1 ∧ StageR vis fe m' a' ∧ IWGrow m m' := by
  by_cases h0 : rdW (m.arr64 CTL) taSch.cs + 2 = 0
  · simp [taAW, h0] at hb
  rw [taAW.arm1 n m no nl lvls ho hl e h0] at hb
  have hf0 := mclearG_frame taSch m
  have hM0 := memoRG_clear taSch taSch_wf bmKey (fun w : Word => decE w) m mp0 hM h0
  obtain ⟨hS0, hg0⟩ := L.Ind.StageR.frame_hi hS hf0 (by intro b hb; simp at hb)
    (by intro x hx; simp [taSch] at hx; rcases hx with rfl | rfl <;> decide) (by simp) (by simp [taSch])
  obtain ⟨⟨t, mp1⟩, a1, hrun, rfl, hS1, hg1, hM1⟩ := taGoOK dn fe vis n _ a no nl lvls ho hl CWF e names holes ∅
    hS0 he hlv (TaIn.grow ⟨hdec, hit, hho, hht⟩ hg0) hM0 _ _ hb
  rw [CWF_eq] at hrun
  refine ⟨a1, mp1, ?_, hM1, hS1, hg0.trans hg1⟩
  simp only [ConRon.Arena.targetAbs, StateT.run_bind]
  rw [hrun]
  rfl

end L.Ind

end
