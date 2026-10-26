import ConAgua.Arena.RecCheckSpec9
import ConAgua.Arena.IndRealWalk

/-!
# `RecCheck`: `targetParamsDefEq` (lane `indproofs3`, helper `rec`)

The per-component parameter defeq: a step (`target_params_def_eq_step`: the closedness test, the
canon forms, the member abstraction, syntactic or inferred-and-defeq) and the recursion over both
slices (`target_params_def_eq`, rewritten to the twin's list recursion: lists of different lengths
are compared up to the shorter one's end, then `false`; before, L answered `false` up front, which
skipped the twin's callees and so its failures). Callees: `bvar_b` (lane `exprops4`'s real function
at the twin's `coreWalkFuel`, any exec fuel: `bvbW_stageC`), `fvar_b`, `infer_type_core`,
`is_def_eq_core` (stubs), `target_canon_params` (`RecCheckSpec9`), `target_abs` (helper `rec3`'s,
with its write set `taAW_mfr`, new here). L: handle guards after both `target_abs` calls (the
model carries no `< 2^32` bound on the result; the twin compares `EIdx`s).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `target_abs`' write set -/

theorem taCW_same {n : Nat} {m m' : Mem} {no nl lvls ho hl hh nn vus r : Word}
    (h : taCW n m no nl lvls ho hl hh nn vus = some (r, m')) : m' = m := by
  cases n with
  | zero => simp [taCW] at h
  | succ n =>
    simp only [taCW] at h
    by_cases hv : vus ≠ lvls
    · rw [ite_eq_left hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
    rw [ite_eq_right hv] at h
    rcases hf : findW n m no nl nn with _ | fr <;> rw [hf] at h <;>
      try (simp only [taCK, reduceCtorEq] at h; done)
    simp only [taCK] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
    split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm)

theorem taGoW_mfr (n : Nat) :
    (∀ (m m' : Mem) (no nl lvls ho hl f h r : Word), taGoW n m no nl lvls ho hl f h = some (r, m') →
      MFr [TAM] [212, 213] m m') ∧
    (∀ (m m' : Mem) (no nl lvls ho hl f1 g x y z r : Word),
      taNodeW n m no nl lvls ho hl f1 g x y z = some (r, m') → MFr [TAM] [212, 213] m m') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ _ h => by simp [taGoW] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [taNodeW] at h⟩
  | succ j =>
  have ihG : ∀ (m m' : Mem) (no nl lvls ho hl f h r : Word), taGoW j m no nl lvls ho hl f h = some (r, m') →
      MFr [TAM] [212, 213] m m' := (ih j (by omega)).1
  refine ⟨?_, ?_⟩
  · intro m m' no nl lvls ho hl f h r hg
    by_cases hf : f = 0
    · rw [taGoW_abort (hf := hf)] at hg; simp at hg
    rw [taGoW_view (hf := hf)] at hg
    unfold taG1 at hg
    split at hg; · simp at hg
    split at hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact MFr.refl _ _ _
    split at hg
    · rw [taCW_same hg]; exact MFr.refl _ _ _
    unfold taG3 at hg
    split at hg; · simp at hg
    split at hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact MFr.refl _ _ _
    cases hn : taNodeW j m no nl lvls ho hl (f - 1) _ _ _ _ with
    | none => rw [hn] at hg; simp [taG4] at hg
    | some pr =>
      obtain ⟨rn, m1⟩ := pr
      rw [hn, taG4_some] at hg
      rcases hs : msetG taSch m1 h 0 rn with _ | m2 <;> simp only [hs, taG5, reduceCtorEq] at hg
      simp only [Option.some.injEq, Prod.mk.injEq] at hg
      rw [← hg.2]
      cases j with
      | zero => simp [taNodeW] at hn
      | succ i =>
        exact ((ih (i + 1) (by omega)).2 _ _ _ _ _ _ _ _ _ _ _ _ _ hn).trans
          ⟨_, _, msetG_frame taSch taSch_wf m1 m2 h 0 rn hs, by simp [taSch, TAM], by simp [taSch]⟩
  · intro m m' no nl lvls ho hl f1 g x y z r hn
    unfold taNodeW at hn
    split at hn
    · rcases h1 : taGoW j m no nl lvls ho hl f1 x with _ | ⟨a2, m1⟩ <;> simp only [h1, taB1, reduceCtorEq] at hn
      rcases h2 : taGoW j m1 no nl lvls ho hl f1 y with _ | ⟨x2, m2⟩ <;> simp only [h2, taB2, reduceCtorEq] at hn
      exact ((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans (rpMkW_mfr hn).up
    split at hn
    · rcases h1 : taGoW j m no nl lvls ho hl f1 x with _ | ⟨a2, m1⟩ <;> simp only [h1, taL1, reduceCtorEq] at hn
      rcases h2 : taGoW j m1 no nl lvls ho hl f1 y with _ | ⟨x2, m2⟩ <;> simp only [h2, taL2, reduceCtorEq] at hn
      rcases h3 : taGoW j m2 no nl lvls ho hl f1 z with _ | ⟨c2, m3⟩ <;> simp only [h3, taL3, reduceCtorEq] at hn
      exact (((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans
        (ihG _ _ _ _ _ _ _ _ _ _ h3)).trans (rpMkW_mfr hn).up
    · rcases h1 : taGoW j m no nl lvls ho hl f1 z with _ | ⟨a2, m1⟩ <;> simp only [h1, taP1, reduceCtorEq] at hn
      exact (ihG _ _ _ _ _ _ _ _ _ _ h1).trans (rpMkW_mfr hn).up

/-- **`target_abs` writes only its memo** (array `TAM`, `CTL[212]`, `CTL[213]`) besides the stores'
interns. -/
theorem taAW_mfr {n : Nat} {m m' : Mem} {no nl lvls ho hl e r : Word}
    (h : taAW n m no nl lvls ho hl e = some (r, m')) : MFr [TAM] [212, 213] m m' := by
  by_cases h0 : rdW (m.arr64 CTL) taSch.cs + 2 = 0
  · simp [taAW, h0] at h
  rw [taAW_eq n m no nl lvls ho hl e h0] at h
  exact MFr.trans ⟨_, _, mclearG_frame taSch m, by simp, by simp [taSch]⟩ ((taGoW_mfr n).1 _ _ _ _ _ _ _ _ _ _ h)

theorem RcMR.setTa {m m' : Mem} (h : RcMR m) (hf : MFr [TAM] [212, 213] m m') (hn : ∃ mp, taMR m' mp) :
    RcMR m' := ⟨h.pos.mfr hf (by simp [PosAv, NOM, DPM, RAM, HBM, RFM, TAM]), hn⟩

/-! ## Callees at any exec fuel -/

def tcpF : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, pfo, pfl, e => tcpW n m pfo pfl e

def taF : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lvls, ho, hl, e => taAW n m no nl lvls ho hl e

theorem tcp_specF (p : Prog) (L : RcLook p) (n : Nat) (s₀ : St) (pfo pfl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_canon_params" [pfo, pfl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ tcpF n s₀.mem pfo pfl e = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact targetCanonParams_spec p L.rx L.r3 L.tcp n s₀ pfo pfl e

theorem ta_specF (p : Prog) (L : TaLook p) (n : Nat) (s₀ : St) (no nl lvls ho hl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_abs" [no, nl, lvls, ho, hl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ taF n s₀.mem no nl lvls ho hl e = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact targetAbs_spec p L n s₀ no nl lvls ho hl e

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem tcpF_ok (n : Nat) {m m' : Mem} {a : AState} {pfo pfl e : Word} {pfvs : List EIdx} {r : List Word}
    (h : tcpF n m pfo pfl e = some (r, m')) (hS : StageR dn vis fe m a) (hpf : HSl0 m pfo pfl pfvs)
    (he : H e) (hP : RcMR m) :
    ∃ a', (ConRon.Arena.targetCanonParams pfvs (decE e)).run a = .ok (decE (r.headD 0), a') ∧
      H (r.headD 0) ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  cases n with
  | zero => cases h
  | succ n => exact tcpW_ok dn fe vis n h hS hpf he hP

theorem taF_ok (n : Nat) {m m' : Mem} {a : AState} {no nl lvls ho hl e r : Word} {names : List NIdx}
    {holes : List EIdx} (h : taF n m no nl lvls ho hl e = some (r, m')) (hS : StageR dn vis fe m a)
    (he : H e) (hlv : H lvls)
    (hdec : decHL m no.toNat nl.toNat = some names) (hit : no.toNat + nl.toNat ≤ iwTop m)
    (hho : decHL m ho.toNat hl.toNat = some holes) (hht : ho.toNat + hl.toNat ≤ iwTop m) (hP : RcMR m) :
    ∃ a', (ConRon.Arena.targetAbs names (decI lvls) holes (decE e)).run a = .ok (decE r, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  cases n with
  | zero => cases h
  | succ n =>
    obtain ⟨mp, hM⟩ := hP.ta
    obtain ⟨a', mp1, hrun, hM1, hS', hg⟩ :=
      taAW_ok n dn fe vis m m' a no nl lvls ho hl e r names holes mp h hS he hlv hdec hit hho hht hM
    exact ⟨a', hrun, hS', hg, hP.setTa (taAW_mfr h) ⟨mp1, hM1⟩⟩

/-- **`bvar_b` under the stage relation at the twin's `coreWalkFuel`**, at any exec fuel (the L
fuel word `CWF` is `coreWalkFuel`: `bvbW_okF`'s first alternative). -/
theorem bvbW_stageC {m m' : Mem} {a : AState} (hS : StageR dn vis fe m a) (n : Nat)
    (h x : Word) (hh : H h) (hb : bvbW n m h CWF = some (x, m')) :
    ∃ a', (bvarB coreWalkFuel (decE h)).run a = .ok (x.toNat, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      MFr [] [] m m' := by
  obtain ⟨a', hrun, hD⟩ := bvbW_okF n coreWalkFuel m m' a hS.1.arena h CWF x hh (.inl (Nat.le_of_eq CWF_eq)) hb
  have hfr : BbFrame m m' := by
    match n, hb with
    | n + 1, hb =>
      by_cases hs : derBW m h = 32767
      · rw [bvbW_sat (n := n) (m := m) (h := h) (f := CWF) hs] at hb
        match n, hb with
        | k + 1, hb => rw [bbN_succ] at hb; exact bbMemoW_frame k m m' h CWF x hb
      · rw [bvbW_pk (n := n) (m := m) (h := h) (f := CWF) hs] at hb
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
        exact MemFrame.refl _ _ _
  have hk : sp a' = sp a := by
    rw [bvarB_run] at hrun
    split at hrun
    · exact (keeps_bvarBoundMemo coreWalkFuel (decE h)).run hrun
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun; rw [hrun.2]
  have hcp : cp a' = cp a := by simp only [sp, Prod.mk.injEq] at hk; simp [cp, hk.2.1, hk.2.2]
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hD hfr (by simp [BMEMO]) (by
    intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide) hcp
  exact ⟨a', hrun, hS', hg, bvbW_mfr hb⟩

end rel

/-! ## `target_params_def_eq_step`: the word model -/

def pdsK11 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

def pdsK10 (cR : CallM) (n : Nat) (vis d av bv : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => pdsK11 (cR n "is_def_eq_core" [vis, d, av, bv] m)

def pdsK9 (cR : CallM) (n : Nat) (vis d av bv : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => pdsK10 cR n vis d av bv (cR n "infer_type_core" [vis, d, bv] m)

def pdsK8 (cR : CallM) (n : Nat) (vis d av : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (bv, m) =>
    if 4294967296 ≤ bv then none
    else if av = bv then some ([1], m)
    else pdsK9 cR n vis d av bv (cR n "infer_type_core" [vis, d, av] m)

def pdsK7 (cR : CallM) (n : Nat) (vis d no nl lvls ho hl av : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => pdsK8 cR n vis d av (taF n m no nl lvls ho hl (r.headD 0))

def pdsK6 (cR : CallM) (n : Nat) (vis d no nl lvls ho hl pfo pfl b : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (av, m) =>
    if 4294967296 ≤ av then none else pdsK7 cR n vis d no nl lvls ho hl av (tcpF n m pfo pfl b)

def pdsK5 (cR : CallM) (n : Nat) (vis d no nl lvls ho hl pfo pfl b : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => pdsK6 cR n vis d no nl lvls ho hl pfo pfl b (taF n m no nl lvls ho hl (r.headD 0))

def pdsK4 (cR : CallM) (n : Nat) (vis d no nl lvls ho hl pfo pfl a b : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if pfl < r.headD 0 then some ([0], m) else pdsK5 cR n vis d no nl lvls ho hl pfo pfl b (tcpF n m pfo pfl a)

def pdsK3 (cR : CallM) (n : Nat) (vis d no nl lvls ho hl pfo pfl a b : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if pfl < r.headD 0 then some ([0], m)
    else pdsK4 cR n vis d no nl lvls ho hl pfo pfl a b (fvbF m [CWF, b])

def pdsK2 (cR : CallM) (n : Nat) (vis d no nl lvls ho hl pfo pfl a b : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (x, m) =>
    if x ≠ 0 then some ([0], m) else pdsK3 cR n vis d no nl lvls ho hl pfo pfl a b (fvbF m [CWF, a])

def pdsK1 (cR : CallM) (n : Nat) (vis d no nl lvls ho hl pfo pfl a b : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (x, m) =>
    if x ≠ 0 then some ([0], m) else pdsK2 cR n vis d no nl lvls ho hl pfo pfl a b (bvbW n m b CWF)

/-- **The model of `target_params_def_eq_step`** (body fuel `n`). -/
def pdsW (cR : CallM) (n : Nat) (m : Mem) (vis d no nl lvls ho hl pfo pfl a b : Word) : Option (List Word × Mem) :=
  pdsK1 cR n vis d no nl lvls ho hl pfo pfl a b (bvbW n m a CWF)

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis d no nl lvls ho hl pfo pfl a b av bv x : Word) (r : List Word)
theorem pdsK11_some : pdsK11 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem pdsK10_some : pdsK10 cR n vis d av bv (some (r, m)) = pdsK11 (cR n "is_def_eq_core" [vis, d, av, bv] m) := rfl
theorem pdsK9_some : pdsK9 cR n vis d av bv (some (r, m)) =
    pdsK10 cR n vis d av bv (cR n "infer_type_core" [vis, d, bv] m) := rfl
theorem pdsK8_big (h : 4294967296 ≤ bv) : pdsK8 cR n vis d av (some (bv, m)) = none := by simp [pdsK8, h]
theorem pdsK8_eq (h : ¬ 4294967296 ≤ bv) (he : av = bv) : pdsK8 cR n vis d av (some (bv, m)) = some ([1], m) := by
  simp [pdsK8, h, he]
theorem pdsK8_ne (h : ¬ 4294967296 ≤ bv) (he : ¬ av = bv) : pdsK8 cR n vis d av (some (bv, m)) =
    pdsK9 cR n vis d av bv (cR n "infer_type_core" [vis, d, av] m) := by simp [pdsK8, h, he]
theorem pdsK7_some : pdsK7 cR n vis d no nl lvls ho hl av (some (r, m)) =
    pdsK8 cR n vis d av (taF n m no nl lvls ho hl (r.headD 0)) := rfl
theorem pdsK6_big (h : 4294967296 ≤ av) : pdsK6 cR n vis d no nl lvls ho hl pfo pfl b (some (av, m)) = none := by
  simp [pdsK6, h]
theorem pdsK6_ok (h : ¬ 4294967296 ≤ av) : pdsK6 cR n vis d no nl lvls ho hl pfo pfl b (some (av, m)) =
    pdsK7 cR n vis d no nl lvls ho hl av (tcpF n m pfo pfl b) := by simp [pdsK6, h]
theorem pdsK5_some : pdsK5 cR n vis d no nl lvls ho hl pfo pfl b (some (r, m)) =
    pdsK6 cR n vis d no nl lvls ho hl pfo pfl b (taF n m no nl lvls ho hl (r.headD 0)) := rfl
theorem pdsK4_out (h : pfl < r.headD 0) : pdsK4 cR n vis d no nl lvls ho hl pfo pfl a b (some (r, m)) =
    some ([0], m) := by simp only [pdsK4]; rw [ite_eq_left h]
theorem pdsK4_ok (h : ¬ pfl < r.headD 0) : pdsK4 cR n vis d no nl lvls ho hl pfo pfl a b (some (r, m)) =
    pdsK5 cR n vis d no nl lvls ho hl pfo pfl b (tcpF n m pfo pfl a) := by simp only [pdsK4]; rw [ite_eq_right h]
theorem pdsK3_out (h : pfl < r.headD 0) : pdsK3 cR n vis d no nl lvls ho hl pfo pfl a b (some (r, m)) =
    some ([0], m) := by simp only [pdsK3]; rw [ite_eq_left h]
theorem pdsK3_ok (h : ¬ pfl < r.headD 0) : pdsK3 cR n vis d no nl lvls ho hl pfo pfl a b (some (r, m)) =
    pdsK4 cR n vis d no nl lvls ho hl pfo pfl a b (fvbF m [CWF, b]) := by simp only [pdsK3]; rw [ite_eq_right h]
theorem pdsK2_b (h : x ≠ 0) : pdsK2 cR n vis d no nl lvls ho hl pfo pfl a b (some (x, m)) = some ([0], m) := by
  simp [pdsK2, h]
theorem pdsK2_ok (h : ¬ x ≠ 0) : pdsK2 cR n vis d no nl lvls ho hl pfo pfl a b (some (x, m)) =
    pdsK3 cR n vis d no nl lvls ho hl pfo pfl a b (fvbF m [CWF, a]) := by simp [pdsK2, h]
theorem pdsK1_b (h : x ≠ 0) : pdsK1 cR n vis d no nl lvls ho hl pfo pfl a b (some (x, m)) = some ([0], m) := by
  simp [pdsK1, h]
theorem pdsK1_ok (h : ¬ x ≠ 0) : pdsK1 cR n vis d no nl lvls ho hl pfo pfl a b (some (x, m)) =
    pdsK2 cR n vis d no nl lvls ho hl pfo pfl a b (bvbW n m b CWF) := by simp [pdsK1, h]
end arms
attribute [ind_grind] pdsK11_some pdsK10_some pdsK9_some pdsK8_big pdsK8_eq pdsK8_ne pdsK7_some pdsK6_big
  pdsK6_ok pdsK5_some pdsK4_out pdsK4_ok pdsK3_out pdsK3_ok pdsK2_b pdsK2_ok pdsK1_b pdsK1_ok

/-- The lookups of `target_params_def_eq`. -/
structure TpLook (p : Prog) : Prop where
  rc : RcLook p
  ta : TaLook p
  bvb : BvbProg p
  hf : HfF p
  step : p.lookup "target_params_def_eq_step" = some targetParamsDefEqStep
  tpd : p.lookup "target_params_def_eq" = some targetParamsDefEq

set_option maxHeartbeats 2000000 in
theorem tpdStep_spec (p : Prog) (L : TpLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (vis d no nl lvls ho hl pfo pfl a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_params_def_eq_step"
      [vis, d, no, nl, lvls, ho, hl, pfo, pfl, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ pdsW cR n s₀.mem vis d no nl lvls ho hl pfo pfl a b = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.step]
  simp only [callFn, targetParamsDefEqStep]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bvarBL_spec p L.bvb n, fvbF_spec p L.hf n, tcp_specF p L.rc n, ta_specF p L.ta n,
      hcR n "infer_type_core", hcR n "is_def_eq_core"] <;>
    finish (gen := 40) (instances := 20000) [pdsW, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9, loc_init10, loc_init11]

/-! ## `target_params_def_eq`: the word model -/

def pdsF (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, d, no, nl, lvls, ho, hl, pfo, pfl, a, b => pdsW cR n m vis d no nl lvls ho hl pfo pfl a b

mutual
def pdeW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, d, no, nl, lvls, ho, hl, pfo, pfl, ao, al, bo, bl =>
    if al = 0 then some ([if bl = 0 then 1 else 0], m)
    else if bl = 0 then some ([0], m)
    else pdeK1 cR n vis d no nl lvls ho hl pfo pfl ao al bo bl
      (pdsF cR n m vis d no nl lvls ho hl pfo pfl (rdW (m.arr64 IW) ao) (rdW (m.arr64 IW) bo))
def pdeK1 (cR : CallM) (n : Nat) (vis d no nl lvls ho hl pfo pfl ao al bo bl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0], m1)
    else pdsK11 (pdeW cR n m1 vis d no nl lvls ho hl pfo pfl (ao + 1) (al - 1) (bo + 1) (bl - 1))
end

section arms
variable (cR : CallM) (n : Nat) (m m1 : Mem) (vis d no nl lvls ho hl pfo pfl ao al bo bl : Word) (r : List Word)
theorem pdeW_nil (h : al = 0) : pdeW cR (n + 1) m vis d no nl lvls ho hl pfo pfl ao al bo bl =
    some ([if bl = 0 then 1 else 0], m) := by simp [pdeW, h]
theorem pdeW_nilr (h : ¬ al = 0) (hb : bl = 0) : pdeW cR (n + 1) m vis d no nl lvls ho hl pfo pfl ao al bo bl =
    some ([0], m) := by simp [pdeW, h, hb]
theorem pdeW_cons (h : ¬ al = 0) (hb : ¬ bl = 0) : pdeW cR (n + 1) m vis d no nl lvls ho hl pfo pfl ao al bo bl =
    pdeK1 cR n vis d no nl lvls ho hl pfo pfl ao al bo bl
      (pdsF cR n m vis d no nl lvls ho hl pfo pfl (rdW (m.arr64 IW) ao) (rdW (m.arr64 IW) bo)) := by
  simp [pdeW, h, hb]
theorem pdeK1_stop (h : r.headD 0 = 0) : pdeK1 cR n vis d no nl lvls ho hl pfo pfl ao al bo bl (some (r, m1)) =
    some ([0], m1) := by simp only [pdeK1]; rw [ite_eq_left h]
theorem pdeK1_go (h : ¬ r.headD 0 = 0) : pdeK1 cR n vis d no nl lvls ho hl pfo pfl ao al bo bl (some (r, m1)) =
    pdsK11 (pdeW cR n m1 vis d no nl lvls ho hl pfo pfl (ao + 1) (al - 1) (bo + 1) (bl - 1)) := by simp only [pdeK1]; rw [ite_eq_right h]
end arms
attribute [ind_grind] pdeW_nil pdeW_nilr pdeW_cons pdeK1_stop pdeK1_go

theorem pdsF_spec (p : Prog) (L : TpLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (vis d no nl lvls ho hl pfo pfl a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_params_def_eq_step"
      [vis, d, no, nl, lvls, ho, hl, pfo, pfl, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ pdsF cR n s₀.mem vis d no nl lvls ho hl pfo pfl a b = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact tpdStep_spec p L cR hcR n s₀ vis d no nl lvls ho hl pfo pfl a b

theorem tpd_spec (p : Prog) (L : TpLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) :
    ∀ (s₀ : St) (vis d no nl lvls ho hl pfo pfl ao al bo bl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_params_def_eq"
      [vis, d, no, nl, lvls, ho, hl, pfo, pfl, ao, al, bo, bl]
    ⦃fun r s' => LocEq s' s₀ ∧
      pdeW cR n s₀.mem vis d no nl lvls ho hl pfo pfl ao al bo bl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis d no nl lvls ho hl pfo pfl ao al bo bl
    rw [invoke_eq _ L.tpd]; simp only [callFn, targetParamsDefEq]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis d no nl lvls ho hl pfo pfl ao al bo bl
    rw [invoke_eq _ L.tpd]
    simp only [callFn, targetParamsDefEq]
    sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, pdsF_spec p L cR hcR n, ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9, loc_init10,
        loc_init11, loc_init12]

end L.Ind
