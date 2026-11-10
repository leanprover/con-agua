module

public import ConAgua.Arena.IndPosSpec.DepthGo
public import ConAgua.Arena.IndPosSpec.NoConstWf
import ConAgua.Arena.IndPosSpec.SnocWStage
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPosSpec.InstW
import ConAgua.Arena.IndPosSpec.NestKeyMap
import ConAgua.Arena.LdRd
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.IndPosSpec.Pos2CvLpsWStage
import all ConAgua.Arena.IndPos2
import ConAgua.Arena.IndPosSpec.RootHoles

@[expose] public section

/-!
# NestHoles: `ConRon.Arena.nestHoles.go`, `ConRon.Arena.nestHoles`

The refinement theorems `nestHoles_refines`, `nestHolesGo_refines` and the lemmas only they use.
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
variable (k : Nat) (m3 : Mem) (ctx mm off l oo ol v : Word)
theorem nhK3_big (h : 4294967296 ≤ v) : nhK3 k ctx mm off l oo ol (some (v, m3)) = none := by
  rw [nhK3, ite_eq_left h]
end arms
attribute [ind_grind] nhK3_big

theorem nhGo_spec (p : Prog) (hl : NhLook p) (k : Nat) :
    ∀ (s₀ : St) (ctx mm off l oo ol : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_holes_go" [ctx, mm, off, l, oo, ol]
    ⦃fun r s' => LocEq s' s₀ ∧ nhGoW k s₀.mem ctx mm off l oo ol =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ ctx mm off l oo ol
    rw [invoke_eq _ hl.hgo]; simp only [callFn, nestHolesGoL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ ctx mm off l oo ol
    simp only [invoke_eq _ hl.hgo, callFn, nestHolesGoL]
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, ld64,
      instPisWith_spec p hl.hv hl.hip hl.hi1 k,
      internFVar_spec p hl.hff hl.hfp hl.hif k, slSnoc_specW p hl.ha hl.hc hl.hsn k, ih]
    all_goals subst_vars
    -- locals resolved by `simp` before `grind` (the `sym … finish` form: 6.5 s)
    all_goals (try simp only [LocEq] at *)
    all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
      reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
    all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq, erRd_get]

theorem nestHoles_spec (p : Prog) (hl : NhLook p) (k : Nat) (s₀ : St) (ctx : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_holes" [ctx]
    ⦃fun r s' => LocEq s' s₀ ∧
      nhW k s₀.mem ctx = some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hl.hp, callFn, nestHolesL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, nhGo_spec p hl k] <;>
    finish (gen := 20) [nhW, rdW_eq]

/-- The params slice's end, as the words L reads. -/
theorem ctx_params_end {m : Mem} {p : Word} {c : NestCtx} (hc : decCtx m p.toNat = some c)
    (hin : CtxIn m p.toNat (· < iwTop m)) (hsl : CtxSl m p.toNat) (hsz : iwTop m < 2 ^ 64) :
    (rdW (m.arr64 IW) (p + 7)).toNat + (rdW (m.arr64 IW) (p + 8)).toNat ≤ iwTop m := by
  obtain ⟨-, -, -, -, hpa, -⟩ := decCtx_some hc
  obtain ⟨o7, l7, ho7, hl7, -⟩ := decAt_some hpa
  have h11 := hin.1 10 (by omega)
  have r7 : (rdW (m.arr64 IW) (p + 7)).toNat = o7 := rd_iwN (by simpa using ho7) (by simp; omega)
  have r8 : (rdW (m.arr64 IW) (p + 8)).toNat = l7 := rd_iwN (by simpa using hl7) (by simp; omega)
  rw [r7, r8]; exact hsl 7 (by omega) o7 l7 ho7 hl7

theorem nhGoW_ok (fe : IFEnv) (vis ctx : Word) (c : NestCtx) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (mm off l oo ol : Word) (ns : List NIdx) (out : List EIdx) (r : List Word),
    nhGoW k m ctx mm off l oo ol = some (r, m') → StageR vis fe m a →
    decCtx m ctx.toNat = some c → CtxIn m ctx.toNat (· < iwTop m) → CtxSl m ctx.toNat →
    decHL m off.toNat l.toNat = some ns → (∀ j < l.toNat, off.toNat + j < iwTop m) →
    decHL m oo.toNat ol.toNat = some out → oo.toNat + ol.toNat ≤ iwTop m →
    c.nP + mm.toNat + l.toNat < 2 ^ 64 →
    ∃ x a', (ConRon.Arena.nestHoles.go c mm.toNat ns out).run a = .ok (x, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ NhOut m' r x := by
  induction k with
  | zero => intro m m' a mm off l oo ol ns out r h; simp [nhGoW] at h
  | succ k ih =>
    intro m m' a mm off l oo ol ns out r h hS hc hin hsl hns hnb hout hob hmm
    have hsz := hS.iw.iwSize
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hsz
    by_cases hl0 : l = 0
    · rw [nhGoW_nil (h := hl0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl0
      have : ns = [] := by simpa [decHL, hslice?] using hns.symm
      subst this
      exact ⟨some out, a, by rw [ConRon.Arena.nestHoles.go]; rfl, hS, IWGrow.refl _, rfl, hout, hob⟩
    have hl : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hns2 := hns
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hns2
    obtain ⟨nn, hnn, ns', hns', rfl⟩ := hns2
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      word_add_toNat (show off.toNat + 1 < 2 ^ 64 by have := hnb 0 (by omega); omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hmm1 : (mm + 1).toNat = mm.toNat + 1 := word_add_toNat (by simp; omega)
    rw [ConRon.Arena.nestHoles.go.eq_2]
    -- the member's former
    obtain ⟨-, -, -, -, -, -, -, hfo⟩ := decCtx_some hc
    obtain ⟨fo, fl, hfo1, hfl1, hfos⟩ := decAt_some hfo
    have h12 := hin.1 12 (by omega)
    have r11 : (rdW (m.arr64 IW) (ctx + 11)).toNat = fo := rd_iwN (by simpa using hfo1) (by simp; omega)
    have r12 : (rdW (m.arr64 IW) (ctx + 12)).toNat = fl := rd_iwN (by simpa using hfl1) (by simp; omega)
    have hflen := decPL_length (m := m) hfos
    by_cases hb12 : rdW (m.arr64 IW) (ctx + 12) ≤ mm
    · rw [nhGoW_nof (h := hl0) (h12 := hb12)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : c.formers[mm.toNat]? = none :=
        List.getElem?_eq_none (by rw [hflen, ← r12]; exact UInt64.le_iff_toNat_le.mp hb12)
      exact ⟨none, a, by rw [this]; rfl, hS, IWGrow.refl _, rfl⟩
    rw [nhGoW_cons (h := hl0) (h12 := hb12)] at h
    have hmmf : mm.toNat < fl := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hb12); omega
    have hfx := mapM_opt_get _ _ _ hfos mm.toNat (by simpa using hmmf)
    simp only [List.getElem_range, Option.bind_eq_bind, Option.bind_eq_some_iff] at hfx
    obtain ⟨q, hq, hcvq⟩ := hfx
    have hfoin : fo + mm.toNat < iwTop m := hin.2 11 (by omega) fo fl (by simpa using hfo1) (by simpa using hfl1) _ hmmf
    have eq : (rdW (m.arr64 IW) (ctx + 11) + mm).toNat = fo + mm.toNat := by
      rw [word_add_toNat (by omega), r11]
    have rq : (rdW (m.arr64 IW) (rdW (m.arr64 IW) (ctx + 11) + mm)).toNat = q := by
      have := rd_iwN (m := m) (p := rdW (m.arr64 IW) (ctx + 11) + mm) (i := 0) (by simpa [eq] using hq)
        (by simp; omega)
      simpa using this
    obtain ⟨w, hw, hwH', hwd'⟩ := hd?_some (decCV_type hcvq)
    have e3 : (rdW (m.arr64 IW) (rdW (m.arr64 IW) (ctx + 11) + mm) + 3).toNat = q + 3 := by
      rw [word_add_toNat (by have := erecP_lt64 hw; simp; omega), rq]; rfl
    have hrw : erRd m (rdW (m.arr64 IW) (rdW (m.arr64 IW) (ctx + 11) + mm) + 3) = w :=
      erRd_of_erA (by rw [e3]; exact hw)
    rw [hrw] at h
    have hgf : c.formers[mm.toNat]? = some (c.formers[mm.toNat]'(by rw [hflen]; exact hmmf)) :=
      List.getElem?_eq_getElem _
    rw [hgf]
    generalize c.formers[mm.toNat]'(by rw [hflen]; exact hmmf) = cv at hcvq hwd'
    -- the former's type at the parameters
    obtain ⟨hnames, hnamesb, hpa, hpab, hnP, -, -, -, -, h11⟩ := ctx_fields hc hin htop
    have hpe := ctx_params_end hc hin hsl htop
    rcases hinst : instW k m (rdW (m.arr64 IW) (ctx + 7)) (rdW (m.arr64 IW) (ctx + 8)) w with _ | ⟨r2, m2⟩ <;> rw [hinst] at h; · simp [nhK2] at h
    obtain ⟨x, a2, hrun2, hS2, hg2, hx⟩ := instW_ok k (fun _ => none) fe vis m m2 a _ _ w c.params r2 hinst hS hwH' hpa
      (by omega) hpe
    simp only
    rw [hwd']
    have hRm2 : RdS m m2 (· < iwTop m) := RdS.of_grow hg2
    cases x with
    | none =>
      have : r2.headD 0 = 0 := hx
      rw [nhK2_none (h := this)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨none, a2, by simp only [StateT.run_bind, hrun2, except_ok_bind]; rfl, hS2, hg2, rfl⟩
    | some t =>
    obtain ⟨hx1, htH, htd⟩ := hx
    rw [nhK2_some (h := by rw [hx1]; decide)] at h
    have hnP2 : (rdW (m2.arr64 IW) (ctx + 4)).toNat = c.nP := by
      have : rdW (m2.arr64 IW) (ctx + 4) = rdW (m.arr64 IW) (ctx + 4) := by
        have e : (ctx + 4).toNat = ctx.toNat + 4 := word_add_toNat (by simp; omega)
        simp only [rdW, e]; rw [hg2.iwGet _ (by omega)]
      rw [this, hnP]
    have hu : (rdW (m2.arr64 IW) (ctx + 4) + mm).toNat = c.nP + mm.toNat := by
      rw [word_add_toNat (by rw [hnP2]; omega), hnP2]
    rcases hfv : fvinternW m2 (rdW (m2.arr64 IW) (ctx + 4) + mm) (r2.tail.headD 0) with _ | ⟨v, m3⟩ <;> rw [hfv] at h; · simp [nhK3] at h
    obtain ⟨a3, hrun3, hS3, hg3⟩ := internFVar_stage hS2 _ _ htH hfv
    by_cases hvb : 4294967296 ≤ v
    · rw [nhK3_big (h := hvb)] at h; simp at h
    rw [nhK3_ok (h := hvb)] at h
    have hvlt := lt_of_notbig hvb
    have hg23 := hg2.trans hg3
    have hout3 : decHL m3 oo.toNat ol.toNat = some out := by
      rw [decHL_agree (RdS.of_grow hg23) (fun j hj => by omega)]; exact hout
    rcases hsn : snocW k m3 oo ol v with _ | ⟨r4, m4⟩ <;> rw [hsn] at h; · simp [nhK4] at h
    rw [nhK4_some] at h
    obtain ⟨hr4, hdec4, hg4, -, hol1, ht4⟩ := snocW_dec hsn hS3.iw.iwSize hS3.iw.ctl
      (by have := hg23.iw; omega) hvlt hout3
    have hS4 := snocW_stage hsn hS3
    subst hr4
    simp only [List.headD_cons, List.tail_cons] at h
    have hg24 := hg23.trans hg4
    obtain ⟨xr, a', hrun, hS', hg', hout'⟩ := ih m4 m' a3 (mm + 1) (off + 1) (l - 1) _ _ ns' (out ++ [decI v]) r h
      hS4 ((CtxIn.grow hin hg24).1 hc) (CtxIn.grow hin hg24).2 (hsl.grow hin hg24)
      (by rw [hoff1, hl1, decHL_agree (RdS.of_grow hg24) (fun j hj => by
            have := hnb (j + 1) (by omega); omega)]; simpa [decHL] using hns')
      (fun j hj => by rw [hoff1, hl1] at *; have := hnb (j + 1) (by omega); have := hg24.iw; omega)
      hdec4 (by omega) (by rw [hmm1, hl1]; omega)
    refine ⟨xr, a', ?_, hS', hg24.trans hg', hout'⟩
    simp only [StateT.run_bind, hrun2, except_ok_bind]
    simp only [internFVarE]
    rw [← hu, ← htd, ← decE_eq, hrun3]
    simp only [except_ok_bind]
    rw [hmm1] at hrun
    exact hrun

section census
variable (p : Prog) (hl : NhLook p)
include hl

/-- **`nest_holes` refines `nestHoles`** (through `inst_pis_with`'s stub; the ctx's slices end below
the top and `nP + |names| < 2^64`). -/
@[refines ConRon.Arena.nestHoles]
theorem nestHoles_refines (k : Nat) (s₀ : St) (a₀ : AState)
    (fe : IFEnv) (vis ctx : Word) (c : NestCtx) (hS : StageR vis fe s₀.mem a₀)
    (hc : decCtx s₀.mem ctx.toNat = some c) (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem))
    (hsl : CtxSl s₀.mem ctx.toNat) (hhi : c.hiAt 0 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_holes" [ctx]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestHoles c) a₀ ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.nestHoles c) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      NhOut s'.mem r (AM.res (ConRon.Arena.nestHoles c) a₀); ⊤⦄ := by
  refine triple_post (nestHoles_spec p hl k s₀ ctx) ?_
  rintro r s' ⟨hlc, hm⟩
  have htop : iwTop s₀.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  obtain ⟨hn, hnb, -⟩ := ctx_fields hc hin htop
  have hlen := decHL_length _ hn
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := nhGoW_ok fe vis ctx c k _ _ a₀ 0 _ _ 0 0 c.names [] _ hm hS hc hin
    hsl hn hnb (by simp [decHL, hslice?]) (by simp) (by have := hlen; simp [NestCtx.hiAt] at hhi; simp; omega)
  have he : ConRon.Arena.nestHoles c = ConRon.Arena.nestHoles.go c 0 c.names [] := rfl
  simp only [show (0 : Word).toNat = 0 from rfl, ← he] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hlc, hok, by rw [hst]; exact hS', hg, ?_⟩
  rw [hres]
  cases x with
  | none => exact hout
  | some l => obtain ⟨h1, h2, h3⟩ := hout; exact ⟨h1, h2, h3⟩

/-- **`nest_holes_go` refines `nestHoles.go`**: from member `mm` on, the names `ns` (a slice of the
context's names below the top) appended to the holes so far (`out`, below the top). Its one caller,
`nestHoles` (`nestHoles_refines` above), discharges every hypothesis from its own pre: the context
decoded with its words and slices below the top, `nP + |names| < 2^64`. -/
@[refines ConRon.Arena.nestHoles.go]
theorem nestHolesGo_refines (k : Nat) (s₀ : St) (a₀ : AState)
    (fe : IFEnv) (vis ctx mm off l oo ol : Word) (c : NestCtx) (ns : List NIdx) (out : List EIdx)
    (hS : StageR vis fe s₀.mem a₀) (hc : decCtx s₀.mem ctx.toNat = some c)
    (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem)) (hsl : CtxSl s₀.mem ctx.toNat)
    (hns : decHL s₀.mem off.toNat l.toNat = some ns) (hnb : ∀ j < l.toNat, off.toNat + j < iwTop s₀.mem)
    (hout : decHL s₀.mem oo.toNat ol.toNat = some out) (hob : oo.toNat + ol.toNat ≤ iwTop s₀.mem)
    (hmm : c.nP + mm.toNat + l.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_holes_go" [ctx, mm, off, l, oo, ol]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestHoles.go c mm.toNat ns out) a₀ ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.nestHoles.go c mm.toNat ns out) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ NhOut s'.mem r (AM.res (ConRon.Arena.nestHoles.go c mm.toNat ns out) a₀); ⊤⦄ := by
  refine triple_post (nhGo_spec p hl k s₀ ctx mm off l oo ol) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hNh⟩ := nhGoW_ok fe vis ctx c k _ _ a₀ mm off l oo ol ns out _ hm hS hc hin
    hsl hns hnb hout hob hmm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hlc, hok, by rw [hst]; exact hS', hg, ?_⟩
  rw [hres]
  cases x with
  | none => exact hNh
  | some l => obtain ⟨h1, h2, h3⟩ := hNh; exact ⟨h1, h2, h3⟩

end census

def nrcK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([r3.headD 0, r3.tail.headD 0], m3)
def nrcK2 (k : Nat) (ctx : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => nrcK3 (pccW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1))
      (rdW (m2.arr64 IW) (ctx + 10)) (rdW (m2.arr64 IW) (ctx + 4)) (r2.headD 0))
def nrcK1 (cR : CallM) (k : Nat) (ctx cv : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => nrcK2 k ctx (cR (k + 2) "inst_lp_fast" [CWF, r1.headD 0, r1.tail.headD 0,
      rdW (m1.arr64 IW) (ctx + 10), erRd m1 (cv + 3)] m1)
/-- The model of `nest_root_canon(ctx, cv)` at exec fuel `k + 3` (its `inst_lp_fast` read through `cR`). -/
def nrcW (cR : CallM) (k : Nat) (m : Mem) (ctx cv : Word) : Option (List Word × Mem) :=
  nrcK1 cR k ctx cv (cvLpsW (k + 2) m cv)

section arms
variable (cR : CallM) (k : Nat) (m1 m2 m3 : Mem) (ctx cv : Word) (r1 r2 r3 : List Word)
theorem nrcK3_some : nrcK3 (some (r3, m3)) = some ([r3.headD 0, r3.tail.headD 0], m3) := rfl
theorem nrcK2_some : nrcK2 k ctx (some (r2, m2)) = nrcK3 (pccW k m2 (rdW (m2.arr64 IW) ctx)
    (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 10)) (rdW (m2.arr64 IW) (ctx + 4)) (r2.headD 0)) := rfl
theorem nrcK1_some : nrcK1 cR k ctx cv (some (r1, m1)) = nrcK2 k ctx (cR (k + 2) "inst_lp_fast" [CWF, r1.headD 0,
    r1.tail.headD 0, rdW (m1.arr64 IW) (ctx + 10), erRd m1 (cv + 3)] m1) := rfl
end arms
attribute [ind_grind] nrcK3_some nrcK2_some nrcK1_some

/-- `nest_canon_crest` keeps `AbsOK` (`IndRealAbsPos.pccW_afr`; a hypothesis here, proved below). -/
def PccAfr : Prop :=
  ∀ (k : Nat) (m m' : Mem) (no nl us nn cty : Word) (r : List Word), pccW k m no nl us nn cty = some (r, m') →
    AFr m m'

/-! ## `nest_uniform_ok` refines `nestUniformOk` -/

def nuK3 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (o, m3) => some ([if o = 0 then 1 else 0], m3)
def nuK2 (k : Nat) (ctx : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0], m2)
    else nuK3 (noConstWf (k + 3) m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) 0 0 (r2.tail.headD 0))
def nuK1 (cR : CallM) (k : Nat) (ctx cv : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if r1.headD 0 ≠ 0 then some ([0], m1) else nuK2 k ctx (nrcW cR k m1 ctx cv)
/-- The model of `nest_uniform_ok(ctx, cv)` at exec fuel `k + 4`. -/
def nuW (cR : CallM) (k : Nat) (m : Mem) (ctx cv : Word) : Option (List Word × Mem) :=
  nuK1 cR k ctx cv (pdoW (k + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
    (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (erRd m (cv + 3)))

section arms
variable (cR : CallM) (k : Nat) (m1 m2 m3 : Mem) (ctx cv o : Word) (r1 r2 : List Word)
theorem nuK3_some : nuK3 (some (o, m3)) = some ([if o = 0 then 1 else 0], m3) := rfl
theorem nuK2_none (h : r2.headD 0 = 0) : nuK2 k ctx (some (r2, m2)) = some ([0], m2) := by rw [nuK2, ite_eq_left h]
theorem nuK2_some (h : ¬ r2.headD 0 = 0) : nuK2 k ctx (some (r2, m2)) =
    nuK3 (noConstWf (k + 3) m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) 0 0 (r2.tail.headD 0)) := by
  rw [nuK2, ite_eq_right h]
theorem nuK1_occ (h : r1.headD 0 ≠ 0) : nuK1 cR k ctx cv (some (r1, m1)) = some ([0], m1) := by rw [nuK1, ite_eq_left h]
theorem nuK1_ok (h : ¬ r1.headD 0 ≠ 0) : nuK1 cR k ctx cv (some (r1, m1)) = nuK2 k ctx (nrcW cR k m1 ctx cv) := by
  rw [nuK1, ite_eq_right h]
end arms
attribute [ind_grind] nuK3_some nuK2_none nuK2_some nuK1_occ nuK1_ok

/-- What `AbsOK` across `nest_uniform_ok` needs of its callees (`IndRealAbsPos.nuAfr`). -/
structure NuAfr : Prop where
  pcc : PccAfr
  pdo : ∀ (k : Nat) (m m' : Mem) (no nl lo hi n e : Word) (r : List Word), pdoW k m no nl lo hi n e = some (r, m') →
    AFr m m'
  noc : ∀ (k : Nat) (m m' : Mem) (no nl lo hi e o : Word), noConstWf k m no nl lo hi e = some (o, m') → AFr m m'

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

/-- `nest_uniform_ok` at any exec fuel (below `4` it never returns). -/
def nuWf (cR : CallM) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | k + 4, m, ctx, cv => nuW cR k m ctx cv
  | _, _, _, _ => none

end L.Ind

end

end
