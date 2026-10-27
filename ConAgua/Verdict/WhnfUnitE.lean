import ConAgua.Verdict.WhnfModels7E
import ConAgua.Verdict.WhnfSlotE

/-!
# `struct_unit_cert`, `struct_unit_head`, `struct_unit_tail`: error claims (lane `verdicts-b`, helper `k2`)

Their verdicts are the `infer_io`, `whnf` and `defeq` slots'. `struct_unit_head` has a hand error
model (`suhH`) with the store of the spine's top checked in bounds (the generated `suhE` drops it).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- Error model of `struct_unit_head`, the top's store checked. -/
def suhH (p : Prog) (n : Nat) (m : Mem) (mode vis d b wta : Word) : Except Err (List Word × Mem) :=
  match callE p n "get_app_fn" [wta] m with
  | .error e => .error e
  | .ok (r, m₁) =>
    if r.headD 0 >>> 28 ≠ 3 then .ok ([0], m₁)
    else if tierW (r.headD 0) ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0 then .error (.abort 0)
    else if ¬ idxW (r.headD 0) < tcnt m₁ CONST (tierW (r.headD 0)) then .error (.abort 0)
    else
    match callE p n "env_find" [tfld m₁ CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0, vis] m₁ with
    | .error e => .error e
    | .ok (r₂, m₂) =>
      if r₂.headD 0 = 0 then .ok ([0], m₂)
      else if rdW (m₂.arr64 EREC) (r₂.tail.headD 0) ≠ 3 then .ok ([0], m₂)
      else match callE p n "get_app_args" [wta] m₂ with
      | .error e => .error e
      | .ok (r₃, m₃) =>
        if ¬ (136 : Word).toNat < (m₃.arr64 CTL).size then .error (.abort 0)
        else match callE p n "ls_node" [tfld m₁ CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 1]
            (m₃.set64 CTL 136 (rdW (m₂.arr64 CTL) 136)) with
        | .error e => .error e
        | .ok (r₄, m₄) =>
          match callE p n "reserved_contains_w" [tfld m₁ CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0]
              m₄ with
          | .error e => .error e
          | .ok (r₅, m₅) =>
            if rdW (m₂.arr64 EREC) (r₂.tail.headD 0 + 9) = 0 then .ok ([0], m₅)
            else if r₅.headD 0 ≠ 0 then .ok ([0], m₅)
            else if r₃.tail.headD 0 ≠ rdW (m₂.arr64 EREC) (r₂.tail.headD 0 + 10) then .ok ([0], m₅)
            else if r₄.tail.headD 0 ≠ rdW (m₂.arr64 EREC) (r₂.tail.headD 0 + 3) then .ok ([0], m₅)
            else match callE p n "struct_unit_tail" [mode, vis, d, b, wta] m₅ with
              | .error e => .error e
              | .ok (r₆, m₆) => .ok ([r₆.headD 0], m₆)

set_option experimental.vcgen true in
set_option maxRecDepth 8000 in
theorem suhH_spec (p : Prog) (hp : p.lookup "struct_unit_head" = some structUnitHeadL) (n : Nat)
    (s₀ : St) (mode vis d b wta : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_unit_head" [mode, vis, d, b, wta]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 → suhH p n s₀.mem mode vis d b wta = .error ε⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structUnitHeadL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_specE, evalE_tld, tld,
    evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64,
    callE_spec p n "get_app_fn", callE_spec p n "env_find", callE_spec p n "get_app_args",
    callE_spec p n "ls_node", callE_spec p n "reserved_contains_w", callE_spec p n "struct_unit_tail"] <;>
  simp_all [suhH, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, tierW, idxW,
    CTL, EREC, CONST]

theorem whnfUnitE_nv : ∀ f ∈ ["get_app_fn", "env_find", "get_app_args", "ls_node", "reserved_contains_w"],
    f ∈ L.Checker.nvFns := by
  decide +kernel

section suErr
variable (r : CoreFnsA) (depth : Nat) (b wta : EIdx)

theorem suTail_err_io (a : AState) (ce : CheckError) (h : (r.inferIO depth b).run a = .error ce) :
    (suTailT r depth b wta).run a = .error ce := by
  simp only [suTailT, StateT.run_bind, h]; rfl

theorem suTail_err_whnf (a a₁ : AState) (tb : EIdx) (h1 : (r.inferIO depth b).run a = .ok (tb, a₁))
    (ce : CheckError) (h : (r.whnf depth tb).run a₁ = .error ce) :
    (suTailT r depth b wta).run a = .error ce := by
  simp only [suTailT, StateT.run_bind, h1, except_ok_bind, h]; rfl

theorem suTail_err_defeq (a a₁ a₂ : AState) (tb wtb : EIdx) (h1 : (r.inferIO depth b).run a = .ok (tb, a₁))
    (h2 : (r.whnf depth tb).run a₁ = .ok (wtb, a₂)) (hf : isForallE wtb = false) (ce : CheckError)
    (h : (r.defeq depth wta wtb).run a₂ = .error ce) :
    (suTailT r depth b wta).run a = .error ce := by
  simp only [suTailT, StateT.run_bind, h1, except_ok_bind, h2, hf, Bool.false_eq_true, ↓reduceIte, h]

end suErr

section sucErr
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx)

theorem suc_err_io (s : AState) (ce : CheckError) (h : (r.inferIO depth a).run s = .error ce) :
    (structUnitCert r fe depth a b).run s = .error ce := by
  rw [structUnitCert_eq]; simp only [StateT.run_bind, h]; rfl

theorem suc_err_whnf (s s₁ : AState) (ta : EIdx) (h1 : (r.inferIO depth a).run s = .ok (ta, s₁))
    (ce : CheckError) (h : (r.whnf depth ta).run s₁ = .error ce) :
    (structUnitCert r fe depth a b).run s = .error ce := by
  rw [structUnitCert_eq]; simp only [StateT.run_bind, h1, except_ok_bind, h]; rfl

theorem suc_err_head (s s₁ s₂ : AState) (ta wta : EIdx) (h1 : (r.inferIO depth a).run s = .ok (ta, s₁))
    (h2 : (r.whnf depth ta).run s₁ = .ok (wta, s₂)) (ce : CheckError)
    (h : (suHeadT r fe depth b wta).run s₂ = .error ce) :
    (structUnitCert r fe depth a b).run s = .error ce := by
  rw [structUnitCert_eq]; simp only [StateT.run_bind, h1, except_ok_bind, h2, h]

end sucErr

section su
variable (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (hnv : closedNV p L.Checker.nvFns = true)

include hq in
/-- **`struct_unit_tail`'s verdicts** are the `infer_io`, `whnf` and `defeq` slots'. -/
theorem suTail_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d b wta : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hwta : HW wta) :
    CoreSpecE p (n + 1) "struct_unit_tail" [mode, vis, d, b, wta]
      (suTailT (coreKnot (decMode mode) fe id F) d.toNat (decE b) (decE wta)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (sutE_spec p hq.suTail (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d b wta) hc0 (Err.code_ne_of_cls hk0)
  simp only [sutE] at hW
  cases c1 : callE p n "infer_io" [mode, vis, d, b] s₀.mem with
  | error e1 =>
    rw [c1, sutE.k_infer_io.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => suTail_err_io (wta := _) (ce := ce) (h := h'))
      (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).inferIO F s₀ a₀ dn vis fe M eb mode d b hF hn hs hb) c1)
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [c1] at hW
  simp only [sutE.k_infer_io] at hW
  obtain ⟨hok1, ⟨M₁, hS₁, -, -⟩, hres1, hr1⟩ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).inferIO F
    s₀ a₀ dn vis fe M eb mode d b hF hn hs hb) (callW_of_callE c1)
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  cases c2 : callE p n "whnf" [mode, vis, d, r₁.headD 0] m₁ with
  | error e2 =>
    rw [c2, sutE.k_whnf.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => suTail_err_whnf (wta := _) (h1 := hrun1) (ce := ce) (h := h'))
      (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d
        (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hr1) c2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [c2] at hW
  simp only [sutE.k_whnf] at hW
  obtain ⟨hok2, ⟨M₂, hS₂, -, -⟩, hres2, hh2⟩ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).whnf F
    ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hr1)
    (callW_of_callE c2)
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  by_cases h6 : r₂.headD 0 >>> 28 = 6
  · rw [ite_eq_left h6] at hW; cases hW
  rw [ite_eq_right h6] at hW
  have hfa : isForallE (decH r₂) = false := by
    simp only [isForallE, decH, tag_beq_w _ hh2 6 (by decide) ETag.forallE rfl 6 rfl]; simpa using h6
  have hW' := err_of_k (by intro q e; simp [sutE.k_defeq]) (fun _ => rfl) hW
  exact ErrClaim.of_run_err (fun ce h' => suTail_err_defeq (h1 := hrun1) (h2 := hrun2) (hf := hfa) (ce := ce)
      (h := h'))
    (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).defeq F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d wta
      (r₂.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ hwta hh2) hW')

include hq hc hnv in
/-- **`struct_unit_head`'s verdicts** are `struct_unit_tail`'s. -/
theorem suHead_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d b wta : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hwta : HW wta) :
    CoreSpecE p (n + 1) "struct_unit_head" [mode, vis, d, b, wta]
      (suHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decE wta)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (suhH_spec p hq.suHead n ⟨s₀.mem, Locals.init []⟩ mode vis d b wta) hc0
    (Err.code_ne_of_cls hk0)
  simp only [suhH] at hW
  have hS := hs.rel
  have hR := hS.arena.1
  cases c1 : callE p n "get_app_fn" [wta] s₀.mem with
  | error e1 =>
    rw [c1] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfUnitE_nv "get_app_fn" (by simp)) c1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [c1] at hW
  simp only at hW
  obtain ⟨rfl, hh, hgaf⟩ := getAppFn_callW (a := a₀) hq.leaf hR hwta (callW_of_callE c1)
  generalize r₁.headD 0 = h at hh hgaf hW
  by_cases h3 : h >>> 28 ≠ 3
  · rw [ite_eq_left h3] at hW; cases hW
  rw [ite_eq_right h3] at hW
  have h3' : h >>> 28 = 3 := by simpa using h3
  by_cases hsc : tierW h ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left hsc] at hW; cases hW; exact absurd rfl hk0
  rw [ite_eq_right hsc] at hW
  by_cases hcc : ¬ idxW h < tcnt s₀.mem CONST (tierW h)
  · rw [ite_eq_left hcc] at hW; cases hW; exact absurd rfl hk0
  rw [ite_eq_right hcc] at hW
  have hvo : viewOK s₀.mem h CONST := ⟨hsc, by simpa using hcc⟩
  obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s₀.mem a₀ hR h hh hvo h3'
  have hct : ((decE h).tag == ETag.const) = true := by rw [tag_beq_const _ hh]; simp [h3']
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 0 = k at hnw hW hv
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 1 = us2 at huw hW hv
  cases c2 : callE p n "env_find" [k, vis] s₀.mem with
  | error e2 =>
    rw [c2] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfUnitE_nv "env_find" (by simp)) c2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [c2] at hW
  simp only at hW
  obtain ⟨rfl, hfind, hfound⟩ := envFind_callW hq.leaf.core hS.env hnw (callW_of_callE c2)
  by_cases h0 : r₂.headD 0 = 0
  · rw [ite_eq_left h0] at hW; cases hW
  rw [ite_eq_right h0] at hW
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hind := decCI_indK hci (erecP_ext _) hS.erec
  by_cases h4 : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0) ≠ 3
  · rw [ite_eq_left h4] at hW; cases hW
  rw [ite_eq_right h4] at hW
  have h4' : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0) = 3 := by simpa using h4
  obtain ⟨cvT, caps, hci_eq⟩ := hind.1 h4'
  rw [hci_eq] at hci
  have hIR := decCI_indCaps hci (erecP_ext _) hS.erec
  cases c3 : callE p n "get_app_args" [wta] s₀.mem with
  | error e3 =>
    rw [c3] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfUnitE_nv "get_app_args" (by simp)) c3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [c3] at hW
  simp only at hW
  obtain ⟨hf3, hg3, -, -, targs, hargs, hsp⟩ := getAppArgs_callW hq.leaf.core.spine hS hwta
    (callW_of_callE c3)
  by_cases h136 : ¬ (136 : Word).toNat < (m₃.arr64 CTL).size
  · rw [ite_eq_left h136] at hW; cases hW; exact absurd rfl hk0
  rw [ite_eq_right h136] at hW
  have h136' : (136 : Word).toNat < (m₃.arr64 CTL).size := by simpa using h136
  obtain ⟨hS₃, hK₃⟩ := hS.restoreTop hf3 hg3 h136'
  have hlen : targs.length = (r₃.tail.headD 0).toNat := by simpa using hsp.size
  cases c4 : callE p n "ls_node" [us2] (m₃.set64 CTL 136 (rdW (s₀.mem.arr64 CTL) 136)) with
  | error e4 =>
    rw [c4] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfUnitE_nv "ls_node" (by simp)) c4
  | ok q =>
  obtain ⟨r₄, m₄⟩ := q
  rw [c4] at hW
  simp only at hW
  obtain ⟨t₄, ht₄, ht₄s, hne, hr₄⟩ := triple_of_callE
    (s₀ := ⟨m₃.set64 CTL 136 (rdW (s₀.mem.arr64 CTL) 136), Locals.init []⟩)
    (lsNode_spec p hq.leaf.core.lsn n ⟨m₃.set64 CTL 136 (rdW (s₀.mem.arr64 CTL) 136), Locals.init []⟩
      us2) c4
  have em₄ : m₄ = m₃.set64 CTL 136 (rdW (s₀.mem.arr64 CTL) 136) := by rw [← ht₄, ht₄s]
  rw [hr₄] at hne
  have hvl := defeq_lsNodeW_viewLen hS₃.arena.1 huw hne
  rw [← hr₄] at hvl
  subst em₄
  cases c5 : callE p n "reserved_contains_w" [k] (m₃.set64 CTL 136 (rdW (s₀.mem.arr64 CTL) 136)) with
  | error e5 =>
    rw [c5] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfUnitE_nv "reserved_contains_w" (by simp)) c5
  | ok q =>
  obtain ⟨r₅, m₅⟩ := q
  rw [c5] at hW
  simp only at hW
  obtain ⟨hA₅, hr₅⟩ := reservedContains_callW hc hS₃ hnw (callW_of_callE c5)
  have hA₅' : CoreAfter dn s₀.mem m₅ a₀ vis fe M eb := by
    obtain ⟨M', hS', hK', hSt'⟩ := hA₅
    exact ⟨M', hS', hK', hK₃.trans hSt'⟩
  obtain ⟨M₅, hS₅, -, -⟩ := hA₅'
  have hlpT : cvT.levelParams.length = (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 3)).toNat :=
    hslice?_length hIR.lp
  have hiff : (caps.unitlike = true ∧ a₀.pins.reserved.contains (decI k) = false ∧
      targs.length = caps.unitParams ∧ (r₄.tail.headD 0).toNat = cvT.levelParams.length) ↔
      uhOK (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 9)) (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 10))
        (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 3)) (r₃.tail.headD 0) (r₄.tail.headD 0) r₅ := by
    unfold uhOK
    rw [hIR.unitlike, ← hr₅, hlen, hIR.unitParams, hlpT]
    simp only [decBool, bne_iff_ne, ne_eq, bne_eq_false_iff_eq,
      UInt64.toNat_inj]
  have hrunH := suHead_ind (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) _ a₀ _ hgaf _ _ hct hv
    cvT caps (by rw [hfind', hci_eq]) targs hargs hS.pins _ hvl
  by_cases hok : uhOK (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 9))
      (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 10)) (rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 3))
      (r₃.tail.headD 0) (r₄.tail.headD 0) r₅
  · obtain ⟨o1, o2, o3, o4⟩ := hok
    simp only [o1, o2, o3, o4, ne_eq, not_true_eq_false, ↓reduceIte] at hW
    rw [ite_eq_left (hiff.mpr ⟨o1, o2, o3, o4⟩)] at hrunH
    cases c6 : callE p n "struct_unit_tail" [mode, vis, d, b, wta] m₅ with
    | error e6 =>
      rw [c6] at hW; cases hW
      cases n with
      | zero => exact ErrClaim.of_callE_zeroW c6
      | succ N =>
      exact ErrClaim.of_run_err (fun ce h' => by rw [hrunH]; exact h')
        (CoreSpecE.of_callE (suTail_refinesE p hq hnv N (hk.mono (Nat.le_succ N)) (hkE.mono (Nat.le_succ N))
          F ⟨m₅, Locals.init []⟩ a₀ dn vis fe M₅ eb mode d b wta (by omega) (by omega)
          ⟨hS₅, hs.mode4, hs.eb_mode⟩ hb hwta) c6)
    | ok q => rw [c6] at hW; cases hW
  · unfold uhOK at hok
    by_cases o1 : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 9) = 0
    · rw [ite_eq_left o1] at hW; cases hW
    rw [ite_eq_right o1] at hW
    by_cases o2 : r₅.headD 0 ≠ 0
    · rw [ite_eq_left o2] at hW; cases hW
    rw [ite_eq_right o2] at hW
    by_cases o3 : r₃.tail.headD 0 ≠ rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 10)
    · rw [ite_eq_left o3] at hW; cases hW
    rw [ite_eq_right o3] at hW
    by_cases o4 : r₄.tail.headD 0 ≠ rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 3)
    · rw [ite_eq_left o4] at hW; cases hW
    exact absurd ⟨o1, by simpa using o2, by simpa using o3, by simpa using o4⟩ hok

include hq hc hnv in
/-- **`struct_unit_cert`'s verdicts** are the `infer_io`, `whnf` slots' and `struct_unit_head`'s. -/
theorem suCert_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpecE p (n + 1) "struct_unit_cert" [mode, vis, d, a, b]
      (structUnitCert (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (sucE_spec p hq.sunit (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hk0)
  simp only [sucE] at hW
  cases c1 : callE p n "infer_io" [mode, vis, d, a] s₀.mem with
  | error e1 =>
    rw [c1, sucE.k_infer_io.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => suc_err_io (fe := fe) (b := _) (ce := ce) (h := h'))
      (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).inferIO F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha) c1)
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [c1] at hW
  simp only [sucE.k_infer_io] at hW
  obtain ⟨hok1, ⟨M₁, hS₁, -, -⟩, hres1, hr1⟩ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).inferIO F
    s₀ a₀ dn vis fe M eb mode d a hF hn hs ha) (callW_of_callE c1)
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  cases c2 : callE p n "whnf" [mode, vis, d, r₁.headD 0] m₁ with
  | error e2 =>
    rw [c2, sucE.k_whnf.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => suc_err_whnf (fe := fe) (b := _) (h1 := hrun1) (ce := ce) (h := h'))
      (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d
        (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hr1) c2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [c2] at hW
  simp only [sucE.k_whnf] at hW
  obtain ⟨hok2, ⟨M₂, hS₂, -, -⟩, hres2, hh2⟩ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).whnf F
    ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hr1)
    (callW_of_callE c2)
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  have hW' := err_of_k (by intro q e; simp [sucE.k_struct_unit_head]) (fun _ => rfl) hW
  cases n with
  | zero => exact ErrClaim.of_callE_zeroW hW'
  | succ N =>
  exact ErrClaim.of_run_err (fun ce h' => suc_err_head (h1 := hrun1) (h2 := hrun2) (ce := ce) (h := h'))
    (CoreSpecE.of_callE (suHead_refinesE p hq hc hnv N (hk.mono (Nat.le_succ N)) (hkE.mono (Nat.le_succ N))
      F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d b (r₂.headD 0) (by omega) (by omega)
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ hb hh2) hW')

end su

end L.Arena
