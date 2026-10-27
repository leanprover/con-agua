import ConAgua.Arena.WhnfIotaRefine4
import ConAgua.Arena.IndPosSpec.NestBlockOfKey

/-!
# ι-reduction: proofs of `WhnfIota.lean`'s specs, part 6 (`iota_ctor_never_prop`, `iota_case3`)

The L function is split into small ones (`e_rec_get`, `const_name_of`, `ind_caps_check`) and the
`caps_never_zero` stub's statement is corrected (see `CapsNeverZeroOK`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The small L functions -/

/-- Model of `e_rec_get`. -/
def eRecGetW (m : Mem) (k : Word) : Option Word :=
  if k.toNat < (m.arr64 EREC).size then some (rdW (m.arr64 EREC) k) else none

theorem eRecGet_spec (p : Prog) (hp : p.lookup "e_rec_get" = some eRecGetL) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "e_rec_get" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ eRecGetW s₀.mem k = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, eRecGetL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
    finish [eRecGetW, rdW]

/-- Model of `const_name_of`. -/
def cnoW (m : Mem) (hh : Word) : Option Word :=
  if tierW hh ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m CONST (tierW hh) ≤ idxW hh then none
  else some (tfld m CONST (tierW hh) (idxW hh) 0)

theorem constNameOf_spec (p : Prog) (hp : p.lookup "const_name_of" = some constNameOfL) (n : Nat)
    (s₀ : St) (hh : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "const_name_of" [hh]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ cnoW s₀.mem hh = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, constNameOfL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE] <;>
    finish [cnoW, tierW, idxW]

/-- Model of `ind_caps_check` (callees at fuel `n`). -/
def iccW (p : Prog) (n : Nat) (m : Mem) (indP us : Word) : Option (Word × Mem) :=
  match callW p n "e_rec_get" [indP] m with
  | none => none
  | some (k, m0) =>
  if k.headD 0 ≠ 3 then some (0, m0) else
  match callW p n "ls_node" [us] m0 with
  | none => none
  | some (r1, m1) =>
  match callW p n "e_rec_get" [indP + 3] m1 with
  | none => none
  | some (lp, m2) =>
  if lp.headD 0 ≠ r1.tail.headD 0 then some (0, m2) else
  match callW p n "e_rec_get" [indP + 2] m2 with
  | none => none
  | some (po, m3) =>
  match callW p n "e_rec_get" [indP + 12] m3 with
  | none => none
  | some (swd, m4) =>
  match callW p n "e_rec_get" [indP + 13] m4 with
  | none => none
  | some (so, m5) =>
  match callW p n "e_rec_get" [indP + 14] m5 with
  | none => none
  | some (sc, m6) =>
  match callW p n "caps_never_zero"
      [po.headD 0, lp.headD 0, us, swd.headD 0, so.headD 0, sc.headD 0] m6 with
  | none => none
  | some (nz, m7) => some (nz.headD 0, m7)

theorem indCapsCheck_spec (p : Prog) (hp : p.lookup "ind_caps_check" = some indCapsCheckL)
    (n : Nat) (s₀ : St) (indP us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ind_caps_check" [indP, us]
    ⦃fun r s' => LocEq s' s₀ ∧ iccW p n s₀.mem indP us = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, indCapsCheckL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "e_rec_get", callW_spec p n "ls_node", callW_spec p n "caps_never_zero"] <;>
  simp_all [iccW, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ,
    Sig.retVal, Sig.retOr]

/-- Model of `iota_ctor_never_prop` (callees at fuel `n`). -/
def inpW (p : Prog) (n : Nat) (m : Mem) (vis ctorP us : Word) : Option (Word × Mem) :=
  match callW p n "e_rec_get" [ctorP + 4] m with
  | none => none
  | some (ty, m0) =>
  match callW p n "pi_result" [ty.headD 0] m0 with
  | none => none
  | some (r1, m1) =>
  match callW p n "get_app_fn" [r1.headD 0] m1 with
  | none => none
  | some (r2, m2) =>
  if r2.headD 0 >>> 28 ≠ 3 then some (0, m2) else
  match callW p n "const_name_of" [r2.headD 0] m2 with
  | none => none
  | some (r3, m3) =>
  match callW p n "env_find" [r3.headD 0, vis] m3 with
  | none => none
  | some (r4, m4) =>
  if r4.headD 0 = 0 then some (0, m4) else
  match callW p n "ind_caps_check" [r4.tail.headD 0, us] m4 with
  | none => none
  | some (r5, m5) => some (r5.headD 0, m5)

theorem iotaCtorNeverProp_spec (p : Prog)
    (hp : p.lookup "iota_ctor_never_prop" = some iotaCtorNeverPropL) (n : Nat) (s₀ : St)
    (vis ctorP us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "iota_ctor_never_prop" [vis, ctorP, us]
    ⦃fun r s' => LocEq s' s₀ ∧ inpW p n s₀.mem vis ctorP us = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaCtorNeverPropL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "e_rec_get", callW_spec p n "pi_result", callW_spec p n "get_app_fn",
    callW_spec p n "const_name_of", callW_spec p n "env_find",
    callW_spec p n "ind_caps_check"] <;>
  simp_all [inpW, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ,
    Sig.retVal, Sig.retOr]


/-! ## The record of an inductive -/

theorem nat?_some {a : Array Word} {i k : Nat} (h : nat? a i = some k) :
    ∃ w, a[i]? = some w ∧ w.toNat = k := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, hk⟩ := h
  exact ⟨w, hw, hk⟩

theorem nat?_of {a : Array Word} {i : Nat} {w : Word} (h : a[i]? = some w) : nat? a i = some w.toNat := by
  simp [nat?, h]

theorem hlist?_slice {a : Array Word} {i : Nat} {l : List NIdx} (h : hlist? a i = some l) :
    ∃ o c : Word, a[i]? = some o ∧ a[i+1]? = some c ∧ hslice? a o.toNat c.toNat = some l := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, c, hc, hs⟩ := h
  obtain ⟨wo, hwo, rfl⟩ := nat?_some ho
  obtain ⟨wc, hwc, rfl⟩ := nat?_some hc
  exact ⟨wo, wc, hwo, hwc, hs⟩

theorem decPW_ww {b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {pw : ConLeche.PropWhen} {swd so sc : Word} (h : decPW b dn q = some pw)
    (h0 : b[q]? = some swd) (h1 : b[q+1]? = some so) (h2 : b[q+2]? = some sc) :
    decPWw b dn swd so sc = some pw := by
  simp only [decPW, nat?_of h0, Option.bind_eq_bind, Option.bind_some] at h
  simp only [decPWw]
  rcases hs : swd.toNat with _ | _ | k
  · rw [hs] at h; simpa using h
  · rw [hs] at h
    simp only [hlist?, nat?_of h1, nat?_of h2, Option.bind_eq_bind, Option.bind_some] at h
    simpa using h
  · rw [hs] at h; simp at h

theorem decCI_ind_fields (b : Array Word) (dn : NIdx → Option ConLeche.Name) (q : Nat)
    (cv : IConstantVal) (caps : IIndCaps) (h : decCI b dn q = some (.indInfo cv caps)) :
    ∃ po pc swd so sc : Word, b[q+2]? = some po ∧ b[q+3]? = some pc ∧
      hslice? b po.toNat pc.toNat = some cv.levelParams ∧ b[q+12]? = some swd ∧
      b[q+13]? = some so ∧ b[q+14]? = some sc ∧ decPWw b dn swd so sc = some caps.sortZ := by
  have hk := L.Ind.decCI_indInfo_kind h
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk', h⟩ := h
  have hk3 : k = 3 := Option.some.inj (hk'.symm.trans hk)
  subst hk3
  simp only [Option.bind_eq_some_iff, Option.some.injEq, IConstantInfo.indInfo.injEq] at h
  obtain ⟨cv', hcv, caps', hcaps, hc1, hc2⟩ := h
  subst hc1; subst hc2
  simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcv
  obtain ⟨nm, hnm, ls, hls, ty, hty, hcv⟩ := hcv
  have hcv' : ls = cv'.levelParams := by have := Option.some.inj hcv; rw [← this]
  obtain ⟨o, c, ho, hc, hs⟩ := hlist?_slice hls
  simp only [decCaps, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcaps
  obtain ⟨a0, -, a1, -, a2, -, a3, -, a4, -, a5, -, a6, -, a7, hpw, a8, -, a9, h9, a10, h10, hfin⟩ :=
    hcaps
  have hsz9 : q + 5 + 12 < b.size := L.Ind.nat?_idx h9
  obtain ⟨o10, c10, ho10, hc10, -⟩ := hlist?_slice h10
  have hsz10 : q + 5 + 13 + 1 < b.size := (Array.getElem?_eq_some_iff.mp hc10).1
  have e12 : q + 12 < b.size := by omega
  have e13 : q + 13 < b.size := by omega
  have e14 : q + 14 < b.size := by omega
  have g12 : b[q+12]? = some b[q+12] := Array.getElem?_eq_getElem e12
  have g13 : b[q+13]? = some b[q+13] := Array.getElem?_eq_getElem e13
  have g14 : b[q+14]? = some b[q+14] := Array.getElem?_eq_getElem e14
  have hww := decPW_ww hpw g12 g13 g14
  have hcz : a7 = caps'.sortZ := by have := Option.some.inj hfin; rw [← this]
  refine ⟨o, c, _, _, _, ho, hc, ?_, g12, g13, g14, ?_⟩
  · rw [← hcv']; exact hs
  · rw [← hcz]; exact hww

/-! ## The head name of a `const` handle -/

theorem viewConstName_f (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h CONST) (_hg : h >>> 28 = 3) :
    a.store.viewConstName (decE h) = some (decI (tfld m CONST (tierW h) (idxW h) 0)) := by
  obtain ⟨k, hk, hn, hu⟩ := node_of m a h constCS CeRecRel (·.consts) _ hR.const hv.2
  have hfl := ConsR.flag hR.app
  have e : a.store.viewConstName (decE h) =
      ((if tierW h = 0 then a.store.pers else a.store.scr).consts.node? (idxW h).toNat).map
        (fun r => r.n) := by
    unfold EStore.viewConstName EStore.persGetConstName
    rw [decE_pers h hh]
    by_cases ht : tierW h = 0
    · simp [ht, ETables.getConstName, decE_idx h]
    · have hon : a.store.scratchOn = true := by
        rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hv.1 ⟨ht, h1⟩
      simp [ht, hon, ETables.getConstName, decE_idx h]
  rw [e, Tbl.node?, hk]
  simp [hn, decI_word]


/-! ## The family test -/

/-- The twin's tail of `iotaCtorNeverProp` at an inductive's record. -/
def inpTail (cvT : IConstantVal) (caps : IIndCaps) (us : LsIdx) : AM Bool := do
  match ← viewLsLen us with
  | none => failDanglingLs
  | some usl =>
    if cvT.levelParams.length == usl then capsNeverZero cvT.levelParams us caps else pure false

theorem rdW_get (b : Array Word) (x v : Word) (hx : b[x.toNat]? = some v) : rdW b x = v := by
  simp [rdW, hx]

theorem eRec_val {m : Mem} {k v : Word} (h : eRecGetW m k = some v) :
    rdW (m.arr64 EREC) k = v := by
  simp only [eRecGetW] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h
  · cases h

theorem inpTail_short (cvT : IConstantVal) (caps : IIndCaps) (us : LsIdx) (a : AState) (usl : Nat)
    (hv : a.store.lss.viewLen us = some usl) (hne : cvT.levelParams.length ≠ usl) :
    (inpTail cvT caps us).run a = .ok (false, a) := by
  have hv' : (viewLsLen us).run a = .ok (some usl, a) := by rw [viewLsLen_run, hv]
  simp only [inpTail, StateT.run_bind, hv', except_ok_bind]
  have : (cvT.levelParams.length == usl) = false := by simpa using hne
  simp [this]; rfl

theorem inpTail_full (cvT : IConstantVal) (caps : IIndCaps) (us : LsIdx) (a a' : AState) (usl : Nat)
    (b : Bool) (hv : a.store.lss.viewLen us = some usl) (heq : cvT.levelParams.length = usl)
    (hc : (capsNeverZero cvT.levelParams us caps).run a = .ok (b, a')) :
    (inpTail cvT caps us).run a = .ok (b, a') := by
  have hv' : (viewLsLen us).run a = .ok (some usl, a) := by rw [viewLsLen_run, hv]
  simp only [inpTail, StateT.run_bind, hv', except_ok_bind]
  simp [heq, hc]

theorem iccW_ok (p : Prog) (hp : IotaProg4 p) (hcn : CapsNeverZeroOK p) (n : Nat)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb : Word) (indP us : Word)
    (hus : HW us) (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (cvT : IConstantVal) (caps : IIndCaps)
    (hci : decCI (m.arr64 EREC) dn indP.toNat = some (.indInfo cvT caps))
    (hfe : ∃ c, fe.find? c = some (.indInfo cvT caps)) (w : Word) (mF : Mem)
    (h : iccW p n m indP us = some (w, mF)) :
    ∃ (b : Bool) (a' : AState), (inpTail cvT caps (decI us)).run a = .ok (b, a') ∧
      (w != 0) = b ∧ CoreAfter dn m mF a' vis fe M eb ∧ HW w := by
  obtain ⟨po, pc, swd, so, sc, hpo, hpc, hsl, hswd, hso, hsc, hpw⟩ :=
    decCI_ind_fields _ dn _ cvT caps hci
  obtain ⟨wk, hwk, hwk3⟩ := nat?_some (L.Ind.decCI_indInfo_kind hci)
  have hbnd := L.Ind.decCI_indInfo_bound hci
  have hspn := hS.erec
  have a2 : (indP + 2).toNat = indP.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have a3 : (indP + 3).toNat = indP.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have a12 : (indP + 12).toNat = indP.toNat + 12 := by rw [UInt64.toNat_add]; simp; omega
  have a13 : (indP + 13).toNat = indP.toNat + 13 := by rw [UInt64.toNat_add]; simp; omega
  have a14 : (indP + 14).toNat = indP.toNat + 14 := by rw [UInt64.toNat_add]; simp; omega
  have rk : rdW (m.arr64 EREC) indP = 3 := by
    rw [rdW_get _ _ wk hwk]; exact UInt64.toNat_inj.mp (by rw [hwk3]; rfl)
  have r2 : rdW (m.arr64 EREC) (indP + 2) = po := rdW_get _ _ _ (by rw [a2]; exact hpo)
  have r3 : rdW (m.arr64 EREC) (indP + 3) = pc := rdW_get _ _ _ (by rw [a3]; exact hpc)
  have r12 : rdW (m.arr64 EREC) (indP + 12) = swd := rdW_get _ _ _ (by rw [a12]; exact hswd)
  have r13 : rdW (m.arr64 EREC) (indP + 13) = so := rdW_get _ _ _ (by rw [a13]; exact hso)
  have r14 : rdW (m.arr64 EREC) (indP + 14) = sc := rdW_get _ _ _ (by rw [a14]; exact hsc)
  simp only [iccW] at h
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n' =>
  -- the kind word
  rcases c0 : callW p (n' + 1) "e_rec_get" [indP] m with _ | ⟨k, m0⟩ <;>
    simp only [c0, reduceCtorEq] at h
  obtain ⟨t0, ht0, -, hmem0, hget0⟩ := triple_of_callW
    (eRecGet_spec p hp.eRecGet n' ⟨m, Locals.init []⟩ indP) c0
  obtain rfl : m0 = m := by rw [← ht0]; exact hmem0
  have hk : k.headD 0 = 3 := by rw [← eRec_val hget0]; exact rk
  rw [ite_eq_right (by rw [hk]; decide)] at h
  -- the level count
  rcases c1 : callW p (n' + 1) "ls_node" [us] m0 with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at h
  obtain ⟨t1, ht1, ht1s, hne1, hr1⟩ := triple_of_callW
    (lsNode_spec p hp.lvl.lsnode (n' + 1) ⟨m0, Locals.init []⟩ us) c1
  obtain rfl : m1 = m0 := by rw [← ht1, ht1s]
  obtain ⟨o1, l1, hl1⟩ : ∃ o l, lsNodeW m1 us = [o, l] := by
    rcases lsNodeW_cases m1 us with h' | h'
    · rw [h'] at hr1; exact absurd hr1 hne1
    · exact h'
  have hr1' : r1 = [o1, l1] := by rw [hr1]; exact hl1
  subst hr1'
  have hvl : a.store.lss.viewLen (decI us) = some l1.toNat := lsNodeW_viewLen hS.arena.1 hus hl1
  have hlen : cvT.levelParams.length = pc.toNat := hslice?_length hsl
  rcases c2 : callW p (n' + 1) "e_rec_get" [indP + 3] m1 with _ | ⟨lp, m2⟩ <;>
    simp only [c2, reduceCtorEq] at h
  obtain ⟨t2, ht2, -, hmem2, hget2⟩ := triple_of_callW
    (eRecGet_spec p hp.eRecGet n' ⟨m1, Locals.init []⟩ (indP + 3)) c2
  obtain rfl : m2 = m1 := by rw [← ht2]; exact hmem2
  have hlp : lp.headD 0 = pc := by rw [← eRec_val hget2]; exact r3
  by_cases hne : lp.headD 0 ≠ [o1, l1].tail.headD 0
  · rw [ite_eq_left hne] at h
    obtain ⟨hw0, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hne' : cvT.levelParams.length ≠ l1.toNat := by
      rw [hlen]; intro he; apply hne; rw [hlp]; exact UInt64.toNat_inj.mp he
    refine ⟨false, a, inpTail_short cvT caps _ a _ hvl hne', ?_, ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, ?_⟩
    · rw [← hw0]; rfl
    · rw [← hw0]; unfold HW; decide
  rw [ite_eq_right hne] at h
  have heq : cvT.levelParams.length = l1.toNat := by
    rw [hlen]; have := Classical.not_not.mp hne; rw [hlp] at this; simp at this; rw [this]
  have hlps : hslice? (m2.arr64 EREC) po.toNat pc.toNat = some cvT.levelParams := hsl
  rcases c3 : callW p (n' + 1) "e_rec_get" [indP + 2] m2 with _ | ⟨po', m3⟩ <;>
    simp only [c3, reduceCtorEq] at h
  obtain ⟨t3, ht3, -, hmem3, hget3⟩ := triple_of_callW
    (eRecGet_spec p hp.eRecGet n' ⟨m2, Locals.init []⟩ (indP + 2)) c3
  have e3 : m3 = m2 := by rw [← ht3]; exact hmem3
  have hpo' : po'.headD 0 = po := by rw [← eRec_val hget3]; exact r2
  rcases c4 : callW p (n' + 1) "e_rec_get" [indP + 12] m3 with _ | ⟨swd', m4⟩ <;>
    simp only [c4, reduceCtorEq] at h
  obtain ⟨t4, ht4, -, hmem4, hget4⟩ := triple_of_callW
    (eRecGet_spec p hp.eRecGet n' ⟨m3, Locals.init []⟩ (indP + 12)) c4
  have e4 : m4 = m3 := by rw [← ht4]; exact hmem4
  have hswd' : swd'.headD 0 = swd := by rw [← eRec_val hget4]; rw [e3]; exact r12
  rcases c5 : callW p (n' + 1) "e_rec_get" [indP + 13] m4 with _ | ⟨so', m5⟩ <;>
    simp only [c5, reduceCtorEq] at h
  obtain ⟨t5, ht5, -, hmem5, hget5⟩ := triple_of_callW
    (eRecGet_spec p hp.eRecGet n' ⟨m4, Locals.init []⟩ (indP + 13)) c5
  have e5 : m5 = m4 := by rw [← ht5]; exact hmem5
  have hso' : so'.headD 0 = so := by rw [← eRec_val hget5]; rw [e4, e3]; exact r13
  rcases c6 : callW p (n' + 1) "e_rec_get" [indP + 14] m5 with _ | ⟨sc', m6⟩ <;>
    simp only [c6, reduceCtorEq] at h
  obtain ⟨t6, ht6, -, hmem6, hget6⟩ := triple_of_callW
    (eRecGet_spec p hp.eRecGet n' ⟨m5, Locals.init []⟩ (indP + 14)) c6
  have e6 : m6 = m5 := by rw [← ht6]; exact hmem6
  have hsc' : sc'.headD 0 = sc := by rw [← eRec_val hget6]; rw [e5, e4, e3]; exact r14
  rcases c7 : callW p (n' + 1) "caps_never_zero"
      [po'.headD 0, lp.headD 0, us, swd'.headD 0, so'.headD 0, sc'.headD 0] m6 with _ | ⟨nz, m7⟩ <;>
    simp only [c7, reduceCtorEq] at h
  obtain ⟨hw0, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  rw [e6, e5, e4, e3] at c7
  rw [hpo', hlp, hswd', hso', hsc'] at c7
  obtain ⟨hrun7, ⟨M7, hS7, hK7, hSt7⟩, hr7⟩ := CoreSpec.run
    (hcn (n' + 1) ⟨m2, Locals.init []⟩ a dn vis fe M eb po pc us swd so sc cvT.levelParams
      caps.sortZ hS hus hlps
      (hS.den.constLps _ _ hfe.choose_spec) hpw) c7
  have hrunC : (capsNeverZero cvT.levelParams (decI us) caps).run a =
      .ok (decBool nz, AM.st (capsNeverZeroPW cvT.levelParams (decI us) caps.sortZ) a) := hrun7
  refine ⟨decBool nz, _, inpTail_full cvT caps _ a _ _ _ hvl heq hrunC, ?_,
    ⟨M7, hS7, hK7, hSt7⟩, ?_⟩
  · rw [← hw0]; rfl
  · rw [← hw0]; exact hr7


section inpRun
variable (fe : IFEnv) (cvj : IConstantVal) (us : LsIdx) (a : AState) (pr hh : EIdx)
  (hpr : (piResult coreWalkFuel cvj.type).run a = .ok (pr, a))
  (hga : (getAppFn coreWalkFuel pr).run a = .ok (hh, a))

theorem viewConstName_run (a : AState) (h : EIdx) :
    (viewConstName h).run a = .ok (a.store.viewConstName h, a) := rfl

include hpr hga in
theorem inp_run_not (ht : hh.tag ≠ ETag.const) :
    (iotaCtorNeverProp fe cvj us).run a = .ok (false, a) := by
  have : (hh.tag == ETag.const) = false := by simpa using ht
  simp only [iotaCtorNeverProp, StateT.run_bind, hpr, except_ok_bind, hga, this]
  simp; rfl

include hpr hga in
theorem inp_run_other (T : NIdx) (hv : a.store.viewConstName hh = some T)
    (ht : hh.tag = ETag.const) (hf : ∀ cvT caps, fe.find? T ≠ some (.indInfo cvT caps)) :
    (iotaCtorNeverProp fe cvj us).run a = .ok (false, a) := by
  simp only [iotaCtorNeverProp, StateT.run_bind, hpr, except_ok_bind, hga, ht, beq_self_eq_true,
    ↓reduceIte, viewConstName_run, hv]
  cases hfi : fe.find? T with
  | none => simp; rfl
  | some ci =>
    cases ci with
    | indInfo cvT caps => exact absurd hfi (hf cvT caps)
    | _ => simp; rfl

include hpr hga in
theorem inp_run_ind (T : NIdx) (hv : a.store.viewConstName hh = some T)
    (ht : hh.tag = ETag.const) (cvT : IConstantVal) (caps : IIndCaps)
    (hf : fe.find? T = some (.indInfo cvT caps)) (b : Bool) (a' : AState)
    (htl : (inpTail cvT caps us).run a = .ok (b, a')) :
    (iotaCtorNeverProp fe cvj us).run a = .ok (b, a') := by
  simp only [iotaCtorNeverProp, StateT.run_bind, hpr, except_ok_bind, hga, ht, beq_self_eq_true,
    ↓reduceIte, viewConstName_run, hv, hf]
  exact htl

end inpRun


theorem rdW_eq_three {b : Array Word} {x : Word} (h : rdW b x = 3) : b[x.toNat]? = some 3 := by
  cases hx : b[x.toNat]? with
  | none => simp [rdW, hx] at h
  | some w => simp only [rdW, hx, Option.getD_some] at h; rw [h]

theorem iccW_kind (p : Prog) (hp : IotaProg4 p) (n : Nat) (m : Mem) (indP us w : Word) (mF : Mem)
    (hk : rdW (m.arr64 EREC) indP ≠ 3) (h : iccW p n m indP us = some (w, mF)) :
    w = 0 ∧ mF = m := by
  simp only [iccW] at h
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n' =>
  rcases c0 : callW p (n' + 1) "e_rec_get" [indP] m with _ | ⟨k, m0⟩ <;>
    simp only [c0, reduceCtorEq] at h
  obtain ⟨t0, ht0, -, hmem0, hget0⟩ := triple_of_callW
    (eRecGet_spec p hp.eRecGet n' ⟨m, Locals.init []⟩ indP) c0
  have hm0 : m0 = m := by rw [← ht0]; exact hmem0
  have hkk : k.headD 0 = rdW (m.arr64 EREC) indP := (eRec_val hget0).symm
  rw [ite_eq_left (by rw [hkk]; exact hk)] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, by rw [← h.2, hm0]⟩

/-- **`iota_ctor_never_prop` refines `iotaCtorNeverProp`.** Statement changes: the L function is
split (`e_rec_get`, `const_name_of`, `ind_caps_check`), `caps_never_zero`'s statement is corrected
(`CapsNeverZeroOK`), and the callee fuel is generic (`CoreSpec p n`, as before). -/
@[refines ConRon.Arena.iotaCtorNeverProp]
theorem iotaCtorNeverProp_refines (p : Prog) (hp : IotaProg4 p) (hcn : CapsNeverZeroOK p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb ctorP us : Word) (cvj : IConstantVal) (cnP cnF : Nat),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW us →
    decCI (s₀.mem.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj cnP cnF) →
    CoreSpec p n "iota_ctor_never_prop" [vis, ctorP, us] (iotaCtorNeverProp fe cvj (decI us)) decBool
      s₀ a₀ dn vis fe MM eb := by
  intro n s₀ a₀ dn vis fe MM eb ctorP us cvj cnP cnF hS hus hci
  cases n with
  | zero => exact invoke_zero_triple
  | succ n' =>
  refine triple_post (iotaCtorNeverProp_spec p hp.iotaCtorNeverProp n' s₀ vis ctorP us) fun r s'
    ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  have hR := hS.arena.1
  simp only [inpW] at hW
  cases n' with
  | zero => rw [callW_zero] at hW; cases hW
  | succ n' =>
  -- the constructor's type
  have hk4 : rdW (s₀.mem.arr64 EREC) ctorP = 4 :=
    Classical.byContradiction fun hne =>
      (decCI_ctor hci (fun i v hv => hv) hS.erec).2 hne cvj cnP cnF rfl
  obtain ⟨cv', np', nf', hcv, hty, hty32⟩ := (decCI_ctor hci (fun i v hv => hv) hS.erec).1 hk4
  have hcvj : cvj = cv' := by
    have := hcv; simp only [IConstantInfo.ctorInfo.injEq] at this; exact this.1
  subst hcvj
  -- the constructor's type
  rcases c0 : callW p (n' + 1) "e_rec_get" [ctorP + 4] s₀.mem with _ | ⟨ty, m0⟩ <;>
    simp only [c0, reduceCtorEq] at hW
  obtain ⟨t0, ht0, -, hmem0, hget0⟩ := triple_of_callW
    (eRecGet_spec p hp.eRecGet n' ⟨s₀.mem, Locals.init []⟩ (ctorP + 4)) c0
  obtain rfl : m0 = s₀.mem := by rw [← ht0]; exact hmem0
  have hty0 : ty.headD 0 = rdW (s₀.mem.arr64 EREC) (ctorP + 4) := (eRec_val hget0).symm
  have hty32' : HW (ty.headD 0) := by rw [hty0]; exact hty32
  rcases c1 : callW p (n' + 1) "pi_result" [ty.headD 0] s₀.mem with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨t1, ht1, hmem1, -, hHW1, hrun1⟩ := triple_of_callW
    (piResult_refines' p hp.spine.pires (n' + 1) ⟨s₀.mem, Locals.init []⟩ a₀ hR (ty.headD 0) hty32') c1
  obtain rfl : m1 = s₀.mem := by rw [← ht1]; exact hmem1
  rcases c2 : callW p (n' + 1) "get_app_fn" [r1.headD 0] s₀.mem with _ | ⟨r2, m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨t2, ht2, hmem2, -, hHW2, hrun2⟩ := triple_of_callW
    (getAppFn_refines' p hp.spine.fn (n' + 1) ⟨s₀.mem, Locals.init []⟩ a₀ hR (r1.headD 0) hHW1) c2
  obtain rfl : m2 = s₀.mem := by rw [← ht2]; exact hmem2
  have hpr : (piResult coreWalkFuel cvj.type).run a₀ = .ok (decE (r1.headD 0), a₀) := by
    rw [hty, ← hty0]; exact hrun1
  have hga : (getAppFn coreWalkFuel (decE (r1.headD 0))).run a₀ = .ok (decE (r2.headD 0), a₀) := hrun2
  by_cases h3 : r2.headD 0 >>> 28 ≠ 3
  · rw [ite_eq_left h3] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have hrun := inp_run_not fe cvj (decI us) a₀ _ _ hpr hga
      (fun ht => h3 ((decE_tag_eq _ hHW2 3 (by decide)).mp ht))
    refine CoreRef.of_pure hS hrun hm.symm ?_ ?_
    · show false = decBool r; simp only [decBool]; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [ite_eq_right h3] at hW
  have h3' : r2.headD 0 >>> 28 = 3 := by simpa using h3
  rcases c3 : callW p (n' + 1) "const_name_of" [r2.headD 0] s₀.mem with _ | ⟨r3, m3⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  obtain ⟨t3, ht3, -, hmem3, hcno⟩ := triple_of_callW
    (constNameOf_spec p hp.constNameOf n' ⟨s₀.mem, Locals.init []⟩ (r2.headD 0)) c3
  obtain rfl : m3 = s₀.mem := by rw [← ht3]; exact hmem3
  simp only [cnoW] at hcno
  obtain ⟨g1, hcno⟩ := of_ite_none hcno
  obtain ⟨g2, hcno⟩ := of_ite_none hcno
  simp only [Option.some.injEq] at hcno
  have hvc : viewOK s₀.mem (r2.headD 0) CONST := ⟨g1, UInt64.not_le.mp g2⟩
  obtain ⟨hvw, hn32, -⟩ := view_const_f s₀.mem a₀ hR (r2.headD 0) hHW2 hvc h3'
  have hvn := viewConstName_f s₀.mem a₀ hR (r2.headD 0) hHW2 hvc h3'
  rw [hcno] at hvn hn32
  have htag : (decE (r2.headD 0)).tag = ETag.const := (decE_tag_eq _ hHW2 3 (by decide)).mpr h3'
  rcases c4 : callW p (n' + 1) "env_find" [r3.headD 0, vis] s₀.mem with _ | ⟨r4, m4⟩ <;>
    simp only [c4, reduceCtorEq] at hW
  obtain ⟨t4, ht4, hm4, -, hfind⟩ := triple_of_callW
    (envFind_refines p hp.envix hp.envrow hp.envfind (n' + 1) ⟨s₀.mem, Locals.init []⟩ vis _ hS.env
      hn32) c4
  obtain ⟨t4', ht4', hm4', -, hfound⟩ := triple_of_callW
    (envFind_found p hp.envix hp.envrow hp.envfind (n' + 1) ⟨s₀.mem, Locals.init []⟩ vis _ hn32) c4
  obtain rfl : m4 = s₀.mem := by rw [← ht4]; exact hm4
  by_cases h0 : r4.headD 0 = 0
  · rw [ite_eq_left h0] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have hnone : fe.find? (decI (r3.headD 0)) = none := by
      rw [hfind]; simp only [decFound, h0, ↓reduceIte]
    have hrun := inp_run_other fe cvj (decI us) a₀ _ _ hpr hga (decI (r3.headD 0)) hvn htag
      (fun cvT caps hc => by rw [hnone] at hc; cases hc)
    refine CoreRef.of_pure hS hrun hm.symm ?_ ?_
    · show false = decBool r; simp only [decBool]; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [ite_eq_right h0] at hW
  obtain ⟨htag2, hrow, hq⟩ := hfound h0
  obtain ⟨ci, hci2⟩ := hS.env.found_some (r3.headD 0) hn32 htag2 hrow
  have hfind' : fe.find? (decI (r3.headD 0)) = some ci := by
    rw [hfind]; simp only [decFound, h0, ↓reduceIte, hq]; exact hci2
  rw [← hq] at hci2
  have hciF := ArrExt.decCI (erecP_ext _) hci2
  rcases c5 : callW p (n' + 1) "ind_caps_check" [r4.tail.headD 0, us] s₀.mem with _ | ⟨r5, m5⟩ <;>
    simp only [c5, reduceCtorEq] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨t5, ht5, -, hicc⟩ := triple_of_callW
    (indCapsCheck_spec p hp.indCapsCheck n' ⟨s₀.mem, Locals.init []⟩ (r4.tail.headD 0) us) c5
  rw [ht5] at hicc
  by_cases hk3 : rdW (s₀.mem.arr64 EREC) (r4.tail.headD 0) = 3
  · have hg := rdW_eq_three hk3
    obtain ⟨cvT, caps, rfl, -⟩ := L.Ind.decCI_kind3 hciF (nat?_of hg)
    obtain ⟨b, a', htail, hb, hCA, hw5⟩ := iccW_ok p hp hcn n' dn vis fe eb (r4.tail.headD 0) us hus
      s₀.mem a₀ MM hS cvT caps hciF ⟨_, hfind'⟩ (r5.headD 0) m5 hicc
    have hrun := inp_run_ind fe cvj (decI us) a₀ _ _ hpr hga (decI (r3.headD 0)) hvn htag cvT caps
      hfind' b a' htail
    have hr' : r5.headD 0 = r.headD 0 := hr
    refine CoreRef.of_run hrun (hm ▸ hCA) ?_ ?_
    · simp only [decBool, ← hr', hb]
    · unfold ResH HW; rw [← hr']; exact hw5
  · obtain ⟨hw0, hm5⟩ := iccW_kind p hp n' s₀.mem (r4.tail.headD 0) us _ m5 hk3 hicc
    have hnind : ∀ cvT caps, fe.find? (decI (r3.headD 0)) ≠ some (.indInfo cvT caps) := by
      intro cvT caps hc
      rw [hfind'] at hc
      have hc' : ci = .indInfo cvT caps := Option.some.inj hc
      subst hc'
      obtain ⟨w, hw, hw3⟩ := nat?_some (L.Ind.decCI_indInfo_kind hciF)
      apply hk3
      rw [rdW_get _ _ w hw]
      exact UInt64.toNat_inj.mp (by rw [hw3]; rfl)
    have hrun := inp_run_other fe cvj (decI us) a₀ _ _ hpr hga (decI (r3.headD 0)) hvn htag hnind
    refine CoreRef.of_pure hS hrun (by rw [← hm, hm5]) ?_ ?_
    · show false = decBool r; simp only [decBool]; rw [← hr, hw0]; rfl
    · unfold ResH HW; rw [← hr, hw0]; decide


/-! ## `iota_case3(rlk, vis, ctorP, us)` -/

/-- Model of `iota_case3` (callee at fuel `n`). -/
def icW (p : Prog) (n : Nat) (m : Mem) (rlk vis ctorP us : Word) : Option (Word × Mem) :=
  if rlk ≠ 0 then some (0, m)
  else match callW p n "iota_ctor_never_prop" [vis, ctorP, us] m with
    | none => none
    | some (r, m') => some (if r.headD 0 = 0 then 1 else 0, m')

theorem iotaCase3_spec (p : Prog) (hp : p.lookup "iota_case3" = some iotaCase3L) (n : Nat)
    (s₀ : St) (rlk vis ctorP us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "iota_case3" [rlk, vis, ctorP, us]
    ⦃fun r s' => LocEq s' s₀ ∧ icW p n s₀.mem rlk vis ctorP us = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaCase3L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "iota_ctor_never_prop"] <;>
    finish [icW]

theorem iotaCase3_run_k (fe : IFEnv) (rl : IRecRule) (cvj : IConstantVal) (us : LsIdx) (a : AState)
    (hk : rl.k = true) : (iotaCase3 fe rl cvj us).run a = .ok (false, a) := by
  simp [iotaCase3, hk]; rfl

theorem iotaCase3_run_nk (fe : IFEnv) (rl : IRecRule) (cvj : IConstantVal) (us : LsIdx) (a a' : AState)
    (np : Bool) (hk : rl.k = false) (h : (iotaCtorNeverProp fe cvj us).run a = .ok (np, a')) :
    (iotaCase3 fe rl cvj us).run a = .ok (!np, a') := by
  simp only [iotaCase3, hk, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, h, except_ok_bind]
  rfl

/-- **`iota_case3` refines `iotaCase3`.** -/
@[refines ConRon.Arena.iotaCase3]
theorem iotaCase3_refines (p : Prog) (hp : IotaProg4 p) (hcn : CapsNeverZeroOK p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb rlk ctorP us : Word) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW us → rl.k = (rlk != 0) →
    decCI (s₀.mem.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj cnP cnF) →
    CoreSpec p n "iota_case3" [rlk, vis, ctorP, us] (iotaCase3 fe rl cvj (decI us)) decBool s₀ a₀ dn
      vis fe MM eb := by
  intro n s₀ a₀ dn vis fe MM eb rlk ctorP us rl cvj cnP cnF hS hus hrl hci
  cases n with
  | zero => exact invoke_zero_triple
  | succ n' =>
  refine triple_post (iotaCase3_spec p hp.iotaCase3 n' s₀ rlk vis ctorP us) fun r s' ⟨hloc, hW⟩ =>
    ⟨hloc, ?_⟩
  simp only [icW] at hW
  by_cases hr0 : rlk ≠ 0
  · rw [ite_eq_left hr0] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have hk : rl.k = true := by rw [hrl]; simpa using hr0
    refine CoreRef.of_pure hS (iotaCase3_run_k fe rl cvj (decI us) a₀ hk) hm.symm ?_ ?_
    · show false = decBool r; simp only [decBool]; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [ite_eq_right hr0] at hW
  have hk : rl.k = false := by
    rw [hrl]; have : rlk = 0 := Classical.not_not.mp hr0
    rw [this]; rfl
  rcases c1 : callW p n' "iota_ctor_never_prop" [vis, ctorP, us] s₀.mem with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, hr1⟩ := CoreSpec.run
    (iotaCtorNeverProp_refines p hp hcn n' ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb ctorP us cvj
      cnP cnF hS hus hci) c1
  have hrunF := iotaCase3_run_nk fe rl cvj (decI us) a₀ _ (decBool r1) hk hrun1
  refine CoreRef.of_run hrunF ⟨M1, hS1, hK1, hSt1⟩ ?_ ?_
  · by_cases h1 : r1.headD 0 = 0
    · rw [h1] at hr; simp only [decBool, h1]; rw [← hr]; rfl
    · rw [ite_eq_right h1] at hr; simp only [decBool]; rw [← hr]
      have h1' : (r1.headD 0 != 0) = true := bne_iff_ne.mpr h1
      rw [h1']; decide
  · unfold ResH HW; rw [← hr]; split <;> decide

end L.Arena
