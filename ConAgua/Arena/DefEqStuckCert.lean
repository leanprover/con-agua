import ConAgua.Arena.DefEqStuckGo

/-!
# `struct_eta_cert_wtb`, `struct_eta_cert_with`, `struct_eta_cert` (lane `defeq`, helper `defeq-top`)

`structEtaCertWith` in L's pieces: the constructor's head and spine (`with`), the type's head
and spine (`wtb`, `setWtbT`), then `go` (`DefEqStuckGo.lean`). The slices pushed on the way stay
on the stack until `with` puts the top back (`GrowRef.restore`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Records -/

theorem erecP_frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : EREC ∉ A) (hC : (129 : Word) ∉ C) : erecP m' = erecP m := by
  unfold erecP erecTop
  rw [hf.1 EREC hA (by decide), hf.2.1 129 hC]

/-- The kind word of a decoded record says whether it is an inductive. -/
theorem decCI_indK {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI a dn q.toNat = some ci) (hab : ArrExt a b)
    (hsz : b.size < 2 ^ 63) :
    (rdW b q = 3 → ∃ cv caps, ci = .indInfo cv caps) ∧
    (rdW b q ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  have hrd : rdW b q = w := by
    have := rdW_ext hab hsz (k := 0) (by decide) (by simpa using hq); simpa using this
  rw [hrd]
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  constructor
  · intro hw; subst hw
    simp only [show UInt64.toNat 3 = 3 from rfl, Option.bind_eq_some_iff] at h
    obtain ⟨cv, -, caps, -, hc⟩ := h
    cases hc
    exact ⟨cv, caps, rfl⟩
  · intro hw cv caps hc
    subst hc
    have hne : w.toNat ≠ 3 := fun e => hw (UInt64.toNat_inj.mp (by rw [e]; rfl))
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h hne; simp [Option.bind_eq_some_iff] at h hne)

/-! ## The twin, after the constructor's spine -/

/-- **`structEtaCertWith` past the constructor's spine**, copied. -/
def setWtbT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
    (cvc : IConstantVal) (aargs : List EIdx) (wtb : EIdx) : AM Bool := do
  let hh ← getAppFn coreWalkFuel wtb
  if hh.tag == ETag.const then
    view hh >>= fun v => match v with
      | .const T us' =>
        match fe.find? T with
        | some (.indInfo cvT caps) => do
          let targs ← getAppArgs coreWalkFuel wtb
          setGoT r fe depth b c us cvc T us' cvT caps aargs targs
        | _ => pure false
      | _ => pure false
  else pure false

section wtbRuns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
  (cvc : IConstantVal) (aargs : List EIdx) (wtb : EIdx) (a : AState) (hh : EIdx)
  (hgaf : (getAppFn coreWalkFuel wtb).run a = .ok (hh, a))

include hgaf

theorem setWtbT_nonconst (ht : (hh.tag == ETag.const) = false) :
    (setWtbT r fe depth b c us cvc aargs wtb).run a = .ok (false, a) := by
  simp only [setWtbT, StateT.run_bind, hgaf, except_ok_bind, ht, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem setWtbT_other (T : NIdx) (us' : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : a.store.view hh = some (.const T us'))
    (hf : ∀ cv caps, fe.find? T ≠ some (.indInfo cv caps)) :
    (setWtbT r fe depth b c us cvc aargs wtb).run a = .ok (false, a) := by
  simp only [setWtbT, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv]
  rcases hc : fe.find? T with _ | ⟨_ | _ | _ | ⟨cv, caps⟩ | _ | _ | _⟩ <;> try rfl
  all_goals exact absurd hc (hf cv caps)

theorem setWtbT_ind (T : NIdx) (us' : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : a.store.view hh = some (.const T us')) (cvT : IConstantVal) (caps : IIndCaps)
    (hf : fe.find? T = some (.indInfo cvT caps)) (targs : List EIdx)
    (hargs : (getAppArgs coreWalkFuel wtb).run a = .ok (targs, a)) :
    (setWtbT r fe depth b c us cvc aargs wtb).run a =
      (setGoT r fe depth b c us cvc T us' cvT caps aargs targs).run a := by
  simp only [setWtbT, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv, hf,
    hargs]

end wtbRuns

/-! ## The model of `struct_eta_cert_wtb` -/

section wbK
variable (p : Prog) (n : Nat) (mode vis d b us c pc ao an wtb : Word)

def wbK3 (T q us2 : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => call1W p n "struct_eta_cert_go"
      [mode, vis, d, b, us, c, pc, T, q, us2, ao, an, r.headD 0, r.tail.headD 0] m

def wbK2 (T us2 : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, m)
    else if rdW (m.arr64 EREC) (r.tail.headD 0) ≠ 3 then some (0, m)
    else wbK3 p n mode vis d b us c pc ao an T (r.tail.headD 0) us2
      (callW p n "get_app_args" [wtb] m)

/-- **The model of `struct_eta_cert_wtb`** past `get_app_fn`'s run. -/
def wbK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 >>> 28 ≠ 3 then some (0, m)
    else if tierW (r.headD 0) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m CONST (tierW (r.headD 0)) ≤ idxW (r.headD 0) then none
    else wbK2 p n mode vis d b us c pc ao an wtb
      (tfld m CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0)
      (tfld m CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 1)
      (callW p n "env_find" [tfld m CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0, vis] m)

variable (r : List Word) (m : Mem) (T us2 q : Word)

theorem wbK3_some : wbK3 p n mode vis d b us c pc ao an T q us2 (some (r, m)) =
    call1W p n "struct_eta_cert_go"
      [mode, vis, d, b, us, c, pc, T, q, us2, ao, an, r.headD 0, r.tail.headD 0] m := rfl

end wbK

theorem setWtb_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St)
    (mode vis d b us c pc ao an wtb : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_eta_cert_wtb"
      [mode, vis, d, b, us, c, pc, ao, an, wtb]
    ⦃fun r s' => LocEq s' s₀ ∧ wbK1 p n mode vis d b us c pc ao an wtb
      (callW p n "get_app_fn" [wtb] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.setWtb]
  simp only [callFn, structEtaCertWtbL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, evalE_tld, tld,
    evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "get_app_args",
      callW_spec p n "struct_eta_cert_go"] <;>
  simp_all [wbK1, wbK2, wbK3, call1W, tierW, idxW, LocEq, BinOp.eval,
    St.setLocs_cons, CTL, EREC,
    CREC, Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-- A step that only pushed (twin unchanged) in front of a run that grew the stack. -/
theorem growRef_preG {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (hg : StackGrew m₀ m₁)
    (h : GrowRef T a₀ dec dn m₁ vis fe M eb r m ok) : GrowRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨hok, ⟨M'', hS'', hK'', hSt''⟩, hres, hr⟩ := h
  exact ⟨hok, ⟨M'', hS'', hK'', hg.trans hSt''⟩, hres, hr⟩

theorem addW_toNat {x y : Word} (h : x.toNat + y.toNat < 2 ^ 64) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

/-- **`struct_eta_cert_wtb` refines `setWtbT`** at the knot (its slices left on the stack). -/
@[refines_part ConRon.Arena.structEtaCertWith "the type's head and spine (setWtbT)"]
theorem setWtb_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d b us c pc ao an wtb : Word) (aargs : Array EIdx) (cvc : IConstantVal) (np nf : Nat)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b)
    (hus : HW us) (hcw : HW c) (hwtb : HW wtb)
    (hvus : ∃ x c', a₀.store.view x = some (.const c' (decI us)))
    (hcvc : decCI (erecP s₀.mem) dn pc.toNat = some (.ctorInfo cvc np nf))
    (ha : SpineR s₀.mem ao an aargs) (hat : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    GrowSpec p (n + 1) "struct_eta_cert_wtb" [mode, vis, d, b, us, c, pc, ao, an, wtb]
      (setWtbT (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decI c) (decI us) cvc
        aargs.toList (decE wtb)) decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (setWtb_spec p hq n s₀ mode vis d b us c pc ao an wtb)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hR := hS.arena.1
  have hres : ∀ x : Word, some (x, s.mem) = some (r.headD 0, s'.mem) → HW x → ∀ v,
      (setWtbT (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decI c) (decI us) cvc
        aargs.toList (decE wtb)).run a₀ = .ok (v, a₀) → v = (x != 0) →
      GrowRef (setWtbT (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decI c) (decI us) cvc
        aargs.toList (decE wtb)) a₀ decBool dn s.mem vis fe M eb r s'.mem := by
    intro x hxy hx v hv hvx
    obtain ⟨h1, h3⟩ := some_pair_inj hxy
    rw [← h3]
    refine growRef_pure hS hv ?_ ?_
    · rw [hvx, decBool, ← h1]
    · unfold ResH; rw [← h1]; exact hx
  obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
  obtain ⟨rfl, hh, hgaf⟩ := getAppFn_callW hq.leaf hR hwtb hc1
  simp only [wbK1] at hW1
  generalize r₁.headD 0 = h at hh hgaf hW1
  rcases (Classical.em (h >>> 28 = 3)).symm with h3 | h3
  · simp only [ne_eq, h3, not_false_eq_true, ↓reduceIte] at hW1
    exact hres 0 hW1 hw0 _
      (setWtbT_nonconst _ fe _ _ _ _ _ _ _ a₀ _ hgaf (by rw [tag_beq_const _ hh]; simp [h3])) rfl
  have hsc : ¬ (tierW h ≠ 0 ∧ rdW (s.mem.arr64 CTL) 1 = 0) := fun hsc => by simp [h3, hsc] at hW1
  have hcc : ¬ tcnt s.mem CONST (tierW h) ≤ idxW h := fun hcc => by simp [h3, hsc, hcc] at hW1
  simp only [h3, hsc, hcc, ne_eq, not_true_eq_false, ↓reduceIte] at hW1
  have hvo : viewOK s.mem h CONST := ⟨hsc, by simpa using hcc⟩
  obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s.mem a₀ hR h hh hvo h3
  have hct : ((decE h).tag == ETag.const) = true := by rw [tag_beq_const _ hh]; simp [h3]
  generalize tfld s.mem CONST (tierW h) (idxW h) 0 = k at hnw hW1 hv
  generalize tfld s.mem CONST (tierW h) (idxW h) 1 = us2 at huw hW1 hv
  obtain ⟨r₂, m₂, hc2, hW2⟩ := callW_cases rfl hW1
  obtain ⟨rfl, hfind, hfound⟩ := envFind_callW hq.leaf.core hS.env hnw hc2
  simp only [wbK2] at hW2
  by_cases h0 : r₂.headD 0 = 0
  · simp only [h0, ↓reduceIte] at hW2
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [decFound, h0, ↓reduceIte]
    exact hres 0 hW2 hw0 _ (setWtbT_other _ fe _ _ _ _ _ _ _ a₀ _ hgaf _ _ hct hv
      (fun cv caps e => by rw [hnone] at e; cases e)) rfl
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hind := decCI_indK hci (erecP_ext _) hS.erec
  rcases (Classical.em (rdW (s.mem.arr64 EREC) (r₂.tail.headD 0) = 3)).symm with h4 | h4
  · simp only [h0, h4, ne_eq, not_false_eq_true, ↓reduceIte] at hW2
    exact hres 0 hW2 hw0 _ (setWtbT_other _ fe _ _ _ _ _ _ _ a₀ _ hgaf _ _ hct hv
      (fun cv caps e => hind.2 h4 cv caps (by rw [hfind'] at e; exact Option.some.inj e))) rfl
  simp only [h0, h4, ne_eq, not_true_eq_false, ↓reduceIte] at hW2
  obtain ⟨cvT, caps, hci_eq⟩ := hind.1 h4
  rw [hci_eq] at hci
  -- the type's spine
  obtain ⟨r₃, m₃, hc3, hW3⟩ := callW_cases rfl hW2
  obtain ⟨hf3, hg3, hr30, htop3, targs, hargs, hsp⟩ := getAppArgs_callW hq.leaf.core.spine hS hwtb hc3
  have hS₃ := hS.frame_stk hf3 (by simp) (by simp)
  have hep : erecP m₃ = erecP s.mem := erecP_frame hf3 (by simp [EREC, SPN]) (by simp)
  rw [wbK3_some] at hW3
  refine growRef_congrS (setWtbT_ind _ fe _ _ _ _ _ _ _ a₀ _ hgaf _ _ hct hv cvT caps
    (by rw [hfind', hci_eq]) targs hargs) ?_
  refine growRef_preG hg3 ?_
  have hspn := hS.spn
  have hb3 := hsp.bound
  have hsz3 : (m₃.arr64 SPN).size < 2 ^ 63 := hg3.size ▸ hspn
  have htt : (r₃.headD 0).toNat + (r₃.tail.headD 0).toNat ≤ (spTop m₃).toNat := by
    have e := addW_toNat (x := r₃.headD 0) (y := r₃.tail.headD 0) (by omega)
    rw [htop3, ← hr30]; omega
  cases n with
  | zero => simp [call1W, callW_zero] at hW3
  | succ n' =>
  exact GrowSpec.of_call1W (s₀ := ⟨m₃, Locals.init []⟩)
    (setGo_refines p hq hi hc n' (hk.mono (by omega)) F ⟨m₃, Locals.init []⟩ a₀ dn vis fe M eb mode d
      b us c pc k (r₂.tail.headD 0) us2 ao an (r₃.headD 0) (r₃.tail.headD 0) aargs targs.toArray
      cvc np nf cvT caps (by omega) (by omega) ⟨hS₃, hs.mode4, hs.eb_mode⟩ hb hus hcw hnw huw
      hvus ⟨_, _, hv⟩ (by rw [hep]; exact hcvc) (by rw [hep]; exact hci) (ha.grew hg3 hat hspn) hsp
      (Nat.le_trans hat (UInt64.le_iff_toNat_le.mp hg3.1)) htt)
    (fun r r' h => by simp only [decBool, h]) (by simpa using hW3)

/-! ## `struct_eta_cert_with` -/

theorem structEtaCertWith_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b wtb : EIdx) :
    structEtaCertWith r fe depth a b wtb = (do
      let hh ← getAppFn coreWalkFuel a
      if hh.tag == ETag.const then
        view hh >>= fun v => match v with
          | .const c us =>
            match fe.find? c with
            | some (.ctorInfo cvc cnP cnF) => do
              let aargs ← getAppArgs coreWalkFuel a
              if aargs.length = cnP + cnF then setWtbT r fe depth b c us cvc aargs wtb
              else pure false
            | _ => pure false
          | _ => pure false
      else pure false) := rfl

section swK
variable (p : Prog) (n : Nat) (mode vis d a b wtb : Word)

/-- The top put back, then the verdict `v`. -/
def swRet (top v : Word) (m : Mem) : Option (Word × Mem) :=
  if (136 : Word).toNat < (m.arr64 CTL).size then some (v, m.set64 CTL 136 top) else none

def swK3 (top : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => swRet top (r.headD 0) m

/-- After the constructor's spine: the count test, then `wtb`. -/
def swK2 (us c top pc : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.tail.headD 0 < rdW (m.arr64 EREC) (pc + 6) then swRet top 0 m
    else if r.tail.headD 0 - rdW (m.arr64 EREC) (pc + 6) ≠ rdW (m.arr64 EREC) (pc + 5) then
      swRet top 0 m
    else swK3 top (callW p n "struct_eta_cert_wtb"
      [mode, vis, d, b, us, c, pc, r.headD 0, r.tail.headD 0, wtb] m)

def swK1' (c us : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, m)
    else if rdW (m.arr64 EREC) (r.tail.headD 0) ≠ 4 then some (0, m)
    else swK2 p n mode vis d b wtb us c (rdW (m.arr64 CTL) 136) (r.tail.headD 0)
      (callW p n "get_app_args" [a] m)

/-- **The model of `struct_eta_cert_with`** past `get_app_fn`'s run. -/
def swK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 >>> 28 ≠ 3 then some (0, m)
    else if tierW (r.headD 0) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m CONST (tierW (r.headD 0)) ≤ idxW (r.headD 0) then none
    else swK1' p n mode vis d a b wtb
      (tfld m CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0)
      (tfld m CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 1)
      (callW p n "env_find" [tfld m CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0, vis] m)

end swK

theorem setWith_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (mode vis d a b wtb : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_eta_cert_with" [mode, vis, d, a, b, wtb]
    ⦃fun r s' => LocEq s' s₀ ∧ swK1 p n mode vis d a b wtb
      (callW p n "get_app_fn" [a] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.setWith]
  simp only [callFn, structEtaCertWithL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, evalE_tld, tld,
    evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64_spec,
      callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "get_app_args",
      callW_spec p n "struct_eta_cert_wtb"] <;>
  simp_all [swK1, swK1', swK2, swK3, swRet, call1W, tierW, idxW, LocEq,
    BinOp.eval, St.setLocs_cons,
    CTL, EREC, CREC, Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ, size_set64] <;>
  (intro h1; exact absurd h1 (UInt64.not_lt.mpr ‹_›))

section withRuns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b wtb : EIdx) (st : AState) (hh : EIdx)
  (hgaf : (getAppFn coreWalkFuel a).run st = .ok (hh, st))

include hgaf

theorem setWith_nonconst (ht : (hh.tag == ETag.const) = false) :
    (structEtaCertWith r fe depth a b wtb).run st = .ok (false, st) := by
  rw [structEtaCertWith_eq]
  simp only [StateT.run_bind, hgaf, except_ok_bind, ht, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem setWith_other (c : NIdx) (us : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : st.store.view hh = some (.const c us))
    (hf : ∀ cv np nf, fe.find? c ≠ some (.ctorInfo cv np nf)) :
    (structEtaCertWith r fe depth a b wtb).run st = .ok (false, st) := by
  rw [structEtaCertWith_eq]
  simp only [StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv]
  rcases hc : fe.find? c with _ | ⟨_ | _ | _ | _ | ⟨cv, np, nf⟩ | _ | _⟩ <;> try rfl
  all_goals exact absurd hc (hf cv np nf)

theorem setWith_ctor (c : NIdx) (us : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : st.store.view hh = some (.const c us)) (cvc : IConstantVal) (np nf : Nat)
    (hf : fe.find? c = some (.ctorInfo cvc np nf)) (aargs : List EIdx)
    (hargs : (getAppArgs coreWalkFuel a).run st = .ok (aargs, st)) :
    (structEtaCertWith r fe depth a b wtb).run st =
      (if aargs.length = np + nf then setWtbT r fe depth b c us cvc aargs wtb else pure false).run st := by
  rw [structEtaCertWith_eq]
  simp only [StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv, hf, hargs]

end withRuns

/-- The L count test is the twin's. -/
theorem count_iff (an npw nfw : Word) :
    an.toNat = npw.toNat + nfw.toNat ↔ (¬ an < nfw ∧ an - nfw = npw) := by
  constructor
  · intro h
    have h1 : ¬ an < nfw := by rw [UInt64.lt_iff_toNat_lt]; omega
    refine ⟨h1, UInt64.toNat_inj.mp ?_⟩
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]; omega
  · rintro ⟨h1, h2⟩
    have h1' : nfw.toNat ≤ an.toNat := Nat.not_lt.mp (fun h => h1 (UInt64.lt_iff_toNat_lt.mpr h))
    have := congrArg UInt64.toNat h2
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h1')] at this; omega

/-- **`struct_eta_cert_with` refines `structEtaCertWith`** at the knot (the top put back). -/
@[refines ConRon.Arena.structEtaCertWith]
theorem setWith_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b wtb : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hwtb : HW wtb) :
    CoreSpec p (n + 1) "struct_eta_cert_with" [mode, vis, d, a, b, wtb]
      (structEtaCertWith (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (decE wtb))
      decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (setWith_spec p hq n s₀ mode vis d a b wtb)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hR := hS.arena.1
  have hres : ∀ x : Word, some (x, s.mem) = some (r.headD 0, s'.mem) → HW x → ∀ v,
      (structEtaCertWith (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)
        (decE wtb)).run a₀ = .ok (v, a₀) → v = (x != 0) →
      CoreRef (structEtaCertWith (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)
        (decE wtb)) a₀ decBool dn s.mem vis fe M eb r s'.mem := by
    intro x hxy hx v hv hvx
    obtain ⟨h1, h3⟩ := some_pair_inj hxy
    rw [← h3]
    refine coreRef_pure hS hv ?_ ?_
    · rw [hvx, decBool, ← h1]
    · unfold ResH; rw [← h1]; exact hx
  obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
  obtain ⟨rfl, hh, hgaf⟩ := getAppFn_callW hq.leaf hR ha hc1
  simp only [swK1] at hW1
  generalize r₁.headD 0 = h at hh hgaf hW1
  rcases (Classical.em (h >>> 28 = 3)).symm with h3 | h3
  · simp only [ne_eq, h3, not_false_eq_true, ↓reduceIte] at hW1
    exact hres 0 hW1 hw0 _
      (setWith_nonconst _ fe _ _ _ _ a₀ _ hgaf (by rw [tag_beq_const _ hh]; simp [h3])) rfl
  have hsc : ¬ (tierW h ≠ 0 ∧ rdW (s.mem.arr64 CTL) 1 = 0) := fun hsc => by simp [h3, hsc] at hW1
  have hcc : ¬ tcnt s.mem CONST (tierW h) ≤ idxW h := fun hcc => by simp [h3, hsc, hcc] at hW1
  simp only [h3, hsc, hcc, ne_eq, not_true_eq_false, ↓reduceIte] at hW1
  have hvo : viewOK s.mem h CONST := ⟨hsc, by simpa using hcc⟩
  obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s.mem a₀ hR h hh hvo h3
  have hct : ((decE h).tag == ETag.const) = true := by rw [tag_beq_const _ hh]; simp [h3]
  generalize tfld s.mem CONST (tierW h) (idxW h) 0 = k at hnw hW1 hv
  generalize tfld s.mem CONST (tierW h) (idxW h) 1 = us at huw hW1 hv
  obtain ⟨r₂, m₂, hc2, hW2⟩ := callW_cases rfl hW1
  obtain ⟨rfl, hfind, hfound⟩ := envFind_callW hq.leaf.core hS.env hnw hc2
  simp only [swK1'] at hW2
  by_cases h0 : r₂.headD 0 = 0
  · simp only [h0, ↓reduceIte] at hW2
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [decFound, h0, ↓reduceIte]
    exact hres 0 hW2 hw0 _ (setWith_other _ fe _ _ _ _ a₀ _ hgaf _ _ hct hv
      (fun cv np nf e => by rw [hnone] at e; cases e)) rfl
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hctor := decCI_ctorF hci (erecP_ext _) hS.erec
  rcases (Classical.em (rdW (s.mem.arr64 EREC) (r₂.tail.headD 0) = 4)).symm with h4 | h4
  · simp only [h0, h4, ne_eq, not_false_eq_true, ↓reduceIte] at hW2
    exact hres 0 hW2 hw0 _ (setWith_other _ fe _ _ _ _ a₀ _ hgaf _ _ hct hv
      (fun cv np nf e => hctor.2 h4 cv np nf (by rw [hfind'] at e; exact Option.some.inj e))) rfl
  simp only [h0, h4, ne_eq, not_true_eq_false, ↓reduceIte] at hW2
  obtain ⟨cvc, hci_eq⟩ := hctor.1 h4
  rw [hci_eq] at hci
  -- the constructor's spine
  obtain ⟨r₃, m₃, hc3, hW3⟩ := callW_cases rfl hW2
  obtain ⟨hf3, hg3, hr30, htop3, aargs, hargs, hsp⟩ := getAppArgs_callW hq.leaf.core.spine hS ha hc3
  have hS₃ := hS.frame_stk hf3 (by simp) (by simp)
  have hep : erecP m₃ = erecP s.mem := erecP_frame hf3 (by simp [EREC, SPN]) (by simp)
  have herec : m₃.arr64 EREC = s.mem.arr64 EREC := hf3.1 EREC (by simp [EREC, SPN]) (by decide)
  refine coreRef_congr (setWith_ctor _ fe _ _ _ _ a₀ _ hgaf _ _ hct hv cvc _ _
    (by rw [hfind', hci_eq]) aargs hargs) ?_
  have hlen : aargs.length = (r₃.tail.headD 0).toNat := by simpa using hsp.size
  simp only [swK2, herec] at hW3
  have hspn := hS.spn
  have hsz3 : (m₃.arr64 SPN).size < 2 ^ 63 := hg3.size ▸ hspn
  by_cases hcnt : ¬ r₃.tail.headD 0 < rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 6) ∧
      r₃.tail.headD 0 - rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 6) =
        rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 5)
  · rw [if_neg hcnt.1, if_neg (by simpa using hcnt.2)] at hW3
    rw [if_pos (by rw [hlen]; exact (count_iff _ _ _).mpr hcnt)]
    obtain ⟨r₄, m₄, hc4, hW4⟩ := callW_cases rfl hW3
    simp only [swK3, swRet] at hW4
    have h136 : (136 : Word).toNat < (m₄.arr64 CTL).size := by
      by_cases hh' : (136 : Word).toNat < (m₄.arr64 CTL).size
      · exact hh'
      · simp only [hh', ↓reduceIte] at hW4; cases hW4
    simp only [h136, ↓reduceIte] at hW4
    obtain ⟨hr, hm⟩ := some_pair_inj hW4
    rw [← hm]
    cases n with
    | zero => rw [callW_zero] at hc4; cases hc4
    | succ n' =>
    have hg := GrowSpec.of_callW (setWtb_refines p hq hi hc n' (hk.mono (by omega)) F
      ⟨m₃, Locals.init []⟩ a₀ dn vis fe M eb mode d b us k (r₂.tail.headD 0) (r₃.headD 0)
      (r₃.tail.headD 0) wtb aargs.toArray cvc _ _ (by omega) (by omega) ⟨hS₃, hs.mode4, hs.eb_mode⟩
      hb huw hnw hwtb ⟨_, _, hv⟩ (by rw [hep]; exact hci) hsp (by
        have e := addW_toNat (x := r₃.headD 0) (y := r₃.tail.headD 0) (by have := hsp.bound; omega)
        rw [htop3, ← hr30]; omega)) hc4
    have hg' := growRef_preG hg3 hg
    have := hg'.restore h136
    simp only [List.toList_toArray] at this
    exact ⟨this.1, this.2.1, this.2.2.1.trans (by simp only [decBool, hr]),
      by unfold ResH; rw [← hr]; exact this.2.2.2⟩
  · have hW3' : swRet (rdW (s.mem.arr64 CTL) 136) 0 m₃ = some (r.headD 0, s'.mem) := by
      by_cases hc1 : r₃.tail.headD 0 < rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 6)
      · rw [if_pos hc1] at hW3; exact hW3
      · rw [if_neg hc1, if_pos (fun e => hcnt ⟨hc1, e⟩)] at hW3; exact hW3
    simp only [swRet] at hW3'
    have h136 : (136 : Word).toNat < (m₃.arr64 CTL).size := by
      by_cases hh' : (136 : Word).toNat < (m₃.arr64 CTL).size
      · exact hh'
      · simp only [hh', ↓reduceIte] at hW3'; cases hW3'
    simp only [h136, ↓reduceIte] at hW3'
    obtain ⟨hr, hm⟩ := some_pair_inj hW3'
    rw [← hm]
    rw [if_neg (by rw [hlen, count_iff]; exact hcnt)]
    obtain ⟨hS', hK'⟩ := hS.restoreTop hf3 hg3 h136
    obtain ⟨hok, hst, hres'⟩ := AM.of_run_ok (pure false : AM Bool) a₀ a₀ false rfl
    refine ⟨hok, by rw [hst]; exact ⟨M, hS', KeptAll.refl _ _, hK'⟩, ?_,
      by unfold ResH; rw [← hr]; exact hw0⟩
    rw [hres', decBool, ← hr]; rfl

theorem setWith_at (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d a b wtb : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      HW a → HW b → HW wtb →
      CoreSpec p n "struct_eta_cert_with" [mode, vis, d, a, b, wtb]
        (structEtaCertWith (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (decE wtb))
        decBool s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, b, wtb, hF, hn, hs, h1, h2, h3 =>
      setWith_refines p hq hi hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b wtb
        (by omega) (by omega) hs h1 h2 h3

theorem etaCtorShape_at (p : Prog) (hq : StuckProg p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
      (fe : IFEnv) (MM : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
      CoreSpec p n "eta_ctor_shape" [vis, e] (etaCtorShape fe (decE e)) decBool s₀ a₀ dn vis fe MM eb
  | 0, s₀, a₀, dn, vis, fe, MM, eb, _, _, _ => CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe MM eb _
  | n + 1, s₀, a₀, dn, vis, fe, MM, eb, e, hS, he =>
      etaCtorShape_refines p hq n s₀ a₀ dn vis fe MM eb e hS he

/-! ## `struct_eta_cert` -/

section secK
variable (p : Prog) (n : Nat) (mode vis d a b : Word)

def secK3 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => call1W p n "struct_eta_cert_with" [mode, vis, d, a, b, r.headD 0] m

def secK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => secK3 p n mode vis d a b (callW p n "whnf" [mode, vis, d, r.headD 0] m)

/-- **The model of `struct_eta_cert`** past `eta_ctor_shape`'s run. -/
def secK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, m)
    else secK2 p n mode vis d a b (callW p n "infer_io" [mode, vis, d, b] m)

variable (r : List Word) (m : Mem)
theorem secK3_some : secK3 p n mode vis d a b (some (r, m)) =
    call1W p n "struct_eta_cert_with" [mode, vis, d, a, b, r.headD 0] m := rfl
theorem secK2_some : secK2 p n mode vis d a b (some (r, m)) =
    secK3 p n mode vis d a b (callW p n "whnf" [mode, vis, d, r.headD 0] m) := rfl
theorem secK1_no (h : r.headD 0 = 0) : secK1 p n mode vis d a b (some (r, m)) = some (0, m) := by
  simp only [secK1, h, ↓reduceIte]
theorem secK1_yes (h : r.headD 0 ≠ 0) : secK1 p n mode vis d a b (some (r, m)) =
    secK2 p n mode vis d a b (callW p n "infer_io" [mode, vis, d, b] m) := by
  simp only [secK1, h, ↓reduceIte]

end secK

theorem setCert_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_eta_cert" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ secK1 p n mode vis d a b
      (callW p n "eta_ctor_shape" [vis, a] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.setCert]
  simp only [callFn, structEtaCertL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "eta_ctor_shape",
      callW_spec p n "infer_io", callW_spec p n "whnf", callW_spec p n "struct_eta_cert_with"] <;>
  simp_all [secK1, secK2, secK3, call1W, LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

/-- **`struct_eta_cert` refines `structEtaCert`** at the knot. -/
@[refines ConRon.Arena.structEtaCert]
theorem setCert_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "struct_eta_cert" [mode, vis, d, a, b]
      (structEtaCert (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (setCert_spec p hq n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hK := hk n (Nat.le_refl _)
  obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
  have h₁ := CoreSpec.of_callW (etaCtorShape_at p hq n s a₀ dn vis fe M eb a hs.rel ha) hc1
  unfold structEtaCert
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [secK1_no (h := h0)] at hW1
    obtain ⟨hr, hm⟩ := some_pair_inj hW1
    rw [← hm, decBool_false_of h0]
    exact coreRef_pure hS₁ rfl (decBool_false_of hr.symm).symm (by unfold ResH; rw [← hr]; exact hw0)
  rw [secK1_yes (h := h0)] at hW1
  rw [decBool_true_of h0]
  simp only [↓reduceIte]
  obtain ⟨r₂, m₂, hc2, hW2⟩ := callW_cases rfl hW1
  rw [secK2_some] at hW2
  obtain ⟨r₃, m₃, hc3, hW3⟩ := callW_cases rfl hW2
  rw [secK3_some] at hW3
  have h₂ := CoreSpec.of_callW (hK.inferIO F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d b hF hn
    ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  have h₃ := CoreSpec.of_callW (hK.whnf F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d (r₂.headD 0)
    hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₂.2.2.2) hc3
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  exact CoreSpec.of_call1W (s₀ := ⟨m₃, Locals.init []⟩)
    (setWith_at p hq hi hc n hk F _ _ dn vis fe M₃ eb mode d a b (r₃.headD 0) hF hn
      ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hb h₃.2.2.2)
    (fun r r' h => by simp only [decBool, h]) hW3

end L.Arena
