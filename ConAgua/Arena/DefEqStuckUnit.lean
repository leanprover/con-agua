import ConAgua.Arena.DefEqStuckCert
import ConAgua.Census.Attr

/-!
# `struct_unit_cert` refines `structUnitCert` (lane `defeq`, helper `defeq-top`)

In L's pieces: `struct_unit_cert` (`a`'s type), `struct_unit_head` (its head, family and spine;
the record words read before any call after `env_find`, the twin's pure readers first),
`struct_unit_tail` (`b`'s type against it).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin in L's pieces -/

/-- `structUnitCert` once the family is certified, copied. -/
def suTailT (r : CoreFnsA) (depth : Nat) (b wta : EIdx) : AM Bool := do
  let tb ← r.inferIO depth b
  let wtb ← r.whnf depth tb
  if isForallE wtb then pure false
  else r.defeq depth wta wtb

/-- `structUnitCert` past `a`'s type `wta`, copied. -/
def suHeadT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b wta : EIdx) : AM Bool := do
  let hh ← getAppFn coreWalkFuel wta
  if hh.tag == ETag.const then
    view hh >>= fun v => match v with
      | .const T us' =>
        match fe.find? T with
        | some (.indInfo cvT caps) => do
          let targs ← getAppArgs coreWalkFuel wta
          let reserved ← reservedBasisNames
          match ← viewLsLen us' with
          | none => failDanglingLs
          | some uslen =>
          if caps.unitlike = true ∧ reserved.contains T = false ∧
              targs.length = caps.unitParams ∧
              uslen = cvT.levelParams.length then
            suTailT r depth b wta
          else pure false
        | _ => pure false
      | _ => pure false
  else pure false

theorem structUnitCert_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    structUnitCert r fe depth a b = (do
      let ta ← r.inferIO depth a
      let wta ← r.whnf depth ta
      suHeadT r fe depth b wta) := rfl

section headRuns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b wta : EIdx) (st : AState) (hh : EIdx)
  (hgaf : (getAppFn coreWalkFuel wta).run st = .ok (hh, st))

include hgaf

theorem suHead_nonconst (ht : (hh.tag == ETag.const) = false) :
    (suHeadT r fe depth b wta).run st = .ok (false, st) := by
  simp only [suHeadT, StateT.run_bind, hgaf, except_ok_bind, ht, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem suHead_other (T : NIdx) (us' : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : st.store.view hh = some (.const T us'))
    (hf : ∀ cv caps, fe.find? T ≠ some (.indInfo cv caps)) :
    (suHeadT r fe depth b wta).run st = .ok (false, st) := by
  simp only [suHeadT, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv]
  rcases hc : fe.find? T with _ | ⟨_ | _ | _ | ⟨cv, caps⟩ | _ | _ | _⟩ <;> try rfl
  all_goals exact absurd hc (hf cv caps)

theorem suHead_ind (T : NIdx) (us' : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : st.store.view hh = some (.const T us')) (cvT : IConstantVal) (caps : IIndCaps)
    (hf : fe.find? T = some (.indInfo cvT caps)) (targs : List EIdx)
    (hargs : (getAppArgs coreWalkFuel wta).run st = .ok (targs, st)) {m : Mem}
    (hP : PinsFull m st.pins) (uslen : Nat) (hvl : st.store.lss.viewLen us' = some uslen) :
    (suHeadT r fe depth b wta).run st =
      (if caps.unitlike = true ∧ st.pins.reserved.contains T = false ∧
          targs.length = caps.unitParams ∧ uslen = cvT.levelParams.length then
        suTailT r depth b wta
      else pure false).run st := by
  simp only [suHeadT, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv, hf,
    hargs, reservedBasisNames_run hP, viewLsLen_run, hvl]

end headRuns

/-- A core run whose twin has no effect, in front of a core run. -/
theorem coreRef_pre {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop}
    (hA : CoreAfter dn m₀ m₁ a₀ vis fe M eb)
    (h : ∀ M', CoreS dn m₁ a₀ vis fe M' eb → CoreRef T a₀ dec dn m₁ vis fe M' eb r m ok) :
    CoreRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨M', hS, hK, hSt⟩ := hA
  obtain ⟨hok, hA', hres, hr⟩ := h M' hS
  exact ⟨hok, CoreAfter.comp hK hSt hA', hres, hr⟩

/-! ## `struct_unit_tail` -/

section utK
variable (p : Prog) (n : Nat) (mode vis d b wta : Word)

def utK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 >>> 28 = 6 then some (0, m)
    else call1W p n "defeq" [mode, vis, d, wta, r.headD 0] m

def utK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => utK2 p n mode vis d wta (callW p n "whnf" [mode, vis, d, r.headD 0] m)

variable (r : List Word) (m : Mem)
theorem utK1_some : utK1 p n mode vis d wta (some (r, m)) =
    utK2 p n mode vis d wta (callW p n "whnf" [mode, vis, d, r.headD 0] m) := rfl

end utK

theorem suTail_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (mode vis d b wta : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_unit_tail" [mode, vis, d, b, wta]
    ⦃fun r s' => LocEq s' s₀ ∧ utK1 p n mode vis d wta
      (callW p n "infer_io" [mode, vis, d, b] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.suTail]
  simp only [callFn, structUnitTailL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "infer_io",
      callW_spec p n "whnf", callW_spec p n "defeq"] <;>
  simp_all [utK1, utK2, call1W, LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

/-- **`struct_unit_tail` refines `suTailT`** at the knot. -/
@[refines_part ConRon.Arena.structUnitCert "b's type against a's (suTailT)"]
theorem suTail_refines (p : Prog) (hq : StuckProg p) (n : Nat) (hk : KnotUpTo p n) (F : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d b wta : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hwta : HW wta) :
    CoreSpec p (n + 1) "struct_unit_tail" [mode, vis, d, b, wta]
      (suTailT (coreKnot (decMode mode) fe id F) d.toNat (decE b) (decE wta)) decBool
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (suTail_spec p hq n s₀ mode vis d b wta)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hK := hk n (Nat.le_refl _)
  obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
  rw [utK1_some] at hW1
  obtain ⟨r₂, m₂, hc2, hW2⟩ := callW_cases rfl hW1
  have h₁ := CoreSpec.of_callW (hK.inferIO F s a₀ dn vis fe M eb mode d b hF hn hs hb) hc1
  unfold suTailT
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  have h₂ := CoreSpec.of_callW (hK.whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0)
    hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  have hh2 : HW (r₂.headD 0) := h₂.2.2.2
  simp only [isForallE, decH, tag_beq_w _ hh2 6 (by decide) ETag.forallE rfl 6 rfl]
  simp only [utK2] at hW2
  by_cases h6 : r₂.headD 0 >>> 28 = 6
  · simp only [h6, ↓reduceIte] at hW2
    obtain ⟨hr, hm⟩ := some_pair_inj hW2
    rw [← hm]
    simp only [h6, decide_true, ↓reduceIte]
    exact coreRef_pure hS₂ rfl (decBool_false_of hr.symm).symm (by unfold ResH; rw [← hr]; exact hw0)
  simp only [h6, ↓reduceIte] at hW2
  simp only [h6, decide_false, Bool.false_eq_true, ↓reduceIte]
  exact CoreSpec.of_call1W (s₀ := ⟨m₂, Locals.init []⟩)
    (hK.defeq F _ _ dn vis fe M₂ eb mode d wta (r₂.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ hwta hh2)
    (fun r r' h => by simp only [decBool, h]) hW2

theorem suTail_at (p : Prog) (hq : StuckProg p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d b wta : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      HW b → HW wta →
      CoreSpec p n "struct_unit_tail" [mode, vis, d, b, wta]
        (suTailT (coreKnot (decMode mode) fe id F) d.toNat (decE b) (decE wta)) decBool
        s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, b, wta, hF, hn, hs, h1, h2 =>
      suTail_refines p hq n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d b wta
        (by omega) (by omega) hs h1 h2

/-! ## `struct_unit_head` -/

section uhK
variable (p : Prog) (n : Nat) (mode vis d b wta : Word)

/-- The tests, then the tail. -/
def uhK5 (ul up lpn tn uslen : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if ul = 0 then some (0, m)
    else if r.headD 0 ≠ 0 then some (0, m)
    else if tn ≠ up then some (0, m)
    else if uslen ≠ lpn then some (0, m)
    else call1W p n "struct_unit_tail" [mode, vis, d, b, wta] m

def uhK4 (T ul up lpn tn : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => uhK5 p n mode vis d b wta ul up lpn tn (r.tail.headD 0)
      (callW p n "reserved_contains_w" [T] m)

/-- After the type's spine: the top put back, `ls_node`. -/
def uhK3 (T us2 ul up lpn top : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if (136 : Word).toNat < (m.arr64 CTL).size then
      uhK4 p n mode vis d b wta T ul up lpn (r.tail.headD 0)
        (callW p n "ls_node" [us2] (m.set64 CTL 136 top))
    else none

def uhK2 (T us2 : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, m)
    else if rdW (m.arr64 EREC) (r.tail.headD 0) ≠ 3 then some (0, m)
    else uhK3 p n mode vis d b wta T us2 (rdW (m.arr64 EREC) (r.tail.headD 0 + 9))
      (rdW (m.arr64 EREC) (r.tail.headD 0 + 10)) (rdW (m.arr64 EREC) (r.tail.headD 0 + 3))
      (rdW (m.arr64 CTL) 136) (callW p n "get_app_args" [wta] m)

/-- **The model of `struct_unit_head`** past `get_app_fn`'s run. -/
def uhK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 >>> 28 ≠ 3 then some (0, m)
    else if tierW (r.headD 0) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m CONST (tierW (r.headD 0)) ≤ idxW (r.headD 0) then none
    else uhK2 p n mode vis d b wta
      (tfld m CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0)
      (tfld m CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 1)
      (callW p n "env_find" [tfld m CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0, vis] m)

variable (T us2 ul up lpn tn top uslen : Word) (r : List Word) (m : Mem)

theorem uhK4_some : uhK4 p n mode vis d b wta T ul up lpn tn (some (r, m)) =
    uhK5 p n mode vis d b wta ul up lpn tn (r.tail.headD 0) (callW p n "reserved_contains_w" [T] m) := rfl

/-- The tests of `struct_unit_head`, all passed. -/
def uhOK : Prop := ul ≠ 0 ∧ r.headD 0 = 0 ∧ tn = up ∧ uslen = lpn

theorem uhK5_yes (h : uhOK ul up lpn tn uslen r) : uhK5 p n mode vis d b wta ul up lpn tn uslen (some (r, m)) =
    call1W p n "struct_unit_tail" [mode, vis, d, b, wta] m := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [uhK5, h1, h2, h3, h4, ne_eq, not_true_eq_false, ↓reduceIte]

theorem uhK5_no (h : ¬ uhOK ul up lpn tn uslen r) :
    uhK5 p n mode vis d b wta ul up lpn tn uslen (some (r, m)) = some (0, m) := by
  unfold uhK5
  by_cases h1 : ul = 0
  · simp only [h1, ↓reduceIte]
  by_cases h2 : r.headD 0 ≠ 0
  · simp only [h1, h2, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h3 : tn ≠ up
  · simp only [h1, h2, h3, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h4 : uslen ≠ lpn
  · simp only [h1, h2, h3, h4, ne_eq, not_false_eq_true, ↓reduceIte]
  exact absurd ⟨h1, by simpa using h2, by simpa using h3, by simpa using h4⟩ h

end uhK

theorem suHead_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (mode vis d b wta : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_unit_head" [mode, vis, d, b, wta]
    ⦃fun r s' => LocEq s' s₀ ∧ uhK1 p n mode vis d b wta
      (callW p n "get_app_fn" [wta] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.suHead]
  simp only [callFn, structUnitHeadL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, evalE_tld, tld,
    evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64_spec,
      callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "get_app_args",
      callW_spec p n "ls_node", callW_spec p n "reserved_contains_w",
      callW_spec p n "struct_unit_tail"] <;>
  simp_all [uhK1, uhK2, uhK3, uhK4, uhK5, call1W, tierW, idxW, LocEq,
    BinOp.eval, St.setLocs_cons,
    CTL, EREC, Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-- **`struct_unit_head` refines `suHeadT`** at the knot (the top put back). -/
@[refines_part ConRon.Arena.structUnitCert "a's type's head, family and spine (suHeadT)"]
theorem suHead_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d b wta : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hwta : HW wta) :
    CoreSpec p (n + 1) "struct_unit_head" [mode, vis, d, b, wta]
      (suHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decE wta)) decBool
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (suHead_spec p hq n s₀ mode vis d b wta)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hR := hS.arena.1
  have hres : ∀ x : Word, some (x, s.mem) = some (r.headD 0, s'.mem) → HW x → ∀ v,
      (suHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decE wta)).run a₀ =
        .ok (v, a₀) → v = (x != 0) →
      CoreRef (suHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decE wta)) a₀ decBool
        dn s.mem vis fe M eb r s'.mem := by
    intro x hxy hx v hv hvx
    obtain ⟨h1, h3⟩ := some_pair_inj hxy
    rw [← h3]
    refine coreRef_pure hS hv ?_ ?_
    · rw [hvx, decBool, ← h1]
    · unfold ResH; rw [← h1]; exact hx
  obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
  obtain ⟨rfl, hh, hgaf⟩ := getAppFn_callW hq.leaf hR hwta hc1
  simp only [uhK1] at hW1
  generalize r₁.headD 0 = h at hh hgaf hW1
  rcases (Classical.em (h >>> 28 = 3)).symm with h3 | h3
  · simp only [ne_eq, h3, not_false_eq_true, ↓reduceIte] at hW1
    exact hres 0 hW1 hw0 _
      (suHead_nonconst _ fe _ _ _ a₀ _ hgaf (by rw [tag_beq_const _ hh]; simp [h3])) rfl
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
  simp only [uhK2] at hW2
  by_cases h0 : r₂.headD 0 = 0
  · simp only [h0, ↓reduceIte] at hW2
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [decFound, h0, ↓reduceIte]
    exact hres 0 hW2 hw0 _ (suHead_other _ fe _ _ _ a₀ _ hgaf _ _ hct hv
      (fun cv caps e => by rw [hnone] at e; cases e)) rfl
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hind := decCI_indK hci (erecP_ext _) hS.erec
  rcases (Classical.em (rdW (s.mem.arr64 EREC) (r₂.tail.headD 0) = 3)).symm with h4 | h4
  · simp only [h0, h4, ne_eq, not_false_eq_true, ↓reduceIte] at hW2
    exact hres 0 hW2 hw0 _ (suHead_other _ fe _ _ _ a₀ _ hgaf _ _ hct hv
      (fun cv caps e => hind.2 h4 cv caps (by rw [hfind'] at e; exact Option.some.inj e))) rfl
  simp only [h0, h4, ne_eq, not_true_eq_false, ↓reduceIte] at hW2
  obtain ⟨cvT, caps, hci_eq⟩ := hind.1 h4
  rw [hci_eq] at hci
  have hIR := decCI_indCaps hci (erecP_ext _) hS.erec
  -- the type's spine, the top put back
  obtain ⟨r₃, m₃, hc3, hW3⟩ := callW_cases rfl hW2
  obtain ⟨hf3, hg3, -, -, targs, hargs, hsp⟩ := getAppArgs_callW hq.leaf.core.spine hS hwta hc3
  simp only [uhK3] at hW3
  have h136 : (136 : Word).toNat < (m₃.arr64 CTL).size := by
    by_cases hh' : (136 : Word).toNat < (m₃.arr64 CTL).size
    · exact hh'
    · simp only [hh', ↓reduceIte] at hW3; cases hW3
  simp only [h136, ↓reduceIte] at hW3
  obtain ⟨hS₃, hK₃⟩ := hS.restoreTop hf3 hg3 h136
  have hlen : targs.length = (r₃.tail.headD 0).toNat := by simpa using hsp.size
  -- `ls_node`
  obtain ⟨r₄, m₄, hc4, hW4⟩ := callW_cases rfl hW3
  obtain ⟨t₄, ht₄, ht₄s, hne, hr₄⟩ := triple_of_callW
    (s₀ := ⟨m₃.set64 CTL 136 (rdW (s.mem.arr64 CTL) 136), Locals.init []⟩)
    (lsNode_spec p hq.leaf.core.lsn n ⟨m₃.set64 CTL 136 (rdW (s.mem.arr64 CTL) 136), Locals.init []⟩
      us2) hc4
  have em₄ : m₄ = m₃.set64 CTL 136 (rdW (s.mem.arr64 CTL) 136) := by rw [← ht₄, ht₄s]
  rw [hr₄] at hne
  have hvl := defeq_lsNodeW_viewLen hS₃.arena.1 huw hne
  rw [← hr₄] at hvl
  rw [em₄, uhK4_some] at hW4
  -- `reserved_contains`
  obtain ⟨r₅, m₅, hc5, hW5⟩ := callW_cases rfl hW4
  obtain ⟨hA₅, hr₅⟩ := reservedContains_callW hc hS₃ hnw hc5
  refine coreRef_congr (suHead_ind _ fe _ _ _ a₀ _ hgaf _ _ hct hv cvT caps
    (by rw [hfind', hci_eq]) targs hargs hS.pins _ hvl) ?_
  have hA₅' : CoreAfter dn s.mem m₅ a₀ vis fe M eb := by
    obtain ⟨M', hS', hK', hSt'⟩ := hA₅
    exact ⟨M', hS', hK', hK₃.trans hSt'⟩
  refine coreRef_pre hA₅' (fun M₅ hS₅ => ?_)
  have hlpT : cvT.levelParams.length = (rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 3)).toNat :=
    hslice?_length hIR.lp
  have hiff : (caps.unitlike = true ∧ a₀.pins.reserved.contains (decI k) = false ∧
      targs.length = caps.unitParams ∧ (r₄.tail.headD 0).toNat = cvT.levelParams.length) ↔
      uhOK (rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 9)) (rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 10))
        (rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 3)) (r₃.tail.headD 0) (r₄.tail.headD 0) r₅ := by
    unfold uhOK
    rw [hIR.unitlike, ← hr₅, hlen, hIR.unitParams, hlpT]
    simp only [decBool, bne_iff_ne, ne_eq, bne_eq_false_iff_eq,
      UInt64.toNat_inj]
  by_cases hok : uhOK (rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 9))
      (rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 10)) (rdW (s.mem.arr64 EREC) (r₂.tail.headD 0 + 3))
      (r₃.tail.headD 0) (r₄.tail.headD 0) r₅
  · rw [uhK5_yes (h := hok)] at hW5
    rw [ite_eq_left (hiff.mpr hok)]
    exact CoreSpec.of_call1W (s₀ := ⟨m₅, Locals.init []⟩)
      (suTail_at p hq n hk F _ _ dn vis fe M₅ eb mode d b wta hF hn ⟨hS₅, hs.mode4, hs.eb_mode⟩ hb hwta)
      (fun r r' h => by simp only [decBool, h]) hW5
  · rw [uhK5_no (h := hok)] at hW5
    obtain ⟨hr, hm⟩ := some_pair_inj hW5
    rw [← hm, ite_eq_right (fun h => hok (hiff.mp h))]
    exact coreRef_pure hS₅ rfl (decBool_false_of hr.symm).symm (by unfold ResH; rw [← hr]; exact hw0)

theorem suHead_at (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d b wta : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      HW b → HW wta →
      CoreSpec p n "struct_unit_head" [mode, vis, d, b, wta]
        (suHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decE wta)) decBool
        s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, b, wta, hF, hn, hs, h1, h2 =>
      suHead_refines p hq hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d b wta
        (by omega) (by omega) hs h1 h2

/-! ## `struct_unit_cert` -/

section sucK
variable (p : Prog) (n : Nat) (mode vis d a b : Word)

def sucK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => call1W p n "struct_unit_head" [mode, vis, d, b, r.headD 0] m

/-- **The model of `struct_unit_cert`** past `infer_io`'s run. -/
def sucK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => sucK2 p n mode vis d b (callW p n "whnf" [mode, vis, d, r.headD 0] m)

variable (r : List Word) (m : Mem)
theorem sucK2_some : sucK2 p n mode vis d b (some (r, m)) =
    call1W p n "struct_unit_head" [mode, vis, d, b, r.headD 0] m := rfl
theorem sucK1_some : sucK1 p n mode vis d b (some (r, m)) =
    sucK2 p n mode vis d b (callW p n "whnf" [mode, vis, d, r.headD 0] m) := rfl

end sucK

theorem suCert_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_unit_cert" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ sucK1 p n mode vis d b
      (callW p n "infer_io" [mode, vis, d, a] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.sunit]
  simp only [callFn, structUnitCertL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "infer_io",
      callW_spec p n "whnf", callW_spec p n "struct_unit_head"] <;>
  simp_all [sucK1, sucK2, call1W, LocEq, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

/-- **`struct_unit_cert` refines `structUnitCert`** at the knot. -/
@[refines ConRon.Arena.structUnitCert]
theorem suCert_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "struct_unit_cert" [mode, vis, d, a, b]
      (structUnitCert (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (suCert_spec p hq n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hK := hk n (Nat.le_refl _)
  rw [structUnitCert_eq]
  obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
  rw [sucK1_some] at hW1
  obtain ⟨r₂, m₂, hc2, hW2⟩ := callW_cases rfl hW1
  rw [sucK2_some] at hW2
  have h₁ := CoreSpec.of_callW (hK.inferIO F s a₀ dn vis fe M eb mode d a hF hn hs ha) hc1
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  have h₂ := CoreSpec.of_callW (hK.whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0)
    hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  exact CoreSpec.of_call1W (s₀ := ⟨m₂, Locals.init []⟩)
    (suHead_at p hq hc n hk F _ _ dn vis fe M₂ eb mode d b (r₂.headD 0) hF hn
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ hb h₂.2.2.2)
    (fun r r' h => by simp only [decBool, h]) hW2

end L.Arena
