import ConAgua.Arena.InferBodyBindPi

/-!
# The bodies' dispatchers: `infer_body`, `infer_body_io` (lane `defeq`)

`e_view` reads the node (`L.Ind.eView_refines`), the dispatcher calls the clause, and each clause's
refinement (`InferLeaves.lean`, `InferBodyLet.lean`, `InferBodySpine*.lean`, `InferBodyBind*.lean`)
is the twin's arm (`inferBody_*`, `inferBodyIO_*`). Together: `InferBodySpec p n` and
`InferIOBodySpec p n` from `KnotUpTo p n`, the programs, and the callees with no proof yet
(`InferCallees`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## The `.const` arm of the io body -/

theorem LsStore.viewLen_of_view (st : LsStore) (i : LsIdx) (ids : List LIdx)
    (h : st.view i = some ids) : st.viewLen i = some ids.length := by
  unfold LsStore.view at h
  unfold LsStore.viewLen LsStore.persGetLen
  split at h
  · rw [if_pos (by assumption)]
    unfold LsTables.get at h; unfold LsTables.getLen
    split at h
    · rw [if_pos (by assumption)]
      cases e : i |> fun _ => (st.pers.lists.node? i.idxNat) with
      | none | some r => simp_all
    · cases h
  · rw [if_neg (by assumption)]
    split at h
    · rw [if_pos (by assumption)]
      unfold LsTables.get at h; unfold LsTables.getLen
      split at h
      · rw [if_pos (by assumption)]
        cases e : (st.scr.lists.node? i.idxNat) with
        | none | some r => simp_all
      · cases h
    · cases h

/-- **The `.const` clause of `inferBodyIO`**, copied (the length read by `viewLsLen`). -/
def inferConstIOT (fe : IFEnv) (n : NIdx) (us : LsIdx) : AM EIdx :=
  match fe.find? n with
  | none => do
    let err ← unknownConstError n
    fail err
  | some ci => do
    let cv := ci.toConstantVal
    match ← viewLsLen us with
    | none => failDanglingLs
    | some usl =>
    if usl != cv.levelParams.length then do
      fail (.invalid "incorrect number of universe levels")
    else constTyAt cv us

/-- `inferBodyIO`'s `.const` arm is `inferConstIOT`. -/
@[refines_part ConRon.Arena.inferBodyIO "const"]
theorem inferBodyIO_const (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState) (n : NIdx)
    (us : LsIdx) (hv : a.store.view e = some (.const n us)) :
    (inferBodyIO r fe d e).run a = (inferConstIOT fe n us).run a := by
  simp only [inferBodyIO, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  rfl

/-- **A successful run of the full `.const` clause is one of the io clause.** -/
theorem inferConstIOT_of_T (fe : IFEnv) (n : NIdx) (us : LsIdx) (a : AState) (x : EIdx) (a' : AState)
    (h : (inferConstT fe n us).run a = .ok (x, a')) : (inferConstIOT fe n us).run a = .ok (x, a') := by
  unfold inferConstT at h; unfold inferConstIOT
  cases hf : fe.find? n with
  | none => rw [hf] at h; exact h
  | some ci =>
  rw [hf] at h
  simp only [StateT.run_bind] at h ⊢
  generalize ci.toConstantVal = cv at h ⊢
  generalize a = a₁ at h ⊢
  cases hv : a₁.store.lss.view us with
  | none =>
    have e1 : ∃ err, (viewLs us).run a₁ = .error err := by
      refine ⟨.internal "arena: dangling level-list handle", ?_⟩
      simp only [viewLs, StateT.run_bind, StateT.run_get, pure_bind, hv]; rfl
    obtain ⟨err, e1⟩ := e1
    rw [e1] at h; cases h
  | some ids =>
  have hl := LsStore.viewLen_of_view _ _ _ hv
  have e1 : (viewLs us).run a₁ = .ok (ids, a₁) := viewLs_run us a₁ ids hv
  have e2 : (viewLsLen us).run a₁ = .ok (some ids.length, a₁) := by
    simp [viewLsLen, hl, StateT.run_bind, StateT.run_get]; rfl
  rw [e1] at h; rw [e2]
  simp only [except_ok_bind] at h ⊢
  exact h

/-! ## The callees and programs -/

/-- `infer_proj(mode, io, vis, d, sn, i, pe)` refines `inferProj` at both grades (the step this
file leaves open: `InferProj*.lean`). -/
def InferProjOK (p : Prog) : Prop :=
  ∀ n, KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d sn i pe : Word), n ≤ F → n ≤ 2 ^ 62 →
    SlotPre s₀ a₀ dn vis fe M eb mode → HW sn → HW pe →
    CoreSpec p (n + 1) "infer_proj" [mode, 0, vis, d, sn, i, pe]
      (inferProj (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat (decE pe)) decH
      s₀ a₀ dn vis fe M eb ∧
    CoreSpec p (n + 1) "infer_proj" [mode, 1, vis, d, sn, i, pe]
      (inferProj (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decI sn) i.toNat
        (decE pe)) decH s₀ a₀ dn vis fe M eb

/-- **The callees of the inference bodies with no proof here.** -/
structure InferCallees (p : Prog) : Prop where
  inst1 : Inst1OK p
  instList : InstListOK p
  abs1 : Abstract1OK p
  absRange : AbstractRangeOK p
  constTy : ConstTyAtOK p
  lit : InferLitCallees p
  eager : IsEagerReduceH p
  bcap : BStkCap
  proj : InferProjOK p

/-- **What the bodies need of a program.** -/
structure InferAllProg (p : Prog) : Prop where
  leaf : InferLeafProg p
  knot : KnotProg p
  body : InferBodyProg p
  spio : SpineInferProg p
  spine : SpineProg p
  spf : SpineFProg p
  bind : BindProg p
  eview : p.lookup "e_view" = some L.Ind.eView
  inferBody : p.lookup "infer_body" = some inferBodyL
  inferBodyIO : p.lookup "infer_body_io" = some inferBodyIOL

/-! ## The models -/

section models
variable (p : Prog) (n : Nat) (m : Mem) (mode vis d e g x1 x2 x3 : Word)

/-- The `.sort` arm: `succ`, then the sort. -/
def sortArmK : Option (Word × Mem) :=
  match callW p n "intern_succ" [x1] m with
  | none => none
  | some (r, m₁) => call1W p n "intern_sort" [r.headD 0] m₁

/-- The full body's arms past `e_view`. -/
def bodyArmK : Option (Word × Mem) :=
  if g = 2 then sortArmK p n m x1
  else if g = 1 then (if x1 < d then some (x2, m) else none)
  else if g = 3 then call1W p n "infer_const" [vis, x1, x2] m
  else if g = 8 then call1W p n "infer_lit" [vis, e] m
  else if g = 6 then call1W p n "infer_forall" [mode, vis, d, x1, x2] m
  else if g = 5 then call1W p n "infer_lam" [mode, vis, d, x1, x2] m
  else if g = 4 then call1W p n "infer_app" [mode, vis, d, e] m
  else if g = 9 then call1W p n "infer_proj" [mode, 0, vis, d, x1, x2, x3] m
  else if g = 7 then call1W p n "infer_let" [mode, vis, d, x1, x2, x3] m
  else none

/-- The io `.letE` arm: the body at the value. -/
def letIOArmK : Option (Word × Mem) :=
  match callW p n "inst1" [x3, x2, 0] m with
  | none => none
  | some (r, m₁) => call1W p n "infer_io" [mode, vis, d, r.headD 0] m₁

/-- The io body's arms past `e_view`. -/
def bodyIOArmK : Option (Word × Mem) :=
  if g = 2 then sortArmK p n m x1
  else if g = 1 then (if x1 < d then some (x2, m) else none)
  else if g = 3 then call1W p n "infer_const" [vis, x1, x2] m
  else if g = 8 then call1W p n "infer_lit" [vis, e] m
  else if g = 6 then call1W p n "infer_forall_io" [mode, vis, d, x1, x2] m
  else if g = 5 then call1W p n "infer_lam_io" [mode, vis, d, x1, x2] m
  else if g = 4 then call1W p n "infer_app_io" [mode, vis, d, e] m
  else if g = 9 then call1W p n "infer_proj" [mode, 1, vis, d, x1, x2, x3] m
  else if g = 7 then letIOArmK p n m mode vis d x2 x3
  else none

/-- **The model of `infer_body`.** -/
def bodyK : Option (Word × Mem) :=
  match callW p n "e_view" [e] m with
  | none => none
  | some (r, m₁) => bodyArmK p n m₁ mode vis d e (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0)
      (r.tail.tail.tail.headD 0)

/-- **The model of `infer_body_io`.** -/
def bodyIOK : Option (Word × Mem) :=
  match callW p n "e_view" [e] m with
  | none => none
  | some (r, m₁) => bodyIOArmK p n m₁ mode vis d e (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0)
      (r.tail.tail.tail.headD 0)

end models

theorem inferBody_spec (p : Prog) (hq : InferAllProg p) (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_body" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ bodyK p n s₀.mem mode vis d e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.inferBody]
  simp only [callFn, inferBodyL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "e_view",
      callW_spec p n "intern_succ", callW_spec p n "intern_sort", callW_spec p n "infer_const",
      callW_spec p n "infer_lit", callW_spec p n "infer_forall", callW_spec p n "infer_lam",
      callW_spec p n "infer_app", callW_spec p n "infer_proj", callW_spec p n "infer_let"] <;>
  simp_all [bodyK, bodyArmK, sortArmK, call1W, LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

theorem inferBodyIO_spec (p : Prog) (hq : InferAllProg p) (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_body_io" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ bodyIOK p n s₀.mem mode vis d e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.inferBodyIO]
  simp only [callFn, inferBodyIOL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "e_view",
      callW_spec p n "intern_succ", callW_spec p n "intern_sort", callW_spec p n "infer_const",
      callW_spec p n "infer_lit", callW_spec p n "infer_forall_io", callW_spec p n "infer_lam_io",
      callW_spec p n "infer_app_io", callW_spec p n "infer_proj", callW_spec p n "inst1",
      callW_spec p n "infer_io"] <;>
  simp_all [bodyIOK, bodyIOArmK, sortArmK, letIOArmK, call1W, LocEq, BinOp.eval, St.setLocs_cons,
    Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

/-! ## The arms -/

theorem eViewW_head (m : Mem) (h : Word) (hne : L.Ind.eViewW m h ≠ []) :
    (L.Ind.eViewW m h).headD 0 = h >>> 28 := by
  unfold L.Ind.eViewW at hne ⊢
  dsimp only at hne ⊢
  have c0 : ¬ (4294967295 : Word) < h := fun c0 => by rw [if_pos c0] at hne; exact absurd rfl hne
  rw [if_neg c0] at hne ⊢
  have c1 : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := fun c1 => by rw [if_pos c1] at hne; exact absurd rfl hne
  rw [if_neg c1] at hne ⊢
  by_cases g0 : h >>> 28 = 0
  · rw [if_pos g0] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [if_neg hc, g0]; rfl
  rw [if_neg g0] at hne ⊢
  by_cases g1 : h >>> 28 = 1
  · rw [if_pos g1] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [if_neg hc, g1]; rfl
  rw [if_neg g1] at hne ⊢
  by_cases g2 : h >>> 28 = 2
  · rw [if_pos g2] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [if_neg hc, g2]; rfl
  rw [if_neg g2] at hne ⊢
  by_cases g3 : h >>> 28 = 3
  · rw [if_pos g3] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [if_neg hc, g3]; rfl
  rw [if_neg g3] at hne ⊢
  by_cases g4 : h >>> 28 = 4
  · rw [if_pos g4] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [if_neg hc, g4]; rfl
  rw [if_neg g4] at hne ⊢
  by_cases g5 : h >>> 28 = 5
  · rw [if_pos g5] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [if_neg hc, g5]; rfl
  rw [if_neg g5] at hne ⊢
  by_cases g6 : h >>> 28 = 6
  · rw [if_pos g6] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [if_neg hc, g6]; rfl
  rw [if_neg g6] at hne ⊢
  by_cases g7 : h >>> 28 = 7
  · rw [if_pos g7] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [if_neg hc, g7]; rfl
  rw [if_neg g7] at hne ⊢
  by_cases g8 : h >>> 28 = 8
  · rw [if_pos g8] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [if_neg hc, g8]; rfl
  rw [if_neg g8] at hne ⊢
  by_cases g9 : h >>> 28 = 9
  · rw [if_pos g9] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [if_neg hc, g9]; rfl
  rw [if_neg g9] at hne ⊢
  exact absurd rfl hne

section arms
variable (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)

theorem inferBody_sort (u : LIdx) (hv : a.store.view e = some (.sort u)) :
    (inferBody r fe d e).run a = (internLNode (.succ u) >>= fun su => internE (.sort su)).run a := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]

theorem inferBodyIO_sort (u : LIdx) (hv : a.store.view e = some (.sort u)) :
    (inferBodyIO r fe d e).run a = (internLNode (.succ u) >>= fun su => internE (.sort su)).run a := by
  simp only [inferBodyIO, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]

theorem inferBody_fvar (i : Nat) (ty : EIdx) (hv : a.store.view e = some (.fvar i ty)) (hi : i < d) :
    (inferBody r fe d e).run a = .ok (ty, a) := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hi, ↓reduceIte]; rfl

theorem inferBodyIO_fvar (i : Nat) (ty : EIdx) (hv : a.store.view e = some (.fvar i ty)) (hi : i < d) :
    (inferBodyIO r fe d e).run a = .ok (ty, a) := by
  simp only [inferBodyIO, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hi, ↓reduceIte]; rfl

theorem inferBody_proj (sn : NIdx) (i : Nat) (pe : EIdx) (hv : a.store.view e = some (.proj sn i pe)) :
    (inferBody r fe d e).run a = (inferProj r fe d sn i pe).run a := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]

theorem inferBodyIO_proj (sn : NIdx) (i : Nat) (pe : EIdx) (hv : a.store.view e = some (.proj sn i pe)) :
    (inferBodyIO r fe d e).run a = (inferProj r fe d sn i pe).run a := by
  simp only [inferBodyIO, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]

theorem inferBodyIO_let (ty v b : EIdx) (hv : a.store.view e = some (.letE ty v b)) :
    (inferBodyIO r fe d e).run a =
      (instantiate1Fast coreWalkFuel b v 0 >>= fun ob => r.infer d ob).run a := by
  simp only [inferBodyIO, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]

end arms

/-- A refinement of a twin run carries over to a twin run that succeeds wherever it does, alike. -/
theorem coreRef_of_imp {α : Type} [Inhabited α] {T T' : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop}
    (himp : ∀ x a', T.run a₀ = .ok (x, a') → T'.run a₀ = .ok (x, a'))
    (h : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok) : CoreRef T' a₀ dec dn m₀ vis fe M eb r m ok :=
  coreRef_congr ((himp _ _ (AM.run_of_ok _ _ h.1)).trans (AM.run_of_ok _ _ h.1).symm) h

theorem getD1 (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> rfl
theorem getD2 (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩ <;> rfl
theorem getD3 (r : List Word) : r.getD 3 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, t⟩⟩⟩⟩ <;> rfl

/-! ## `infer_body` refines `inferBody` -/

/-- **`infer_body` refines `inferBody`** at the knot one level down: `InferBodySpec p n` for every
`n`, from the programs and the callees with no proof here (`InferCallees`). -/
@[refines ConRon.Arena.inferBody]
theorem inferBody_refines (p : Prog) (hq : InferAllProg p) (hc : InferCallees p) :
    ∀ n, InferBodySpec p n := by
  intro n F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he hk
  cases n with
  | zero => exact CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe MM eb _
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (inferBody_spec p hq n s₀ mode vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold bodyK at hW
  cases hc0 : callW p n "e_view" [e] s.mem with
  | none => rw [hc0] at hW; cases hW
  | some q =>
  obtain ⟨r₀, m₀⟩ := q
  rw [hc0] at hW; dsimp only at hW
  obtain ⟨t₀, ht₀, hts, hne, hr0⟩ := triple_of_callW (L.Ind.eView_spec p hq.eview n s e) hc0
  have hm₀ : m₀ = s.mem := by rw [← ht₀, hts]
  subst hm₀
  subst hr0
  obtain ⟨v, hv, hvr⟩ := L.Ind.eViewW_ok s.mem a₀ hS.arena.1 e hne
  have hhd := eViewW_head s.mem e hne
  have fin : ∀ {T : AM EIdx} {f : FnName} {vs : List Word},
      CoreSpec p n f vs T decH ⟨s.mem, Locals.init []⟩ a₀ dn vis fe MM eb →
      call1W p n f vs s.mem = some (r.headD 0, s'.mem) →
      CoreRef T a₀ decH dn s.mem vis fe MM eb r s'.mem :=
    fun hsp h => CoreSpec.of_call1W hsp (fun r r' h => by simp only [decH, h]) h
  have hsl : SlotPre ⟨s.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode := ⟨hS, hs.mode4, hs.eb_mode⟩
  have hz : ∀ {f : FnName} {vs : List Word} {w : Word} {m' : Mem}, call1W p 0 f vs s.mem ≠ some (w, m') :=
    fun h => by simp [call1W, callW_zero] at h
  cases v with
  | bvar i =>
    obtain ⟨hg, -⟩ := hvr
    simp (config := { decide := true }) only [bodyArmK, hg, ↓reduceIte] at hW
    cases hW
  | fvar idx ty =>
    obtain ⟨hg, hi, hty, hdec⟩ := hvr
    simp (config := { decide := true }) only [bodyArmK, hg, ↓reduceIte] at hW
    rw [getD1] at hi; rw [getD2] at hty hdec
    by_cases hlt : (L.Ind.eViewW s.mem e).tail.headD 0 < d
    · simp only [hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr, hm⟩ := hW
      have hi' : idx < d.toNat := by rw [← hi]; exact UInt64.lt_iff_toNat_lt.mp hlt
      have hrun := inferBody_fvar (coreKnot (decMode mode) fe id F) fe d.toNat (decE e) a₀ idx ty hv hi'
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
      refine ⟨hok, ?_, by rw [hres, decH, ← hr, hdec], by unfold ResH; rw [← hr]; exact hty⟩
      rw [hst, ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
    · simp only [hlt, ↓reduceIte] at hW; cases hW
  | sort u =>
    obtain ⟨hg, hu, hdec⟩ := hvr
    rw [getD1] at hu hdec
    simp (config := { decide := true }) only [bodyArmK, hg, ↓reduceIte, sortArmK] at hW
    cases h1 : callW p n "intern_succ" [(L.Ind.eViewW s.mem e).tail.headD 0] s.mem with
    | none => rw [h1] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [h1] at hW; dsimp only at hW
    obtain ⟨s₁, hs₁, -, hsu⟩ := triple_of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
      (internSucc_spec p hq.body.suf hq.body.sup hq.body.sui n _ _) h1
    rw [hs₁] at hsu
    have h₁ := internSucc_core hS _ hu r₁ hsu (by rw [hdec]; exact hS.den.sort _ _ hv)
    rw [hdec] at h₁
    refine coreRef_congr (inferBody_sort _ fe d.toNat (decE e) a₀ u hv) (coreRef_bind h₁ (fun M₁ hS₁ => ?_))
    have hso := of_call1W (X := fun m w m' => sointernW m (r₁.headD 0) = some (w, m'))
      (fun s₀ => internSort_spec p hq.body.sof hq.body.sop hq.body.soi n s₀ (r₁.headD 0)) hW
    exact internSort_core hS₁ (r₁.headD 0) h₁.2.2.2 r hso (by
      have hd := internLNode_res_den (v := .succ u) hS
        (fun c hc => by simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc; subst hc; exact hS.den.sort _ _ hv)
        (fun n hn => by simp [LNodeView.nchildren] at hn) h₁.1
      rw [h₁.2.2.1] at hd; exact hd)
  | const nm us =>
    obtain ⟨hg, hn1, hdn, hu2, hdu⟩ := hvr
    rw [getD1] at hn1 hdn; rw [getD2] at hu2 hdu
    simp (config := { decide := true }) only [bodyArmK, hg, ↓reduceIte] at hW
    cases n with
    | zero => exact absurd hW hz
    | succ k =>
    rw [← hdn, ← hdu] at hv
    exact coreRef_congr (inferBody_const _ fe d.toNat (decE e) a₀ _ _ hv)
      (fin (inferConst_refines p hq.leaf hc.constTy k _ a₀ dn vis fe MM eb _ _ hS hn1 hu2) hW)
  | lit l =>
    have hg : (L.Ind.eViewW s.mem e).headD 0 = 8 := hvr
    simp (config := { decide := true }) only [bodyArmK, hg, ↓reduceIte] at hW
    cases n with
    | zero => exact absurd hW hz
    | succ k =>
    have h8 : e >>> 28 = 8 := by rw [← hhd, hg]
    exact coreRef_congr (inferBody_lit _ fe d.toNat (decE e) a₀ l hv)
      (fin (inferLit_refines p hq.leaf hc.lit k _ a₀ dn vis fe MM eb e l hS he h8 hv) hW)
  | forallE ty b =>
    obtain ⟨hg, h1, hd1, h2, hd2⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2 hd2
    simp (config := { decide := true }) only [bodyArmK, hg, ↓reduceIte] at hW
    cases n with
    | zero => exact absurd hW hz
    | succ k =>
    rw [← hd1, ← hd2] at hv
    exact coreRef_congr (inferBody_forall _ fe d.toNat (decE e) a₀ _ _ hv)
      (fin (inferForall_refines p hq.leaf hq.bind hq.body hc.instList hc.bcap k (hk.mono (by omega))
        F (by omega) (by omega) _ a₀ dn vis fe MM eb mode d _ _ hsl h1 h2) hW)
  | lam ty b =>
    obtain ⟨hg, h1, hd1, h2, hd2⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2 hd2
    simp (config := { decide := true }) only [bodyArmK, hg, ↓reduceIte] at hW
    cases n with
    | zero => exact absurd hW hz
    | succ k =>
    rw [← hd1, ← hd2] at hv
    exact coreRef_congr (inferBody_lam _ fe d.toNat (decE e) a₀ _ _ hv)
      (fin (inferLam_refines p hq.leaf hq.bind hq.body hc.instList hc.absRange hc.bcap k
        (hk.mono (by omega)) F (by omega) (by omega) _ a₀ dn vis fe MM eb mode d _ _ hsl h1 h2) hW)
  | app f x =>
    obtain ⟨hg, -⟩ := hvr
    simp (config := { decide := true }) only [bodyArmK, hg, ↓reduceIte] at hW
    cases n with
    | zero => exact absurd hW hz
    | succ k =>
    have h4 : e >>> 28 = 4 := by rw [← hhd, hg]
    exact coreRef_congr (inferBody_app _ fe d.toNat (decE e) a₀ f x hv)
      (fin (inferApp_refines p hq.leaf hq.knot hq.spf hq.spine hc.eager hc.instList k (hk.mono (by omega))
        F (by omega) (by omega) _ a₀ dn vis fe MM eb mode d e hsl he h4) hW)
  | letE ty v b =>
    obtain ⟨hg, h1, hd1, h2, hd2, h3, hd3⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2 hd2; rw [getD3] at h3 hd3
    simp (config := { decide := true }) only [bodyArmK, hg, ↓reduceIte] at hW
    cases n with
    | zero => exact absurd hW hz
    | succ k =>
    rw [← hd1, ← hd2, ← hd3] at hv
    exact coreRef_congr (inferBody_let _ fe d.toNat (decE e) a₀ _ _ _ hv)
      (fin (inferLet_refines p hq.leaf hq.body hc.inst1 k (hk.mono (by omega)) F _ a₀ dn vis fe MM eb
        mode d _ _ _ (by omega) (by omega) hsl h1 h2 h3) hW)
  | proj sn i pe =>
    obtain ⟨hg, h1, hd1, h2, h3, hd3⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2; rw [getD3] at h3 hd3
    simp (config := { decide := true }) only [bodyArmK, hg, ↓reduceIte] at hW
    cases n with
    | zero => exact absurd hW hz
    | succ k =>
    rw [← hd1, ← h2, ← hd3] at hv
    exact coreRef_congr (inferBody_proj _ fe d.toNat (decE e) a₀ _ _ _ hv)
      (fin (hc.proj k (hk.mono (by omega)) F _ a₀ dn vis fe MM eb mode d _ _ _ (by omega) (by omega) hsl
        h1 h3).1 hW)

/-- **`infer_body_io` refines `inferBodyIO`** at the io view of the knot one level down:
`InferIOBodySpec p n` for every `n`. -/
@[refines ConRon.Arena.inferBodyIO]
theorem inferBodyIO_refines (p : Prog) (hq : InferAllProg p) (hc : InferCallees p) :
    ∀ n, InferIOBodySpec p n := by
  intro n F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he hk
  cases n with
  | zero => exact CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe MM eb _
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (inferBodyIO_spec p hq n s₀ mode vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold bodyIOK at hW
  cases hc0 : callW p n "e_view" [e] s.mem with
  | none => rw [hc0] at hW; cases hW
  | some q =>
  obtain ⟨r₀, m₀⟩ := q
  rw [hc0] at hW; dsimp only at hW
  obtain ⟨t₀, ht₀, hts, hne, hr0⟩ := triple_of_callW (L.Ind.eView_spec p hq.eview n s e) hc0
  have hm₀ : m₀ = s.mem := by rw [← ht₀, hts]
  subst hm₀
  subst hr0
  obtain ⟨v, hv, hvr⟩ := L.Ind.eViewW_ok s.mem a₀ hS.arena.1 e hne
  have hhd := eViewW_head s.mem e hne
  have fin : ∀ {T : AM EIdx} {f : FnName} {vs : List Word},
      CoreSpec p n f vs T decH ⟨s.mem, Locals.init []⟩ a₀ dn vis fe MM eb →
      call1W p n f vs s.mem = some (r.headD 0, s'.mem) →
      CoreRef T a₀ decH dn s.mem vis fe MM eb r s'.mem :=
    fun hsp h => CoreSpec.of_call1W hsp (fun r r' h => by simp only [decH, h]) h
  have hsl : SlotPre ⟨s.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode := ⟨hS, hs.mode4, hs.eb_mode⟩
  have hz : ∀ {f : FnName} {vs : List Word} {w : Word} {m' : Mem}, call1W p 0 f vs s.mem ≠ some (w, m') :=
    fun h => by simp [call1W, callW_zero] at h
  cases v with
  | bvar i =>
    obtain ⟨hg, -⟩ := hvr
    simp (config := { decide := true }) only [bodyIOArmK, hg, ↓reduceIte] at hW
    cases hW
  | fvar idx ty =>
    obtain ⟨hg, hi, hty, hdec⟩ := hvr
    simp (config := { decide := true }) only [bodyIOArmK, hg, ↓reduceIte] at hW
    rw [getD1] at hi; rw [getD2] at hty hdec
    by_cases hlt : (L.Ind.eViewW s.mem e).tail.headD 0 < d
    · simp only [hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr, hm⟩ := hW
      have hi' : idx < d.toNat := by rw [← hi]; exact UInt64.lt_iff_toNat_lt.mp hlt
      have hrun := inferBodyIO_fvar (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE e) a₀ idx ty hv hi'
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
      refine ⟨hok, ?_, by rw [hres, decH, ← hr, hdec], by unfold ResH; rw [← hr]; exact hty⟩
      rw [hst, ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
    · simp only [hlt, ↓reduceIte] at hW; cases hW
  | sort u =>
    obtain ⟨hg, hu, hdec⟩ := hvr
    rw [getD1] at hu hdec
    simp (config := { decide := true }) only [bodyIOArmK, hg, ↓reduceIte, sortArmK] at hW
    cases h1 : callW p n "intern_succ" [(L.Ind.eViewW s.mem e).tail.headD 0] s.mem with
    | none => rw [h1] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [h1] at hW; dsimp only at hW
    obtain ⟨s₁, hs₁, -, hsu⟩ := triple_of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
      (internSucc_spec p hq.body.suf hq.body.sup hq.body.sui n _ _) h1
    rw [hs₁] at hsu
    have h₁ := internSucc_core hS _ hu r₁ hsu (by rw [hdec]; exact hS.den.sort _ _ hv)
    rw [hdec] at h₁
    refine coreRef_congr (inferBodyIO_sort _ fe d.toNat (decE e) a₀ u hv) (coreRef_bind h₁ (fun M₁ hS₁ => ?_))
    have hso := of_call1W (X := fun m w m' => sointernW m (r₁.headD 0) = some (w, m'))
      (fun s₀ => internSort_spec p hq.body.sof hq.body.sop hq.body.soi n s₀ (r₁.headD 0)) hW
    exact internSort_core hS₁ (r₁.headD 0) h₁.2.2.2 r hso (by
      have hd := internLNode_res_den (v := .succ u) hS
        (fun c hc => by simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc; subst hc; exact hS.den.sort _ _ hv)
        (fun n hn => by simp [LNodeView.nchildren] at hn) h₁.1
      rw [h₁.2.2.1] at hd; exact hd)
  | const nm us =>
    obtain ⟨hg, hn1, hdn, hu2, hdu⟩ := hvr
    rw [getD1] at hn1 hdn; rw [getD2] at hu2 hdu
    simp (config := { decide := true }) only [bodyIOArmK, hg, ↓reduceIte] at hW
    cases n with
    | zero => exact absurd hW hz
    | succ k =>
    rw [← hdn, ← hdu] at hv
    exact coreRef_congr (inferBodyIO_const _ fe d.toNat (decE e) a₀ _ _ hv)
      (coreRef_of_imp (inferConstIOT_of_T fe _ _ a₀)
        (fin (inferConst_refines p hq.leaf hc.constTy k _ a₀ dn vis fe MM eb _ _ hS hn1 hu2) hW))
  | lit l =>
    have hg : (L.Ind.eViewW s.mem e).headD 0 = 8 := hvr
    simp (config := { decide := true }) only [bodyIOArmK, hg, ↓reduceIte] at hW
    cases n with
    | zero => exact absurd hW hz
    | succ k =>
    have h8 : e >>> 28 = 8 := by rw [← hhd, hg]
    exact coreRef_congr (inferBodyIO_lit _ fe d.toNat (decE e) a₀ l hv)
      (fin (inferLit_refines p hq.leaf hc.lit k _ a₀ dn vis fe MM eb e l hS he h8 hv) hW)
  | forallE ty b =>
    obtain ⟨hg, h1, hd1, h2, hd2⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2 hd2
    simp (config := { decide := true }) only [bodyIOArmK, hg, ↓reduceIte] at hW
    cases n with
    | zero => exact absurd hW hz
    | succ k =>
    rw [← hd1, ← hd2] at hv
    exact coreRef_congr (inferBodyIO_forall _ fe d.toNat (decE e) a₀ _ _ hv)
      (fin (inferForallIO_refines p hq.leaf hq.body hc.inst1 k (hk.mono (by omega)) F _ a₀ dn vis fe MM eb
        mode d _ _ (by omega) (by omega) hsl h1 h2) hW)
  | lam ty b =>
    obtain ⟨hg, h1, hd1, h2, hd2⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2 hd2
    simp (config := { decide := true }) only [bodyIOArmK, hg, ↓reduceIte] at hW
    cases n with
    | zero => exact absurd hW hz
    | succ k =>
    rw [← hd1, ← hd2] at hv
    exact coreRef_congr (inferBodyIO_lam _ fe d.toNat (decE e) a₀ _ _ hv)
      (fin (inferLamIO_refines p hq.leaf hq.body hc.inst1 hc.abs1 k (hk.mono (by omega)) F _ a₀ dn vis fe
        MM eb mode d _ _ (by omega) (by omega) hsl h1 h2) hW)
  | app f x =>
    obtain ⟨hg, -⟩ := hvr
    simp (config := { decide := true }) only [bodyIOArmK, hg, ↓reduceIte] at hW
    cases n with
    | zero => exact absurd hW hz
    | succ k =>
    have h4 : e >>> 28 = 4 := by rw [← hhd, hg]
    exact coreRef_congr (inferBodyIO_app _ fe d.toNat (decE e) a₀ f x hv)
      (fin (inferAppIO_refines p hq.spio hq.spine hc.instList k (hk.mono (by omega))
        F (by omega) (by omega) _ a₀ dn vis fe MM eb mode d e hsl he h4) hW)
  | letE ty v b =>
    obtain ⟨hg, h1, hd1, h2, hd2, h3, hd3⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2 hd2; rw [getD3] at h3 hd3
    simp (config := { decide := true }) only [bodyIOArmK, hg, ↓reduceIte, letIOArmK] at hW
    rw [← hd1, ← hd2, ← hd3] at hv
    cases hi : callW p n "inst1" [(L.Ind.eViewW s.mem e).tail.tail.tail.headD 0,
        (L.Ind.eViewW s.mem e).tail.tail.headD 0, 0] s.mem with
    | none => rw [hi] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hi] at hW; dsimp only at hW
    have h₁ := CoreSpec.of_callW (hc.inst1 n ⟨s.mem, Locals.init []⟩ a₀ dn vis fe MM eb _ _ 0 hS h3 h2) hi
    refine coreRef_congr (inferBodyIO_let _ fe d.toNat (decE e) a₀ _ _ _ hv)
      (coreRef_bind h₁ (fun M₁ hS₁ => ?_))
    exact CoreSpec.of_call1W (s₀ := ⟨m₁, Locals.init []⟩)
      ((hk n (by omega)).inferIO F _ _ dn vis fe M₁ eb mode d (r₁.headD 0) (by omega) (by omega)
        ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) (fun r r' h => by simp only [decH, h]) hW
  | proj sn i pe =>
    obtain ⟨hg, h1, hd1, h2, h3, hd3⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2; rw [getD3] at h3 hd3
    simp (config := { decide := true }) only [bodyIOArmK, hg, ↓reduceIte] at hW
    cases n with
    | zero => exact absurd hW hz
    | succ k =>
    rw [← hd1, ← h2, ← hd3] at hv
    exact coreRef_congr (inferBodyIO_proj _ fe d.toNat (decE e) a₀ _ _ _ hv)
      (fin (hc.proj k (hk.mono (by omega)) F _ a₀ dn vis fe MM eb mode d _ _ _ (by omega) (by omega) hsl
        h1 h3).2 hW)

end L.Arena

namespace L.Arena

/-- **The knot's `infer` slot one level up**, from the body. -/
@[refines_part ConRon.Arena.coreKnot "infer (step)"]
theorem inferSlot_step (p : Prog) (hq : InferAllProg p) (hc : InferCallees p) (n : Nat)
    (hk : KnotUpTo p n) : InferSlot p (n + 1) :=
  infer_refines p hq.knot n hk (inferBody_refines p hq hc n)

/-- **The knot's `inferIO` slot one level up**, from the io body. -/
@[refines_part ConRon.Arena.coreKnot "inferIO (step)"]
theorem inferIOSlot_step (p : Prog) (hq : InferAllProg p) (hc : InferCallees p) (n : Nat)
    (hk : KnotUpTo p n) : InferIOSlot p (n + 1) :=
  inferIO_refines p hq.knot n hk (inferBodyIO_refines p hq hc n)

end L.Arena
