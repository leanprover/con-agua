import ConAgua.Arena.InferBodyBindPi
import ConAgua.Arena.InferBodySpineF
import ConAgua.Arena.InferBodyDispModels

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

namespace L.Arena

/-! ## The `.const` arm of the io body -/

theorem LsStore.viewLen_of_view (st : LsStore) (i : LsIdx) (ids : List LIdx)
    (h : st.view i = some ids) : st.viewLen i = some ids.length := by
  unfold LsStore.view at h
  unfold LsStore.viewLen LsStore.persGetLen
  split at h
  · rw [ite_eq_left (by assumption)]
    unfold LsTables.get at h; unfold LsTables.getLen
    split at h
    · rw [ite_eq_left (by assumption)]
      cases e : i |> fun _ => (st.pers.lists.node? i.idxNat) with
      | none | some r => simp_all
    · cases h
  · rw [ite_eq_right (by assumption)]
    split at h
    · rw [ite_eq_left (by assumption)]
      unfold LsTables.get at h; unfold LsTables.getLen
      split at h
      · rw [ite_eq_left (by assumption)]
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
    simp [viewLsLen, hl, StateT.run_get]; rfl
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

/-! ## The arms -/

theorem eViewW_head (m : Mem) (h : Word) (hne : L.Ind.eViewW m h ≠ []) :
    (L.Ind.eViewW m h).headD 0 = h >>> 28 := by
  unfold L.Ind.eViewW at hne ⊢
  dsimp only at hne ⊢
  have c0 : ¬ (4294967295 : Word) < h := fun c0 => by rw [ite_eq_left c0] at hne; exact absurd rfl hne
  rw [ite_eq_right c0] at hne ⊢
  have c1 : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := fun c1 => by rw [ite_eq_left c1] at hne; exact absurd rfl hne
  rw [ite_eq_right c1] at hne ⊢
  by_cases g0 : h >>> 28 = 0
  · rw [ite_eq_left g0] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [ite_eq_right hc, g0]; rfl
  rw [ite_eq_right g0] at hne ⊢
  by_cases g1 : h >>> 28 = 1
  · rw [ite_eq_left g1] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [ite_eq_right hc, g1]; rfl
  rw [ite_eq_right g1] at hne ⊢
  by_cases g2 : h >>> 28 = 2
  · rw [ite_eq_left g2] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [ite_eq_right hc, g2]; rfl
  rw [ite_eq_right g2] at hne ⊢
  by_cases g3 : h >>> 28 = 3
  · rw [ite_eq_left g3] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [ite_eq_right hc, g3]; rfl
  rw [ite_eq_right g3] at hne ⊢
  by_cases g4 : h >>> 28 = 4
  · rw [ite_eq_left g4] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [ite_eq_right hc, g4]; rfl
  rw [ite_eq_right g4] at hne ⊢
  by_cases g5 : h >>> 28 = 5
  · rw [ite_eq_left g5] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [ite_eq_right hc, g5]; rfl
  rw [ite_eq_right g5] at hne ⊢
  by_cases g6 : h >>> 28 = 6
  · rw [ite_eq_left g6] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [ite_eq_right hc, g6]; rfl
  rw [ite_eq_right g6] at hne ⊢
  by_cases g7 : h >>> 28 = 7
  · rw [ite_eq_left g7] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [ite_eq_right hc, g7]; rfl
  rw [ite_eq_right g7] at hne ⊢
  by_cases g8 : h >>> 28 = 8
  · rw [ite_eq_left g8] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [ite_eq_right hc, g8]; rfl
  rw [ite_eq_right g8] at hne ⊢
  by_cases g9 : h >>> 28 = 9
  · rw [ite_eq_left g9] at hne ⊢
    split at hne
    · exact absurd rfl hne
    · rename_i hc; rw [ite_eq_right hc, g9]; rfl
  rw [ite_eq_right g9] at hne ⊢
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
  coreRef_congr ((himp _ _ (AM.run_of_ok _ _ h.run)).trans (AM.run_of_ok _ _ h.run).symm) h

theorem getD1 (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> rfl
theorem getD2 (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩ <;> rfl
theorem getD3 (r : List Word) : r.getD 3 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, t⟩⟩⟩⟩ <;> rfl

/-! ## The twin's arms that fail at the dispatcher -/

section armsE
variable (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)

theorem inferBody_bvarE (i : Nat) (hv : a.store.view e = some (.bvar i)) :
    (inferBody r fe d e).run a = .error (.notImplemented "inferType beyond the supported fragment") := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; rfl

theorem inferBodyIO_bvarE (i : Nat) (hv : a.store.view e = some (.bvar i)) :
    (inferBodyIO r fe d e).run a =
      .error (.notImplemented "inferType beyond the supported fragment") := by
  simp only [inferBodyIO, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; rfl

theorem inferBody_fvarE (i : Nat) (ty : EIdx) (hv : a.store.view e = some (.fvar i ty)) (hi : ¬ i < d) :
    (inferBody r fe d e).run a = .error (.invalid "free variable out of scope") := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hi, ↓reduceIte]; rfl

theorem inferBodyIO_fvarE (i : Nat) (ty : EIdx) (hv : a.store.view e = some (.fvar i ty))
    (hi : ¬ i < d) :
    (inferBodyIO r fe d e).run a = .error (.invalid "free variable out of scope") := by
  simp only [inferBodyIO, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hi, ↓reduceIte]; rfl

end armsE

/-- **The io `.const` clause fails where the full one does** (with a class other than `0`: the
two differ only in how a dangling level list fails). -/
theorem inferConstIOT_err (fe : IFEnv) (n : NIdx) (us : LsIdx) (a : AState) (ce : CheckError)
    (h : (inferConstT fe n us).run a = .error ce) (hc : twinCls ce ≠ 0) :
    (inferConstIOT fe n us).run a = .error ce := by
  unfold inferConstT at h; unfold inferConstIOT
  cases hf : fe.find? n with
  | none => rw [hf] at h; exact h
  | some ci =>
  rw [hf] at h
  simp only [StateT.run_bind] at h ⊢
  generalize ci.toConstantVal = cv at h ⊢
  cases hv : a.store.lss.view us with
  | none =>
    have e1 : (viewLs us).run a = .error (.internal "arena: dangling level-list handle") := by
      simp only [viewLs, StateT.run_bind, StateT.run_get, pure_bind, hv]; rfl
    rw [e1] at h
    have h' : (Except.error (CheckError.internal "arena: dangling level-list handle") :
        Except CheckError (EIdx × AState)) = .error ce := h
    cases h'; exact absurd rfl hc
  | some ids =>
  have hl := LsStore.viewLen_of_view _ _ _ hv
  have e1 : (viewLs us).run a = .ok (ids, a) := viewLs_run us a ids hv
  have e2 : (viewLsLen us).run a = .ok (some ids.length, a) := by
    simp [viewLsLen, hl, StateT.run_get]; rfl
  rw [e1] at h; rw [e2]
  simp only [except_ok_bind] at h ⊢
  exact h

/-- An io `.const` claim from the full one. -/
theorem ErrClaim.constIO {fe : IFEnv} {n : NIdx} {us : LsIdx} {a : AState} {e : Err}
    (h : ErrClaim (inferConstT fe n us) a e) : ErrClaim (inferConstIOT fe n us) a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h hk
  exact ⟨ce, inferConstIOT_err fe n us a ce hce (by rw [hc]; exact hk), hc⟩

/-! ## The bodies, both outcomes -/

/-- `infer_proj`'s error claim at both grades (the error half of `InferProjOK`; `ip_ref`'s, which
lives above this file). -/
def InferProjOKE (p : Prog) : Prop :=
  ∀ n, KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d sn i pe : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW sn →
    HW pe →
    CoreSpecE p (n + 1) "infer_proj" [mode, 0, vis, d, sn, i, pe]
      (inferProj (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat (decE pe)) s₀ a₀ ∧
    CoreSpecE p (n + 1) "infer_proj" [mode, 1, vis, d, sn, i, pe]
      (inferProj (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decI sn) i.toNat
        (decE pe)) s₀ a₀

/-- **What the bodies' errors assume**: `InferG` and `infer_proj`'s claim. -/
structure InferBodyG (p : Prog) (n : Nat) : Prop extends InferG p n where
  proj : InferProjOKE p

/-- **An arm of a body**: its callee, read through its run (`k` the model's continuation, which
re-lists the result word), is the body's result; the callee's halves at every fuel `k + 1`. -/
theorem bodyArm_ref {G : Prop} {p : Prog} {n : Nat} {f : FnName} {args : List Word} {s₀ : St}
    {T : AM EIdx} {a : AState} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} {K : Except Err (List Word × Mem) → Except Err (List Word × Mem)}
    (hk0 : ∀ e, K (.error e) = .error e) (hk : ∀ r m, K (.ok (r, m)) = .ok ([r.headD 0], m))
    (h : ∀ k, n = k + 1 → CoreSpec p n f args T decH s₀ a dn vis fe M eb ∧
      (G → CoreSpecE p n f args T s₀ a)) :
    RefE G (K (callE p n f args s₀.mem)) T a (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  cases n with
  | zero => exact RefE.callE_zero hk0
  | succ k =>
  obtain ⟨hok, herr⟩ := h k rfl
  rw [← bind_pure T]
  refine RefE.bind_callE hk0 hok herr fun r m _ h₁ => ?_
  rw [hk]; exact RefE.ret rfl ⟨h₁.after, rfl, h₁.resOk⟩

/-- **`intern_succ` refines `internLNode (.succ …)` under `CoreS`, as its `CoreSpec`** (for
`RefE.bind_callW`). -/
theorem internSucc_coreSpec {p : Prog} (hb : InferBodyProg p) (n : Nat) (s₀ : St) {a : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn s₀.mem a vis fe M eb) (u : Word) (hu : HW u)
    (hdu : ∃ l, denoteL a.store.ls (decI u) = some l) :
    CoreSpec p n "intern_succ" [u] (internLNode (.succ (decI u))) decLv s₀ a dn vis fe M eb :=
  L.M.triple_of_run fun _ _ _ hp hr => by
    subst hp
    obtain ⟨hl, hsu⟩ := L.M.of_run (P := fun s => s = _) rfl hr
      (internSucc_spec p hb.suf hb.sup hb.sui n _ u)
    exact ⟨hl, internSucc_core hS u hu _ hsu hdu⟩

/-- **`intern_sort` refines `internE (.sort …)` under `CoreS`, as its `CoreSpec`**. -/
theorem internSort_coreSpec {p : Prog} (hb : InferBodyProg p) (n : Nat) (s₀ : St) {a : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn s₀.mem a vis fe M eb) (u : Word) (hu : HW u)
    (hdu : ∃ l, denoteL a.store.ls (decI u) = some l) :
    CoreSpec p n "intern_sort" [u] (internE (.sort (decI u))) decH s₀ a dn vis fe M eb :=
  L.M.triple_of_run fun _ _ _ hp hr => by
    subst hp
    obtain ⟨hl, hso⟩ := L.M.of_run (P := fun s => s = _) rfl hr
      (internSort_spec p hb.sof hb.sop hb.soi n _ u)
    exact ⟨hl, internSort_core hS u hu _ hso hdu⟩

/-- **`infer_body` refines `inferBody`, both outcomes**, at the knot one level down: each clause's
errors are its arm's, a free variable out of scope rejects, a loose bound variable declines;
`e_view` and the interning claim nothing. -/
theorem ib_ref (p : Prog) (hq : InferAllProg p) (hc : InferCallees p) (n : Nat) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d e : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (he : HW e) (hk : KnotUpTo p n) :
    RefE (InferBodyG p n) (ibE p (n + 1) s₀.mem mode vis d e)
      (inferBody (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) a₀
      (CorePost decH dn s₀.mem vis fe MM eb ResH) := by
  have hS := hs.rel
  simp only [ibE]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => triple_of_callW
    (L.Ind.eView_spec p hq.eview n ⟨s₀.mem, Locals.init []⟩ e) h) fun r₀ m₀ ⟨t₀, ht₀, hts, hne, hr0⟩ => ?_
  have hm₀ : m₀ = s₀.mem := by rw [← ht₀, hts]
  subst hm₀ hr0
  obtain ⟨v, hv, hvr⟩ := L.Ind.eViewW_ok s₀.mem a₀ hS.arena.base e hne
  have hhd := eViewW_head s₀.mem e hne
  have hs : SlotPre ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode := ⟨hS, hs.mode4, hs.eb_mode⟩
  simp only [ibE.k_e_view]
  cases v with
  | bvar i =>
    obtain ⟨hg, -⟩ := hvr
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    refine RefE.of_run_eq (T' := (fail (.notImplemented "inferType beyond the supported fragment") : AM EIdx)) (a' := a₀) ((inferBody_bvarE _ fe d.toNat (decE e) a₀ i hv).trans rfl) ?_
    exact fun _ => ErrClaim.fail _ _ rfl
  | fvar idx ty =>
    obtain ⟨hg, hi, hty, hdec⟩ := hvr
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    rw [getD1] at hi; rw [getD2] at hty hdec
    by_cases hlt : (L.Ind.eViewW s₀.mem e).tail.headD 0 < d
    · rw [ite_eq_left hlt]
      have hi' : idx < d.toNat := by rw [← hi]; exact UInt64.lt_iff_toNat_lt.mp hlt
      exact RefE.ret (inferBody_fvar _ fe d.toNat (decE e) a₀ idx ty hv hi')
        (CorePost.ret hS hdec.symm hty)
    · rw [ite_eq_right hlt]
      have hi' : ¬ idx < d.toNat := fun h => hlt (by rw [UInt64.lt_iff_toNat_lt, hi]; exact h)
      refine RefE.of_run_eq (T' := (fail (.invalid "free variable out of scope") : AM EIdx)) (a' := a₀) ((inferBody_fvarE _ fe d.toNat (decE e) a₀ idx ty hv hi').trans rfl) ?_
      exact fun _ => ErrClaim.fail _ _ rfl
  | sort u =>
    obtain ⟨hg, hu, hdec⟩ := hvr
    rw [getD1] at hu hdec
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    refine RefE.of_run_eq (inferBody_sort _ fe d.toNat (decE e) a₀ u hv) ?_
    subst hdec
    refine RefE.bind_callW (fun _ => rfl) (internSucc_coreSpec hq.body n s₀ hS _ hu
      (hS.den.sort _ _ hv)) fun r₁ m₁ _ h₁ => ?_
    obtain ⟨M₁, hS₁, hK₁, hSt₁⟩ := h₁.after
    have hd := internLNode_res_den (v := .succ _) hS
      (fun c hc => by
        simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc
        subst hc; exact hS.den.sort _ _ hv)
      (fun n hn => by simp [LNodeView.nchildren] at hn) h₁.run
    rw [h₁.res] at hd
    simp only [ibE.k_intern_succ]
    rw [← bind_pure (internE _)]
    refine RefE.bind_callW (fun _ => rfl) (internSort_coreSpec hq.body n ⟨m₁, Locals.init []⟩ hS₁ _ h₁.resOk hd)
      fun _ _ _ h₂ => ?_
    exact RefE.ret rfl ⟨CoreAfter.comp hK₁ hSt₁ h₂.after, rfl, h₂.resOk⟩
  | const nm us =>
    obtain ⟨hg, hn1, hdn, hu2, hdu⟩ := hvr
    rw [getD1] at hn1 hdn; rw [getD2] at hu2 hdu
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    rw [← hdn, ← hdu] at hv
    refine RefE.of_run_eq (inferBody_const _ fe d.toNat (decE e) a₀ _ _ hv) ?_
    refine bodyArm_ref (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl) (fun _ _ => rfl) fun k hk' => ?_
    subst hk'
    exact ⟨inferConst_refines p hq.leaf hc.constTy k _ a₀ dn vis fe MM eb _ _ hS hn1 hu2,
      fun hG => RefE.coreSpecE (inferConstE_spec p hq.leaf.inferConst hq.leaf.lsNode (k + 1) _ vis _ _)
        hG.nv hG.nv (inferConst_ref p hq.leaf hc.constTy k _ a₀ dn vis fe MM eb _ _ hS hn1 hu2)⟩
  | lit l =>
    have hg : (L.Ind.eViewW s₀.mem e).headD 0 = 8 := hvr
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    have h8 : e >>> 28 = 8 := by rw [← hhd, hg]
    refine RefE.of_run_eq (inferBody_lit _ fe d.toNat (decE e) a₀ l hv) ?_
    refine bodyArm_ref (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl) (fun _ _ => rfl) fun k hk' => ?_
    subst hk'
    exact ⟨inferLit_refines p hq.leaf hc.lit k _ a₀ dn vis fe MM eb e l hS he h8 hv,
      fun hG => RefE.coreSpecE (ilE_spec p hq.leaf.inferLit (k + 1) _ vis e) hG.nv hG.nv
        (il_ref p hq.leaf hc.lit k _ a₀ dn vis fe MM eb e l hS he h8 hv)⟩
  | forallE ty b =>
    obtain ⟨hg, h1, hd1, h2, hd2⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2 hd2
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    rw [← hd1, ← hd2] at hv
    refine RefE.of_run_eq (inferBody_forall _ fe d.toNat (decE e) a₀ _ _ hv) ?_
    refine bodyArm_ref (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl) (fun _ _ => rfl) fun k hk' => ?_
    subst hk'
    exact ⟨inferForall_refines p hq.leaf hq.bind hq.body hc.instList hc.bcap k (hk.mono (by omega))
        F (by omega) (by omega) _ a₀ dn vis fe MM eb mode d _ _ hs h1 h2,
      fun hG => RefE.coreSpecE (ifrE_spec p hq.bind.fa (k + 1) _ mode vis d _ _) hG.nv
        (hG.toInferG.mono (by omega)) (ifr_ref p hq.leaf hq.bind hq.body hc.instList hc.bcap k
          (hk.mono (by omega)) F (by omega) (by omega) _ a₀ dn vis fe MM eb mode d _ _ hs h1 h2)⟩
  | lam ty b =>
    obtain ⟨hg, h1, hd1, h2, hd2⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2 hd2
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    rw [← hd1, ← hd2] at hv
    refine RefE.of_run_eq (inferBody_lam _ fe d.toNat (decE e) a₀ _ _ hv) ?_
    refine bodyArm_ref (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl) (fun _ _ => rfl) fun k hk' => ?_
    subst hk'
    exact ⟨inferLam_refines p hq.leaf hq.bind hq.body hc.instList hc.absRange hc.bcap k
        (hk.mono (by omega)) F (by omega) (by omega) _ a₀ dn vis fe MM eb mode d _ _ hs h1 h2,
      fun hG => RefE.coreSpecE (ilmE_spec p hq.bind.lam (k + 1) _ mode vis d _ _) hG.nv
        (hG.toInferG.mono (by omega)) (ilm_ref p hq.leaf hq.bind hq.body hc.instList hc.absRange
          hc.bcap k (hk.mono (by omega)) F (by omega) (by omega) _ a₀ dn vis fe MM eb mode d _ _ hs h1
          h2)⟩
  | app f x =>
    obtain ⟨hg, -⟩ := hvr
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    have h4 : e >>> 28 = 4 := by rw [← hhd, hg]
    refine RefE.of_run_eq (inferBody_app _ fe d.toNat (decE e) a₀ f x hv) ?_
    refine bodyArm_ref (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl) (fun _ _ => rfl) fun k hk' => ?_
    subst hk'
    exact ⟨inferApp_refines p hq.leaf hq.knot hq.spf hq.spine hc.eager hc.instList k (hk.mono (by omega))
        F (by omega) (by omega) _ a₀ dn vis fe MM eb mode d e hs he h4,
      fun hG => RefE.coreSpecE (aE_spec p hq.spf.app (k + 1) _ mode vis d e) hG.nv
        (hG.toInferG.mono (by omega)) (a_ref p hq.leaf hq.knot hq.spf hq.spine hc.eager hc.instList k
          (hk.mono (by omega)) F (by omega) (by omega) _ a₀ dn vis fe MM eb mode d e hs he h4)⟩
  | letE ty v b =>
    obtain ⟨hg, h1, hd1, h2, hd2, h3, hd3⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2 hd2; rw [getD3] at h3 hd3
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    rw [← hd1, ← hd2, ← hd3] at hv
    refine RefE.of_run_eq (inferBody_let _ fe d.toNat (decE e) a₀ _ _ _ hv) ?_
    refine bodyArm_ref (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl) (fun _ _ => rfl) fun k hk' => ?_
    subst hk'
    exact ⟨inferLet_refines p hq.leaf hq.body hc.inst1 k (hk.mono (by omega)) F _ a₀ dn vis fe MM eb
        mode d _ _ _ (by omega) (by omega) hs h1 h2 h3,
      fun hG => RefE.coreSpecE (iletE_spec p hq.body.inferLet (k + 1) _ mode vis d _ _ _) hG.nv
        (hG.toInferG.mono (by omega)) (ilet_ref p hq.leaf hc.inst1 k (hk.mono (by omega)) F _ a₀ dn vis
          fe MM eb mode d _ _ _ (by omega) (by omega) hs h1 h2 h3)⟩
  | proj sn i pe =>
    obtain ⟨hg, h1, hd1, h2, h3, hd3⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2; rw [getD3] at h3 hd3
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    rw [← hd1, ← h2, ← hd3] at hv
    refine RefE.of_run_eq (inferBody_proj _ fe d.toNat (decE e) a₀ _ _ _ hv) ?_
    refine bodyArm_ref (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl) (fun _ _ => rfl) fun k hk' => ?_
    subst hk'
    exact ⟨(hc.proj k (hk.mono (by omega)) F _ a₀ dn vis fe MM eb mode d _ _ _ (by omega) (by omega) hs
        h1 h3).1,
      fun hG => (hG.proj k (hk.mono (by omega)) (hG.knot.mono (by omega)) F _ a₀ dn vis fe MM eb mode
        d _ _ _ (by omega) (by omega) hs h1 h3).1⟩

/-- **`infer_body_io` refines `inferBodyIO`, both outcomes**, at the io view of the knot one level down: each clause's
errors are its arm's, a free variable out of scope rejects, a loose bound variable declines;
`e_view` and the interning claim nothing. -/
theorem ibo_ref (p : Prog) (hq : InferAllProg p) (hc : InferCallees p) (n : Nat) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d e : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (he : HW e) (hk : KnotUpTo p n) :
    RefE (InferBodyG p n) (iboE p (n + 1) s₀.mem mode vis d e)
      (inferBodyIO (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE e)) a₀
      (CorePost decH dn s₀.mem vis fe MM eb ResH) := by
  have hS := hs.rel
  simp only [iboE]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => triple_of_callW
    (L.Ind.eView_spec p hq.eview n ⟨s₀.mem, Locals.init []⟩ e) h) fun r₀ m₀ ⟨t₀, ht₀, hts, hne, hr0⟩ => ?_
  have hm₀ : m₀ = s₀.mem := by rw [← ht₀, hts]
  subst hm₀ hr0
  obtain ⟨v, hv, hvr⟩ := L.Ind.eViewW_ok s₀.mem a₀ hS.arena.base e hne
  have hhd := eViewW_head s₀.mem e hne
  have hs : SlotPre ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode := ⟨hS, hs.mode4, hs.eb_mode⟩
  simp only [iboE.k_e_view]
  cases v with
  | bvar i =>
    obtain ⟨hg, -⟩ := hvr
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    refine RefE.of_run_eq (T' := (fail (.notImplemented "inferType beyond the supported fragment") : AM EIdx)) (a' := a₀) ((inferBodyIO_bvarE _ fe d.toNat (decE e) a₀ i hv).trans rfl) ?_
    exact fun _ => ErrClaim.fail _ _ rfl
  | fvar idx ty =>
    obtain ⟨hg, hi, hty, hdec⟩ := hvr
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    rw [getD1] at hi; rw [getD2] at hty hdec
    by_cases hlt : (L.Ind.eViewW s₀.mem e).tail.headD 0 < d
    · rw [ite_eq_left hlt]
      have hi' : idx < d.toNat := by rw [← hi]; exact UInt64.lt_iff_toNat_lt.mp hlt
      exact RefE.ret (inferBodyIO_fvar _ fe d.toNat (decE e) a₀ idx ty hv hi')
        (CorePost.ret hS hdec.symm hty)
    · rw [ite_eq_right hlt]
      have hi' : ¬ idx < d.toNat := fun h => hlt (by rw [UInt64.lt_iff_toNat_lt, hi]; exact h)
      refine RefE.of_run_eq (T' := (fail (.invalid "free variable out of scope") : AM EIdx)) (a' := a₀) ((inferBodyIO_fvarE _ fe d.toNat (decE e) a₀ idx ty hv hi').trans rfl) ?_
      exact fun _ => ErrClaim.fail _ _ rfl
  | sort u =>
    obtain ⟨hg, hu, hdec⟩ := hvr
    rw [getD1] at hu hdec
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    refine RefE.of_run_eq (inferBodyIO_sort _ fe d.toNat (decE e) a₀ u hv) ?_
    subst hdec
    refine RefE.bind_callW (fun _ => rfl) (internSucc_coreSpec hq.body n s₀ hS _ hu
      (hS.den.sort _ _ hv)) fun r₁ m₁ _ h₁ => ?_
    obtain ⟨M₁, hS₁, hK₁, hSt₁⟩ := h₁.after
    have hd := internLNode_res_den (v := .succ _) hS
      (fun c hc => by
        simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc
        subst hc; exact hS.den.sort _ _ hv)
      (fun n hn => by simp [LNodeView.nchildren] at hn) h₁.run
    rw [h₁.res] at hd
    simp only [iboE.k_intern_succ]
    rw [← bind_pure (internE _)]
    refine RefE.bind_callW (fun _ => rfl) (internSort_coreSpec hq.body n ⟨m₁, Locals.init []⟩ hS₁ _ h₁.resOk hd)
      fun _ _ _ h₂ => ?_
    exact RefE.ret rfl ⟨CoreAfter.comp hK₁ hSt₁ h₂.after, rfl, h₂.resOk⟩
  | const nm us =>
    obtain ⟨hg, hn1, hdn, hu2, hdu⟩ := hvr
    rw [getD1] at hn1 hdn; rw [getD2] at hu2 hdu
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    rw [← hdn, ← hdu] at hv
    refine RefE.of_run_eq (inferBodyIO_const _ fe d.toNat (decE e) a₀ _ _ hv) ?_
    cases n with
    | zero => exact RefE.callE_zero fun _ => rfl
    | succ k =>
    rcases h1 : callE p (k + 1) "infer_const" [vis, (L.Ind.eViewW s₀.mem e).tail.headD 0,
        (L.Ind.eViewW s₀.mem e).tail.tail.headD 0] s₀.mem with e1 | ⟨r₁, m₁⟩
    · exact fun hG => ErrClaim.constIO (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (RefE.coreSpecE (inferConstE_spec p hq.leaf.inferConst hq.leaf.lsNode (k + 1) _ vis _ _) hG.nv
          hG.nv (inferConst_ref p hq.leaf hc.constTy k _ a₀ dn vis fe MM eb _ _ hS hn1 hu2)) h1)
    obtain ⟨hrun, hP⟩ := (coreRef_of_imp (inferConstIOT_of_T fe _ _ a₀) (CoreSpec.of_callW
      (inferConst_refines p hq.leaf hc.constTy k _ a₀ dn vis fe MM eb _ _ hS hn1 hu2)
      (callW_of_callE h1))).post
    exact RefE.ret hrun ⟨hP.after, hP.res, hP.valid⟩
  | lit l =>
    have hg : (L.Ind.eViewW s₀.mem e).headD 0 = 8 := hvr
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    have h8 : e >>> 28 = 8 := by rw [← hhd, hg]
    refine RefE.of_run_eq (inferBodyIO_lit _ fe d.toNat (decE e) a₀ l hv) ?_
    refine bodyArm_ref (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl) (fun _ _ => rfl) fun k hk' => ?_
    subst hk'
    exact ⟨inferLit_refines p hq.leaf hc.lit k _ a₀ dn vis fe MM eb e l hS he h8 hv,
      fun hG => RefE.coreSpecE (ilE_spec p hq.leaf.inferLit (k + 1) _ vis e) hG.nv hG.nv
        (il_ref p hq.leaf hc.lit k _ a₀ dn vis fe MM eb e l hS he h8 hv)⟩
  | forallE ty b =>
    obtain ⟨hg, h1, hd1, h2, hd2⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2 hd2
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    rw [← hd1, ← hd2] at hv
    refine RefE.of_run_eq (inferBodyIO_forall _ fe d.toNat (decE e) a₀ _ _ hv) ?_
    refine bodyArm_ref (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl) (fun _ _ => rfl) fun k hk' => ?_
    subst hk'
    exact ⟨inferForallIO_refines p hq.leaf hq.body hc.inst1 k (hk.mono (by omega)) F _ a₀ dn vis fe MM
        eb mode d _ _ (by omega) (by omega) hs h1 h2,
      fun hG => RefE.coreSpecE (ifaE_spec p hq.body.inferForallIO (k + 1) _ mode vis d _ _) hG.nv
        (hG.toInferG.mono (by omega)) (ifa_ref p hq.leaf hq.body hc.inst1 k (hk.mono (by omega)) F _ a₀
          dn vis fe MM eb mode d _ _ (by omega) (by omega) hs h1 h2)⟩
  | lam ty b =>
    obtain ⟨hg, h1, hd1, h2, hd2⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2 hd2
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    rw [← hd1, ← hd2] at hv
    refine RefE.of_run_eq (inferBodyIO_lam _ fe d.toNat (decE e) a₀ _ _ hv) ?_
    refine bodyArm_ref (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl) (fun _ _ => rfl) fun k hk' => ?_
    subst hk'
    exact ⟨inferLamIO_refines p hq.leaf hq.body hc.inst1 hc.abs1 k (hk.mono (by omega)) F _ a₀ dn vis
        fe MM eb mode d _ _ (by omega) (by omega) hs h1 h2,
      fun hG => RefE.coreSpecE (ilamE_spec p hq.body.inferLamIO (k + 1) _ mode vis d _ _) hG.nv
        (hG.toInferG.mono (by omega)) (ilam_ref p hq.leaf hq.body hc.inst1 hc.abs1 k (hk.mono (by omega))
          F _ a₀ dn vis fe MM eb mode d _ _ (by omega) (by omega) hs h1 h2)⟩
  | app f x =>
    obtain ⟨hg, -⟩ := hvr
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    have h4 : e >>> 28 = 4 := by rw [← hhd, hg]
    refine RefE.of_run_eq (inferBodyIO_app _ fe d.toNat (decE e) a₀ f x hv) ?_
    refine bodyArm_ref (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl) (fun _ _ => rfl) fun k hk' => ?_
    subst hk'
    exact ⟨inferAppIO_refines p hq.spio hq.spine hc.instList k (hk.mono (by omega)) F (by omega)
        (by omega) _ a₀ dn vis fe MM eb mode d e hs he h4,
      fun hG => RefE.coreSpecE (aioE_spec p hq.spio.appIO (k + 1) _ mode vis d e) hG.nv
        (hG.toInferG.mono (by omega)) (aio_ref p hq.spio hq.spine hc.instList k (hk.mono (by omega)) F
          (by omega) (by omega) _ a₀ dn vis fe MM eb mode d e hs he h4)⟩
  | letE ty v b =>
    obtain ⟨hg, h1, hd1, h2, hd2, h3, hd3⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2 hd2; rw [getD3] at h3 hd3
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    rw [← hd1, ← hd2, ← hd3] at hv
    refine RefE.of_run_eq (inferBodyIO_let _ fe d.toNat (decE e) a₀ _ _ _ hv) ?_
    refine RefE.bind_callW (fun _ => rfl) (hc.inst1 n s₀ a₀ dn vis fe MM eb _ _ 0 hS h3 h2)
      fun r₁ m₁ _ ⟨_, ⟨M₁, hS₁, hK₁, hSt₁⟩, _, hrw1⟩ => ?_
    have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
    simp only [iboE.k_inst1]
    rw [← bind_pure (CoreFnsA.infer _ _ _)]
    refine RefE.bind_callE (fun _ => rfl) ((hk n (Nat.le_refl _)).inferIO F _ _ dn vis fe M₁ eb
      mode d (r₁.headD 0) hF hn hs₁ hrw1) (fun (hG : InferBodyG p n) => (hG.knot n (Nat.le_refl _)).inferIO
        F _ _ dn vis fe M₁ eb mode d (r₁.headD 0) hF hn hs₁ hrw1) fun _ _ _ h₄ => ?_
    exact RefE.ret rfl ⟨CoreAfter.comp hK₁ hSt₁ h₄.after, rfl, h₄.resOk⟩
  | proj sn i pe =>
    obtain ⟨hg, h1, hd1, h2, h3, hd3⟩ := hvr
    rw [getD1] at h1 hd1; rw [getD2] at h2; rw [getD3] at h3 hd3
    simp (config := { decide := true }) only [hg, ↓reduceIte]
    rw [← hd1, ← h2, ← hd3] at hv
    refine RefE.of_run_eq (inferBodyIO_proj _ fe d.toNat (decE e) a₀ _ _ _ hv) ?_
    refine bodyArm_ref (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl) (fun _ _ => rfl) fun k hk' => ?_
    subst hk'
    exact ⟨(hc.proj k (hk.mono (by omega)) F _ a₀ dn vis fe MM eb mode d _ _ _ (by omega) (by omega) hs
        h1 h3).2,
      fun hG => (hG.proj k (hk.mono (by omega)) (hG.knot.mono (by omega)) F _ a₀ dn vis fe MM eb mode
        d _ _ _ (by omega) (by omega) hs h1 h3).2⟩

/-- **`infer_body` refines `inferBody`** at the knot one level down: `InferBodySpec p n` for every
`n` (`ib_ref`'s ok half). -/
@[refines ConRon.Arena.inferBody]
theorem inferBody_refines (p : Prog) (hq : InferAllProg p) (hc : InferCallees p) :
    ∀ n, InferBodySpec p n := by
  intro n F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he hk
  cases n with
  | zero => exact CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe MM eb _
  | succ n =>
  exact RefE.coreSpec (ibE_spec p hq.inferBody (n + 1) s₀ mode vis d e)
    (ib_ref p hq hc n F s₀ a₀ dn vis fe MM eb mode d e (by omega) (by omega) hs he (hk.mono (by omega)))

/-- **`infer_body_io` refines `inferBodyIO`** at the io view of the knot one level down
(`ibo_ref`'s ok half). -/
@[refines ConRon.Arena.inferBodyIO]
theorem inferBodyIO_refines (p : Prog) (hq : InferAllProg p) (hc : InferCallees p) :
    ∀ n, InferIOBodySpec p n := by
  intro n F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he hk
  cases n with
  | zero => exact CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe MM eb _
  | succ n =>
  exact RefE.coreSpec (iboE_spec p hq.inferBodyIO (n + 1) s₀ mode vis d e)
    (ibo_ref p hq hc n F s₀ a₀ dn vis fe MM eb mode d e (by omega) (by omega) hs he (hk.mono (by omega)))

/-- **`infer_body`'s verdicts** (`ib_ref`'s error half): `InferBodySpecE p n` for every `n`. -/
theorem inferBody_refinesE (p : Prog) (hq : InferAllProg p) (hc : InferCallees p)
    (hpj : InferProjOKE p) (hnv : closedNV p L.Checker.nvFns = true) : ∀ n, InferBodySpecE p n := by
  intro n F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he hk hkE
  cases n with
  | zero => exact CoreSpecE.zero p _ _ _ s₀ a₀
  | succ n =>
  exact RefE.coreSpecE (ibE_spec p hq.inferBody (n + 1) s₀ mode vis d e) hnv
    ⟨⟨hkE.mono (by omega), hnv⟩, hpj⟩
    (ib_ref p hq hc n F s₀ a₀ dn vis fe MM eb mode d e (by omega) (by omega) hs he (hk.mono (by omega)))

/-- **`infer_body_io`'s verdicts** (`ibo_ref`'s error half). -/
theorem inferBodyIO_refinesE (p : Prog) (hq : InferAllProg p) (hc : InferCallees p)
    (hpj : InferProjOKE p) (hnv : closedNV p L.Checker.nvFns = true) : ∀ n, InferIOBodySpecE p n := by
  intro n F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he hk hkE
  cases n with
  | zero => exact CoreSpecE.zero p _ _ _ s₀ a₀
  | succ n =>
  exact RefE.coreSpecE (iboE_spec p hq.inferBodyIO (n + 1) s₀ mode vis d e) hnv
    ⟨⟨hkE.mono (by omega), hnv⟩, hpj⟩
    (ibo_ref p hq hc n F s₀ a₀ dn vis fe MM eb mode d e (by omega) (by omega) hs he (hk.mono (by omega)))

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
