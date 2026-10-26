import ConAgua.Arena.InferProj

/-!
# `inferProj`: `infer_proj` (lane `defeq2`, helper `defeq2-proj`)

`infer_proj(mode, io, vis, d, sn, i, pe)` refines `inferProj` at both grades (`io = 0`: the knot;
`io = 1`: its io view, `CoreFnsA.ioView`), at L fuel `n + 1` from `KnotUpTo p n`: the subject's
type (`infer`/`infer_io`, then `whnf`), its head constant `T.{us}` (read once, before
`find_proj`), the table lookup, then `infer_proj_at` (`InferProj.lean`). A miss aborts in L where
the twin fails (`projMissError`'s verdict, an error).

**`inferProj_refines : InferProjProg p → InferProjCallees p → InferProjOK p`**, closing
`InferCallees.proj` (`InferBodyDisp.lean`).

Twin-side facts used here: `findProj?` is a pure lookup that answers only entries below the table's
field count (`findProj?_lt`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The model of `infer_proj` -/

section ipK
variable (p : Prog) (n : Nat) (mode io vis d sn i pe : Word)

/-- After `find_proj`: a hit's table record, then `infer_proj_at`. -/
def ipK4 (te cT cu : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then none
    else call1W p n "infer_proj_at" [vis, sn, i, pe, te, cT, cu, r.tail.headD 0] m

/-- At the head `hh` of the subject's type: a constant past the view checks, its name and levels
read, then `find_proj`. -/
def ipHead (te hh : Word) (m : Mem) : Option (Word × Mem) :=
  if hh >>> 28 ≠ 3 then none
  else if tierW hh ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m CONST (tierW hh) ≤ idxW hh then none
  else ipK4 p n vis sn i pe te (tfld m CONST (tierW hh) (idxW hh) 0)
    (tfld m CONST (tierW hh) (idxW hh) 1)
    (callW p n "find_proj" [vis, tfld m CONST (tierW hh) (idxW hh) 0, i] m)

/-- After `whnf`: the head. -/
def ipK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    match callW p n "get_app_fn" [r.headD 0] m with
    | none => none
    | some (r', m') => ipHead p n vis sn i pe (r.headD 0) (r'.headD 0) m'

/-- After the subject's `infer`: `whnf`. -/
def ipK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => ipK2 p n vis sn i pe (callW p n "whnf" [mode, vis, d, r.headD 0] m)

/-- The subject's type at the grade `io`. -/
def ipFirst (m : Mem) : Option (List Word × Mem) :=
  if io ≠ 0 then callW p n "infer_io" [mode, vis, d, pe] m else callW p n "infer" [mode, vis, d, pe] m

end ipK

/-- **The model of `infer_proj`.** -/
def ipW (p : Prog) (n : Nat) (m : Mem) (mode io vis d sn i pe : Word) : Option (Word × Mem) :=
  ipK1 p n mode vis d sn i pe (ipFirst p n mode io vis d pe m)

theorem inferProj_spec (p : Prog) (hp : InferProjProg p) (n : Nat) (s₀ : St)
    (mode io vis d sn i pe : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_proj" [mode, io, vis, d, sn, i, pe]
    ⦃fun r s' => LocEq s' s₀ ∧ ipW p n s₀.mem mode io vis d sn i pe = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ip]
  simp only [callFn, inferProjL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec,
      callW_spec p n "infer_io", callW_spec p n "infer", callW_spec p n "whnf",
      callW_spec p n "get_app_fn", callW_spec p n "find_proj", callW_spec p n "infer_proj_at",
      callW_spec p n "find_table", callW_spec p n "get_app_args", callW_spec p n "env_find",
        evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
  simp_all [ipW, ipFirst, ipK1, ipK2, ipHead, ipK4, call1W, tierW, idxW, Cmp.eval, LocEq, BinOp.eval,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ, CTL, CREC, w_lt_false, w_le_false, tfld, tcnt]

/-! ## `infer_proj` refines `inferProj` -/

/-- **A twin run equal to a refined one**, after core runs that kept the maps and the stack. -/
theorem ipRef_trans {α : Type} [Inhabited α] {T T' : AM α} {a₀ a₁ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M M₁ : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (h : T.run a₀ = T'.run a₁)
    (h' : CoreRef T' a₁ dec dn m₁ vis fe M₁ eb r m ok) (hK : KeptAll M M₁ eb)
    (hSt : StackKept m₀ m₁) : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hr⟩ := h'
  have hrun := AM.run_of_ok _ _ hok
  rw [← h] at hrun
  exact ipRef_of_run hrun hres hS' (hK.trans hK') (hSt.trans hSt') hr

/-- **`infer_proj` at the grade `io` refines `inferProj` at the record `R`**, whose `whnf` is the
knot's and whose `infer` the first call refines (`ipFirst`). -/
theorem inferProj_grade (p : Prog) (hp : InferProjProg p) (hc : InferProjCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode io d sn i pe : Word) (R : CoreFnsA)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hpe : HW pe)
    (hWh : R.whnf = (coreKnot (decMode mode) fe id F).whnf)
    (hI : ∀ (r : List Word) (m : Mem), ipFirst p n mode io vis d pe s₀.mem = some (r, m) →
      CoreRef (R.infer d.toNat (decE pe)) a₀ decH dn s₀.mem vis fe M eb r m) :
    CoreSpec p (n + 1) "infer_proj" [mode, io, vis, d, sn, i, pe]
      (inferProj R fe d.toNat (decI sn) i.toNat (decE pe)) decH s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferProj_spec p hp n s₀ mode io vis d sn i pe)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hK := hk n (Nat.le_refl _)
  unfold ipW at hW
  -- the subject's type
  cases hc1 : ipFirst p n mode io vis d pe s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [hc1] at hW
  have h₁ := hI r₁ m₁ hc1
  have hrun1 := ipRun_of_ref h₁
  obtain ⟨-, ⟨M₁, hS₁, hK₁, hSt₁⟩, -, hrw1⟩ := h₁
  -- `whnf`
  simp only [ipK1] at hW
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  have h₂ := CoreSpec.of_callW (hK.whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0)
    hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hrw1) hc2
  rw [← hWh] at h₂
  have hrun2 := ipRun_of_ref h₂
  obtain ⟨-, ⟨M₂, hS₂, hK₂, hSt₂⟩, -, hrw2⟩ := h₂
  -- `get_app_fn`
  simp only [ipK2] at hW
  cases hc3 : callW p n "get_app_fn" [r₂.headD 0] m₂ with
  | none => rw [hc3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [hc3] at hW
  simp only at hW
  obtain ⟨rfl, hhw, hgaf⟩ := getAppFn_callW hp.leaf hS₂.arena.1 hrw2 hc3
  -- the head constant
  simp only [ipHead] at hW
  obtain ⟨g1, hW⟩ := of_ite_none hW
  have g1' : r₃.headD 0 >>> 28 = 3 := Classical.not_not.mp g1
  obtain ⟨g2, hW⟩ := of_ite_none hW
  obtain ⟨g3, hW⟩ := of_ite_none hW
  have hvOK : viewOK m₃ (r₃.headD 0) CONST := ⟨g2, by simpa using g3⟩
  obtain ⟨cT, cu, hv, hcT, hcu, hcTw, hcuw⟩ := view_const_words m₃ _ hS₂.arena.1 (r₃.headD 0) hhw hvOK g1'
  generalize tfld m₃ CONST (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0 = wT at hcT hcTw hW
  generalize tfld m₃ CONST (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 1 = wu at hcu hcuw hW
  subst hcT hcu
  -- the subject's level list reads back (before the lookup interns the table's name)
  obtain ⟨lsu, hdu⟩ := (hc.den dn m₃ _ vis fe M₂ eb hS₂).constLs _ _ _ hv
  -- `find_proj`
  obtain ⟨r₄, m₄, hc4, hW⟩ := callW_cases (K := ipK4 p n vis sn i pe (r₂.headD 0) wT wu) rfl hW
  simp only [ipK4] at hW
  have h₄ := CoreSpec.of_callW (hc.findProj n ⟨m₃, Locals.init []⟩ _ dn vis fe M₂ eb wT i hS₂ hcTw) hc4
  have hrun4 : fe.findProj? (decI wT) i.toNat =
      decEntry (m₃.arr64 EREC) (r₄.headD 0) (r₄.tail.headD 0) i.toNat := h₄.2.2.1
  obtain ⟨-, ⟨M₄, hS₄, hK₄, hSt₄⟩, -, -⟩ := h₄
  have hE₄ : m₄.arr64 EREC = m₃.arr64 EREC := hc.erec n "find_proj" _ m₃ r₄ m₄ (Or.inl rfl) hc4
  obtain ⟨g4, hW⟩ := of_ite_none hW
  obtain ⟨tbl, hdt, hfe⟩ := hc.projFound n m₃ _ dn vis fe M₂ eb wT i r₄ m₄ hS₂ hc4 g4
  have hde : decEntry (m₃.arr64 EREC) (r₄.headD 0) (r₄.tail.headD 0) i.toNat =
      some (tbl.entry i.toNat) := by
    unfold decEntry; rw [if_neg g4, hdt]; rfl
  rw [hde] at hrun4
  have hq₄ : decTbl (m₄.arr64 EREC) (r₄.tail.headD 0).toNat = some tbl := by rw [hE₄]; exact hdt
  have hi : i.toNat < tbl.numFields := findProj?_lt hrun4
  have hdu₄ := hdu
  -- `infer_proj_at`
  cases n with
  | zero => simp [call1W, callW_zero] at hW
  | succ N =>
  have h₅ := CoreSpec.of_call1W (s₀ := ⟨m₄, Locals.init []⟩) (inferProjAt_refines p hp hc N
    ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb sn i pe (r₂.headD 0) wT wu (r₄.tail.headD 0) tbl hS₄ hq₄ hfe
    hi hcuw hrw2 hpe ⟨lsu, hdu₄⟩) (fun r r' h => by simp only [decH, h]) hW
  refine ipRef_trans ?_ h₅ (hK₁.trans (hK₂.trans hK₄)) (hSt₁.trans (hSt₂.trans hSt₄))
  exact inferProj_hit R fe d.toNat (decI sn) i.toNat (decE pe) a₀ _ _ _ _ _ _ _ _ hrun1 hrun2 hgaf
    (by rw [decE_const_tag _ hhw]; simpa using g1') hv hrun4

/-- **`infer_proj` refines `inferProj` at both grades** (`InferProjOK`, `InferBodyDisp.lean`):
the knot's record at `io = 0`, its io view at `io = 1`. -/
@[refines ConRon.Arena.inferProj]
theorem inferProj_refines (p : Prog) (hp : InferProjProg p) (hc : InferProjCallees p) :
    InferProjOK p := by
  intro n hk F s₀ a₀ dn vis fe M eb mode d sn i pe hF hn hs _ hpe
  have hK := hk n (Nat.le_refl _)
  constructor
  · refine inferProj_grade p hp hc n hk F s₀ a₀ dn vis fe M eb mode 0 d sn i pe _ hF hn hs hpe rfl ?_
    intro r m h
    simp only [ipFirst] at h
    rw [if_neg (by decide)] at h
    exact CoreSpec.of_callW (hK.infer F s₀ a₀ dn vis fe M eb mode d pe hF hn hs hpe) h
  · refine inferProj_grade p hp hc n hk F s₀ a₀ dn vis fe M eb mode 1 d sn i pe _ hF hn hs hpe rfl ?_
    intro r m h
    simp only [ipFirst] at h
    rw [if_pos (by decide)] at h
    exact CoreSpec.of_callW (hK.inferIO F s₀ a₀ dn vis fe M eb mode d pe hF hn hs hpe) h

end L.Arena
