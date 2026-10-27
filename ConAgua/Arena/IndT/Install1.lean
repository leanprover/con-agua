import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndSumSpec.CtlW
import ConAgua.Arena.IndRealOpf3

/-!
# `checkBlockDomsAt`, `checkStructDomsAt` under `StageC` (lane `indstaget`)

`check_block_doms_at`'s model at `realCall p`, from `StageC` and con-ron's preconditions of
`checkBlockDomsAt_specF` (the opened variables and the expected domains denote; their scoping at
the comparison's depth), its twin side transcribed from that spec's proof: `fvarTypeD`
(`fvarTypeD_run`: the twin's state unchanged, an L-only step for the stage), `isDefEqCore`
(`isDefEqC_rsim`), the recursion at the extended store (`denoteEList_ext`).
`check_struct_doms_at` is the same walk with its result words dropped (`sdomsW_eq`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `open_pis_at_fvars_f`, the real call (replacing the stub contract) -/

/-- A call of `open_pis_at_fvars_f` in a program with `opfP` is its model `opfF`. -/
theorem callW_opfF {p : Prog} (hOpf : OpfF p) {n : Nat} {args r : List Word} {m m' : Mem}
    (h : callW p n "open_pis_at_fvars_f" args m = some (r, m')) : opfF m args = some (r, m') := by
  obtain ⟨s', hs, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (opfF_spec p hOpf n _ args) h
  rw [← hs]; exact hW

/-- **`open_pis_at_fvars_f`, the real call, as a `Sim`** (the stub contract's `KeepPost`, the
twin's run, and `AbsOK` after: `opfF_ok`). -/
theorem opfSimRA {p : Prog} (hOpf : OpfF p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {k e i : Word} (he : H e) {m : Mem} {a : AState} (hS : StageR dn vis fe m a)
    (hA : AbsOK m) :
    Sim (callW p n "open_pis_at_fvars_f" [k, e, i] m) (openPisAtFvarsF k.toNat (decI e) i.toNat) a
      (fun r x m' a' => ((StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decOLE m' r x) ∧
        (openPisAtFvarsF k.toNat (decI e) i.toNat).run a = .ok (x, a')) ∧ AbsOK m') := by
  intro r m' h
  obtain ⟨x, a', hrun, ⟨hS', hg, hd⟩, hA'⟩ :=
    opfF_ok dn vis fe k e i he m m' a r (callW_opfF hOpf h) ⟨hS, hA⟩
  exact ⟨x, a', hrun, ⟨⟨hS', hg, hd⟩, hrun⟩, hA'⟩

/-- The same, from the model's run. -/
theorem opfF_okRA {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {k e i : Word}
    (he : H e) {m m' : Mem} {a : AState} {r : List Word} (h : opfF m [k, e, i] = some (r, m'))
    (hS : StageR dn vis fe m a) (hA : AbsOK m) :
    ∃ x a', (openPisAtFvarsF k.toNat (decI e) i.toNat).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decOLE m' r x ∧ AbsOK m' := by
  obtain ⟨x, a', hrun, ⟨hS', hg, hd⟩, hA'⟩ := opfF_ok dn vis fe k e i he m m' a r h ⟨hS, hA⟩
  exact ⟨x, a', hrun, hS', hg, hd, hA'⟩

/-- A `RSim` of a word model is a `Sim` of it. -/
theorem RSim.toSim {α : Type} {mo : Option (List Word × Mem)} {op : AM α} {a : AState}
    {Q : List Word × Mem → AState → α → Prop} (h : RSim mo op a Q) :
    Sim mo op a (fun r x m' a' => Q (r, m') a' x) := fun r m' e => h (r, m') e

/-- A `Sim` also records the twin's run. -/
theorem _root_.L.Arena.Sim.withRunC {β α : Type} {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (h : Sim mo op a Q) :
    Sim mo op a (fun r x m' a' => Q r x m' a' ∧ op.run a = .ok (x, a')) := by
  intro r m' e; obtain ⟨x, a', h1, h2⟩ := h r m' e; exact ⟨x, a', h1, h2, h1⟩

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`check_block_doms_at` under `StageC`** (twin side: con-ron's `checkBlockDomsAt_specF`'s
proof; its scoping hypotheses below the count `j`, as `checkStructDomsAt_spec` states them). -/
theorem domsW_simC (n : Nat) (hn : n ≤ 2 ^ 62) : ∀ (m : Mem) (a : AState) (off fo fl dO dl j : Word)
    (fvs doms : List EIdx) (fvsP domsP : List ConLeche.Expr),
    StageC dn vis fe env m a → AbsOK m →
    decHL m fo.toNat fl.toNat = some fvs → decHL m dO.toNat dl.toNat = some doms →
    fo.toNat + fl.toNat < 2 ^ 64 → dO.toNat + dl.toNat < 2 ^ 64 → fo.toNat + fl.toNat ≤ iwTop m →
    dO.toNat + dl.toNat ≤ iwTop m → off.toNat + fl.toNat < 2 ^ 64 →
    j.toNat ≤ fl.toNat → j.toNat ≤ dl.toNat →
    Frontend.denoteEList a.store fvs = some fvsP → Frontend.denoteEList a.store doms = some domsP →
    (∀ i, i < j.toNat → ∀ x y, fvsP[i]? = some x → domsP[i]? = some y →
      ConLeche.Expr.WScoped (off.toNat + i) x.fvarTypeD ∧ ConLeche.Expr.WScoped (off.toNat + i) y) →
    RSim (domsW (realCall p) n m vis off fo fl dO dl j)
      (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms j.toNat) a
      (fun b a' _ => StageC dn vis fe env b.2 a' ∧ IWGrow m b.2 ∧ AbsOK b.2) := by
  induction n with
  | zero => intros; intro b hb; simp [domsW] at hb
  | succ n ih =>
    intro m a off fo fl dO dl j fvs doms fvsP domsP hC hA hfvs hdoms hfob hdob hfot hdot hoob hjf
      hjd hfP hdP hws
    intro ⟨r, m'⟩ h
    have hStage := hC.stage
    have hfvl := decHL_length m hfvs
    have hdol := decHL_length m hdoms
    by_cases hj : j = 0
    · subst hj
      rw [domsW_zero (realCall p) n m vis off fo fl dO dl 0 rfl] at h
      obtain ⟨-, hm⟩ := Prod.mk.inj (Option.some.inj h)
      subst hm
      exact ⟨(), a, rfl, hC, IWGrow.refl m, hA⟩
    have hjpos : 1 ≤ j.toNat := Nat.pos_of_ne_zero fun h0 => hj (UInt64.toNat_inj.mp (by simpa using h0))
    have hj1 : (j - 1).toNat = j.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hjpos))]
      simp
    by_cases hfl : fl ≤ j - 1
    · rw [domsW_abortF (realCall p) n m vis off fo fl dO dl j hj hfl] at h; simp at h
    by_cases hdl : dl ≤ j - 1
    · rw [domsW_abortD (realCall p) n m vis off fo fl dO dl j hj hfl hdl] at h; simp at h
    rw [domsW_cons (realCall p) n m vis off fo fl dO dl j hj hfl hdl] at h
    have hjm1f : j.toNat - 1 < fl.toNat := by
      have : ¬ fl.toNat ≤ (j - 1).toNat := by rw [← UInt64.le_iff_toNat_le]; exact hfl
      omega
    have hjm1d : j.toNat - 1 < dl.toNat := by
      have : ¬ dl.toNat ≤ (j - 1).toNat := by rw [← UInt64.le_iff_toNat_le]; exact hdl
      omega
    have hfoeq : fo + (j - 1) = UInt64.ofNat (fo.toNat + (j.toNat - 1)) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, hj1]; simp
    have hdoeq : dO + (j - 1) = UInt64.ofNat (dO.toNat + (j.toNat - 1)) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, hj1]; simp
    obtain ⟨wa, hwa_eq, hwa_lt, hwa_dec⟩ := decHL_get' hfvs (j.toNat - 1) hjm1f hfob
    obtain ⟨wb, hwb_eq, hwb_lt, hwb_dec⟩ := decHL_get' hdoms (j.toNat - 1) hjm1d hdob
    rw [hfoeq, hdoeq, hwa_eq, hwb_eq] at h
    have hfvsij : fvs[j.toNat - 1]? = some (decI wa) := by
      rw [List.getElem?_eq_getElem (by omega : j.toNat - 1 < fvs.length)]
      exact congrArg some hwa_dec
    have hdomsij : doms[j.toNat - 1]? = some (decI wb) := by
      rw [List.getElem?_eq_getElem (by omega : j.toNat - 1 < doms.length)]
      exact congrArg some hwb_dec
    obtain ⟨aP, haP, hda⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? fvs fvsP hfP _ _ hfvsij
    obtain ⟨bP, hbP, hdb⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? doms domsP hdP _ _ hdomsij
    obtain ⟨hwx, hwy⟩ := hws (j.toNat - 1) (by omega) aP bP haP hbP
    rcases hra : ftdF m [wa] with _ | ⟨ra, m1⟩
    · rw [hra] at h; simp [domsK1] at h
    rw [hra, domsK1_some] at h
    obtain ⟨x1, a1, hrun1, hStage1, hg1, hw1lt, hw1eq⟩ :=
      ftdF_ok dn vis fe wa hwa_lt m m1 a ra hra hStage
    -- the twin's `fvarTypeD`: its state unchanged, the answer the opened variable's annotation
    obtain ⟨ha1, hx1d⟩ := ConRon.Bridge.Inductives.fvarTypeD_run hC.check.state hda hrun1
    rw [ha1] at hrun1 hStage1
    have hA1 := ftdF_afr hra hA
    have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hStage1 hA1 (PStep.refl hC.check.state)
    have hdep : (off + (j - 1)).toNat = off.toNat + (j.toNat - 1) := by
      rw [UInt64.toNat_add, hj1]; exact Nat.mod_eq_of_lt (by omega)
    have hdx : denoteE a.store (decI (ra.headD 0)) = some aP.fvarTypeD := by rw [hw1eq]; exact hx1d
    rcases hrb : realCall p n "is_def_eq_core" [vis, off + (j - 1), ra.headD 0, wb] m1 with _ | ⟨rb, m2⟩
    · rw [hrb] at h; simp [domsK2] at h
    rw [hrb] at h
    by_cases heq0 : rb.headD 0 = 0
    · rw [domsK2_abort (heq := heq0) ..] at h; simp at h
    rw [domsK2_ok (heq := heq0) ..] at h
    obtain ⟨x2, a2, hrun2, hC2, hg2, hb2eq, hA2, hcs2⟩ :=
      isDefEqC_rsim hq henv n (by omega) hC1 hA1 (off + (j - 1)) (ra.headD 0) wb hw1lt hwb_lt hdx hdb
        (by rw [hdep]; exact hwx) (by rw [hdep]; exact hwy) _ hrb
    dsimp only at hC2 hg2 hb2eq hA2
    rw [hdep] at hrun2
    rcases hw : domsW (realCall p) n m2 vis off fo fl dO dl (j - 1) with _ | ⟨r3, m3⟩
    · rw [hw] at h; simp [domsK3] at h
    rw [hw, domsK3_some] at h
    obtain ⟨-, hm3⟩ := Prod.mk.inj (Option.some.inj h)
    subst hm3
    have hg12 := hg1.trans hg2
    obtain ⟨u, a', hrun3, hC3, hg3, hA3⟩ := ih (by omega) m2 a2 off fo fl dO dl (j - 1) fvs doms fvsP
      domsP hC2 hA2 (by rw [decHL_grow hg12]; exact hfvs; omega)
      (by rw [decHL_grow hg12]; exact hdoms; omega) hfob hdob (by have := hg12.1; omega)
      (by have := hg12.1; omega) hoob (by omega) (by omega)
      (ConRon.Bridge.denoteEList_ext hcs2.ext _ _ hfP) (ConRon.Bridge.denoteEList_ext hcs2.ext _ _ hdP)
      (fun i hi => hws i (by omega)) _ hw
    rw [hj1] at hrun3
    refine ⟨(), a', ?_, hC3, hg12.trans hg3, hA3⟩
    have hjeq : j.toNat = (j.toNat - 1) + 1 := by omega
    have hv2 : x2 = true := by
      rw [← hb2eq]
      simpa [decBool] using heq0
    rw [hjeq]
    show (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms ((j.toNat - 1) + 1)).run a =
      .ok ((), a')
    simp only [ConRon.Arena.checkBlockDomsAt, unwrapOr, hfvsij, hdomsij, pure_bind,
      StateT.run_bind]
    rw [hrun1]
    simp only [bind, Except.bind]
    rw [← hw1eq, hrun2]
    simp only [hv2]
    exact hrun3

include hq henv in
/-- **`check_struct_doms_at` under `StageC`**: `domsW_simC` with the result words dropped
(`sdomsW_eq`); the twins agree on successful runs (`checkStructDomsAt_of_block`). -/
theorem sdomsW_simC (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (off fo fl dO dl j : Word)
    (fvs doms : List EIdx) (fvsP domsP : List ConLeche.Expr)
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hfvs : decHL m fo.toNat fl.toNat = some fvs) (hdoms : decHL m dO.toNat dl.toNat = some doms)
    (hfob : fo.toNat + fl.toNat < 2 ^ 64) (hdob : dO.toNat + dl.toNat < 2 ^ 64)
    (hfot : fo.toNat + fl.toNat ≤ iwTop m) (hdot : dO.toNat + dl.toNat ≤ iwTop m)
    (hoob : off.toNat + fl.toNat < 2 ^ 64) (hjf : j.toNat ≤ fl.toNat) (hjd : j.toNat ≤ dl.toNat)
    (hfP : Frontend.denoteEList a.store fvs = some fvsP)
    (hdP : Frontend.denoteEList a.store doms = some domsP)
    (hws : ∀ i, i < j.toNat → ∀ x y, fvsP[i]? = some x → domsP[i]? = some y →
      ConLeche.Expr.WScoped (off.toNat + i) x.fvarTypeD ∧ ConLeche.Expr.WScoped (off.toNat + i) y) :
    RSim (sdomsW (realCall p) n m vis off fo fl dO dl j)
      (ConRon.Arena.checkStructDomsAt V fe off.toNat fvs doms j.toNat) a
      (fun b a' _ => StageC dn vis fe env b.2 a' ∧ IWGrow m b.2 ∧ AbsOK b.2) := by
  intro ⟨r, m'⟩ e
  rw [sdomsW_eq] at e
  obtain ⟨⟨r0, m0⟩, hd, e⟩ := of_K e rfl
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨-, rfl⟩ := e
  obtain ⟨u, a', hrun, hQ⟩ := domsW_simC hq henv n hn m a off fo fl dO dl j fvs doms fvsP domsP hC hA
    hfvs hdoms hfob hdob hfot hdot hoob hjf hjd hfP hdP hws _ hd
  exact ⟨(), a', checkStructDomsAt_of_block fe _ fvs doms _ _ _ hrun, hQ⟩

include hq henv in
/-- **`check_block_doms_at` refines `checkBlockDomsAt .verified`** under `StageC` (the knot's
`is_def_eq_core`; the inputs' denotations and scoping as con-ron's `checkBlockDomsAt_specF`
asks). -/
@[refines ConRon.Arena.checkBlockDomsAt]
theorem checkBlockDomsAt_refinesC (hp : p.lookup "check_block_doms_at" = some checkBlockDomsAt)
    (hftd : FtdF p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (off fo fl dO dl j : Word)
    (fvs doms : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hfvs : decHL s₀.mem fo.toNat fl.toNat = some fvs)
    (hdoms : decHL s₀.mem dO.toNat dl.toNat = some doms)
    (hfob : fo.toNat + fl.toNat < 2 ^ 64) (hdob : dO.toNat + dl.toNat < 2 ^ 64)
    (hfot : fo.toNat + fl.toNat ≤ iwTop s₀.mem) (hdot : dO.toNat + dl.toNat ≤ iwTop s₀.mem)
    (hoob : off.toNat + fl.toNat < 2 ^ 64) (hjf : j.toNat ≤ fl.toNat) (hjd : j.toNat ≤ dl.toNat)
    {fvsP domsP : List ConLeche.Expr} (hfP : Frontend.denoteEList a₀.store fvs = some fvsP)
    (hdP : Frontend.denoteEList a₀.store doms = some domsP)
    (hc : ∀ (i : Nat) (x : ConLeche.Expr), fvsP[i]? = some x →
      ConLeche.Expr.WScoped (off.toNat + i) x.fvarTypeD)
    (ht : ∀ (i : Nat) (x : ConLeche.Expr), domsP[i]? = some x →
      ConLeche.Expr.WScoped (off.toNat + i) x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_doms_at" [vis, off, fo, fl, dO, dl, j]
    ⦃fun _r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms j.toNat) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms j.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (domsW_spec p hp hftd (realCall p) (realCall_spec p) n s₀ vis off fo fl dO dl j)
    fun _ _ ⟨hl, hw⟩ =>
      let h := (domsW_simC hq henv n hn _ a₀ off fo fl dO dl j fvs doms fvsP domsP hC hA hfvs hdoms
        hfob hdob hfot hdot hoob hjf hjd hfP hdP
        (fun i _ x y hx hy => ⟨hc i x hx, ht i y hy⟩)).am hw
      ⟨hl, h.1, h.2.1, h.2.2⟩

include hq henv in
/-- **`check_struct_doms_at` refines `checkStructDomsAt .verified`** under `StageC` (the inputs'
denotations and scoping as con-ron's `checkStructDomsAt_spec` asks). -/
@[refines ConRon.Arena.checkStructDomsAt]
theorem checkStructDomsAt_refinesC (hg : p.lookup "sl_get" = some slGet)
    (hp : p.lookup "check_struct_doms_at" = some checkStructDomsAtL) (hftd : FtdF p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (off fo fl dO dl j : Word) (fvs doms : List EIdx)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hfvs : decHL s₀.mem fo.toNat fl.toNat = some fvs)
    (hdoms : decHL s₀.mem dO.toNat dl.toNat = some doms)
    (hfob : fo.toNat + fl.toNat < 2 ^ 64) (hdob : dO.toNat + dl.toNat < 2 ^ 64)
    (hfot : fo.toNat + fl.toNat ≤ iwTop s₀.mem) (hdot : dO.toNat + dl.toNat ≤ iwTop s₀.mem)
    (hoob : off.toNat + fl.toNat < 2 ^ 64) (hjf : j.toNat ≤ fl.toNat) (hjd : j.toNat ≤ dl.toNat)
    {fvsP domsP : List ConLeche.Expr} (hfP : Frontend.denoteEList a₀.store fvs = some fvsP)
    (hdP : Frontend.denoteEList a₀.store doms = some domsP)
    (hws : ∀ i, i < j.toNat → ∀ x y, fvsP[i]? = some x → domsP[i]? = some y →
      ConLeche.Expr.WScoped (off.toNat + i) x.fvarTypeD ∧ ConLeche.Expr.WScoped (off.toNat + i) y) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_struct_doms_at" [vis, off, fo, fl, dO, dl, j]
    ⦃fun _r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.checkStructDomsAt V fe off.toNat fvs doms j.toNat) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.checkStructDomsAt V fe off.toNat fvs doms j.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (sdomsW_spec p hg hp hftd (realCall p) (realCall_spec p) n s₀ vis off fo fl dO dl j)
    fun _ _ ⟨hl, hw⟩ =>
      let h := (sdomsW_simC hq henv n hn _ a₀ off fo fl dO dl j fvs doms fvsP domsP hC hA hfvs hdoms
        hfob hdob hfot hdot hoob hjf hjd hfP hdP hws).am hw
      ⟨hl, h.1, h.2.1, h.2.2⟩

end sims

end L.Ind
