module

public import ConAgua.Arena.IotaFrameAt
public import ConAgua.Arena.StageTLift
public import ConAgua.Arena.TwinStep
public import ConRon.Bridge.Inductives.Run
import ConRon.Bridge.Inductives.Rel
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Pers

@[expose] public section

/-!
# The ι reading rule, part 1: the twin steps of `iota_parts_at`'s interning callees (lane ronsync8)

`ctorLevelsAt` and `iotaParamsAt` intern (level lists, bound variables): each is a `PStep` of
the twin state (con-ron's `Bridge/Inductives/Run.lean` frame: the store grown, the read-back
caches' invariants kept, the pins unchanged), so `TwinOK` survives them (`TwinOK.of_pstep`) and
`iota_parts_at` can call the core walk `inst_lp_fast` under `StageT` after them.
-/

open ConRon.Arena

/-- **`TwinOK` across a twin `PStep`** (`TwinOK.of_grow` with the caches' frame `CacheFrame`
for the cache equation): the memory is unchanged. -/
theorem L.Arena.TwinOK.of_pstep {dn : NIdx → Option ConLeche.Name} {m : L.Mem} {a a' : AState}
    {fe : IFEnv} (h : L.Arena.TwinOK dn m a fe) (hp : ConRon.Bridge.Inductives.PStep a a') :
    L.Arena.TwinOK dn m a' fe := by
  obtain ⟨rk, hw⟩ := hp.ok.wf
  have hx := hp.ext
  have hLs : LsStoreWF a'.store.lss := hw.lss
  have hL : LStoreWF a'.store.ls := hLs.ls
  have hN : ∀ i n, denoteN a.store.ns i = some n → denoteN a'.store.ns i = some n :=
    hx.lss.ls.ns
  have hNs : ∀ (l : List NIdx) ks, l.mapM (denoteN a.store.ns) = some ks →
      l.mapM (denoteN a'.store.ns) = some ks := by
    intro l; induction l with
    | nil => intro ks h; simpa using h
    | cons x xs ih =>
      intro ks h
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h ⊢
      obtain ⟨y, hy, ys, hys, rfl⟩ := h
      exact ⟨y, hN _ _ hy, ys, ih _ hys, rfl⟩
  have hLv : ∀ u l, denoteL a.store.ls u = some l → denoteL a'.store.ls u = some l :=
    hx.lss.ls.lvl
  refine ⟨hp.cframe.readL h.readL, hp.cframe.readLs h.readLs, hw.nsWF, h.erec, h.spn, h.memos,
    h.bstk, ?_⟩
  refine ⟨fun x u hv => ?_, fun x c us hv => ?_, ?_, ?_, hp.cframe.readN h.den.readN,
    fun c ci hf => ?_, fun c tbl hf => ?_, fun u hu => L.Arena.denoteL_of_viewW hL hu,
    fun us hus => ?_, fun k x e => hN _ _ (h.den.dnN k x e),
    fun c cv mI rP isK rules hf r hr lvls pins hfi u hu => ?_,
    fun c cv mI rP isK rules hf r hr lvls hfi u hu => ?_⟩
  · exact L.Arena.denoteL_of_viewW hL (hw.lchildOK x _ hv u (by simp [ENodeView.lchildren])).1
  · have hs := (hw.lschildOK x _ hv us (by simp [ENodeView.lschildren])).1
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨xs, hxs⟩ := L.Arena.denoteLs_of_viewW hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · rw [hp.pins]; exact hLv _ _ h.den.zero
  · obtain ⟨l, hl⟩ := h.den.emptyLs; exact ⟨l, by rw [hp.pins]; exact hx.lss.lst _ _ hl⟩
  · obtain ⟨ks, hks⟩ := h.den.constLps c ci hf; exact ⟨ks, hNs _ _ hks⟩
  · obtain ⟨ks, hks⟩ := h.den.proj c tbl hf; exact ⟨ks, hNs _ _ hks⟩
  · obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hus
    obtain ⟨xs, hxs⟩ := L.Arena.denoteLs_of_viewW hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · obtain ⟨L, hL'⟩ := h.den.recRules c cv mI rP isK rules hf r hr lvls pins hfi u hu
    exact ⟨L, hLv _ _ hL'⟩
  · obtain ⟨L, hL'⟩ := h.den.recLevels c cv mI rP isK rules hf r hr lvls hfi u hu
    exact ⟨L, hLv _ _ hL'⟩

namespace L.Ind

open ConRon.Bridge ConRon.Bridge.Inductives

/-! ## The twin steps -/

/-- **`ctorLevelsAt` is a `PStep`** (upstream `ctorLevelsAt_run`'s frame half, from `StateOK`). -/
theorem ctorLevelsAt_pstep {s s' : AState} {rl : IRecRule} {fP : ConLeche.RecRuleFire}
    {lps : List NIdx} {lpsP : List ConLeche.Name} {r : LsIdx} (hok : StateOK s)
    (hf : ConRon.Arena.Frontend.denoteFire s.store rl.fire = some fP)
    (hlps : ConRon.Arena.Frontend.denoteNList s.store.ns lps = some lpsP)
    (hrun : ctorLevelsAt rl lps s = .ok (r, s')) : PStep s s' := by
  simp only [ctorLevelsAt] at hrun
  cases hfr : rl.fire with
  | plain =>
    rw [hfr] at hrun
    obtain ⟨p, -⟩ := paramLevels_run hok hlps hrun
    exact PStep.of_caches p.ok p.ext p.caches p.pins
  | nested lvls pins =>
    rw [hfr] at hrun hf
    simp only [ConRon.Arena.Frontend.denoteFire] at hf
    cases h1 : denoteLList s.store.ls lvls with
    | none => rw [h1] at hf; simp at hf
    | some ls => exact (internLsNode_run hok h1 hrun).1
  | levels lvls =>
    rw [hfr] at hrun hf
    simp only [ConRon.Arena.Frontend.denoteFire, Option.map_eq_some_iff] at hf
    obtain ⟨ls, h1, -⟩ := hf
    exact (internLsNode_run hok h1 hrun).1

/-- **`iotaBVars` is a `PStep`** (upstream `iotaBVars_run`'s frame half). -/
theorem iotaBVars_pstep (rP n : Nat) : ∀ (k i : Nat), n - i = k → ∀ {s s' : AState}
    {r : List EIdx}, StateOK s → iotaBVars rP n i s = .ok (r, s') → PStep s s' := by
  intro k
  induction k with
  | zero =>
    intro i hk s s' r hok hrun
    rw [iotaBVars, ite_eq_right (by omega)] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact PStep.refl hok
  | succ k ih =>
    intro i hk s s' r hok hrun
    rw [iotaBVars, ite_eq_left (by omega)] at hrun
    obtain ⟨b, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨p1, -⟩ := internBVarE_run hok k1
    obtain ⟨bs, s₂, k2, z2⟩ := AM.bind_ok z1
    have p2 := ih (i + 1) (by omega) p1.ok k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    exact p1.trans p2

/-- **`iotaParamsAt` is a `PStep`**. -/
theorem iotaParamsAt_pstep {s s' : AState} {rl : IRecRule} {rP cnP : Nat} {r : List EIdx}
    (hok : StateOK s) (hrun : iotaParamsAt rl rP cnP s = .ok (r, s')) : PStep s s' := by
  simp only [iotaParamsAt] at hrun
  cases hfr : rl.fire with
  | nested lvls pins =>
    rw [hfr] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact PStep.refl hok
  | plain => rw [hfr] at hrun; exact iotaBVars_pstep rP _ _ 0 rfl hok hrun
  | levels lvls => rw [hfr] at hrun; exact iotaBVars_pstep rP _ _ 0 rfl hok hrun

end L.Ind
