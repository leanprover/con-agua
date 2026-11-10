module

public import ConAgua.Arena.AndPinScratch
public import ConRon.Arena.Frontend.Readback
import ConRon.Bridge.StoreBind

@[expose] public section

/-!
# The ROM readers' interning keeps the scratch flag (lane `ronsync2`)

The constant readers (`CIRead.lean`) allocate their records in the tier of the scratch flag
`CTL[1]`, which is the twin's `scratchOn` (`ConsR.flag`). Interning names, levels and expressions
never moves it: every store write is a cons-table append in the current tier. Pure twin reasoning,
with no well-formedness hypothesis (`KeepsScr`, `AndPinScratch.lean`).
-/

open ConRon.Arena

namespace L.Arena

open KeepsScr

theorem internBind_scr (st : EStore) (tag : UInt32) (ty b : EIdx) :
    (st.internBind tag ty b).1.scratchOn = st.scratchOn := by
  unfold EStore.internBind
  dsimp only
  split
  · rfl
  · split
    · split
      · rfl
      · rfl
    · rfl

theorem internNodeE_ks (v : ENodeView) : KeepsScr (internNodeE v) := by
  unfold internNodeE
  refine getBind fun s r s' h => ?_
  dsimp only at h
  cases hf : s.store.find? v with
  | some k => rw [hf] at h; exact (pure' _) _ _ _ h
  | none =>
    rw [hf] at h
    dsimp only at h
    by_cases hc : (if s.store.scratchOn = true then s.store.scr.sizeOf v else s.store.pers.sizeOf v) < v.cap
    · rw [ite_eq_left hc] at h
      generalize hx : s.store.intern v = x at h
      obtain ⟨st', h'⟩ := x
      obtain ⟨_, t1, h1, h2⟩ := ConRon.Bridge.AM.bind_ok h
      rw [(ConRon.Bridge.AM.pure_ok h2).2, ConRon.Bridge.AM.set_ok h1]
      have : st' = (s.store.intern v).1 := by rw [hx]
      rw [this]; exact ConRon.Bridge.EStore.scratchOn_intern _ _
    · rw [ite_eq_right hc] at h
      exact (ConRon.Bridge.AM.fail_ok h).elim

theorem internLamE_ks (ty b : EIdx) : KeepsScr (internLamE ty b) := by
  unfold internLamE
  refine getBind fun s r s' h => ?_
  dsimp only at h
  cases hf : s.store.findBind ETag.lam ty b with
  | some k => rw [hf] at h; exact (pure' _) _ _ _ h
  | none =>
    rw [hf] at h
    dsimp only at h
    by_cases hc : (if s.store.scratchOn = true then s.store.scr.bindSizeOf ETag.lam else s.store.pers.bindSizeOf ETag.lam) < Idx.idxCap
    · rw [ite_eq_left hc] at h
      generalize hx : s.store.internLam ty b = x at h
      obtain ⟨st', h'⟩ := x
      obtain ⟨_, t1, h1, h2⟩ := ConRon.Bridge.AM.bind_ok h
      rw [(ConRon.Bridge.AM.pure_ok h2).2, ConRon.Bridge.AM.set_ok h1]
      have : st' = (s.store.internLam ty b).1 := by rw [hx]
      rw [this]; exact internBind_scr _ _ _ _
    · rw [ite_eq_right hc] at h
      exact (ConRon.Bridge.AM.fail_ok h).elim

theorem internForallEE_ks (ty b : EIdx) : KeepsScr (internForallEE ty b) := by
  unfold internForallEE
  refine getBind fun s r s' h => ?_
  dsimp only at h
  cases hf : s.store.findBind ETag.forallE ty b with
  | some k => rw [hf] at h; exact (pure' _) _ _ _ h
  | none =>
    rw [hf] at h
    dsimp only at h
    by_cases hc : (if s.store.scratchOn = true then s.store.scr.bindSizeOf ETag.forallE else s.store.pers.bindSizeOf ETag.forallE) < Idx.idxCap
    · rw [ite_eq_left hc] at h
      generalize hx : s.store.internForallE ty b = x at h
      obtain ⟨st', h'⟩ := x
      obtain ⟨_, t1, h1, h2⟩ := ConRon.Bridge.AM.bind_ok h
      rw [(ConRon.Bridge.AM.pure_ok h2).2, ConRon.Bridge.AM.set_ok h1]
      have : st' = (s.store.internForallE ty b).1 := by rw [hx]
      rw [this]; exact internBind_scr _ _ _ _
    · rw [ite_eq_right hc] at h
      exact (ConRon.Bridge.AM.fail_ok h).elim

theorem internE_ks : ∀ v : ENodeView, KeepsScr (internE v)
  | .lam ty b => internLamE_ks ty b
  | .forallE ty b => internForallEE_ks ty b
  | .bvar _ => internNodeE_ks _
  | .fvar _ _ => internNodeE_ks _
  | .sort _ => internNodeE_ks _
  | .const _ _ => internNodeE_ks _
  | .app _ _ => internNodeE_ks _
  | .letE _ _ _ => internNodeE_ks _
  | .lit _ => internNodeE_ks _
  | .proj _ _ _ => internNodeE_ks _

theorem internLNode_ks (v : LNodeView) : KeepsScr (internLNode v) := by
  unfold internLNode
  refine getBind fun s r s' h => ?_
  dsimp only at h
  cases hf : s.store.ls.find? v with
  | some k => rw [hf] at h; exact (pure' _) _ _ _ h
  | none =>
    rw [hf] at h
    dsimp only at h
    by_cases hc : (if s.store.ls.scratchOn = true then s.store.ls.scr.sizeOf v else s.store.ls.pers.sizeOf v) < Idx.idxCap
    · rw [ite_eq_left hc] at h
      generalize hx : s.store.internLevel v = x at h
      obtain ⟨st', h'⟩ := x
      obtain ⟨_, t1, h1, h2⟩ := ConRon.Bridge.AM.bind_ok h
      rw [(ConRon.Bridge.AM.pure_ok h2).2, ConRon.Bridge.AM.set_ok h1]
      have : st' = (s.store.internLevel v).1 := by rw [hx]
      rw [this]; rfl
    · rw [ite_eq_right hc] at h
      exact (ConRon.Bridge.AM.fail_ok h).elim

theorem internLsNode_ks (v : LsNodeView) : KeepsScr (internLsNode v) := by
  unfold internLsNode
  refine getBind fun s r s' h => ?_
  dsimp only at h
  cases hf : s.store.lss.find? v with
  | some k => rw [hf] at h; exact (pure' _) _ _ _ h
  | none =>
    rw [hf] at h
    dsimp only at h
    by_cases hc : (if s.store.lss.scratchOn = true then s.store.lss.scr.sizeOf v else s.store.lss.pers.sizeOf v) < Idx.idxCap
    · rw [ite_eq_left hc] at h
      generalize hx : s.store.internLevels v = x at h
      obtain ⟨st', h'⟩ := x
      obtain ⟨_, t1, h1, h2⟩ := ConRon.Bridge.AM.bind_ok h
      rw [(ConRon.Bridge.AM.pure_ok h2).2, ConRon.Bridge.AM.set_ok h1]
      have : st' = (s.store.internLevels v).1 := by rw [hx]
      rw [this]; rfl
    · rw [ite_eq_right hc] at h
      exact (ConRon.Bridge.AM.fail_ok h).elim

theorem internName_ks : ∀ x : ConLeche.Name, KeepsScr (internName x)
  | .anonymous => internNNode_ks _
  | .str p _ => bind' (internName_ks p) fun _ => internNNode_ks _
  | .num p _ => bind' (internName_ks p) fun _ => internNNode_ks _

theorem internLevel_ks : ∀ u : ConLeche.Level, KeepsScr (internLevel u)
  | .zero => internLNode_ks _
  | .succ u => bind' (internLevel_ks u) fun _ => internLNode_ks _
  | .max u v => bind' (internLevel_ks u) fun _ => bind' (internLevel_ks v) fun _ => internLNode_ks _
  | .imax u v => bind' (internLevel_ks u) fun _ => bind' (internLevel_ks v) fun _ => internLNode_ks _
  | .param n => bind' (internName_ks n) fun _ => internLNode_ks _

theorem internLevelList_ks : ∀ us : List ConLeche.Level, KeepsScr (internLevelList us)
  | [] => pure' _
  | u :: us => bind' (internLevel_ks u) fun _ => bind' (internLevelList_ks us) fun _ => pure' _

theorem internLevels_ks (us : List ConLeche.Level) : KeepsScr (internLevels us) :=
  bind' (internLevelList_ks us) fun _ => internLsNode_ks _

theorem internExprGo_ks : ∀ (e : ConLeche.Expr) (m : Frontend.EMemo), KeepsScr (Frontend.internExprGo m e)
  | .bvar _, _ => bind' (internE_ks _) fun _ => pure' _
  | .sort u, _ => bind' (internLevel_ks u) fun _ => bind' (internE_ks _) fun _ => pure' _
  | .const n us, _ => bind' (internName_ks n) fun _ => bind' (internLevels_ks us) fun _ =>
      bind' (internE_ks _) fun _ => pure' _
  | .lit _, _ => bind' (internE_ks _) fun _ => pure' _
  | .fvar _ ty, m => by
    simp only [Frontend.internExprGo]
    split
    · exact pure' _
    · exact bind' (internExprGo_ks ty m) fun _ => bind' (internE_ks _) fun _ => pure' _
  | .app f a, m => by
    simp only [Frontend.internExprGo]
    split
    · exact pure' _
    · exact bind' (internExprGo_ks f m) fun x => bind' (internExprGo_ks a x.1) fun _ =>
        bind' (internE_ks _) fun _ => pure' _
  | .lam ty b, m => by
    simp only [Frontend.internExprGo]
    split
    · exact pure' _
    · exact bind' (internExprGo_ks ty m) fun x => bind' (internExprGo_ks b x.1) fun _ =>
        bind' (internE_ks _) fun _ => pure' _
  | .forallE ty b, m => by
    simp only [Frontend.internExprGo]
    split
    · exact pure' _
    · exact bind' (internExprGo_ks ty m) fun x => bind' (internExprGo_ks b x.1) fun _ =>
        bind' (internE_ks _) fun _ => pure' _
  | .letE ty v b, m => by
    simp only [Frontend.internExprGo]
    split
    · exact pure' _
    · exact bind' (internExprGo_ks ty m) fun x => bind' (internExprGo_ks v x.1) fun y =>
        bind' (internExprGo_ks b y.1) fun _ => bind' (internE_ks _) fun _ => pure' _
  | .proj n _ sub, m => by
    simp only [Frontend.internExprGo]
    split
    · exact pure' _
    · exact bind' (internName_ks n) fun _ => bind' (internExprGo_ks sub m) fun _ =>
        bind' (internE_ks _) fun _ => pure' _

theorem internExprList_ks : ∀ (es : List ConLeche.Expr) (m : Frontend.EMemo),
    KeepsScr (Frontend.internExprList m es)
  | [], _ => pure' _
  | e :: es, m => bind' (internExprGo_ks e m) fun x => bind' (internExprList_ks es x.1) fun _ => pure' _

end L.Arena
