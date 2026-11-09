module

public import ConAgua.Arena.FormerSortRef
public import ConAgua.Arena.LevelZero
import ConAgua.Arena.LevelArena
import ConAgua.Arena.CoreLevels
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.LevelZero

@[expose] public section

/-!
# `lv_never` under `CoreS` (`(zeronessOf l).isNever`), the leaves of `former_never_zero_at`
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **`lv_never`'s model**: `lv_zero` lifted, the heap top put back. -/
l_model lvNeverW_spec (p : Prog) (hf : p.lookup "lv_never" = some lvNever)
  fns [hf ↦ lvNeverW] specs [callW_spec p n "lv_zero"] grind [arena_grind] fold [tierW, idxW]

/-- **`lv_never` is `(zeronessOf l).isNever` under `CoreS`**: the level heap above its top and the
top are all it writes (the top put back). -/
theorem lvNever_core {p : Prog} (hpn : p.lookup "lv_node" = some lvNode)
    (hpp : p.lookup "lh_push" = some lhPush) (hpz : p.lookup "lv_zero" = some lvZero)
    {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {u : Word} (hu : HW u) {L : Level}
    (hd : denoteL a.store.ls (decI u) = some L) {w : Word}
    (h : lvNeverW p n m u = some (w, m')) :
    w = (if (Level.zeronessOf L).isNever then 1 else 0) ∧ CoreS dn m' a vis fe M eb ∧ StackKept m m' := by
  rcases n with _ | n
  · simp [lvNeverW] at h
  rw [lvNeverW.arm1] at h
  rcases hc : callW p n "lv_zero" [u] m with _ | ⟨r, m₁⟩
  · rw [hc, lvNeverW.k_lv_zero.none] at h; cases h
  rw [hc, lvNeverW.k_lv_zero.arm1] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s', hs', -, hz⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lvZero_spec p hpn hpp hpz n ⟨m, Locals.init []⟩ u) hc
  rw [hs'] at hz
  have hl := denoteL_lvR hS.arena.base (decI u) L hd
  rw [decI_word_self u hu] at hl
  obtain ⟨he, hZ⟩ := zeroW_ok n _ _ _ _ _ hl hz
  have hf : MemFrame [LH] [192] m (m₁.set64 CTL 192 (rdW (m.arr64 CTL) 192)) :=
    he.memFrame.trans ((MemFrame.setCtl m₁ 192 _).mono (by simp) (by simp))
  obtain ⟨hS', hK⟩ := hS.frame hf (by simp [LH]) (by simp)
  refine ⟨?_, hS', hK⟩
  rcases hZ with ⟨hx, hpw⟩ | ⟨hx, ps, hpw, -⟩
  · rw [hx, hpw]; simp [PropWhen.isNever]
  · rw [hx, hpw]; simp [PropWhen.isNever]

end L.Arena
