module

meta import ConAgua.L.Semantics
public import ConAgua.Arena.LevelHeapRel
import ConAgua.Census.Attr
public import ConLeche.Kernel.Level
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `allParamsDefined`: are all of a level's parameters in a list of names?

con-leche's `Level.allParamsDefined params l` (Rust `kernel/level.rs:226`), reads only. The
parameter list is a slice `A[o .. o + k)` of name handle words in a word array `A` that the caller
chooses (the declaration's level parameters; the L code is a Lean function of `A`, as the memo
library's is of its schema, and its specs are proved once for a variable `A`). Names compare by
their words (`NameRel`'s injectivity).

* `lv_mem(o, k, w)`: `w ∈ A[o .. o + k)`, `1`/`0`, recursive in the list;
* `lv_apd(l, o, k)`: `allParamsDefined`, `1`/`0`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

section apd
variable (A : ArrId)

/-- **The model of `lv_mem`.** -/
def memW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, o, k, w =>
    if k = 0 then some 0
    else if rdW (m.arr64 A) o = w then some 1
    else memW n m (o + 1) (k - 1) w

theorem memW_nil (n : Nat) (m : Mem) (o k w : Word) (hk : k = 0) :
    memW A (n + 1) m o k w = some 0 := by simp [memW, hk]
theorem memW_hit (n : Nat) (m : Mem) (o k w : Word) (hk : k ≠ 0) (hw : rdW (m.arr64 A) o = w) :
    memW A (n + 1) m o k w = some 1 := by simp [memW, hk, hw]
theorem memW_next (n : Nat) (m : Mem) (o k w : Word) (hk : k ≠ 0) (hw : rdW (m.arr64 A) o ≠ w) :
    memW A (n + 1) m o k w = memW A n m (o + 1) (k - 1) w := by simp [memW, hk, hw]

/-- con-leche: ConLeche/Kernel/Level.lean:44-49 ConLeche.Level.allParamsDefined -/
@[no_expose] def lvMemG : FunDecl := lfn (o, k, w) locals (x) {
  if k == 0 { return 0 };
  if A.u64[o] == w { return 1 };
  x := call lv_mem(o + 1, k - 1, w);
  return x
}

/-- con-leche: ConLeche/Kernel/Level.lean:44-49 ConLeche.Level.allParamsDefined -/
@[no_expose, l_impl ConLeche.Level.allParamsDefined]
def lvApd : FunDecl := lfn (l, o, k) locals (g, a, b, x) {
  (g, a, b) := call lv_node(l);
  if g == 0 { return 1 };
  if g == 4 { x := call lv_mem(o, k, a); return x };
  x := call lv_apd(a, o, k);
  if g == 1 { return x };
  if x == 0 { return 0 };
  x := call lv_apd(b, o, k);
  return x
}

end apd

grind_pattern [level_grind] memW_nil => memW A (n + 1) m o k w
grind_pattern [level_grind] memW_hit => memW A (n + 1) m o k w
grind_pattern [level_grind] memW_next => memW A (n + 1) m o k w

section specs
variable (A : ArrId) (p : Prog) (hpm : p.lookup "lv_mem" = some (lvMemG A))

include hpm in
theorem lvMem_spec (n : Nat) : ∀ (s₀ : St) (o k w : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_mem" [o, k, w]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ memW A n s₀.mem o k w = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ o k w; rw [invoke_eq _ hpm]; simp only [callFn, lvMemG]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o k w
    rw [invoke_eq _ hpm]
    simp only [callFn, lvMemG]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)

end specs

/-- **`lv_apd` is its model `apdW`** (generated). -/
l_model lvApd_spec (A : ArrId) (p : Prog) (hpm : p.lookup "lv_mem" = some (lvMemG A))
  (hpn : p.lookup "lv_node" = some lvNode) (hp : p.lookup "lv_apd" = some lvApd)
  fns [hp ↦ apdW ro]
  specs [lvNode_spec p hpn n, lvMem_spec A p hpm n]
  grind [level_grind] fold [lvG, lvA, lvB] gen 20 noguard ["lv_node"]

/-! ## The refinement -/

open ConLeche

/-- The words `A[o .. o + k)` are the names `ps`. -/
inductive NmsR (N : Word → Name → Prop) (m : Mem) (A : ArrId) : Word → Word → List Name → Prop
  | nil {o : Word} : NmsR N m A o 0 []
  | cons {o k : Word} {x : Name} {xs : List Name} : k ≠ 0 → N (rdW (m.arr64 A) o) x →
      NmsR N m A (o + 1) (k - 1) xs → NmsR N m A o k (x :: xs)

variable {N : Word → Name → Prop} {A : ArrId}

theorem memW_ok (hN : NameRel N) (n : Nat) : ∀ (m : Mem) (o k w x : Word) (ps : List Name)
    (nm : Name), NmsR N m A o k ps → N w nm → memW A n m o k w = some x →
    x = if ps.contains nm then 1 else 0 := by
  induction n with
  | zero => intro m o k w x ps nm _ _ h; simp [memW] at h
  | succ n ih =>
    intro m o k w x ps nm hps hw h
    cases hps with
    | nil => rw [memW_nil A n m o 0 w rfl] at h; simp at h; simp [h]
    | @cons _ _ y ys hk hy hys =>
      by_cases e : rdW (m.arr64 A) o = w
      · rw [memW_hit A n m o _ w hk e] at h; simp at h
        rw [e] at hy
        rw [hN.fn _ _ _ hy hw] at *; simp [← h]
      · rw [memW_next A n m o _ w hk e] at h
        rw [ih _ _ _ _ _ _ _ hys hw h]
        have hne : y ≠ nm := fun h' => e (hN.inj _ _ _ hy (h' ▸ hw))
        simp [Ne.symm hne]

/-- **`lv_apd` is `allParamsDefined`.** -/
@[refines ConLeche.Level.allParamsDefined]
theorem apdW_ok (hN : NameRel N) (n : Nat) : ∀ (m : Mem) (l o k x : Word) (L : Level)
    (ps : List Name), LvR N m l L → NmsR N m A o k ps → apdW A n m l o k = some x →
    x = if Level.allParamsDefined ps L then 1 else 0 := by
  induction n with
  | zero => intro m l o k x L ps _ _ h; simp [apdW] at h
  | succ n ih =>
    intro m l o k x L ps hl hps h
    cases hl with
    | zero hv =>
      rw [apdW.arm1 A n m l o k (lv_fields hv).1] at h; simp at h; simp [Level.allParamsDefined, ← h]
    | param hv hn =>
      rw [apdW.arm2 A n m l o k (by simp [lvG, hv]) (lv_fields hv).1, (lv_fields hv).2.1] at h
      rw [memW_ok hN n _ _ _ _ _ _ _ hps hn h]; simp [Level.allParamsDefined]
    | succ hv ha =>
      rw [apdW.arm3 A n m l o k (by simp [lvG, hv]) (by simp [lvG, hv]), (lv_fields hv).1,
        (lv_fields hv).2.1] at h
      cases e : apdW A n m _ o k with
      | none => rw [e, apdW.k_lv_apd.none] at h; cases h
      | some y =>
        rw [e, apdW.k_lv_apd.arm1 (hc1 := rfl)] at h; cases h
        rw [ih _ _ _ _ _ _ _ ha hps e]; rfl
    | @max _ a b L₁ L₂ hv ha hb | @imax _ a b L₁ L₂ hv ha hb =>
      rw [apdW.arm3 A n m l o k (by simp [lvG, hv]) (by simp [lvG, hv]), (lv_fields hv).2.1,
        (lv_fields hv).2.2] at h
      cases e : apdW A n m a o k with
      | none => rw [e, apdW.k_lv_apd.none] at h; cases h
      | some y =>
        rw [e] at h
        have hy := ih _ _ _ _ _ _ _ ha hps e
        by_cases hy0 : y = 0
        · subst hy0; rw [apdW.k_lv_apd.arm2 (hc1 := by simp [lvG, hv]) (hc2 := rfl)] at h; simp at h
          have : Level.allParamsDefined ps L₁ = false := by revert hy; cases Level.allParamsDefined ps L₁ <;> simp
          simp [Level.allParamsDefined, this, ← h]
        · rw [apdW.k_lv_apd.arm3 (hc1 := by simp [lvG, hv]) (hc2 := hy0)] at h
          have : Level.allParamsDefined ps L₁ = true := by revert hy; cases Level.allParamsDefined ps L₁ <;> simp_all
          rw [ih _ _ _ _ _ _ _ hb hps h]; simp [Level.allParamsDefined, this]

end L.Arena
