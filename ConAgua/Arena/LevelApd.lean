module

public import ConAgua.Arena.LevelHeapRel
import ConAgua.Census.Attr
public import ConLeche.Kernel.Level
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
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
def lvMemG : FunDecl := lfn (o, k, w) locals (x) {
  if k == 0 { return 0 };
  if A.u64[o] == w { return 1 };
  x := call lv_mem(o + 1, k - 1, w);
  return x
}

mutual
/-- **The model of `lv_apd`.** -/
def apdW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, l, o, k =>
    if lvG m l = 0 then some 1
    else if lvG m l = 4 then memW A n m o k (lvA m l)
    else if lvG m l = 1 then apdW n m (lvA m l) o k
    else apdK n m (lvB m l) o k (apdW n m (lvA m l) o k)

/-- After the first child of a `max`/`imax`. -/
def apdK (n : Nat) (m : Mem) (b o k : Word) : Option Word → Option Word
  | none => none
  | some x => if x = 0 then some 0 else apdW n m b o k
end

section arms
variable (n : Nat) (m : Mem) (l o k b x : Word)
theorem apdW_zero (h : lvG m l = 0) : apdW A (n + 1) m l o k = some 1 := by rw [apdW]; simp [h]
theorem apdW_param (_h0 : lvG m l ≠ 0) (h : lvG m l = 4) :
    apdW A (n + 1) m l o k = memW A n m o k (lvA m l) := by rw [apdW]; simp [h]
theorem apdW_succ (_h0 : lvG m l ≠ 0) (_h4 : lvG m l ≠ 4) (h : lvG m l = 1) :
    apdW A (n + 1) m l o k = apdW A n m (lvA m l) o k := by rw [apdW]; simp [h]
theorem apdW_bin (h0 : lvG m l ≠ 0) (h4 : lvG m l ≠ 4) (h1 : lvG m l ≠ 1) :
    apdW A (n + 1) m l o k = apdK A n m (lvB m l) o k (apdW A n m (lvA m l) o k) := by
  rw [apdW]; simp [h0, h4, h1]
theorem apK_zero : apdK A n m b o k (some 0) = some 0 := by rw [apdK]; simp
theorem apK_ne (hx : x ≠ 0) : apdK A n m b o k (some x) = apdW A n m b o k := by rw [apdK]; simp [hx]
end arms

/-- con-leche: ConLeche/Kernel/Level.lean:44-49 ConLeche.Level.allParamsDefined -/
@[l_impl ConLeche.Level.allParamsDefined]
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
grind_pattern [level_grind] apdW_zero => apdW A (n + 1) m l o k
grind_pattern [level_grind] apdW_param => apdW A (n + 1) m l o k
grind_pattern [level_grind] apdW_succ => apdW A (n + 1) m l o k
grind_pattern [level_grind] apdW_bin => apdW A (n + 1) m l o k
grind_pattern [level_grind] apK_zero => apdK A n m b o k (some 0)
grind_pattern [level_grind] apK_ne => apdK A n m b o k (some x)

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

include hpm in
theorem lvApd_spec (hpn : p.lookup "lv_node" = some lvNode) (hp : p.lookup "lv_apd" = some lvApd)
    (n : Nat) : ∀ (s₀ : St) (l o k : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_apd" [l, o, k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ apdW A n s₀.mem l o k = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ l o k; rw [invoke_eq _ hp]; simp only [callFn, lvApd]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ l o k
    rw [invoke_eq _ hp]
    simp only [callFn, lvApd]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hpn n,
        lvMem_spec A p hpm n, ih] <;>
      finish (gen := 20)

end specs

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
      rw [apdW_zero A n m l o k (lv_fields hv).1] at h; simp at h; simp [Level.allParamsDefined, ← h]
    | param hv hn =>
      rw [apdW_param A n m l o k (by simp [lvG, hv]) (lv_fields hv).1, (lv_fields hv).2.1] at h
      rw [memW_ok hN n _ _ _ _ _ _ _ hps hn h]; simp [Level.allParamsDefined]
    | succ hv ha =>
      rw [apdW_succ A n m l o k (by simp [lvG, hv]) (by simp [lvG, hv]) (lv_fields hv).1,
        (lv_fields hv).2.1] at h
      rw [ih _ _ _ _ _ _ _ ha hps h]; rfl
    | @max _ a b L₁ L₂ hv ha hb | @imax _ a b L₁ L₂ hv ha hb =>
      rw [apdW_bin A n m l o k (by simp [lvG, hv]) (by simp [lvG, hv]) (by simp [lvG, hv]),
        (lv_fields hv).2.1, (lv_fields hv).2.2] at h
      cases e : apdW A n m a o k with
      | none => rw [e] at h; simp [apdK] at h
      | some y =>
        rw [e] at h
        have hy := ih _ _ _ _ _ _ _ ha hps e
        by_cases hy0 : y = 0
        · subst hy0; rw [apK_zero] at h; simp at h
          have : Level.allParamsDefined ps L₁ = false := by revert hy; cases Level.allParamsDefined ps L₁ <;> simp
          simp [Level.allParamsDefined, this, ← h]
        · rw [apK_ne (hx := hy0)] at h
          have : Level.allParamsDefined ps L₁ = true := by revert hy; cases Level.allParamsDefined ps L₁ <;> simp_all
          rw [ih _ _ _ _ _ _ _ hb hps h]; simp [Level.allParamsDefined, this]

end L.Arena
