module

public import ConAgua.Arena.DeclCanonRules
public import ConAgua.Arena.DeclCanonConst
import ConAgua.Arena.DeclCanonSpec2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclRec
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.DeclArmsCanon

@[expose] public section

/-!
# `ci_canon_defn`, `ci_canon_rec`, `ci_canon_eq`, `canon_eq_list` (lane `decls3`, helper `decls3-canon`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A twin conditional whose condition is an `AM Bool`, with the state changing along the way. -/
theorem andThen_st {A B : AM Bool} {a a1 : AState} {r r1 : Word} {b1 : Bool} {Q : AState → Prop}
    (hA : A.run a = .ok (b1, a1)) (hr1 : r1 = if b1 then 1 else 0)
    (hB : r1 ≠ 0 → ∃ b2 a2, B.run a1 = .ok (b2, a2) ∧ r = (if b2 then 1 else 0) ∧ Q a2)
    (h0 : r1 = 0 → r = 0 ∧ Q a1) :
    ∃ b a', (do let x ← A; if x = true then B else pure false : AM Bool).run a = .ok (b, a') ∧
      r = (if b then 1 else 0) ∧ Q a' := by
  cases b1
  · obtain ⟨hr, hQ⟩ := h0 (by simpa using hr1)
    refine ⟨false, a1, ?_, by simp [hr], hQ⟩
    simp [StateT.run_bind, hA, exc_ok_bind']; rfl
  · obtain ⟨b2, a2, hb2, hr, hQ⟩ := hB (by simp [hr1])
    refine ⟨b2, a2, ?_, hr, hQ⟩
    simp [StateT.run_bind, hA, exc_ok_bind', hb2]

/-- The state-and-pool facts every comparison carries. -/
def CQ (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem) (a' : AState) : Prop :=
  StageR vis fe m' a' ∧ IWGrow m m' ∧ PoolSmall m' ∧ LitInj a'


/-! ## `ci_canon_defn` -/

mutual
/-- **The model of `ci_canon_defn(p, q)`**. -/
def cdW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, p, q => cdK0 k m p q (if hintEqB (erRdT m) (p + 6) (q + 6) then 1 else 0)

/-- After `hint_eq`. -/
def cdK0 (k : Nat) (m : Mem) (p q e : Word) : Option (Word × Mem) :=
  if e = 0 then some (0, m) else cdK1 k p q (cvceW k m (p + 1) (q + 1))

/-- After `cv_canon_eq`. -/
def cdK1 (k : Nat) (p q : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (e, m1) => if e = 0 then some (0, m1) else cdK2 k p q (ctxW k m1 (p + 1) (q + 1))

/-- After `canon_ctx`. -/
def cdK2 (k : Nat) (p q : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (rc, m2) =>
    ceW k m2 (rc.headD 0) (rc.tail.headD 0) (rc.tail.tail.headD 0) (rc.tail.tail.tail.headD 0)
      (rc.tail.tail.tail.tail.headD 0) (rc.tail.tail.tail.tail.tail.headD 0) 4000000000
      (rdW (m2.arr64 EREC) (p + 5)) (rdW (m2.arr64 EREC) (q + 5))
end

section arms
variable (k : Nat) (m m1 m2 : Mem) (p q e : Word) (rc : List Word)
theorem cdW_succ : cdW (k + 1) m p q =
    cdK0 k m p q (if hintEqB (erRdT m) (p + 6) (q + 6) then 1 else 0) := by rw [cdW]
theorem cdK0_def : cdK0 k m p q e =
    (if e = 0 then some (0, m) else cdK1 k p q (cvceW k m (p + 1) (q + 1))) := by rw [cdK0]
theorem cdK1_some : cdK1 k p q (some (e, m1)) =
    (if e = 0 then some (0, m1) else cdK2 k p q (ctxW k m1 (p + 1) (q + 1))) := by rw [cdK1]
theorem cdK2_some : cdK2 k p q (some (rc, m2)) =
    ceW k m2 (rc.headD 0) (rc.tail.headD 0) (rc.tail.tail.headD 0) (rc.tail.tail.tail.headD 0)
      (rc.tail.tail.tail.tail.headD 0) (rc.tail.tail.tail.tail.tail.headD 0) 4000000000
      (rdW (m2.arr64 EREC) (p + 5)) (rdW (m2.arr64 EREC) (q + 5)) := by rw [cdK2]
end arms

grind_pattern [ind_grind] cdW_succ => cdW (k + 1) m p q
grind_pattern [ind_grind] cdK0_def => cdK0 k m p q e
grind_pattern [ind_grind] cdK1_some => cdK1 k p q (some (e, m1))
grind_pattern [ind_grind] cdK2_some => cdK2 k p q (some (rc, m2))

theorem ciCanonDefn_spec (pr : Prog) (hp : CanonProg pr) (n : Nat) (s₀ : St) (p q : Word) :
    ⦃fun s => s = s₀⦄ invoke pr (exec pr n) "ci_canon_defn" [p, q]
    ⦃fun x s' => LocEq s' s₀ ∧ cdW n s₀.mem p q = some (x.headD 0, s'.mem); ⊤⦄ := by
  sorry

theorem ciD_defn {a : Array Word} {p : Nat} {cv : IConstantVal}
    {v : EIdx} {hi : ConLeche.ReducibilityHint} (h : decCI (aread a) p = some (.defnInfo cv v hi)) :
    decCV (aread a) (p + 1) = some cv ∧ hd? (aread a) (p + 5) = some v ∧ decHint (aread a) (p + 6) = some hi := by
  sorry

theorem cdW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} (k : Nat)
    {m m' : Mem} {p q x : Word} {cv cv' : IConstantVal} {v v' : EIdx}
    {hi hi' : ConLeche.ReducibilityHint}
    (h : cdW k m p q = some (x, m')) (hS : StageR vis fe m a)
    (hp : decCI (erecP m) p.toNat = some (.defnInfo cv v hi))
    (hq : decCI (erecP m) q.toNat = some (.defnInfo cv' v' hi'))
    (hP : PoolSmall m) (hL : LitInj a) :
    ∃ (b : Bool) (a' : AState),
      (IConstantInfo.canonEq (.defnInfo cv v hi) (.defnInfo cv' v' hi')).run a = .ok (b, a') ∧
      x = (if b then 1 else 0) ∧ CQ dn vis fe m m' a' := by
  sorry

/-! ## `ci_canon_rec` -/

mutual
/-- **The model of `ci_canon_rec(p, q)`**. -/
def cwW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, p, q =>
    if rdW (m.arr64 EREC) (p + 5) ≠ rdW (m.arr64 EREC) (q + 5) ∨
        rdW (m.arr64 EREC) (p + 6) ≠ rdW (m.arr64 EREC) (q + 6) then some (0, m)
    else cwK1 k p q (cvceW k m (p + 1) (q + 1))

/-- After `cv_canon_eq`. -/
def cwK1 (k : Nat) (p q : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (e, m1) => if e = 0 then some (0, m1) else cwK2 k p q (ctxW k m1 (p + 1) (q + 1))

/-- After `canon_ctx`. -/
def cwK2 (k : Nat) (p q : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (rc, m2) =>
    cnCrW k m2 (rc.headD 0) (rc.tail.headD 0) (rc.tail.tail.headD 0) (rc.tail.tail.tail.headD 0)
      (rc.tail.tail.tail.tail.headD 0) (rc.tail.tail.tail.tail.tail.headD 0) 4000000000
      (rdW (m2.arr64 EREC) (p + 7)) (rdW (m2.arr64 EREC) (p + 8))
      (rdW (m2.arr64 EREC) (q + 7)) (rdW (m2.arr64 EREC) (q + 8))
end

section arms
variable (k : Nat) (m m1 m2 : Mem) (p q e : Word) (rc : List Word)
theorem cwW_succ : cwW (k + 1) m p q =
    (if rdW (m.arr64 EREC) (p + 5) ≠ rdW (m.arr64 EREC) (q + 5) ∨
        rdW (m.arr64 EREC) (p + 6) ≠ rdW (m.arr64 EREC) (q + 6) then some (0, m)
    else cwK1 k p q (cvceW k m (p + 1) (q + 1))) := by rw [cwW]
theorem cwK1_some : cwK1 k p q (some (e, m1)) =
    (if e = 0 then some (0, m1) else cwK2 k p q (ctxW k m1 (p + 1) (q + 1))) := by rw [cwK1]
theorem cwK2_some : cwK2 k p q (some (rc, m2)) =
    cnCrW k m2 (rc.headD 0) (rc.tail.headD 0) (rc.tail.tail.headD 0) (rc.tail.tail.tail.headD 0)
      (rc.tail.tail.tail.tail.headD 0) (rc.tail.tail.tail.tail.tail.headD 0) 4000000000
      (rdW (m2.arr64 EREC) (p + 7)) (rdW (m2.arr64 EREC) (p + 8))
      (rdW (m2.arr64 EREC) (q + 7)) (rdW (m2.arr64 EREC) (q + 8)) := by rw [cwK2]
end arms

grind_pattern [ind_grind] cwW_succ => cwW (k + 1) m p q
grind_pattern [ind_grind] cwK1_some => cwK1 k p q (some (e, m1))
grind_pattern [ind_grind] cwK2_some => cwK2 k p q (some (rc, m2))

theorem ciCanonRec_spec (pr : Prog) (hp : CanonProg pr) (n : Nat) (s₀ : St) (p q : Word) :
    ⦃fun s => s = s₀⦄ invoke pr (exec pr n) "ci_canon_rec" [p, q]
    ⦃fun x s' => LocEq s' s₀ ∧ cwW n s₀.mem p q = some (x.headD 0, s'.mem); ⊤⦄ := by
  sorry

theorem ciD_rec {a : Array Word} {p : Nat} {cv : IConstantVal}
    {mi rp : Nat} {isK : Bool} {rules : List IRecRule}
    (h : decCI (aread a) p = some (.recInfo cv mi rp isK rules)) :
    decCV (aread a) (p + 1) = some cv ∧ nat? (aread a) (p + 5) = some mi ∧ nat? (aread a) (p + 6) = some rp ∧
    bool? (aread a) (p + 9) = some isK ∧
    ∃ o c, nat? (aread a) (p + 7) = some o ∧ nat? (aread a) (p + 8) = some c ∧ decRules (aread a) o c = some rules := by
  sorry

theorem cwW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} (k : Nat)
    {m m' : Mem} {p q x : Word} {cv cv' : IConstantVal} {mi mi' rp rp' : Nat}
    {isK isK' : Bool} {rules rules' : List IRecRule}
    (h : cwW k m p q = some (x, m')) (hS : StageR vis fe m a)
    (hp : decCI (erecP m) p.toNat = some (.recInfo cv mi rp isK rules))
    (hq : decCI (erecP m) q.toNat = some (.recInfo cv' mi' rp' isK' rules'))
    (hP : PoolSmall m) (hL : LitInj a) :
    ∃ (b : Bool) (a' : AState),
      (IConstantInfo.canonEq (.recInfo cv mi rp isK rules) (.recInfo cv' mi' rp' isK' rules')).run a =
        .ok (b, a') ∧ x = (if b then 1 else 0) ∧ CQ dn vis fe m m' a' := by
  sorry

/-! ## `ci_canon_eq` -/

/-- **The model of `ci_canon_eq(p, q)`**. -/
def cieW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, p, q =>
    if rdW (m.arr64 EREC) p ≠ rdW (m.arr64 EREC) q then some (0, m)
    else if 5 < rdW (m.arr64 EREC) p then none
    else if rdW (m.arr64 EREC) p = 1 then cdW k m p q
    else if rdW (m.arr64 EREC) p = 4 ∧ (rdW (m.arr64 EREC) (p + 5) ≠ rdW (m.arr64 EREC) (q + 5) ∨
        rdW (m.arr64 EREC) (p + 6) ≠ rdW (m.arr64 EREC) (q + 6)) then some (0, m)
    else if rdW (m.arr64 EREC) p = 5 then cwW k m p q
    else cvceW k m (p + 1) (q + 1)

theorem cieW_succ (k : Nat) (m : Mem) (p q : Word) : cieW (k + 1) m p q =
    (if rdW (m.arr64 EREC) p ≠ rdW (m.arr64 EREC) q then some (0, m)
    else if 5 < rdW (m.arr64 EREC) p then none
    else if rdW (m.arr64 EREC) p = 1 then cdW k m p q
    else if rdW (m.arr64 EREC) p = 4 ∧ (rdW (m.arr64 EREC) (p + 5) ≠ rdW (m.arr64 EREC) (q + 5) ∨
        rdW (m.arr64 EREC) (p + 6) ≠ rdW (m.arr64 EREC) (q + 6)) then some (0, m)
    else if rdW (m.arr64 EREC) p = 5 then cwW k m p q
    else cvceW k m (p + 1) (q + 1)) := rfl

grind_pattern [ind_grind] cieW_succ => cieW (k + 1) m p q

theorem ciCanonEq_spec (pr : Prog) (hp : CanonProg pr) (n : Nat) (s₀ : St) (p q : Word) :
    ⦃fun s => s = s₀⦄ invoke pr (exec pr n) "ci_canon_eq" [p, q]
    ⦃fun x s' => LocEq s' s₀ ∧ cieW n s₀.mem p q = some (x.headD 0, s'.mem); ⊤⦄ := by
  sorry

theorem cieW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {a : AState} (k : Nat) {m m' : Mem} {p q x : Word} {c c' : IConstantInfo}
    (h : cieW k m p q = some (x, m')) (hS : StageR vis fe m a)
    (hp : decCI (erecP m) p.toNat = some c) (hq : decCI (erecP m) q.toNat = some c')
    (hP : PoolSmall m) (hL : LitInj a) :
    ∃ (b : Bool) (a' : AState), (c.canonEq c').run a = .ok (b, a') ∧ x = (if b then 1 else 0) ∧
      CQ dn vis fe m m' a' := by
  sorry

/-- **`ci_canon_eq` refines `IConstantInfo.canonEq`.** -/
@[refines ConRon.Arena.IConstantInfo.canonEq]
theorem ciCanonEq_refines (pr : Prog) (hp : CanonProg pr) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (p q : Word) (c c' : IConstantInfo) :
    RefAM pr "ci_canon_eq" [p, q]
      (fun m a => StageR vis fe m a ∧ decCI (erecP m) p.toNat = some c ∧
        decCI (erecP m) q.toNat = some c' ∧ PoolSmall m ∧ LitInj a)
      (c.canonEq c') (CPostL dn vis fe decW0B) := by
  sorry

/-! ## `canon_eq_list` -/

mutual
/-- **The model of `canon_eq_list(o, l, o', l')`**. -/
def celW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, o1, l1, o2, l2 =>
    if l1 = 0 ∧ l2 = 0 then some (1, m)
    else if l1 = 0 ∨ l2 = 0 then some (0, m)
    else celK1 k o1 l1 o2 l2 (cieW k m (rdW (m.arr64 IW) o1) (rdW (m.arr64 IW) o2))

/-- After `ci_canon_eq`. -/
def celK1 (k : Nat) (o1 l1 o2 l2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (e, m1) => if e = 0 then some (0, m1) else celW k m1 (o1 + 1) (l1 - 1) (o2 + 1) (l2 - 1)
end

section arms
variable (k : Nat) (m m1 : Mem) (o1 l1 o2 l2 e : Word)
theorem celW_succ : celW (k + 1) m o1 l1 o2 l2 =
    (if l1 = 0 ∧ l2 = 0 then some (1, m)
    else if l1 = 0 ∨ l2 = 0 then some (0, m)
    else celK1 k o1 l1 o2 l2 (cieW k m (rdW (m.arr64 IW) o1) (rdW (m.arr64 IW) o2))) := by rw [celW]
theorem celK1_some : celK1 k o1 l1 o2 l2 (some (e, m1)) =
    (if e = 0 then some (0, m1) else celW k m1 (o1 + 1) (l1 - 1) (o2 + 1) (l2 - 1)) := by
  rw [celK1]
end arms

grind_pattern [ind_grind] celW_succ => celW (k + 1) m o1 l1 o2 l2
grind_pattern [ind_grind] celK1_some => celK1 k o1 l1 o2 l2 (some (e, m1))

theorem canonEqListL_spec (pr : Prog) (hp : CanonProg pr) (n : Nat) :
    ∀ (s₀ : St) (o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke pr (exec pr n) "canon_eq_list" [o1, l1, o2, l2]
    ⦃fun x s' => LocEq s' s₀ ∧ celW n s₀.mem o1 l1 o2 l2 = some (x.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o1 l1 o2 l2
    rw [invoke_eq _ (hp.get "canon_eq_list")]; simp only [callFn, canonEqListL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o1 l1 o2 l2
    rw [invoke_eq _ (hp.get "canon_eq_list")]
    simp only [callFn, canonEqListL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        ciCanonEq_spec pr hp n, ih] <;>
      finish (gen := 20) [rdW_eq]


theorem decPL_zero {α : Type} (m : Mem) (f : Nat → Option α) (o : Nat) : decPL m f o 0 = some [] := by
  simp [decPL]

/-- A pointer slice stays decoded when the pool grows (below its top) and the record decoder
only gains. -/
theorem decPL_grow {α : Type} {m m' : Mem} {f f' : Nat → Option α} (hg : IWGrow m m')
    (hf : ∀ q x, f q = some x → f' q = some x) :
    ∀ (c o : Nat) (xs : List α), o + c ≤ iwTop m → decPL m f o c = some xs →
    decPL m' f' o c = some xs := by
  intro c
  induction c with
  | zero => intro o xs _ h; simpa [decPL] using h
  | succ c ih =>
    intro o xs hb h
    rw [decPL_succ] at h ⊢
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
    obtain ⟨v, hv, x, hx, ys, hys, rfl⟩ := h
    refine ⟨v, ?_, x, hf _ _ hx, ys, ih (o + 1) ys (by omega) hys, rfl⟩
    simp only [iwN, nat?, iwA, aread_apply, Option.map_eq_some_iff] at hv ⊢
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨w, by rw [hg.iwGet o (by omega)]; exact hw, rfl⟩

theorem celW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (o1 l1 o2 l2 x : Word) (xs ys : List IConstantInfo),
    celW k m o1 l1 o2 l2 = some (x, m') → StageR vis fe m a →
    decPL m (fun q => decCI (erecP m) q) o1.toNat l1.toNat = some xs →
    decPL m (fun q => decCI (erecP m) q) o2.toNat l2.toNat = some ys →
    o1.toNat + l1.toNat ≤ iwTop m → o2.toNat + l2.toNat ≤ iwTop m → PoolSmall m → LitInj a →
    ∃ (b : Bool) (a' : AState), (ConRon.Arena.canonEqList xs ys).run a = .ok (b, a') ∧
      x = (if b then 1 else 0) ∧ CQ dn vis fe m m' a' := by
  sorry

/-- **`canon_eq_list` refines `canonEqList`.** The records are `EREC` pointers in two `IW` slices
(decoded below the record pool's top, as the other record statements). -/
@[refines ConRon.Arena.canonEqList]
theorem canonEqList_refines (pr : Prog) (hp : CanonProg pr) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (o1 l1 o2 l2 : Word) (xs ys : List IConstantInfo) :
    RefAM pr "canon_eq_list" [o1, l1, o2, l2]
      (fun m a => StageR vis fe m a ∧
        decPL m (fun q => decCI (erecP m) q) o1.toNat l1.toNat = some xs ∧
        decPL m (fun q => decCI (erecP m) q) o2.toNat l2.toNat = some ys ∧
        o1.toNat + l1.toNat ≤ iwTop m ∧ o2.toNat + l2.toNat ≤ iwTop m ∧ PoolSmall m ∧ LitInj a)
      (ConRon.Arena.canonEqList xs ys) (CPostL dn vis fe decW0B) := by
  sorry

end L.Ind
