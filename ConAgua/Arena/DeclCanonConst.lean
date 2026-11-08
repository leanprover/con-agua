module

public import ConAgua.Arena.DeclCanonNames
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclRec
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPartsSpec.MemberNames
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.DeclCvg
import all ConAgua.Arena.DeclArmsCanon

@[expose] public section

/-!
# Constants: `cv_lps`, the renaming context, `cv_canon_eq` (lane `decls3`, helper `decls3-canon`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem decRL_two {k : IdxKind} {m : Mem} {r : List Word} {xs : List (Idx k)}
    (_h2 : r = [r.headD 0, r.tail.headD 0])
    (hd : decHL m (r.headD 0).toNat (r.tail.headD 0).toNat = some xs)
    (hb : (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m) :
    decRL (fun m => decHL m) 0 m r xs := by
  simpa only [decRL, getD0, cnGetD1] using (⟨hd, hb⟩ : _ ∧ _)

theorem allocW_mem' {m m1 : Mem} {q k : Word} (h : allocW m k = some (q, m1)) :
    m1 = allocMem m k := by
  simp only [allocW] at h
  have h1 : ¬ m.len64 IW < rdW (m.arr64 CTL) 200 := fun h1 => by simp [h1] at h
  have h2 : ¬ m.len64 IW - rdW (m.arr64 CTL) 200 < k := fun h2 => by simp [h1, h2] at h
  simp only [h1, h2, ite_false, Option.some.injEq, Prod.mk.injEq] at h
  exact h.2.symm

theorem erCopyW_size (n : Nat) : ∀ (m m' : Mem) (d s l : Word), erCopyW n m d s l = some m' →
    ∀ b, (m'.arr64 b).size = (m.arr64 b).size := by
  induction n with
  | zero => intro m m' d s l h; simp [erCopyW] at h
  | succ n ih =>
    intro m m' d s l h b
    by_cases hl : l = 0
    · rw [erCopyW_nil n m d s l hl] at h; cases h; rfl
    · rw [erCopyW_step n m d s l hl] at h
      rw [ih _ _ _ _ _ h b]
      exact size_set64 _ _ _ _ _

theorem erToIwW_size {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : erToIwW n m o l = some (r, m')) : ∀ b, (m'.arr64 b).size = (m.arr64 b).size := by
  simp only [erToIwW] at h
  rcases hal : allocW m l with _ | ⟨q, m1⟩ <;> simp only [hal, reduceCtorEq] at h
  rcases hcp : erCopyW (n - 1) m1 q o l with _ | m2 <;> simp only [hcp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨-, rfl⟩ := h
  intro b
  have hm1 : m1 = allocMem m l := allocW_mem' hal
  rw [erCopyW_size _ _ _ _ _ _ hcp b, hm1]
  exact (allocMem_frame m l).size b

/-- `cv_lps` under the stage relation: the level parameters as a fresh `IW` slice. -/
theorem cvLpsW_ok {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : L.Arena.cvLpsW n m q = some (r, m')) (hS : StageR vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ decRL (fun m => decHL m) 0 m' r cv.levelParams ∧
      (∀ b, (m'.arr64 b).size = (m.arr64 b).size) := by
  sorry

/-! ## `canon_ctx` -/

mutual
/-- **The model of `canon_ctx(cp, cq)`**. -/
def ctxW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, cp, cq => ctxK1 k cp cq (cnW k m (rdW (m.arr64 EREC) (cp + 2)))

/-- After `canon_names`. -/
def ctxK1 (k : Nat) (cp cq : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m1) => ctxK2 k cq rc (L.Arena.cvLpsW k m1 cp)

/-- After the first `cv_lps`. -/
def ctxK2 (k : Nat) (cq : Word) (rc : List Word) : Option (List Word × Mem) →
    Option (List Word × Mem)
  | none => none
  | some (rp, m2) => ctxK3 rc rp (L.Arena.cvLpsW k m2 cq)

/-- After the second. -/
def ctxK3 (rc rp : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rq, m3) =>
    some ([rp.headD 0, rp.tail.headD 0, rq.headD 0, rq.tail.headD 0, rc.headD 0, rc.tail.headD 0], m3)
end

section arms
variable (k : Nat) (m m1 m2 m3 : Mem) (cp cq : Word) (rc rp rq : List Word)
theorem ctxW_succ : ctxW (k + 1) m cp cq = ctxK1 k cp cq (cnW k m (rdW (m.arr64 EREC) (cp + 2))) := by
  rw [ctxW]
theorem ctxK1_some : ctxK1 k cp cq (some (rc, m1)) = ctxK2 k cq rc (L.Arena.cvLpsW k m1 cp) := by
  rw [ctxK1]
theorem ctxK2_some : ctxK2 k cq rc (some (rp, m2)) = ctxK3 rc rp (L.Arena.cvLpsW k m2 cq) := by
  rw [ctxK2]
theorem ctxK3_some : ctxK3 rc rp (some (rq, m3)) =
    some ([rp.headD 0, rp.tail.headD 0, rq.headD 0, rq.tail.headD 0, rc.headD 0, rc.tail.headD 0],
      m3) := by
  rw [ctxK3]
end arms

grind_pattern [ind_grind] ctxW_succ => ctxW (k + 1) m cp cq
grind_pattern [ind_grind] ctxK1_some => ctxK1 k cp cq (some (rc, m1))
grind_pattern [ind_grind] ctxK2_some => ctxK2 k cq rc (some (rp, m2))
grind_pattern [ind_grind] ctxK3_some => ctxK3 rc rp (some (rq, m3))

theorem canonCtx_spec (p : Prog) (hp : CanonProg p) (n : Nat) (s₀ : St) (cp cq : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_ctx" [cp, cq]
    ⦃fun r s' => LocEq s' s₀ ∧ ctxW n s₀.mem cp cq = some (r, s'.mem); ⊤⦄ := by
  sorry

theorem ctxW_ok {vis : Word} {fe : IFEnv} {a : AState} (k : Nat)
    {m m' : Mem} {cp cq : Word} {r : List Word} {cv cv' : IConstantVal}
    (h : ctxW k m cp cq = some (r, m')) (hS : StageR vis fe m a)
    (hcv : decCV (erecP m) cp.toNat = some cv) (hcv' : decCV (erecP m) cq.toNat = some cv')
    (hP : PoolSmall m) (hL : LitInj a) :
    ∃ (cs : List NIdx) (a' : AState) (po pl qo ql co cl : Word),
      r = [po, pl, qo, ql, co, cl] ∧
      (ConRon.Arena.canonNames cv.levelParams.length).run a = .ok (cs, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ PoolSmall m' ∧ LitInj a' ∧
      CtxR m' po pl qo ql co cl cv.levelParams cv'.levelParams cs := by
  sorry

/-! ## `cv_canon_eq` -/

mutual
/-- **The model of `cv_canon_eq(q, r)`**. -/
def cvceW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, q, r =>
    if rdW (m.arr64 EREC) q ≠ rdW (m.arr64 EREC) r ∨
        rdW (m.arr64 EREC) (q + 2) ≠ rdW (m.arr64 EREC) (r + 2) then some (0, m)
    else cvcK1 k q r (ctxW k m q r)

/-- After `canon_ctx`. -/
def cvcK1 (k : Nat) (q r : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (rc, m1) =>
    ceW k m1 (rc.headD 0) (rc.tail.headD 0) (rc.tail.tail.headD 0) (rc.tail.tail.tail.headD 0)
      (rc.tail.tail.tail.tail.headD 0) (rc.tail.tail.tail.tail.tail.headD 0) 4000000000
      (rdW (m1.arr64 EREC) (q + 3)) (rdW (m1.arr64 EREC) (r + 3))
end

section arms
variable (k : Nat) (m m1 : Mem) (q r : Word) (rc : List Word)
theorem cvceW_succ : cvceW (k + 1) m q r =
    (if rdW (m.arr64 EREC) q ≠ rdW (m.arr64 EREC) r ∨
        rdW (m.arr64 EREC) (q + 2) ≠ rdW (m.arr64 EREC) (r + 2) then some (0, m)
    else cvcK1 k q r (ctxW k m q r)) := by rw [cvceW]
theorem cvcK1_some : cvcK1 k q r (some (rc, m1)) =
    ceW k m1 (rc.headD 0) (rc.tail.headD 0) (rc.tail.tail.headD 0) (rc.tail.tail.tail.headD 0)
      (rc.tail.tail.tail.tail.headD 0) (rc.tail.tail.tail.tail.tail.headD 0) 4000000000
      (rdW (m1.arr64 EREC) (q + 3)) (rdW (m1.arr64 EREC) (r + 3)) := by rw [cvcK1]
end arms

grind_pattern [ind_grind] cvceW_succ => cvceW (k + 1) m q r
grind_pattern [ind_grind] cvcK1_some => cvcK1 k q r (some (rc, m1))

theorem cvCanonEq_spec (p : Prog) (hp : CanonProg p) (n : Nat) (s₀ : St) (q r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cv_canon_eq" [q, r]
    ⦃fun x s' => LocEq s' s₀ ∧ cvceW n s₀.mem q r = some (x.headD 0, s'.mem); ⊤⦄ := by
  sorry

/-- The three words of a constant value that the comparison reads. -/
theorem cvWords {m : Mem} {q : Word} {cv : IConstantVal} (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (h : decCV (erA m) q.toNat = some cv) :
    ∃ wn w2 wt : Word, rdW (m.arr64 EREC) q = wn ∧ rdW (m.arr64 EREC) (q + 2) = w2 ∧
      rdW (m.arr64 EREC) (q + 3) = wt ∧ wn.toNat < 2 ^ 32 ∧ wt.toNat < 2 ^ 32 ∧
      cv.name = decI wn ∧ cv.type = decI wt ∧ w2.toNat = cv.levelParams.length := by
  sorry

set_option maxRecDepth 100000 in
theorem cvceW_ok {vis : Word} {fe : IFEnv} {a : AState} (k : Nat)
    {m m' : Mem} {q r : Word} {x : Word} {cv cv' : IConstantVal}
    (h : cvceW k m q r = some (x, m')) (hS : StageR vis fe m a)
    (hcv : decCV (erecP m) q.toNat = some cv) (hcv' : decCV (erecP m) r.toNat = some cv')
    (hP : PoolSmall m) (hL : LitInj a) :
    ∃ (b : Bool) (a' : AState), (cv.canonEq cv').run a = .ok (b, a') ∧ x = (if b then 1 else 0) ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ PoolSmall m' ∧ LitInj a' := by
  sorry

/-- **`cv_canon_eq` refines `IConstantVal.canonEq`.** -/
@[refines ConRon.Arena.IConstantVal.canonEq]
theorem cvCanonEq_refines (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (q r : Word) (cv cv' : IConstantVal) :
    RefAM p "cv_canon_eq" [q, r]
      (fun m a => StageR vis fe m a ∧ decCV (erecP m) q.toNat = some cv ∧
        decCV (erecP m) r.toNat = some cv' ∧ PoolSmall m ∧ LitInj a)
      (cv.canonEq cv') (CPostL dn vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hcv, hcv', hP, hL⟩
  refine triple_post (cvCanonEq_spec p hp n s₀ q r) ?_
  rintro x s' ⟨hl, hx⟩
  obtain ⟨b, a', hb, hrb, hS', hg, hP', hL'⟩ := cvceW_ok n hx hS hcv hcv' hP hL
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hb
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres]
  exact ⟨⟨⟨hS', hg, decW0B_of' hrb⟩, hP'⟩, hL'⟩

end L.Ind
