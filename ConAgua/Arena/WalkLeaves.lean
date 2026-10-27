module

public import ConAgua.L.PureEval
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.WalkScope
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `leafGuard`: the fabrication leaf guard (lane `whnf3`)

con-ron's `leafGuard` (`Arena/ExprOps.lean:1251-1256`, con-leche's `leafGuard`): every `fvar` leaf
reachable from the fabrication `fab` is one of the leaves of `base`. Three walks, each a twin
function with a walk-local map:

* `fl_go(h, k, c)`: `fvarLeavesGo` — the reachable `fvar` leaves of `base`, with a `seen` set (memo
  table `FLM`, array 152, `CTL[154]`/`CTL[155]`, key `(h, 0)`, inserted *before* the view, as the
  twin). The twin's accumulator `acc` (consed on the way in) is the word array `LVS` (154), two words
  `(idx, ty)` per leaf in push order, so `acc` is its first `k` entries read from the end; `fl_go`
  returns the new count. A push past the array's capacity aborts.
* `leaf_mem(k, x, y)`: `leafMem acc x y`, scanning `LVS` from entry `k - 1` down (`acc`'s order).
* `lsb_go(h, k, c)`: `leavesSubGo` — the memoized subset test against the first `k` leaves (memo
  table `LSM`, array 153, `CTL[156]`/`CTL[157]`, key `(h, 0)`), the arms short-circuiting as
  `leavesSubArm*`.

`leaf_guard(fab, base)`: the `fvar`-range cutoff on `fab`, then clear `FLM`, `fl_go(base, 0, 4·10⁹)`,
clear `LSM`, `lsb_go(fab, k, 4·10⁹)` (`coreWalkFuel`, the twin's `fuel`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- `fvarLeavesGo`'s `seen` set. -/
abbrev FLM : ArrId := 152
abbrev flSch : MemoSch := ⟨FLM, 154⟩
/-- `leavesSubGo`'s memo. -/
abbrev LSM : ArrId := 153
abbrev lsbSch : MemoSch := ⟨LSM, 156⟩
/-- The leaf list (`fvarLeavesGo`'s accumulator): `(idx, ty)` at words `2 j`, `2 j + 1`. -/
abbrev LVS : ArrId := 154

/-! ## `fl_go`: the leaves of `base` -/

/-- Push the leaf `(x, y)` at entry `k`. -/
def lvsPush (m : Mem) (k x y : Word) : Mem := (m.set64 LVS (k * 2) x).set64 LVS (k * 2 + 1) y

mutual
/-- **The model of `fl_go`**: the new count. -/
def flW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, k, c =>
    if c = 0 then none
    else if derFW m h = 0 then some (k, m)
    else if mfindG flSch m h 0 = [] then none
    else if (mfindG flSch m h 0).headD 0 ≠ 0 then some (k, m)
    else
      match msetG flSch m h 0 0 with
      | none => none
      | some m₁ => flNodeW n m₁ h k (c - 1)

/-- **The model of `fl_node`**. -/
def flNodeW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, k, c =>
    if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if h >>> 28 = 0 then
      if tcnt m BVAR (tierW h) ≤ idxW h then none else some (k, m)
    else if h >>> 28 = 1 then
      if tcnt m FVAR (tierW h) ≤ idxW h then none
      else if m.len64 LVS >>> 1 ≤ k then none
      else flW n (lvsPush m k (tfld m FVAR (tierW h) (idxW h) 0)
          (tfld m FVAR (tierW h) (idxW h) 1))
        (tfld m FVAR (tierW h) (idxW h) 1) (k + 1) c
    else if h >>> 28 = 4 then
      if tcnt m APP (tierW h) ≤ idxW h then none
      else
        match flW n m (tfld m APP (tierW h) (idxW h) 0) k c with
        | none => none
        | some (k₁, m₁) => flW n m₁ (tfld m APP (tierW h) (idxW h) 1) k₁ c
    else if h >>> 28 = 5 then
      if tcnt m LAM (tierW h) ≤ idxW h then none
      else
        match flW n m (tfld m LAM (tierW h) (idxW h) 0) k c with
        | none => none
        | some (k₁, m₁) => flW n m₁ (tfld m LAM (tierW h) (idxW h) 1) k₁ c
    else if h >>> 28 = 6 then
      if tcnt m FORALL (tierW h) ≤ idxW h then none
      else
        match flW n m (tfld m FORALL (tierW h) (idxW h) 0) k c with
        | none => none
        | some (k₁, m₁) => flW n m₁ (tfld m FORALL (tierW h) (idxW h) 1) k₁ c
    else if h >>> 28 = 9 then
      if tcnt m PROJ (tierW h) ≤ idxW h then none
      else flW n m (tfld m PROJ (tierW h) (idxW h) 2) k c
    else if h >>> 28 = 7 then
      if tcnt m LET (tierW h) ≤ idxW h then none
      else
        match flW n m (tfld m LET (tierW h) (idxW h) 0) k c with
        | none => none
        | some (k₁, m₁) =>
          match flW n m₁ (tfld m LET (tierW h) (idxW h) 1) k₁ c with
          | none => none
          | some (k₂, m₂) => flW n m₂ (tfld m LET (tierW h) (idxW h) 2) k₂ c
    else if h >>> 28 = 2 then
      if tcnt m SORT (tierW h) ≤ idxW h then none else some (k, m)
    else if h >>> 28 = 3 then
      if tcnt m CONST (tierW h) ≤ idxW h then none else some (k, m)
    else if h >>> 28 = 8 then
      if tcnt m LIT (tierW h) ≤ idxW h then none else some (k, m)
    else none
end

/-- After `fl_put`: the node. -/
def flPutK (n : Nat) (h k c : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m₁ => flNodeW n m₁ h k c

/-- Two children in a row, the count threaded. -/
def flSeqK (n : Nat) (b c : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (k₁, m₁) => flW n m₁ b k₁ c

/-- Three children in a row. -/
def flSeq3K (n : Nat) (v b c : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (k₁, m₁) => flSeqK n b c (flW n m₁ v k₁ c)

section flArms
variable (n : Nat) (m m₁ : Mem) (h k k₁ c b v : Word)

theorem flPutK_some : flPutK n h k c (some m₁) = flNodeW n m₁ h k c := rfl
theorem flSeqK_some : flSeqK n b c (some (k₁, m₁)) = flW n m₁ b k₁ c := rfl
theorem flSeq3K_some : flSeq3K n v b c (some (k₁, m₁)) = flSeqK n b c (flW n m₁ v k₁ c) := rfl

theorem flW_cut (hc : c ≠ 0) (hf : derFW m h = 0) : flW (n + 1) m h k c = some (k, m) := by
  rw [flW]; simp [hc, hf]

theorem flW_hit (hc : c ≠ 0) (hf : derFW m h ≠ 0) (hr : mfindG flSch m h 0 ≠ [])
    (hh : (mfindG flSch m h 0).headD 0 ≠ 0) : flW (n + 1) m h k c = some (k, m) := by
  rw [flW]; simp only [hc, hf, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem flW_miss (hc : c ≠ 0) (hf : derFW m h ≠ 0) (hr : mfindG flSch m h 0 ≠ [])
    (hh : (mfindG flSch m h 0).headD 0 = 0) :
    flW (n + 1) m h k c = flPutK n h k (c - 1) (msetG flSch m h 0 0) := by
  rw [flW]; simp only [hc, hf, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, flPutK]

theorem flNodeW_bvar (hg : h >>> 28 = 0) (hv : viewOK m h BVAR) : flNodeW (n + 1) m h k c = some (k, m) := by
  rw [flNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem flNodeW_sort (hg : h >>> 28 = 2) (hv : viewOK m h SORT) : flNodeW (n + 1) m h k c = some (k, m) := by
  rw [flNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem flNodeW_const (hg : h >>> 28 = 3) (hv : viewOK m h CONST) : flNodeW (n + 1) m h k c = some (k, m) := by
  rw [flNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem flNodeW_lit (hg : h >>> 28 = 8) (hv : viewOK m h LIT) : flNodeW (n + 1) m h k c = some (k, m) := by
  rw [flNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem flNodeW_fvar (hg : h >>> 28 = 1) (hv : viewOK m h FVAR) (hl : ¬ m.len64 LVS >>> 1 ≤ k) :
    flNodeW (n + 1) m h k c = flW n (lvsPush m k (tfld m FVAR (tierW h) (idxW h) 0)
          (tfld m FVAR (tierW h) (idxW h) 1))
        (tfld m FVAR (tierW h) (idxW h) 1) (k + 1) c := by
  rw [flNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2, hl]

theorem flNodeW_app (hv : viewOK m h APP) (hg : h >>> 28 = 4) :
    flNodeW (n + 1) m h k c = flSeqK n (tfld m APP (tierW h) (idxW h) 1) c
      (flW n m (tfld m APP (tierW h) (idxW h) 0) k c) := by
  rw [flNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, flSeqK]
  simp

theorem flNodeW_lam (hv : viewOK m h LAM) (hg : h >>> 28 = 5) :
    flNodeW (n + 1) m h k c = flSeqK n (tfld m LAM (tierW h) (idxW h) 1) c
      (flW n m (tfld m LAM (tierW h) (idxW h) 0) k c) := by
  rw [flNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, flSeqK]
  simp

theorem flNodeW_forall (hv : viewOK m h FORALL) (hg : h >>> 28 = 6) :
    flNodeW (n + 1) m h k c = flSeqK n (tfld m FORALL (tierW h) (idxW h) 1) c
      (flW n m (tfld m FORALL (tierW h) (idxW h) 0) k c) := by
  rw [flNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, flSeqK]
  simp

theorem flNodeW_proj (hv : viewOK m h PROJ) (hg : h >>> 28 = 9) :
    flNodeW (n + 1) m h k c = flW n m (tfld m PROJ (tierW h) (idxW h) 2) k c := by
  rw [flNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem flNodeW_let (hv : viewOK m h LET) (hg : h >>> 28 = 7) :
    flNodeW (n + 1) m h k c = flSeq3K n (tfld m LET (tierW h) (idxW h) 1)
      (tfld m LET (tierW h) (idxW h) 2) c
      (flW n m (tfld m LET (tierW h) (idxW h) 0) k c) := by
  rw [flNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, flSeq3K, flSeqK]
  split <;> simp_all

end flArms

attribute [arena_grind =] flPutK_some flSeqK_some flSeq3K_some
grind_pattern [arena_grind] flW_cut => flW (n + 1) m h k c
grind_pattern [arena_grind] flW_hit => flW (n + 1) m h k c
grind_pattern [arena_grind] flW_miss => flW (n + 1) m h k c
grind_pattern [arena_grind] flNodeW_bvar => flNodeW (n + 1) m h k c
grind_pattern [arena_grind] flNodeW_sort => flNodeW (n + 1) m h k c
grind_pattern [arena_grind] flNodeW_const => flNodeW (n + 1) m h k c
grind_pattern [arena_grind] flNodeW_lit => flNodeW (n + 1) m h k c
grind_pattern [arena_grind] flNodeW_fvar => flNodeW (n + 1) m h k c
grind_pattern [arena_grind] flNodeW_app => flNodeW (n + 1) m h k c
grind_pattern [arena_grind] flNodeW_lam => flNodeW (n + 1) m h k c
grind_pattern [arena_grind] flNodeW_forall => flNodeW (n + 1) m h k c
grind_pattern [arena_grind] flNodeW_proj => flNodeW (n + 1) m h k c
grind_pattern [arena_grind] flNodeW_let => flNodeW (n + 1) m h k c

/-- con-ron: ConRon/Arena/ExprOps.lean:1051-1078 ConRon.Arena.fvarLeavesGo -/
@[l_impl ConRon.Arena.fvarLeavesGo]
def flGo : FunDecl := lfn (h, k, c) locals (b, x, fd, j, e, u) {
  if c == 0 { abort };
  (b, x) := call der_b(h);
  if x == 0 { return k };
  (fd, j, e) := call fl_find(h, 0);
  if fd != 0 { return k };
  u := call fl_put(h, 0, 0, fd, j);
  x := call fl_node(h, k, c - 1);
  return x
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1051-1078 ConRon.Arena.fvarLeavesGo
con-ron: ConRon/Arena/ExprOps.lean:1080-1087 ConRon.Arena.fvarLeavesGoArmApp
con-ron: ConRon/Arena/ExprOps.lean:1089-1096 ConRon.Arena.fvarLeavesGoArmBind
con-ron: ConRon/Arena/ExprOps.lean:1098-1106 ConRon.Arena.fvarLeavesGoArmLet -/
@[l_impl ConRon.Arena.fvarLeavesGo ConRon.Arena.fvarLeavesGoArmApp ConRon.Arena.fvarLeavesGoArmBind
  ConRon.Arena.fvarLeavesGoArmLet]
def flNode : FunDecl := lfn (h, k, c) locals (g, t, i, f, a, b, x) {
  g := h >> 28;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if BVAR⟨t⟩.count <= i { abort }; return k };
  if g == 1 {
    if FVAR⟨t⟩.count <= i { abort };
    if len(LVS.u64) >> 1 <= k { abort };
    f := FVAR⟨t, i⟩.i;
    a := FVAR⟨t, i⟩.ty;
    LVS.u64[k * 2] := f;
    LVS.u64[k * 2 + 1] := a;
    x := call fl_go(a, k + 1, c);
    return x
  };
  if g == 4 {
    if APP⟨t⟩.count <= i { abort };
    f := APP⟨t, i⟩.f;
    a := APP⟨t, i⟩.a;
    x := call fl_go(f, k, c);
    x := call fl_go(a, x, c);
    return x
  };
  if g == 5 {
    if LAM⟨t⟩.count <= i { abort };
    f := LAM⟨t, i⟩.ty;
    a := LAM⟨t, i⟩.b;
    x := call fl_go(f, k, c);
    x := call fl_go(a, x, c);
    return x
  };
  if g == 6 {
    if FORALL⟨t⟩.count <= i { abort };
    f := FORALL⟨t, i⟩.ty;
    a := FORALL⟨t, i⟩.b;
    x := call fl_go(f, k, c);
    x := call fl_go(a, x, c);
    return x
  };
  if g == 9 {
    if PROJ⟨t⟩.count <= i { abort };
    f := PROJ⟨t, i⟩.e;
    x := call fl_go(f, k, c);
    return x
  };
  if g == 7 {
    if LET⟨t⟩.count <= i { abort };
    f := LET⟨t, i⟩.ty;
    a := LET⟨t, i⟩.v;
    b := LET⟨t, i⟩.b;
    x := call fl_go(f, k, c);
    x := call fl_go(a, x, c);
    x := call fl_go(b, x, c);
    return x
  };
  if g == 2 { if SORT⟨t⟩.count <= i { abort }; return k };
  if g == 3 { if CONST⟨t⟩.count <= i { abort }; return k };
  if g == 8 { if LIT⟨t⟩.count <= i { abort }; return k };
  abort
}

private theorem wl_getElem_rdW {a : Array Word} {x : Word} (h : x.toNat < a.size) :
    a[x.toNat] = rdW a x := (rdW_eq a x _ rfl h).symm

private theorem wl_rd64_rdW (m : Mem) (a : ArrId) (i : Word) : L.rd64 m a i = rdW (m.arr64 a) i := by
  simp [L.rd64, rdW, Array.getD_eq_getD_getElem?]

section flgo
variable (p : Prog) (hpd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "fl_find" = some (memoFindG flSch))
  (hps : p.lookup "fl_put" = some (memoPutG flSch)) (hp : p.lookup "fl_go" = some flGo)
  (hpn : p.lookup "fl_node" = some flNode)

def FlGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h k c : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "fl_go" [h, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ flW n s₀.mem h k c = some (r.headD 0, s'.mem); ⊤⦄

def FlNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (h k c : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "fl_node" [h, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ flNodeW n s₀.mem h k c = some (r.headD 0, s'.mem); ⊤⦄

include hpd hpf hps hp in
theorem flGo_step (n : Nat) (ih : FlNodeSpec p n) : FlGoSpec p (n + 1) := by
  unfold FlNodeSpec at ih
  intro s₀ h k c
  rw [invoke_eq _ hp]
  simp only [callFn, flGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, derB_spec p hpd n,
      memoFindG_spec flSch p _ hpf n, memoPutG_spec flSch p _ hps n, ih] <;>
    -- as `wsGo_step`: the miss path is deep
    finish (instances := 5000) (gen := 12)

set_option maxHeartbeats 1000000 in
include hpn in
theorem flNode_step (n : Nat) (ih : FlGoSpec p n) : FlNodeSpec p (n + 1) := by
  unfold FlGoSpec at ih
  intro s₀ h k c
  rw [invoke_eq _ hpn]
  simp only [callFn, flNode]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld,
    evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64, ih]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
    reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Cond.pval, Expr.pval,
    Bool.and_eq_true, wl_rd64_rdW, Expr.pval_cntE] at *)
  all_goals grind [lang_grind, arena_grind, viewOK, tierW, idxW, lvsPush]

include hpd hpf hps hp hpn in
theorem flGo_spec (n : Nat) : FlGoSpec p n ∧ FlNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ h k c; rw [invoke_eq _ hp]; simp only [callFn, flGo]; vcgen [exec] <;> grind
    · intro s₀ h k c; rw [invoke_eq _ hpn]; simp only [callFn, flNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨flGo_step p hpd hpf hps hp n ih.2, flNode_step p hpn n ih.1⟩

end flgo

/-! ## `leaf_mem(k, x, y)`: membership in the first `k` leaves, newest first -/

/-- **The model of `leaf_mem`'s loop** from the cursor `j` down. -/
def lfmW (a : Array Word) (x y j : Word) : Word :=
  if j = 0 then 0
  else if rdW a ((j - 1) * 2) = x ∧ rdW a ((j - 1) * 2 + 1) = y then 1
  else lfmW a x y (j - 1)
termination_by j.toNat
decreasing_by
  have : j.toNat ≠ 0 := fun e => ‹¬ j = 0› (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega

theorem lfmW_zero (a : Array Word) (x y : Word) : lfmW a x y 0 = 0 := by rw [lfmW]; simp
theorem lfmW_hit (a : Array Word) (x y j : Word) (hj : j ≠ 0)
    (h : rdW a ((j - 1) * 2) = x ∧ rdW a ((j - 1) * 2 + 1) = y) : lfmW a x y j = 1 := by
  rw [lfmW]; simp [hj, h.1, h.2]
theorem lfmW_next (a : Array Word) (x y j : Word) (hj : j ≠ 0)
    (h : ¬ (rdW a ((j - 1) * 2) = x ∧ rdW a ((j - 1) * 2 + 1) = y)) : lfmW a x y j = lfmW a x y (j - 1) := by
  rw [lfmW]; simp only [hj, ↓reduceIte, h]

grind_pattern [arena_grind] lfmW_zero => lfmW a x y 0
grind_pattern [arena_grind] lfmW_hit => lfmW a x y j
grind_pattern [arena_grind] lfmW_next => lfmW a x y j

def lmLoop : Stmt := lblk (k, x, y, j) {
  while j != 0 {
    j := j - 1;
    if LVS.u64[j * 2] == x && LVS.u64[j * 2 + 1] == y { return 1 }
  }
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1144-1151 ConRon.Arena.leafMem -/
@[l_impl ConRon.Arena.leafMem]
def leafMemL : FunDecl := lfn (k, x, y) locals (j) {
  j := k;
  ⟪lmLoop⟫;
  return 0
}

section lm
variable (p : Prog) (hp : p.lookup "leaf_mem" = some leafMemL)

theorem lmLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n lmLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [lfmW (s₀.mem.arr64 LVS) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := lmLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish

theorem lmLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) lmLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [lfmW (s₀.mem.arr64 LVS) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)]; ⊤⦄ :=
  Triple.step_exec (lmLoop_spec p (n + 1) s₀)

include hp in
theorem leafMem_spec (n : Nat) (s₀ : St) (k x y : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "leaf_mem" [k, x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = lfmW (s₀.mem.arr64 LVS) x y k; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, leafMemL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, lmLoop_step_spec p n] <;> finish

end lm

/-! ## `lsb_go`: every leaf of `fab` among the first `k` leaves -/

/-- Record the result `r` at `h` and return it. -/
def lsbSet (m : Mem) (h r : Word) : Option (Word × Mem) :=
  match msetG lsbSch m h 0 r with
  | none => none
  | some m' => some (r, m')

mutual
/-- **The model of `lsb_go`**. -/
def lsbW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, k, c =>
    if c = 0 then none
    else if derFW m h = 0 then some (1, m)
    else if mfindG lsbSch m h 0 = [] then none
    else if (mfindG lsbSch m h 0).headD 0 ≠ 0 then
      some (if rdW (m.arr64 LSM) ((mfindG lsbSch m h 0).tail.headD 0 * 4 + 3) ≠ 0 then 1 else 0, m)
    else
      match lsbNodeW n m h k (c - 1) with
      | none => none
      | some (r, m₁) => lsbSet m₁ h r

/-- **The model of `lsb_node`**. -/
def lsbNodeW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, k, c =>
    if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if h >>> 28 = 0 then
      if tcnt m BVAR (tierW h) ≤ idxW h then none else some (1, m)
    else if h >>> 28 = 1 then
      if tcnt m FVAR (tierW h) ≤ idxW h then none
      else if lfmW (m.arr64 LVS) (tfld m FVAR (tierW h) (idxW h) 0)
          (tfld m FVAR (tierW h) (idxW h) 1) k = 0 then some (0, m)
      else lsbW n m (tfld m FVAR (tierW h) (idxW h) 1) k c
    else if h >>> 28 = 4 then
      if tcnt m APP (tierW h) ≤ idxW h then none
      else
        match lsbW n m (tfld m APP (tierW h) (idxW h) 0) k c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else lsbW n m₁ (tfld m APP (tierW h) (idxW h) 1) k c
    else if h >>> 28 = 5 then
      if tcnt m LAM (tierW h) ≤ idxW h then none
      else
        match lsbW n m (tfld m LAM (tierW h) (idxW h) 0) k c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else lsbW n m₁ (tfld m LAM (tierW h) (idxW h) 1) k c
    else if h >>> 28 = 6 then
      if tcnt m FORALL (tierW h) ≤ idxW h then none
      else
        match lsbW n m (tfld m FORALL (tierW h) (idxW h) 0) k c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else lsbW n m₁ (tfld m FORALL (tierW h) (idxW h) 1) k c
    else if h >>> 28 = 9 then
      if tcnt m PROJ (tierW h) ≤ idxW h then none
      else lsbW n m (tfld m PROJ (tierW h) (idxW h) 2) k c
    else if h >>> 28 = 7 then
      if tcnt m LET (tierW h) ≤ idxW h then none
      else
        match lsbW n m (tfld m LET (tierW h) (idxW h) 0) k c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else
          match lsbW n m₁ (tfld m LET (tierW h) (idxW h) 1) k c with
          | none => none
          | some (y, m₂) =>
            if y = 0 then some (0, m₂) else lsbW n m₂ (tfld m LET (tierW h) (idxW h) 2) k c
    else if h >>> 28 = 2 then
      if tcnt m SORT (tierW h) ≤ idxW h then none else some (1, m)
    else if h >>> 28 = 3 then
      if tcnt m CONST (tierW h) ≤ idxW h then none else some (1, m)
    else if h >>> 28 = 8 then
      if tcnt m LIT (tierW h) ≤ idxW h then none else some (1, m)
    else none
end

def lsbK (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => lsbSet m₁ h r

def lsbAndK (n : Nat) (b k c : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x = 0 then some (0, m₁) else lsbW n m₁ b k c

def lsbLetK (n : Nat) (v b k c : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x = 0 then some (0, m₁) else lsbAndK n b k c (lsbW n m₁ v k c)

section lsArms
variable (n : Nat) (m m₁ : Mem) (h r x k c b v : Word)

theorem lsbK_some : lsbK h (some (r, m₁)) = lsbSet m₁ h r := rfl
theorem lsbAndK_zero : lsbAndK n b k c (some (0, m₁)) = some (0, m₁) := by simp [lsbAndK]
theorem lsbAndK_ne (hx : x ≠ 0) : lsbAndK n b k c (some (x, m₁)) = lsbW n m₁ b k c := by
  simp [lsbAndK, hx]
theorem lsbLetK_zero : lsbLetK n v b k c (some (0, m₁)) = some (0, m₁) := by simp [lsbLetK]
theorem lsbLetK_ne (hx : x ≠ 0) : lsbLetK n v b k c (some (x, m₁)) = lsbAndK n b k c (lsbW n m₁ v k c) := by
  simp [lsbLetK, hx]
theorem lsbSet_eq : lsbSet m h r = wsSetK r (msetG lsbSch m h 0 r) := by
  unfold lsbSet wsSetK; cases msetG lsbSch m h 0 r <;> rfl

theorem lsbW_cut (hc : c ≠ 0) (hf : derFW m h = 0) : lsbW (n + 1) m h k c = some (1, m) := by
  rw [lsbW]; simp [hc, hf]

theorem lsbW_hit (hc : c ≠ 0) (hf : derFW m h ≠ 0) (hr : mfindG lsbSch m h 0 ≠ [])
    (hh : (mfindG lsbSch m h 0).headD 0 ≠ 0) :
    lsbW (n + 1) m h k c =
      some (if rdW (m.arr64 LSM) ((mfindG lsbSch m h 0).tail.headD 0 * 4 + 3) ≠ 0 then 1 else 0, m) := by
  rw [lsbW]; simp only [hc, hf, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem lsbW_miss (hc : c ≠ 0) (hf : derFW m h ≠ 0) (hr : mfindG lsbSch m h 0 ≠ [])
    (hh : (mfindG lsbSch m h 0).headD 0 = 0) :
    lsbW (n + 1) m h k c = lsbK h (lsbNodeW n m h k (c - 1)) := by
  rw [lsbW]; simp only [hc, hf, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, lsbK]

theorem lsbNodeW_bvar (hg : h >>> 28 = 0) (hv : viewOK m h BVAR) : lsbNodeW (n + 1) m h k c = some (1, m) := by
  rw [lsbNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem lsbNodeW_sort (hg : h >>> 28 = 2) (hv : viewOK m h SORT) : lsbNodeW (n + 1) m h k c = some (1, m) := by
  rw [lsbNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem lsbNodeW_const (hg : h >>> 28 = 3) (hv : viewOK m h CONST) : lsbNodeW (n + 1) m h k c = some (1, m) := by
  rw [lsbNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem lsbNodeW_lit (hg : h >>> 28 = 8) (hv : viewOK m h LIT) : lsbNodeW (n + 1) m h k c = some (1, m) := by
  rw [lsbNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem lsbNodeW_fvar_in (hg : h >>> 28 = 1) (hv : viewOK m h FVAR)
    (hl : lfmW (m.arr64 LVS) (tfld m FVAR (tierW h) (idxW h) 0)
          (tfld m FVAR (tierW h) (idxW h) 1) k ≠ 0) :
    lsbNodeW (n + 1) m h k c = lsbW n m (tfld m FVAR (tierW h) (idxW h) 1) k c := by
  rw [lsbNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2, hl]

theorem lsbNodeW_fvar_out (hg : h >>> 28 = 1) (hv : viewOK m h FVAR)
    (hl : lfmW (m.arr64 LVS) (tfld m FVAR (tierW h) (idxW h) 0)
          (tfld m FVAR (tierW h) (idxW h) 1) k = 0) :
    lsbNodeW (n + 1) m h k c = some (0, m) := by
  rw [lsbNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2, hl]

theorem lsbNodeW_app (hv : viewOK m h APP) (hg : h >>> 28 = 4) :
    lsbNodeW (n + 1) m h k c = lsbAndK n (tfld m APP (tierW h) (idxW h) 1) k c
      (lsbW n m (tfld m APP (tierW h) (idxW h) 0) k c) := by
  rw [lsbNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, lsbAndK]
  simp

theorem lsbNodeW_lam (hv : viewOK m h LAM) (hg : h >>> 28 = 5) :
    lsbNodeW (n + 1) m h k c = lsbAndK n (tfld m LAM (tierW h) (idxW h) 1) k c
      (lsbW n m (tfld m LAM (tierW h) (idxW h) 0) k c) := by
  rw [lsbNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, lsbAndK]
  simp

theorem lsbNodeW_forall (hv : viewOK m h FORALL) (hg : h >>> 28 = 6) :
    lsbNodeW (n + 1) m h k c = lsbAndK n (tfld m FORALL (tierW h) (idxW h) 1) k c
      (lsbW n m (tfld m FORALL (tierW h) (idxW h) 0) k c) := by
  rw [lsbNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, lsbAndK]
  simp

theorem lsbNodeW_proj (hv : viewOK m h PROJ) (hg : h >>> 28 = 9) :
    lsbNodeW (n + 1) m h k c = lsbW n m (tfld m PROJ (tierW h) (idxW h) 2) k c := by
  rw [lsbNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem lsbNodeW_let (hv : viewOK m h LET) (hg : h >>> 28 = 7) :
    lsbNodeW (n + 1) m h k c = lsbLetK n (tfld m LET (tierW h) (idxW h) 1)
      (tfld m LET (tierW h) (idxW h) 2) k c
      (lsbW n m (tfld m LET (tierW h) (idxW h) 0) k c) := by
  rw [lsbNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, lsbLetK, lsbAndK]
  split <;> simp_all

end lsArms

attribute [arena_grind =] lsbK_some lsbAndK_zero lsbLetK_zero lsbSet_eq
grind_pattern [arena_grind] lsbAndK_ne => lsbAndK n b k c (some (x, m₁))
grind_pattern [arena_grind] lsbLetK_ne => lsbLetK n v b k c (some (x, m₁))
grind_pattern [arena_grind] lsbW_cut => lsbW (n + 1) m h k c
grind_pattern [arena_grind] lsbW_hit => lsbW (n + 1) m h k c
grind_pattern [arena_grind] lsbW_miss => lsbW (n + 1) m h k c
grind_pattern [arena_grind] lsbNodeW_bvar => lsbNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsbNodeW_sort => lsbNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsbNodeW_const => lsbNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsbNodeW_lit => lsbNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsbNodeW_fvar_in => lsbNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsbNodeW_fvar_out => lsbNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsbNodeW_app => lsbNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsbNodeW_lam => lsbNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsbNodeW_forall => lsbNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsbNodeW_proj => lsbNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsbNodeW_let => lsbNodeW (n + 1) m h k c

/-- con-ron: ConRon/Arena/ExprOps.lean:1155-1183 ConRon.Arena.leavesSubGo -/
@[l_impl ConRon.Arena.leavesSubGo]
def lsbGo : FunDecl := lfn (h, k, c) locals (b, x, fd, j, e, r, u) {
  if c == 0 { abort };
  (b, x) := call der_b(h);
  if x == 0 { return 1 };
  (fd, j, e) := call lsb_find(h, 0);
  if fd != 0 { x := LSM.u64[j * 4 + 3]; if x == 0 { return 0 }; return 1 };
  r := call lsb_node(h, k, c - 1);
  (fd, j, e) := call lsb_find(h, 0);
  u := call lsb_put(h, 0, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1155-1183 ConRon.Arena.leavesSubGo
con-ron: ConRon/Arena/ExprOps.lean:1185-1191 ConRon.Arena.leavesSubArmApp
con-ron: ConRon/Arena/ExprOps.lean:1193-1199 ConRon.Arena.leavesSubArmBind
con-ron: ConRon/Arena/ExprOps.lean:1201-1211 ConRon.Arena.leavesSubArmLet -/
@[l_impl ConRon.Arena.leavesSubGo ConRon.Arena.leavesSubArmApp ConRon.Arena.leavesSubArmBind
  ConRon.Arena.leavesSubArmLet]
def lsbNode : FunDecl := lfn (h, k, c) locals (g, t, i, f, a, b, x) {
  g := h >> 28;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if BVAR⟨t⟩.count <= i { abort }; return 1 };
  if g == 1 {
    if FVAR⟨t⟩.count <= i { abort };
    f := FVAR⟨t, i⟩.i;
    a := FVAR⟨t, i⟩.ty;
    x := call leaf_mem(k, f, a);
    if x == 0 { return 0 };
    x := call lsb_go(a, k, c);
    return x
  };
  if g == 4 {
    if APP⟨t⟩.count <= i { abort };
    f := APP⟨t, i⟩.f;
    a := APP⟨t, i⟩.a;
    x := call lsb_go(f, k, c);
    if x == 0 { return 0 };
    x := call lsb_go(a, k, c);
    return x
  };
  if g == 5 {
    if LAM⟨t⟩.count <= i { abort };
    f := LAM⟨t, i⟩.ty;
    a := LAM⟨t, i⟩.b;
    x := call lsb_go(f, k, c);
    if x == 0 { return 0 };
    x := call lsb_go(a, k, c);
    return x
  };
  if g == 6 {
    if FORALL⟨t⟩.count <= i { abort };
    f := FORALL⟨t, i⟩.ty;
    a := FORALL⟨t, i⟩.b;
    x := call lsb_go(f, k, c);
    if x == 0 { return 0 };
    x := call lsb_go(a, k, c);
    return x
  };
  if g == 9 {
    if PROJ⟨t⟩.count <= i { abort };
    f := PROJ⟨t, i⟩.e;
    x := call lsb_go(f, k, c);
    return x
  };
  if g == 7 {
    if LET⟨t⟩.count <= i { abort };
    f := LET⟨t, i⟩.ty;
    a := LET⟨t, i⟩.v;
    b := LET⟨t, i⟩.b;
    x := call lsb_go(f, k, c);
    if x == 0 { return 0 };
    x := call lsb_go(a, k, c);
    if x == 0 { return 0 };
    x := call lsb_go(b, k, c);
    return x
  };
  if g == 2 { if SORT⟨t⟩.count <= i { abort }; return 1 };
  if g == 3 { if CONST⟨t⟩.count <= i { abort }; return 1 };
  if g == 8 { if LIT⟨t⟩.count <= i { abort }; return 1 };
  abort
}

section lsgo
variable (p : Prog) (hpd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "lsb_find" = some (memoFindG lsbSch))
  (hps : p.lookup "lsb_put" = some (memoPutG lsbSch)) (hp : p.lookup "lsb_go" = some lsbGo)
  (hpn : p.lookup "lsb_node" = some lsbNode) (hpm : p.lookup "leaf_mem" = some leafMemL)

def LsbGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h k c : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lsb_go" [h, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ lsbW n s₀.mem h k c = some (r.headD 0, s'.mem); ⊤⦄

def LsbNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (h k c : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lsb_node" [h, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ lsbNodeW n s₀.mem h k c = some (r.headD 0, s'.mem); ⊤⦄

include hpd hpf hps hp in
theorem lsbGo_step (n : Nat) (ih : LsbNodeSpec p n) : LsbGoSpec p (n + 1) := by
  unfold LsbNodeSpec at ih
  intro s₀ h k c
  rw [invoke_eq _ hp]
  simp only [callFn, lsbGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, derB_spec p hpd n,
      memoFindG_spec lsbSch p _ hpf n, memoPutG_spec lsbSch p _ hps n, ih] <;>
    -- as `wsGo_step`: the miss path is deep
    finish (instances := 5000) (gen := 12)

set_option maxHeartbeats 1000000 in
include hpn hpm in
theorem lsbNode_step (n : Nat) (ih : LsbGoSpec p n) : LsbNodeSpec p (n + 1) := by
  unfold LsbGoSpec at ih
  intro s₀ h k c
  rw [invoke_eq _ hpn]
  simp only [callFn, lsbNode]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld,
    evalE_cnt, tcntM, evalE_tierE, evalE_idxE, leafMem_spec p hpm n, ih]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
    reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Cond.pval, Expr.pval,
    Bool.and_eq_true, wl_rd64_rdW, Expr.pval_cntE] at *)
  all_goals grind [lang_grind, arena_grind, viewOK, tierW, idxW]

include hpd hpf hps hp hpn hpm in
theorem lsbGo_spec (n : Nat) : LsbGoSpec p n ∧ LsbNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ h k c; rw [invoke_eq _ hp]; simp only [callFn, lsbGo]; vcgen [exec] <;> grind
    · intro s₀ h k c; rw [invoke_eq _ hpn]; simp only [callFn, lsbNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨lsbGo_step p hpd hpf hps hp n ih.2, lsbNode_step p hpn hpm n ih.1⟩

end lsgo

/-! ## `leaf_guard(fab, base)` -/

/-- After `fl_go`: clear the subset memo and walk `fab`. -/
def lgK (n : Nat) (fab : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (k, m₁) =>
    if rdW (m₁.arr64 CTL) 156 + 2 = 0 then none else lsbW n (mclearG lsbSch m₁) fab k 4000000000

/-- **The model of `leaf_guard`.** -/
def lgW (n : Nat) (m : Mem) (fab base : Word) : Option (Word × Mem) :=
  if derFW m fab = 0 then some (1, m)
  else if rdW (m.arr64 CTL) 154 + 2 = 0 then none
  else lgK n fab (flW n (mclearG flSch m) base 0 4000000000)

theorem lgW_cut (n : Nat) (m : Mem) (fab base : Word) (h : derFW m fab = 0) :
    lgW n m fab base = some (1, m) := by simp [lgW, h]
theorem lgW_go (n : Nat) (m : Mem) (fab base : Word) (h : derFW m fab ≠ 0)
    (h0 : rdW (m.arr64 CTL) 154 + 2 ≠ 0) :
    lgW n m fab base = lgK n fab (flW n (mclearG flSch m) base 0 4000000000) := by simp [lgW, h, h0]
theorem lgK_some (n : Nat) (fab k : Word) (m₁ : Mem) (h0 : rdW (m₁.arr64 CTL) 156 + 2 ≠ 0) :
    lgK n fab (some (k, m₁)) = lsbW n (mclearG lsbSch m₁) fab k 4000000000 := by simp [lgK, h0]

grind_pattern [arena_grind] lgW_cut => lgW n m fab base
grind_pattern [arena_grind] lgW_go => lgW n m fab base
grind_pattern [arena_grind] lgK_some => lgK n fab (some (k, m₁))

/-- con-ron: ConRon/Arena/ExprOps.lean:1245-1256 ConRon.Arena.leafGuard
con-ron: ConRon/Arena/ExprOps.lean:1138-1142 ConRon.Arena.fvarLeavesFast -/
@[l_impl ConRon.Arena.leafGuard ConRon.Arena.fvarLeavesFast]
def leafGuardL : FunDecl := lfn (fab, base) locals (b, x, k, r, u) {
  (b, x) := call der_b(fab);
  if x == 0 { return 1 };
  u := call fl_clear();
  k := call fl_go(base, 0, 4000000000);
  u := call lsb_clear();
  r := call lsb_go(fab, k, 4000000000);
  return r
}

/-- What the specs need of the program. -/
structure LgProg (p : Prog) : Prop where
  derb : p.lookup "der_b" = some derB
  flf : p.lookup "fl_find" = some (memoFindG flSch)
  flp : p.lookup "fl_put" = some (memoPutG flSch)
  flc : p.lookup "fl_clear" = some (memoClearG flSch)
  flgo : p.lookup "fl_go" = some flGo
  flnode : p.lookup "fl_node" = some flNode
  lsf : p.lookup "lsb_find" = some (memoFindG lsbSch)
  lsp : p.lookup "lsb_put" = some (memoPutG lsbSch)
  lsc : p.lookup "lsb_clear" = some (memoClearG lsbSch)
  lsgo : p.lookup "lsb_go" = some lsbGo
  lsnode : p.lookup "lsb_node" = some lsbNode
  lm : p.lookup "leaf_mem" = some leafMemL
  lg : p.lookup "leaf_guard" = some leafGuardL

theorem leafGuard_spec (p : Prog) (hp : LgProg p) (n : Nat) (s₀ : St) (fab base : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "leaf_guard" [fab, base]
    ⦃fun r s' => LocEq s' s₀ ∧ lgW n s₀.mem fab base = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ihf := (flGo_spec p hp.derb hp.flf hp.flp hp.flgo hp.flnode n).1
  have ihs := (lsbGo_spec p hp.derb hp.lsf hp.lsp hp.lsgo hp.lsnode hp.lm n).1
  unfold FlGoSpec at ihf
  unfold LsbGoSpec at ihs
  rw [invoke_eq _ hp.lg]
  simp only [callFn, leafGuardL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, derB_spec p hp.derb n,
      memoClearG_spec flSch p _ hp.flc n, memoClearG_spec lsbSch p _ hp.lsc n, ihf, ihs] <;>
    finish (instances := 5000) (gen := 12)

end L.Arena
