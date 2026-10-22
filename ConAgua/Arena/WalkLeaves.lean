module

public import ConAgua.Arena.WalkScope
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

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
* `ls_go(h, k, c)`: `leavesSubGo` — the memoized subset test against the first `k` leaves (memo
  table `LSM`, array 153, `CTL[156]`/`CTL[157]`, key `(h, 0)`), the arms short-circuiting as
  `leavesSubArm*`.

`leaf_guard(fab, base)`: the `fvar`-range cutoff on `fab`, then clear `FLM`, `fl_go(base, 0, 4·10⁹)`,
clear `LSM`, `ls_go(fab, k, 4·10⁹)` (`coreWalkFuel`, the twin's `fuel`).
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
abbrev lsSch : MemoSch := ⟨LSM, 156⟩
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
      if rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h then none else some (k, m)
    else if h >>> 28 = 1 then
      if rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h then none
      else if m.len64 LVS >>> 1 ≤ k then none
      else flW n (lvsPush m k (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2))
          (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1)))
        (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1)) (k + 1) c
    else if h >>> 28 = 4 then
      if rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h then none
      else
        match flW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) k c with
        | none => none
        | some (k₁, m₁) => flW n m₁ (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) k₁ c
    else if h >>> 28 = 5 then
      if rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h then none
      else
        match flW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) k c with
        | none => none
        | some (k₁, m₁) => flW n m₁ (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) k₁ c
    else if h >>> 28 = 6 then
      if rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h then none
      else
        match flW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) k c with
        | none => none
        | some (k₁, m₁) => flW n m₁ (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) k₁ c
    else if h >>> 28 = 9 then
      if rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h then none
      else flW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) k c
    else if h >>> 28 = 7 then
      if rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h then none
      else
        match flW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) k c with
        | none => none
        | some (k₁, m₁) =>
          match flW n m₁ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) k₁ c with
          | none => none
          | some (k₂, m₂) => flW n m₂ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) k₂ c
    else if h >>> 28 = 2 then
      if rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h then none else some (k, m)
    else if h >>> 28 = 3 then
      if rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h then none else some (k, m)
    else if h >>> 28 = 8 then
      if rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h then none else some (k, m)
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

theorem flNodeW_bvar (hg : h >>> 28 = 0) (hv : viewOK m h 22) : flNodeW (n + 1) m h k c = some (k, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [flNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem flNodeW_sort (hg : h >>> 28 = 2) (hv : viewOK m h 16) : flNodeW (n + 1) m h k c = some (k, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [flNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem flNodeW_const (hg : h >>> 28 = 3) (hv : viewOK m h 18) : flNodeW (n + 1) m h k c = some (k, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [flNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem flNodeW_lit (hg : h >>> 28 = 8) (hv : viewOK m h 2) : flNodeW (n + 1) m h k c = some (k, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [flNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem flNodeW_fvar (hg : h >>> 28 = 1) (hv : viewOK m h 26) (hl : ¬ m.len64 LVS >>> 1 ≤ k) :
    flNodeW (n + 1) m h k c = flW n (lvsPush m k (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2))
          (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1)))
        (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1)) (k + 1) c := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [flNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2, hl]

theorem flNodeW_app (hv : viewOK m h 4) (hg : h >>> 28 = 4) :
    flNodeW (n + 1) m h k c = flSeqK n (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) c
      (flW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) k c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [flNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, flSeqK]
  simp

theorem flNodeW_lam (hv : viewOK m h 28) (hg : h >>> 28 = 5) :
    flNodeW (n + 1) m h k c = flSeqK n (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) c
      (flW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) k c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [flNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, flSeqK]
  simp

theorem flNodeW_forall (hv : viewOK m h 30) (hg : h >>> 28 = 6) :
    flNodeW (n + 1) m h k c = flSeqK n (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) c
      (flW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) k c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [flNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, flSeqK]
  simp

theorem flNodeW_proj (hv : viewOK m h 32) (hg : h >>> 28 = 9) :
    flNodeW (n + 1) m h k c = flW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) k c := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [flNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem flNodeW_let (hv : viewOK m h 20) (hg : h >>> 28 = 7) :
    flNodeW (n + 1) m h k c = flSeq3K n (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1))
      (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) c
      (flW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) k c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [flNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, flSeq3K, flSeqK]
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

@[l_impl ConRon.Arena.fvarLeavesGo ConRon.Arena.fvarLeavesGoArmApp ConRon.Arena.fvarLeavesGoArmBind
  ConRon.Arena.fvarLeavesGoArmLet]
def flNode : FunDecl := lfn (h, k, c) locals (g, t, i, f, a, b, x) {
  g := h >> 28;
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if CTL.u64[22 + t] <= i { abort }; return k };
  if g == 1 {
    if CTL.u64[26 + t] <= i { abort };
    if len(LVS.u64) >> 1 <= k { abort };
    f := FVREC.u64[i * 4 + t * 2];
    a := FVREC.u64[i * 4 + t * 2 + 1];
    LVS.u64[k * 2] := f;
    LVS.u64[k * 2 + 1] := a;
    x := call fl_go(a, k + 1, c);
    return x
  };
  if g == 4 {
    if CTL.u64[4 + t] <= i { abort };
    f := AREC.u64[i * 4 + t * 2];
    a := AREC.u64[i * 4 + t * 2 + 1];
    x := call fl_go(f, k, c);
    x := call fl_go(a, x, c);
    return x
  };
  if g == 5 {
    if CTL.u64[28 + t] <= i { abort };
    f := LAREC.u64[i * 4 + t * 2];
    a := LAREC.u64[i * 4 + t * 2 + 1];
    x := call fl_go(f, k, c);
    x := call fl_go(a, x, c);
    return x
  };
  if g == 6 {
    if CTL.u64[30 + t] <= i { abort };
    f := FAREC.u64[i * 4 + t * 2];
    a := FAREC.u64[i * 4 + t * 2 + 1];
    x := call fl_go(f, k, c);
    x := call fl_go(a, x, c);
    return x
  };
  if g == 9 {
    if CTL.u64[32 + t] <= i { abort };
    f := PJREC.u64[i * 6 + t * 3 + 2];
    x := call fl_go(f, k, c);
    return x
  };
  if g == 7 {
    if CTL.u64[20 + t] <= i { abort };
    f := LEREC.u64[i * 6 + t * 3];
    a := LEREC.u64[i * 6 + t * 3 + 1];
    b := LEREC.u64[i * 6 + t * 3 + 2];
    x := call fl_go(f, k, c);
    x := call fl_go(a, x, c);
    x := call fl_go(b, x, c);
    return x
  };
  if g == 2 { if CTL.u64[16 + t] <= i { abort }; return k };
  if g == 3 { if CTL.u64[18 + t] <= i { abort }; return k };
  if g == 8 { if CTL.u64[2 + t] <= i { abort }; return k };
  abort
}

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
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
    finish [viewOK, tierW, idxW, lvsPush]

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
def lmW (a : Array Word) (x y j : Word) : Word :=
  if j = 0 then 0
  else if rdW a ((j - 1) * 2) = x ∧ rdW a ((j - 1) * 2 + 1) = y then 1
  else lmW a x y (j - 1)
termination_by j.toNat
decreasing_by
  have : j.toNat ≠ 0 := fun e => ‹¬ j = 0› (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega

theorem lmW_zero (a : Array Word) (x y : Word) : lmW a x y 0 = 0 := by rw [lmW]; simp
theorem lmW_hit (a : Array Word) (x y j : Word) (hj : j ≠ 0)
    (h : rdW a ((j - 1) * 2) = x ∧ rdW a ((j - 1) * 2 + 1) = y) : lmW a x y j = 1 := by
  rw [lmW]; simp [hj, h.1, h.2]
theorem lmW_next (a : Array Word) (x y j : Word) (hj : j ≠ 0)
    (h : ¬ (rdW a ((j - 1) * 2) = x ∧ rdW a ((j - 1) * 2 + 1) = y)) : lmW a x y j = lmW a x y (j - 1) := by
  rw [lmW]; simp only [hj, ↓reduceIte, h]

grind_pattern [arena_grind] lmW_zero => lmW a x y 0
grind_pattern [arena_grind] lmW_hit => lmW a x y j
grind_pattern [arena_grind] lmW_next => lmW a x y j

def lmLoop : Stmt := lblk (k, x, y, j) {
  while j != 0 {
    j := j - 1;
    if LVS.u64[j * 2] == x && LVS.u64[j * 2 + 1] == y { return 1 }
  }
}

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
      r.retOr [0] = [lmW (s₀.mem.arr64 LVS) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)]; ⊤⦄ := by
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
      r.retOr [0] = [lmW (s₀.mem.arr64 LVS) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)]; ⊤⦄ :=
  Triple.step_exec (lmLoop_spec p (n + 1) s₀)

include hp in
theorem leafMem_spec (n : Nat) (s₀ : St) (k x y : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "leaf_mem" [k, x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = lmW (s₀.mem.arr64 LVS) x y k; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, leafMemL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, lmLoop_step_spec p n] <;> finish

end lm

/-! ## `ls_go`: every leaf of `fab` among the first `k` leaves -/

/-- Record the result `r` at `h` and return it. -/
def lsSet (m : Mem) (h r : Word) : Option (Word × Mem) :=
  match msetG lsSch m h 0 r with
  | none => none
  | some m' => some (r, m')

mutual
/-- **The model of `ls_go`**. -/
def lsW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, k, c =>
    if c = 0 then none
    else if derFW m h = 0 then some (1, m)
    else if mfindG lsSch m h 0 = [] then none
    else if (mfindG lsSch m h 0).headD 0 ≠ 0 then
      some (if rdW (m.arr64 LSM) ((mfindG lsSch m h 0).tail.headD 0 * 4 + 3) ≠ 0 then 1 else 0, m)
    else
      match lsNodeW n m h k (c - 1) with
      | none => none
      | some (r, m₁) => lsSet m₁ h r

/-- **The model of `ls_node`**. -/
def lsNodeW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, k, c =>
    if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if h >>> 28 = 0 then
      if rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h then none else some (1, m)
    else if h >>> 28 = 1 then
      if rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h then none
      else if lmW (m.arr64 LVS) (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2))
          (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1)) k = 0 then some (0, m)
      else lsW n m (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1)) k c
    else if h >>> 28 = 4 then
      if rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h then none
      else
        match lsW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) k c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else lsW n m₁ (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) k c
    else if h >>> 28 = 5 then
      if rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h then none
      else
        match lsW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) k c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else lsW n m₁ (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) k c
    else if h >>> 28 = 6 then
      if rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h then none
      else
        match lsW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) k c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else lsW n m₁ (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) k c
    else if h >>> 28 = 9 then
      if rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h then none
      else lsW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) k c
    else if h >>> 28 = 7 then
      if rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h then none
      else
        match lsW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) k c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else
          match lsW n m₁ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) k c with
          | none => none
          | some (y, m₂) =>
            if y = 0 then some (0, m₂) else lsW n m₂ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) k c
    else if h >>> 28 = 2 then
      if rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h then none else some (1, m)
    else if h >>> 28 = 3 then
      if rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h then none else some (1, m)
    else if h >>> 28 = 8 then
      if rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h then none else some (1, m)
    else none
end

def lsK (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => lsSet m₁ h r

def lsAndK (n : Nat) (b k c : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x = 0 then some (0, m₁) else lsW n m₁ b k c

def lsLetK (n : Nat) (v b k c : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x = 0 then some (0, m₁) else lsAndK n b k c (lsW n m₁ v k c)

section lsArms
variable (n : Nat) (m m₁ : Mem) (h r x k c b v : Word)

theorem lsK_some : lsK h (some (r, m₁)) = lsSet m₁ h r := rfl
theorem lsAndK_zero : lsAndK n b k c (some (0, m₁)) = some (0, m₁) := by simp [lsAndK]
theorem lsAndK_ne (hx : x ≠ 0) : lsAndK n b k c (some (x, m₁)) = lsW n m₁ b k c := by
  simp [lsAndK, hx]
theorem lsLetK_zero : lsLetK n v b k c (some (0, m₁)) = some (0, m₁) := by simp [lsLetK]
theorem lsLetK_ne (hx : x ≠ 0) : lsLetK n v b k c (some (x, m₁)) = lsAndK n b k c (lsW n m₁ v k c) := by
  simp [lsLetK, hx]
theorem lsSet_eq : lsSet m h r = wsSetK r (msetG lsSch m h 0 r) := by
  unfold lsSet wsSetK; cases msetG lsSch m h 0 r <;> rfl

theorem lsW_cut (hc : c ≠ 0) (hf : derFW m h = 0) : lsW (n + 1) m h k c = some (1, m) := by
  rw [lsW]; simp [hc, hf]

theorem lsW_hit (hc : c ≠ 0) (hf : derFW m h ≠ 0) (hr : mfindG lsSch m h 0 ≠ [])
    (hh : (mfindG lsSch m h 0).headD 0 ≠ 0) :
    lsW (n + 1) m h k c =
      some (if rdW (m.arr64 LSM) ((mfindG lsSch m h 0).tail.headD 0 * 4 + 3) ≠ 0 then 1 else 0, m) := by
  rw [lsW]; simp only [hc, hf, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem lsW_miss (hc : c ≠ 0) (hf : derFW m h ≠ 0) (hr : mfindG lsSch m h 0 ≠ [])
    (hh : (mfindG lsSch m h 0).headD 0 = 0) :
    lsW (n + 1) m h k c = lsK h (lsNodeW n m h k (c - 1)) := by
  rw [lsW]; simp only [hc, hf, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, lsK]

theorem lsNodeW_bvar (hg : h >>> 28 = 0) (hv : viewOK m h 22) : lsNodeW (n + 1) m h k c = some (1, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [lsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem lsNodeW_sort (hg : h >>> 28 = 2) (hv : viewOK m h 16) : lsNodeW (n + 1) m h k c = some (1, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [lsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem lsNodeW_const (hg : h >>> 28 = 3) (hv : viewOK m h 18) : lsNodeW (n + 1) m h k c = some (1, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [lsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem lsNodeW_lit (hg : h >>> 28 = 8) (hv : viewOK m h 2) : lsNodeW (n + 1) m h k c = some (1, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [lsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem lsNodeW_fvar_in (hg : h >>> 28 = 1) (hv : viewOK m h 26)
    (hl : lmW (m.arr64 LVS) (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2))
          (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1)) k ≠ 0) :
    lsNodeW (n + 1) m h k c = lsW n m (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1)) k c := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [lsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2, hl]

theorem lsNodeW_fvar_out (hg : h >>> 28 = 1) (hv : viewOK m h 26)
    (hl : lmW (m.arr64 LVS) (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2))
          (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1)) k = 0) :
    lsNodeW (n + 1) m h k c = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [lsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2, hl]

theorem lsNodeW_app (hv : viewOK m h 4) (hg : h >>> 28 = 4) :
    lsNodeW (n + 1) m h k c = lsAndK n (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) k c
      (lsW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) k c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [lsNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, lsAndK]
  simp

theorem lsNodeW_lam (hv : viewOK m h 28) (hg : h >>> 28 = 5) :
    lsNodeW (n + 1) m h k c = lsAndK n (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) k c
      (lsW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) k c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [lsNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, lsAndK]
  simp

theorem lsNodeW_forall (hv : viewOK m h 30) (hg : h >>> 28 = 6) :
    lsNodeW (n + 1) m h k c = lsAndK n (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) k c
      (lsW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) k c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [lsNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, lsAndK]
  simp

theorem lsNodeW_proj (hv : viewOK m h 32) (hg : h >>> 28 = 9) :
    lsNodeW (n + 1) m h k c = lsW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) k c := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [lsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem lsNodeW_let (hv : viewOK m h 20) (hg : h >>> 28 = 7) :
    lsNodeW (n + 1) m h k c = lsLetK n (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1))
      (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) k c
      (lsW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) k c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [lsNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, lsLetK, lsAndK]
  split <;> simp_all

end lsArms

attribute [arena_grind =] lsK_some lsAndK_zero lsLetK_zero lsSet_eq
grind_pattern [arena_grind] lsAndK_ne => lsAndK n b k c (some (x, m₁))
grind_pattern [arena_grind] lsLetK_ne => lsLetK n v b k c (some (x, m₁))
grind_pattern [arena_grind] lsW_cut => lsW (n + 1) m h k c
grind_pattern [arena_grind] lsW_hit => lsW (n + 1) m h k c
grind_pattern [arena_grind] lsW_miss => lsW (n + 1) m h k c
grind_pattern [arena_grind] lsNodeW_bvar => lsNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsNodeW_sort => lsNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsNodeW_const => lsNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsNodeW_lit => lsNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsNodeW_fvar_in => lsNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsNodeW_fvar_out => lsNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsNodeW_app => lsNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsNodeW_lam => lsNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsNodeW_forall => lsNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsNodeW_proj => lsNodeW (n + 1) m h k c
grind_pattern [arena_grind] lsNodeW_let => lsNodeW (n + 1) m h k c

@[l_impl ConRon.Arena.leavesSubGo]
def lsGo : FunDecl := lfn (h, k, c) locals (b, x, fd, j, e, r, u) {
  if c == 0 { abort };
  (b, x) := call der_b(h);
  if x == 0 { return 1 };
  (fd, j, e) := call ls_find(h, 0);
  if fd != 0 { x := LSM.u64[j * 4 + 3]; if x == 0 { return 0 }; return 1 };
  r := call ls_node(h, k, c - 1);
  (fd, j, e) := call ls_find(h, 0);
  u := call ls_put(h, 0, r, fd, j);
  return r
}

@[l_impl ConRon.Arena.leavesSubGo ConRon.Arena.leavesSubArmApp ConRon.Arena.leavesSubArmBind
  ConRon.Arena.leavesSubArmLet]
def lsNode : FunDecl := lfn (h, k, c) locals (g, t, i, f, a, b, x) {
  g := h >> 28;
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if CTL.u64[22 + t] <= i { abort }; return 1 };
  if g == 1 {
    if CTL.u64[26 + t] <= i { abort };
    f := FVREC.u64[i * 4 + t * 2];
    a := FVREC.u64[i * 4 + t * 2 + 1];
    x := call leaf_mem(k, f, a);
    if x == 0 { return 0 };
    x := call ls_go(a, k, c);
    return x
  };
  if g == 4 {
    if CTL.u64[4 + t] <= i { abort };
    f := AREC.u64[i * 4 + t * 2];
    a := AREC.u64[i * 4 + t * 2 + 1];
    x := call ls_go(f, k, c);
    if x == 0 { return 0 };
    x := call ls_go(a, k, c);
    return x
  };
  if g == 5 {
    if CTL.u64[28 + t] <= i { abort };
    f := LAREC.u64[i * 4 + t * 2];
    a := LAREC.u64[i * 4 + t * 2 + 1];
    x := call ls_go(f, k, c);
    if x == 0 { return 0 };
    x := call ls_go(a, k, c);
    return x
  };
  if g == 6 {
    if CTL.u64[30 + t] <= i { abort };
    f := FAREC.u64[i * 4 + t * 2];
    a := FAREC.u64[i * 4 + t * 2 + 1];
    x := call ls_go(f, k, c);
    if x == 0 { return 0 };
    x := call ls_go(a, k, c);
    return x
  };
  if g == 9 {
    if CTL.u64[32 + t] <= i { abort };
    f := PJREC.u64[i * 6 + t * 3 + 2];
    x := call ls_go(f, k, c);
    return x
  };
  if g == 7 {
    if CTL.u64[20 + t] <= i { abort };
    f := LEREC.u64[i * 6 + t * 3];
    a := LEREC.u64[i * 6 + t * 3 + 1];
    b := LEREC.u64[i * 6 + t * 3 + 2];
    x := call ls_go(f, k, c);
    if x == 0 { return 0 };
    x := call ls_go(a, k, c);
    if x == 0 { return 0 };
    x := call ls_go(b, k, c);
    return x
  };
  if g == 2 { if CTL.u64[16 + t] <= i { abort }; return 1 };
  if g == 3 { if CTL.u64[18 + t] <= i { abort }; return 1 };
  if g == 8 { if CTL.u64[2 + t] <= i { abort }; return 1 };
  abort
}

section lsgo
variable (p : Prog) (hpd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "ls_find" = some (memoFindG lsSch))
  (hps : p.lookup "ls_put" = some (memoPutG lsSch)) (hp : p.lookup "ls_go" = some lsGo)
  (hpn : p.lookup "ls_node" = some lsNode) (hpm : p.lookup "leaf_mem" = some leafMemL)

def LsGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h k c : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ls_go" [h, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ lsW n s₀.mem h k c = some (r.headD 0, s'.mem); ⊤⦄

def LsNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (h k c : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ls_node" [h, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ lsNodeW n s₀.mem h k c = some (r.headD 0, s'.mem); ⊤⦄

include hpd hpf hps hp in
theorem lsGo_step (n : Nat) (ih : LsNodeSpec p n) : LsGoSpec p (n + 1) := by
  unfold LsNodeSpec at ih
  intro s₀ h k c
  rw [invoke_eq _ hp]
  simp only [callFn, lsGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, derB_spec p hpd n,
      memoFindG_spec lsSch p _ hpf n, memoPutG_spec lsSch p _ hps n, ih] <;>
    -- as `wsGo_step`: the miss path is deep
    finish (instances := 5000) (gen := 12)

set_option maxHeartbeats 1000000 in
include hpn hpm in
theorem lsNode_step (n : Nat) (ih : LsGoSpec p n) : LsNodeSpec p (n + 1) := by
  unfold LsGoSpec at ih
  intro s₀ h k c
  rw [invoke_eq _ hpn]
  simp only [callFn, lsNode]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, leafMem_spec p hpm n, ih] <;>
    finish [viewOK, tierW, idxW]

include hpd hpf hps hp hpn hpm in
theorem lsGo_spec (n : Nat) : LsGoSpec p n ∧ LsNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ h k c; rw [invoke_eq _ hp]; simp only [callFn, lsGo]; vcgen [exec] <;> grind
    · intro s₀ h k c; rw [invoke_eq _ hpn]; simp only [callFn, lsNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨lsGo_step p hpd hpf hps hp n ih.2, lsNode_step p hpn hpm n ih.1⟩

end lsgo

/-! ## `leaf_guard(fab, base)` -/

/-- After `fl_go`: clear the subset memo and walk `fab`. -/
def lgK (n : Nat) (fab : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (k, m₁) =>
    if rdW (m₁.arr64 CTL) 156 + 2 = 0 then none else lsW n (mclearG lsSch m₁) fab k 4000000000

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
    lgK n fab (some (k, m₁)) = lsW n (mclearG lsSch m₁) fab k 4000000000 := by simp [lgK, h0]

grind_pattern [arena_grind] lgW_cut => lgW n m fab base
grind_pattern [arena_grind] lgW_go => lgW n m fab base
grind_pattern [arena_grind] lgK_some => lgK n fab (some (k, m₁))

@[l_impl ConRon.Arena.leafGuard ConRon.Arena.fvarLeavesFast]
def leafGuardL : FunDecl := lfn (fab, base) locals (b, x, k, r, u) {
  (b, x) := call der_b(fab);
  if x == 0 { return 1 };
  u := call fl_clear();
  k := call fl_go(base, 0, 4000000000);
  u := call ls_clear();
  r := call ls_go(fab, k, 4000000000);
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
  lsf : p.lookup "ls_find" = some (memoFindG lsSch)
  lsp : p.lookup "ls_put" = some (memoPutG lsSch)
  lsc : p.lookup "ls_clear" = some (memoClearG lsSch)
  lsgo : p.lookup "ls_go" = some lsGo
  lsnode : p.lookup "ls_node" = some lsNode
  lm : p.lookup "leaf_mem" = some leafMemL
  lg : p.lookup "leaf_guard" = some leafGuardL

theorem leafGuard_spec (p : Prog) (hp : LgProg p) (n : Nat) (s₀ : St) (fab base : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "leaf_guard" [fab, base]
    ⦃fun r s' => LocEq s' s₀ ∧ lgW n s₀.mem fab base = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ihf := (flGo_spec p hp.derb hp.flf hp.flp hp.flgo hp.flnode n).1
  have ihs := (lsGo_spec p hp.derb hp.lsf hp.lsp hp.lsgo hp.lsnode hp.lm n).1
  unfold FlGoSpec at ihf
  unfold LsGoSpec at ihs
  rw [invoke_eq _ hp.lg]
  simp only [callFn, leafGuardL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, derB_spec p hp.derb n,
      memoClearG_spec flSch p _ hp.flc n, memoClearG_spec lsSch p _ hp.lsc n, ihf, ihs] <;>
    finish (instances := 5000) (gen := 12)

/-- The leaf guard as one program. -/
def lgProg : Prog :=
  [("der_b", derB), ("fl_find", memoFindG flSch), ("fl_put", memoPutG flSch),
    ("fl_clear", memoClearG flSch), ("fl_go", flGo), ("fl_node", flNode),
    ("ls_find", memoFindG lsSch), ("ls_put", memoPutG lsSch), ("ls_clear", memoClearG lsSch),
    ("ls_go", lsGo), ("ls_node", lsNode), ("leaf_mem", leafMemL), ("leaf_guard", leafGuardL)]

theorem lgProg_ok : LgProg lgProg := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end L.Arena
