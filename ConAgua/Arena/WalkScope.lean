module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.ExprMk
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Layout

@[expose] public section

/-!
# `wscopedBFast`: the memoized scope walk (lane `whnf3`)

con-ron's `wscopedBGo`/`wscopedBFast` (`Arena/ExprOps.lean:959-1048`, con-leche's `wscopedBXP`):
is every `fvar` leaf reachable from `h` (its annotation descended at the leaf's own index) below
the cursor `d`? The twin threads a walk-local `Std.HashMap (EIdx × Nat) Bool`; L keeps it in the
memo library's table at word array `WSM` (151, stamp/count `CTL[152]`/`CTL[153]`), keyed by the
handle word and the cursor word, cleared (an epoch bump) on the entry, as the twin starts from `∅`.

`ws_go(h, d, c)`: `abort` at `c = 0` (the twin's fuel exhausted), the `fvar`-range cutoff off the
derived word (`der_b`'s second result `0`: `true`), the memo probe, else `ws_node(h, d, c - 1)`
and record. `ws_node` views the handle and dispatches as the twin's arms (the `app`, binder and
`letE` arms short-circuit on a `false` child, as `wscopedBGoArm*`):

* `bvar`, `sort`, `const`, `lit`: `1`;
* `fvar idx ty`: `idx < d` ? `ws_go(ty, idx, c)` : `0`;
* `app f a`, `lam ty b`, `forallE ty b`: the first child, then (if `1`) the second;
* `letE ty v b`: the three in order, stopping at a `0`;
* `proj _ _ e`: `ws_go(e, d, c)`.

`wscoped_bfast(d, e)` is `ws_clear(); ws_go(e, d, 4000000000)` (`coreWalkFuel`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- Its schema: array 151, stamp/count `CTL[152]`/`CTL[153]`. -/
abbrev wsSch : MemoSch := ⟨WSM, 152⟩

/-- Record the result `r` at `(h, d)` and return it. -/
def wsSet (m : Mem) (h d r : Word) : Option (Word × Mem) :=
  match msetG wsSch m h d r with
  | none => none
  | some m' => some (r, m')

mutual
/-- **The model of `ws_go`** at L fuel `n`. -/
def wscW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, d, c =>
    if c = 0 then none
    else if derFW m h = 0 then some (1, m)
    else if mfindG wsSch m h d = [] then none
    else if (mfindG wsSch m h d).headD 0 ≠ 0 then
      some (if rdW (m.arr64 WSM) ((mfindG wsSch m h d).tail.headD 0 * 4 + 3) ≠ 0 then 1 else 0, m)
    else
      match wsNodeW n m h d (c - 1) with
      | none => none
      | some (r, m₁) => wsSet m₁ h d r

/-- **The model of `ws_node`**: the view and the dispatch on the tag. -/
def wsNodeW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, d, c =>
    if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if h >>> 28 = 0 then
      if tcnt m BVAR (tierW h) ≤ idxW h then none else some (1, m)
    else if h >>> 28 = 1 then
      if tcnt m FVAR (tierW h) ≤ idxW h then none
      else if tfld m FVAR (tierW h) (idxW h) 0 < d then
        wscW n m (tfld m FVAR (tierW h) (idxW h) 1)
          (tfld m FVAR (tierW h) (idxW h) 0) c
      else some (0, m)
    else if h >>> 28 = 4 then
      if tcnt m APP (tierW h) ≤ idxW h then none
      else
        match wscW n m (tfld m APP (tierW h) (idxW h) 0) d c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else wscW n m₁ (tfld m APP (tierW h) (idxW h) 1) d c
    else if h >>> 28 = 5 then
      if tcnt m LAM (tierW h) ≤ idxW h then none
      else
        match wscW n m (tfld m LAM (tierW h) (idxW h) 0) d c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else wscW n m₁ (tfld m LAM (tierW h) (idxW h) 1) d c
    else if h >>> 28 = 6 then
      if tcnt m FORALL (tierW h) ≤ idxW h then none
      else
        match wscW n m (tfld m FORALL (tierW h) (idxW h) 0) d c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else wscW n m₁ (tfld m FORALL (tierW h) (idxW h) 1) d c
    else if h >>> 28 = 9 then
      if tcnt m PROJ (tierW h) ≤ idxW h then none
      else wscW n m (tfld m PROJ (tierW h) (idxW h) 2) d c
    else if h >>> 28 = 7 then
      if tcnt m LET (tierW h) ≤ idxW h then none
      else
        match wscW n m (tfld m LET (tierW h) (idxW h) 0) d c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else
          match wscW n m₁ (tfld m LET (tierW h) (idxW h) 1) d c with
          | none => none
          | some (y, m₂) =>
            if y = 0 then some (0, m₂) else wscW n m₂ (tfld m LET (tierW h) (idxW h) 2) d c
    else if h >>> 28 = 2 then
      if tcnt m SORT (tierW h) ≤ idxW h then none else some (1, m)
    else if h >>> 28 = 3 then
      if tcnt m CONST (tierW h) ≤ idxW h then none else some (1, m)
    else if h >>> 28 = 8 then
      if tcnt m LIT (tierW h) ≤ idxW h then none else some (1, m)
    else none
end

/-! ### The guarded equations, one per reachable arm -/

/-- After `ws_node`: record the result. -/
def wsK (h d : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => wsSet m₁ h d r

/-- After `ws_put`. -/
def wsSetK (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m' => some (r, m')

/-- A short-circuiting `&&` of two children: after the first, the second if the first is `1`. -/
def wsAndK (n : Nat) (b d c : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x = 0 then some (0, m₁) else wscW n m₁ b d c

/-- The `letE` arm after its first child. -/
def wsLetK (n : Nat) (v b d c : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x = 0 then some (0, m₁) else wsAndK n b d c (wscW n m₁ v d c)

section arms
variable (n : Nat) (m m₁ : Mem) (h r x d c b v : Word)

theorem wsK_some : wsK h d (some (r, m₁)) = wsSet m₁ h d r := rfl
theorem wsSetK_some : wsSetK r (some m₁) = some (r, m₁) := rfl
theorem wsAndK_zero : wsAndK n b d c (some (0, m₁)) = some (0, m₁) := by simp [wsAndK]
theorem wsAndK_ne (hx : x ≠ 0) : wsAndK n b d c (some (x, m₁)) = wscW n m₁ b d c := by
  simp [wsAndK, hx]
theorem wsLetK_zero : wsLetK n v b d c (some (0, m₁)) = some (0, m₁) := by simp [wsLetK]
theorem wsLetK_ne (hx : x ≠ 0) : wsLetK n v b d c (some (x, m₁)) = wsAndK n b d c (wscW n m₁ v d c) := by
  simp [wsLetK, hx]

theorem wsSet_eq : wsSet m h d r = wsSetK r (msetG wsSch m h d r) := by
  simp only [wsSet, wsSetK]

theorem wscW_cut (hc : c ≠ 0) (hf : derFW m h = 0) : wscW (n + 1) m h d c = some (1, m) := by
  rw [wscW]; simp [hc, hf]

theorem wscW_hit (hc : c ≠ 0) (hf : derFW m h ≠ 0) (hr : mfindG wsSch m h d ≠ [])
    (hh : (mfindG wsSch m h d).headD 0 ≠ 0) :
    wscW (n + 1) m h d c =
      some (if rdW (m.arr64 WSM) ((mfindG wsSch m h d).tail.headD 0 * 4 + 3) ≠ 0 then 1 else 0, m) := by
  rw [wscW]; simp only [hc, hf, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem wscW_miss (hc : c ≠ 0) (hf : derFW m h ≠ 0) (hr : mfindG wsSch m h d ≠ [])
    (hh : (mfindG wsSch m h d).headD 0 = 0) :
    wscW (n + 1) m h d c = wsK h d (wsNodeW n m h d (c - 1)) := by
  rw [wscW]; simp only [hc, hf, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, wsK]

theorem wsNodeW_bvar (hg : h >>> 28 = 0) (hv : viewOK m h BVAR) : wsNodeW (n + 1) m h d c = some (1, m) := by
  rw [wsNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem wsNodeW_sort (hg : h >>> 28 = 2) (hv : viewOK m h SORT) : wsNodeW (n + 1) m h d c = some (1, m) := by
  rw [wsNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem wsNodeW_const (hg : h >>> 28 = 3) (hv : viewOK m h CONST) : wsNodeW (n + 1) m h d c = some (1, m) := by
  rw [wsNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem wsNodeW_lit (hg : h >>> 28 = 8) (hv : viewOK m h LIT) : wsNodeW (n + 1) m h d c = some (1, m) := by
  rw [wsNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem wsNodeW_fvar_lt (hg : h >>> 28 = 1) (hv : viewOK m h FVAR)
    (hl : tfld m FVAR (tierW h) (idxW h) 0 < d) :
    wsNodeW (n + 1) m h d c = wscW n m (tfld m FVAR (tierW h) (idxW h) 1)
      (tfld m FVAR (tierW h) (idxW h) 0) c := by
  rw [wsNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2, hl]

theorem wsNodeW_fvar_ge (hg : h >>> 28 = 1) (hv : viewOK m h FVAR)
    (hl : ¬ tfld m FVAR (tierW h) (idxW h) 0 < d) :
    wsNodeW (n + 1) m h d c = some (0, m) := by
  rw [wsNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2, hl]

theorem wsNodeW_app (hv : viewOK m h APP) (hg : h >>> 28 = 4) :
    wsNodeW (n + 1) m h d c = wsAndK n (tfld m APP (tierW h) (idxW h) 1) d c
      (wscW n m (tfld m APP (tierW h) (idxW h) 0) d c) := by
  rw [wsNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, wsAndK]
  simp

theorem wsNodeW_lam (hv : viewOK m h LAM) (hg : h >>> 28 = 5) :
    wsNodeW (n + 1) m h d c = wsAndK n (tfld m LAM (tierW h) (idxW h) 1) d c
      (wscW n m (tfld m LAM (tierW h) (idxW h) 0) d c) := by
  rw [wsNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, wsAndK]
  simp

theorem wsNodeW_forall (hv : viewOK m h FORALL) (hg : h >>> 28 = 6) :
    wsNodeW (n + 1) m h d c = wsAndK n (tfld m FORALL (tierW h) (idxW h) 1) d c
      (wscW n m (tfld m FORALL (tierW h) (idxW h) 0) d c) := by
  rw [wsNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, wsAndK]
  simp

theorem wsNodeW_proj (hv : viewOK m h PROJ) (hg : h >>> 28 = 9) :
    wsNodeW (n + 1) m h d c = wscW n m (tfld m PROJ (tierW h) (idxW h) 2) d c := by
  rw [wsNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem wsNodeW_let (hv : viewOK m h LET) (hg : h >>> 28 = 7) :
    wsNodeW (n + 1) m h d c = wsLetK n (tfld m LET (tierW h) (idxW h) 1)
      (tfld m LET (tierW h) (idxW h) 2) d c
      (wscW n m (tfld m LET (tierW h) (idxW h) 0) d c) := by
  rw [wsNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, wsLetK, wsAndK]
  split <;> simp_all

end arms

attribute [arena_grind =] wsK_some wsSetK_some wsAndK_zero wsLetK_zero wsSet_eq
grind_pattern [arena_grind] wsAndK_ne => wsAndK n b d c (some (x, m₁))
grind_pattern [arena_grind] wsLetK_ne => wsLetK n v b d c (some (x, m₁))
grind_pattern [arena_grind] wscW_cut => wscW (n + 1) m h d c
grind_pattern [arena_grind] wscW_hit => wscW (n + 1) m h d c
grind_pattern [arena_grind] wscW_miss => wscW (n + 1) m h d c
grind_pattern [arena_grind] wsNodeW_bvar => wsNodeW (n + 1) m h d c
grind_pattern [arena_grind] wsNodeW_sort => wsNodeW (n + 1) m h d c
grind_pattern [arena_grind] wsNodeW_const => wsNodeW (n + 1) m h d c
grind_pattern [arena_grind] wsNodeW_lit => wsNodeW (n + 1) m h d c
grind_pattern [arena_grind] wsNodeW_fvar_lt => wsNodeW (n + 1) m h d c
grind_pattern [arena_grind] wsNodeW_fvar_ge => wsNodeW (n + 1) m h d c
grind_pattern [arena_grind] wsNodeW_app => wsNodeW (n + 1) m h d c
grind_pattern [arena_grind] wsNodeW_lam => wsNodeW (n + 1) m h d c
grind_pattern [arena_grind] wsNodeW_forall => wsNodeW (n + 1) m h d c
grind_pattern [arena_grind] wsNodeW_proj => wsNodeW (n + 1) m h d c
grind_pattern [arena_grind] wsNodeW_let => wsNodeW (n + 1) m h d c

/-- con-ron: ConRon/Arena/ExprOps.lean:953-981 ConRon.Arena.wscopedBGo -/
@[l_impl ConRon.Arena.wscopedBGo]
def wsGo : FunDecl := lfn (h, d, c) locals (b, x, fd, j, e, r, u) {
  if c == 0 { abort };
  (b, x) := call der_b(h);
  if x == 0 { return 1 };
  (fd, j, e) := call ws_find(h, d);
  if fd != 0 { x := WSM.u64[j * 4 + 3]; if x == 0 { return 0 }; return 1 };
  r := call ws_node(h, d, c - 1);
  (fd, j, e) := call ws_find(h, d);
  u := call ws_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:953-981 ConRon.Arena.wscopedBGo
con-ron: ConRon/Arena/ExprOps.lean:983-989 ConRon.Arena.wscopedBGoArmApp
con-ron: ConRon/Arena/ExprOps.lean:991-998 ConRon.Arena.wscopedBGoArmBind
con-ron: ConRon/Arena/ExprOps.lean:1000-1010 ConRon.Arena.wscopedBGoArmLet -/
@[l_impl ConRon.Arena.wscopedBGo ConRon.Arena.wscopedBGoArmApp ConRon.Arena.wscopedBGoArmBind
  ConRon.Arena.wscopedBGoArmLet]
def wsNode : FunDecl := lfn (h, d, c) locals (g, t, i, f, a, b, x) {
  g := h >> 28;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if BVAR⟨t⟩.count <= i { abort }; return 1 };
  if g == 1 {
    if FVAR⟨t⟩.count <= i { abort };
    f := FVAR⟨t, i⟩.i;
    a := FVAR⟨t, i⟩.ty;
    if f < d { x := call ws_go(a, f, c); return x };
    return 0
  };
  if g == 4 {
    if APP⟨t⟩.count <= i { abort };
    f := APP⟨t, i⟩.f;
    a := APP⟨t, i⟩.a;
    x := call ws_go(f, d, c);
    if x == 0 { return 0 };
    x := call ws_go(a, d, c);
    return x
  };
  if g == 5 {
    if LAM⟨t⟩.count <= i { abort };
    f := LAM⟨t, i⟩.ty;
    a := LAM⟨t, i⟩.b;
    x := call ws_go(f, d, c);
    if x == 0 { return 0 };
    x := call ws_go(a, d, c);
    return x
  };
  if g == 6 {
    if FORALL⟨t⟩.count <= i { abort };
    f := FORALL⟨t, i⟩.ty;
    a := FORALL⟨t, i⟩.b;
    x := call ws_go(f, d, c);
    if x == 0 { return 0 };
    x := call ws_go(a, d, c);
    return x
  };
  if g == 9 {
    if PROJ⟨t⟩.count <= i { abort };
    f := PROJ⟨t, i⟩.e;
    x := call ws_go(f, d, c);
    return x
  };
  if g == 7 {
    if LET⟨t⟩.count <= i { abort };
    f := LET⟨t, i⟩.ty;
    a := LET⟨t, i⟩.v;
    b := LET⟨t, i⟩.b;
    x := call ws_go(f, d, c);
    if x == 0 { return 0 };
    x := call ws_go(a, d, c);
    if x == 0 { return 0 };
    x := call ws_go(b, d, c);
    return x
  };
  if g == 2 { if SORT⟨t⟩.count <= i { abort }; return 1 };
  if g == 3 { if CONST⟨t⟩.count <= i { abort }; return 1 };
  if g == 8 { if LIT⟨t⟩.count <= i { abort }; return 1 };
  abort
}

section go
variable (p : Prog) (hpd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "ws_find" = some (memoFindG wsSch))
  (hps : p.lookup "ws_put" = some (memoPutG wsSch)) (hp : p.lookup "ws_go" = some wsGo)
  (hpn : p.lookup "ws_node" = some wsNode)

/-- The spec of `ws_go` at fuel `n`. -/
def WsGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h d c : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ws_go" [h, d, c]
    ⦃fun r s' => LocEq s' s₀ ∧ wscW n s₀.mem h d c = some (r.headD 0, s'.mem); ⊤⦄

/-- The spec of `ws_node` at fuel `n`. -/
def WsNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (h d c : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ws_node" [h, d, c]
    ⦃fun r s' => LocEq s' s₀ ∧ wsNodeW n s₀.mem h d c = some (r.headD 0, s'.mem); ⊤⦄

include hpd hpf hps hp in
theorem wsGo_step (n : Nat) (ih : WsNodeSpec p n) : WsGoSpec p (n + 1) := by
  unfold WsNodeSpec at ih
  intro s₀ h d c
  rw [invoke_eq _ hp]
  simp only [callFn, wsGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, derB_spec p hpd n,
      memoFindG_spec wsSch p _ hpf n, memoPutG_spec wsSch p _ hps n, ih] <;>
    -- the miss path (cutoff, probe, node, put) is deeper than the default search reaches
    finish (instances := 5000) (gen := 12)

set_option maxHeartbeats 1000000 in
include hpn in
theorem wsNode_step (n : Nat) (ih : WsGoSpec p n) : WsNodeSpec p (n + 1) := by
  unfold WsGoSpec at ih
  intro s₀ h d c
  rw [invoke_eq _ hpn]
  simp only [callFn, wsNode]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE, ih] <;>
    finish [viewOK, tierW, idxW]

include hpd hpf hps hp hpn in
/-- **`ws_go` and `ws_node` are their models**, at every fuel. -/
theorem wsGo_spec (n : Nat) : WsGoSpec p n ∧ WsNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ h d c; rw [invoke_eq _ hp]; simp only [callFn, wsGo]; vcgen [exec] <;> grind
    · intro s₀ h d c; rw [invoke_eq _ hpn]; simp only [callFn, wsNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨wsGo_step p hpd hpf hps hp n ih.2, wsNode_step p hpn n ih.1⟩

/-! ## `wscoped_bfast(d, e)`: the entry -/

/-- **The model of `wscoped_bfast`**: clear the memo (the twin's `∅`), walk at `coreWalkFuel`. -/
def wsFastW (n : Nat) (m : Mem) (d e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 152 + 2 = 0 then none else wscW n (mclearG wsSch m) e d 4000000000

theorem wsFastW_eq (n : Nat) (m : Mem) (d e : Word) (h0 : rdW (m.arr64 CTL) 152 + 2 ≠ 0) :
    wsFastW n m d e = wscW n (mclearG wsSch m) e d 4000000000 := by simp [wsFastW, h0]

grind_pattern [arena_grind] wsFastW_eq => wsFastW n m d e

/-- con-ron: ConRon/Arena/ExprOps.lean:1043-1047 ConRon.Arena.wscopedBFast -/
@[l_impl ConRon.Arena.wscopedBFast]
def wscopedBFastL : FunDecl := lfn (d, e) locals (r, u) {
  u := call ws_clear();
  r := call ws_go(e, d, 4000000000);
  return r
}

include hpd hpf hps hp hpn in
theorem wscopedBFast_spec (hpc : p.lookup "ws_clear" = some (memoClearG wsSch))
    (hpm : p.lookup "wscoped_bfast" = some wscopedBFastL) (n : Nat) (s₀ : St) (d e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "wscoped_bfast" [d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ wsFastW n s₀.mem d e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (wsGo_spec p hpd hpf hps hp hpn n).1
  unfold WsGoSpec at ih
  rw [invoke_eq _ hpm]
  simp only [callFn, wscopedBFastL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec wsSch p _ hpc n, ih] <;>
    finish

end go

/-- What the specs need of the program. -/
structure WsProg (p : Prog) : Prop where
  derb : p.lookup "der_b" = some derB
  wsf : p.lookup "ws_find" = some (memoFindG wsSch)
  wsp : p.lookup "ws_put" = some (memoPutG wsSch)
  wsc : p.lookup "ws_clear" = some (memoClearG wsSch)
  wsgo : p.lookup "ws_go" = some wsGo
  wsnode : p.lookup "ws_node" = some wsNode
  wsfast : p.lookup "wscoped_bfast" = some wscopedBFastL

end L.Arena
