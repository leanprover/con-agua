module

public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.ExprMk
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

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

/-- The scope walk's memo (`wscopedBGo`'s walk-local map). -/
abbrev WSM : ArrId := 151
/-- Its schema: array 151, stamp/count `CTL[152]`/`CTL[153]`. -/
abbrev wsSch : MemoSch := ⟨WSM, 152⟩

/-- Record the result `r` at `(h, d)` and return it. -/
def wsSet (m : Mem) (h d r : Word) : Option (Word × Mem) :=
  match msetG wsSch m h d r with
  | none => none
  | some m' => some (r, m')

mutual
/-- **The model of `ws_go`** at L fuel `n`. -/
def wsW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
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
      if rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h then none else some (1, m)
    else if h >>> 28 = 1 then
      if rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h then none
      else if rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) < d then
        wsW n m (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1))
          (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2)) c
      else some (0, m)
    else if h >>> 28 = 4 then
      if rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h then none
      else
        match wsW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) d c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else wsW n m₁ (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) d c
    else if h >>> 28 = 5 then
      if rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h then none
      else
        match wsW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) d c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else wsW n m₁ (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) d c
    else if h >>> 28 = 6 then
      if rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h then none
      else
        match wsW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) d c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else wsW n m₁ (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) d c
    else if h >>> 28 = 9 then
      if rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h then none
      else wsW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) d c
    else if h >>> 28 = 7 then
      if rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h then none
      else
        match wsW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) d c with
        | none => none
        | some (x, m₁) =>
          if x = 0 then some (0, m₁) else
          match wsW n m₁ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) d c with
          | none => none
          | some (y, m₂) =>
            if y = 0 then some (0, m₂) else wsW n m₂ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) d c
    else if h >>> 28 = 2 then
      if rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h then none else some (1, m)
    else if h >>> 28 = 3 then
      if rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h then none else some (1, m)
    else if h >>> 28 = 8 then
      if rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h then none else some (1, m)
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
  | some (x, m₁) => if x = 0 then some (0, m₁) else wsW n m₁ b d c

/-- The `letE` arm after its first child. -/
def wsLetK (n : Nat) (v b d c : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x = 0 then some (0, m₁) else wsAndK n b d c (wsW n m₁ v d c)

section arms
variable (n : Nat) (m m₁ : Mem) (h r x d c b v : Word)

theorem wsK_some : wsK h d (some (r, m₁)) = wsSet m₁ h d r := rfl
theorem wsSetK_some : wsSetK r (some m₁) = some (r, m₁) := rfl
theorem wsAndK_zero : wsAndK n b d c (some (0, m₁)) = some (0, m₁) := by simp [wsAndK]
theorem wsAndK_ne (hx : x ≠ 0) : wsAndK n b d c (some (x, m₁)) = wsW n m₁ b d c := by
  simp [wsAndK, hx]
theorem wsLetK_zero : wsLetK n v b d c (some (0, m₁)) = some (0, m₁) := by simp [wsLetK]
theorem wsLetK_ne (hx : x ≠ 0) : wsLetK n v b d c (some (x, m₁)) = wsAndK n b d c (wsW n m₁ v d c) := by
  simp [wsLetK, hx]

theorem wsSet_eq : wsSet m h d r = wsSetK r (msetG wsSch m h d r) := by
  simp only [wsSet, wsSetK]

theorem wsW_cut (hc : c ≠ 0) (hf : derFW m h = 0) : wsW (n + 1) m h d c = some (1, m) := by
  rw [wsW]; simp [hc, hf]

theorem wsW_hit (hc : c ≠ 0) (hf : derFW m h ≠ 0) (hr : mfindG wsSch m h d ≠ [])
    (hh : (mfindG wsSch m h d).headD 0 ≠ 0) :
    wsW (n + 1) m h d c =
      some (if rdW (m.arr64 WSM) ((mfindG wsSch m h d).tail.headD 0 * 4 + 3) ≠ 0 then 1 else 0, m) := by
  rw [wsW]; simp only [hc, hf, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem wsW_miss (hc : c ≠ 0) (hf : derFW m h ≠ 0) (hr : mfindG wsSch m h d ≠ [])
    (hh : (mfindG wsSch m h d).headD 0 = 0) :
    wsW (n + 1) m h d c = wsK h d (wsNodeW n m h d (c - 1)) := by
  rw [wsW]; simp only [hc, hf, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, wsK]

theorem wsNodeW_bvar (hg : h >>> 28 = 0) (hv : viewOK m h 22) : wsNodeW (n + 1) m h d c = some (1, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [wsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem wsNodeW_sort (hg : h >>> 28 = 2) (hv : viewOK m h 16) : wsNodeW (n + 1) m h d c = some (1, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [wsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem wsNodeW_const (hg : h >>> 28 = 3) (hv : viewOK m h 18) : wsNodeW (n + 1) m h d c = some (1, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [wsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem wsNodeW_lit (hg : h >>> 28 = 8) (hv : viewOK m h 2) : wsNodeW (n + 1) m h d c = some (1, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [wsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem wsNodeW_fvar_lt (hg : h >>> 28 = 1) (hv : viewOK m h 26)
    (hl : rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) < d) :
    wsNodeW (n + 1) m h d c = wsW n m (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1))
      (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2)) c := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [wsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2, hl]

theorem wsNodeW_fvar_ge (hg : h >>> 28 = 1) (hv : viewOK m h 26)
    (hl : ¬ rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) < d) :
    wsNodeW (n + 1) m h d c = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [wsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2, hl]

theorem wsNodeW_app (hv : viewOK m h 4) (hg : h >>> 28 = 4) :
    wsNodeW (n + 1) m h d c = wsAndK n (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) d c
      (wsW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) d c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [wsNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, wsAndK]
  simp

theorem wsNodeW_lam (hv : viewOK m h 28) (hg : h >>> 28 = 5) :
    wsNodeW (n + 1) m h d c = wsAndK n (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) d c
      (wsW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) d c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [wsNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, wsAndK]
  simp

theorem wsNodeW_forall (hv : viewOK m h 30) (hg : h >>> 28 = 6) :
    wsNodeW (n + 1) m h d c = wsAndK n (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) d c
      (wsW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) d c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [wsNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, wsAndK]
  simp

theorem wsNodeW_proj (hv : viewOK m h 32) (hg : h >>> 28 = 9) :
    wsNodeW (n + 1) m h d c = wsW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) d c := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [wsNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem wsNodeW_let (hv : viewOK m h 20) (hg : h >>> 28 = 7) :
    wsNodeW (n + 1) m h d c = wsLetK n (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1))
      (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) d c
      (wsW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) d c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [wsNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, wsLetK, wsAndK]
  split <;> simp_all

end arms

attribute [arena_grind =] wsK_some wsSetK_some wsAndK_zero wsLetK_zero wsSet_eq
grind_pattern [arena_grind] wsAndK_ne => wsAndK n b d c (some (x, m₁))
grind_pattern [arena_grind] wsLetK_ne => wsLetK n v b d c (some (x, m₁))
grind_pattern [arena_grind] wsW_cut => wsW (n + 1) m h d c
grind_pattern [arena_grind] wsW_hit => wsW (n + 1) m h d c
grind_pattern [arena_grind] wsW_miss => wsW (n + 1) m h d c
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

@[l_impl ConRon.Arena.wscopedBGo ConRon.Arena.wscopedBGoArmApp ConRon.Arena.wscopedBGoArmBind
  ConRon.Arena.wscopedBGoArmLet]
def wsNode : FunDecl := lfn (h, d, c) locals (g, t, i, f, a, b, x) {
  g := h >> 28;
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if CTL.u64[22 + t] <= i { abort }; return 1 };
  if g == 1 {
    if CTL.u64[26 + t] <= i { abort };
    f := FVREC.u64[i * 4 + t * 2];
    a := FVREC.u64[i * 4 + t * 2 + 1];
    if f < d { x := call ws_go(a, f, c); return x };
    return 0
  };
  if g == 4 {
    if CTL.u64[4 + t] <= i { abort };
    f := AREC.u64[i * 4 + t * 2];
    a := AREC.u64[i * 4 + t * 2 + 1];
    x := call ws_go(f, d, c);
    if x == 0 { return 0 };
    x := call ws_go(a, d, c);
    return x
  };
  if g == 5 {
    if CTL.u64[28 + t] <= i { abort };
    f := LAREC.u64[i * 4 + t * 2];
    a := LAREC.u64[i * 4 + t * 2 + 1];
    x := call ws_go(f, d, c);
    if x == 0 { return 0 };
    x := call ws_go(a, d, c);
    return x
  };
  if g == 6 {
    if CTL.u64[30 + t] <= i { abort };
    f := FAREC.u64[i * 4 + t * 2];
    a := FAREC.u64[i * 4 + t * 2 + 1];
    x := call ws_go(f, d, c);
    if x == 0 { return 0 };
    x := call ws_go(a, d, c);
    return x
  };
  if g == 9 {
    if CTL.u64[32 + t] <= i { abort };
    f := PJREC.u64[i * 6 + t * 3 + 2];
    x := call ws_go(f, d, c);
    return x
  };
  if g == 7 {
    if CTL.u64[20 + t] <= i { abort };
    f := LEREC.u64[i * 6 + t * 3];
    a := LEREC.u64[i * 6 + t * 3 + 1];
    b := LEREC.u64[i * 6 + t * 3 + 2];
    x := call ws_go(f, d, c);
    if x == 0 { return 0 };
    x := call ws_go(a, d, c);
    if x == 0 { return 0 };
    x := call ws_go(b, d, c);
    return x
  };
  if g == 2 { if CTL.u64[16 + t] <= i { abort }; return 1 };
  if g == 3 { if CTL.u64[18 + t] <= i { abort }; return 1 };
  if g == 8 { if CTL.u64[2 + t] <= i { abort }; return 1 };
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
    ⦃fun r s' => LocEq s' s₀ ∧ wsW n s₀.mem h d c = some (r.headD 0, s'.mem); ⊤⦄

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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
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
  if rdW (m.arr64 CTL) 152 + 2 = 0 then none else wsW n (mclearG wsSch m) e d 4000000000

theorem wsFastW_eq (n : Nat) (m : Mem) (d e : Word) (h0 : rdW (m.arr64 CTL) 152 + 2 ≠ 0) :
    wsFastW n m d e = wsW n (mclearG wsSch m) e d 4000000000 := by simp [wsFastW, h0]

grind_pattern [arena_grind] wsFastW_eq => wsFastW n m d e

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

/-- The scope walk as one program. -/
def wsProg : Prog :=
  [("der_b", derB), ("ws_find", memoFindG wsSch), ("ws_put", memoPutG wsSch),
    ("ws_clear", memoClearG wsSch), ("ws_go", wsGo), ("ws_node", wsNode),
    ("wscoped_bfast", wscopedBFastL)]

theorem wsProg_ok : WsProg wsProg := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end L.Arena
