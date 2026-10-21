module

public import ConAgua.Arena.ViewL
public import ConAgua.Arena.AppStore
public import ConAgua.Arena.LetStore
public import ConAgua.Arena.BVarStore
public import ConAgua.Arena.LamStore
public import ConAgua.Arena.ForallStore
public import ConAgua.Arena.ProjStore
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store

@[expose] public section

/-!
# The derived loose-bvar range of expression nodes, and the `mk_*` constructors that keep it

con-ron's store keeps a **derived word** per node (`Tbl.der`, `EStore.derived`, `derOfView`):
a 32-bit hash, the loose-bvar range, the fvar range and a level-param flag, packed
(`packData`). The expression walks read its range field before anything else
(`liftLooseBVarsGo`, `instantiate1Go`, … cut off at `bvarOfData (derived h) ≤ c`), so L must know
it exactly. L keeps **only the range field** (the hash is `mixHash`, opaque; ROADMAP §2 item 10),
and only for the five compound tables, in one word array per table, indexed as the records
(`2 i + t`):

| array | table | count words |
|---|---|---|
| 42 `ADER` | `app` | `CTL[4], CTL[5]` |
| 43 `LADER` | `lam` | `CTL[28], CTL[29]` |
| 44 `FADER` | `forallE` | `CTL[30], CTL[31]` |
| 45 `LEDER` | `letE` | `CTL[20], CTL[21]` |
| 46 `PJDER` | `proj` | `CTL[32], CTL[33]` |

A leaf's range is a function of its record (`bvar i`: `satSucc i`; the others `0`), so it is not
stored. `der_b(h)` returns the range field of `derived h` as the arena computes it, including its
`0` for a handle that does not view (scratch tier closed, index past the count, unknown tag).

**Writers.** `mk_app(f, a)`, `mk_lam`, `mk_forall`, `mk_let`, `mk_proj` are the expression
constructors walks call: the ranges of the children first (`der_b`, on the memory before), then
`intern_*`, then, **if the table grew** (its two counts changed), the new node's range at
`idx * 2 + tier` of the result. A hit writes nothing (the node's range is already there). The
compound tables' `intern_*` are internal from now on: a node interned by them directly would have
no range (`DerRel.lean`'s relation would fail for it).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

abbrev ADER : ArrId := 42
abbrev LADER : ArrId := 43
abbrev FADER : ArrId := 44
abbrev LEDER : ArrId := 45
abbrev PJDER : ArrId := 46

/-! ## `der_b(h)`: the range field of `derived h` -/

/-- **The model of `der_b`.** -/
def derBW (m : Mem) (h : Word) : Word :=
  if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then 0
  else if h >>> 28 = 0 then
    if rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h then 0
    else satSuccW (rdW (m.arr64 BREC) (idxW h * 2 + tierW h))
  else if h >>> 28 = 4 then
    if rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h then 0
    else rdW (m.arr64 ADER) (idxW h * 2 + tierW h)
  else if h >>> 28 = 5 then
    if rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h then 0
    else rdW (m.arr64 LADER) (idxW h * 2 + tierW h)
  else if h >>> 28 = 6 then
    if rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h then 0
    else rdW (m.arr64 FADER) (idxW h * 2 + tierW h)
  else if h >>> 28 = 7 then
    if rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h then 0
    else rdW (m.arr64 LEDER) (idxW h * 2 + tierW h)
  else if h >>> 28 = 9 then
    if rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h then 0
    else rdW (m.arr64 PJDER) (idxW h * 2 + tierW h)
  else 0

def derB : FunDecl := lfn (h) locals (g, t, i, x) {
  g := h >> 28;
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { return 0 };
  if g == 0 {
    if CTL.u64[22 + t] <= i { return 0 };
    x := BREC.u64[i * 2 + t];
    return (x + 1) * u64(x < 32767) + 32767 * u64(32767 <= x)
  };
  if g == 4 { if CTL.u64[4 + t] <= i { return 0 }; return ADER.u64[i * 2 + t] };
  if g == 5 { if CTL.u64[28 + t] <= i { return 0 }; return LADER.u64[i * 2 + t] };
  if g == 6 { if CTL.u64[30 + t] <= i { return 0 }; return FADER.u64[i * 2 + t] };
  if g == 7 { if CTL.u64[20 + t] <= i { return 0 }; return LEDER.u64[i * 2 + t] };
  if g == 9 { if CTL.u64[32 + t] <= i { return 0 }; return PJDER.u64[i * 2 + t] };
  return 0
}

theorem derB_spec (p : Prog) (hp : p.lookup "der_b" = some derB) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "der_b" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = derBW s₀.mem h; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, derB]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [derBW, tierW, idxW, satSuccW]

/-! ## The tail of every `mk_*` -/

/-- The sum of a table's two counts `CTL[c] + CTL[c + 1]`. -/
def cnt2 (m : Mem) (c : Word) : Word := rdW (m.arr64 CTL) c + rdW (m.arr64 CTL) (c + 1)

/-- After `intern_*` (from `m` to `m₁`, result `r`): if the table grew (`cnt2` changed from `s`),
write the range `d` at `A[idx * 2 + tier]` of `r` (an `abort` past the array). -/
def derPutW (A : ArrId) (c : Word) (m₁ : Mem) (s r d : Word) : Option Mem :=
  if cnt2 m₁ c = s then some m₁
  else if m₁.len64 A ≤ idxW r * 2 + tierW r then none
  else some (m₁.set64 A (idxW r * 2 + tierW r) d)

/-- The result of a `mk_*`: `r` and the memory after the tail, or `none`. -/
def mkK (A : ArrId) (c s d : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    match derPutW A c m₁ s r d with
    | none => none
    | some m₂ => some (r, m₂)

theorem mkK_some (A : ArrId) (c s d r : Word) (m₁ : Mem) :
    mkK A c s d (some (r, m₁)) =
      (match derPutW A c m₁ s r d with | none => none | some m₂ => some (r, m₂)) := rfl

attribute [arena_grind =] mkK_some

/-! ## `mk_app(f, a)` -/

/-- **The model of `mk_app`.** -/
def mkAppW (m : Mem) (f a : Word) : Option (Word × Mem) :=
  if (f ||| a) >>> 32 ≠ 0 then none
  else mkK ADER 4 (cnt2 m 4) (maxW (derBW m f) (derBW m a)) (ainternW m f a)

def mkApp : FunDecl := lfn (f, a) locals (x, y, s, r, q) {
  if (f | a) >> 32 != 0 { abort };
  x := call der_b(f);
  y := call der_b(a);
  s := CTL.u64[4] + CTL.u64[5];
  r := call intern_app(f, a);
  if CTL.u64[4] + CTL.u64[5] != s {
    q := (r & 134217727) * 2 + ((r >> 27) & 1);
    if len(ADER.u64) <= q { abort };
    ADER.u64[q] := x + (y - x) * u64(x < y)
  };
  return r
}

/-! ## `mk_lam(ty, body)`, `mk_forall(ty, body)` -/

/-- **The model of `mk_lam`.** -/
def mkLamW (m : Mem) (t b : Word) : Option (Word × Mem) :=
  if (t ||| b) >>> 32 ≠ 0 then none
  else mkK LADER 28 (cnt2 m 28) (maxW (derBW m t) (satPredW (derBW m b))) (lainternW m t b)

def mkLam : FunDecl := lfn (t, b) locals (x, y, s, r, q) {
  if (t | b) >> 32 != 0 { abort };
  x := call der_b(t);
  y := call der_b(b);
  y := y - u64(0 < y) + u64(y == 32767);
  s := CTL.u64[28] + CTL.u64[29];
  r := call intern_lam(t, b);
  if CTL.u64[28] + CTL.u64[29] != s {
    q := (r & 134217727) * 2 + ((r >> 27) & 1);
    if len(LADER.u64) <= q { abort };
    LADER.u64[q] := x + (y - x) * u64(x < y)
  };
  return r
}

/-- **The model of `mk_forall`.** -/
def mkForallW (m : Mem) (t b : Word) : Option (Word × Mem) :=
  if (t ||| b) >>> 32 ≠ 0 then none
  else mkK FADER 30 (cnt2 m 30) (maxW (derBW m t) (satPredW (derBW m b))) (fainternW m t b)

def mkForall : FunDecl := lfn (t, b) locals (x, y, s, r, q) {
  if (t | b) >> 32 != 0 { abort };
  x := call der_b(t);
  y := call der_b(b);
  y := y - u64(0 < y) + u64(y == 32767);
  s := CTL.u64[30] + CTL.u64[31];
  r := call intern_forall(t, b);
  if CTL.u64[30] + CTL.u64[31] != s {
    q := (r & 134217727) * 2 + ((r >> 27) & 1);
    if len(FADER.u64) <= q { abort };
    FADER.u64[q] := x + (y - x) * u64(x < y)
  };
  return r
}

/-! ## `mk_let(ty, val, body)` -/

/-- **The model of `mk_let`.** -/
def mkLetW (m : Mem) (t v b : Word) : Option (Word × Mem) :=
  if (t ||| v ||| b) >>> 32 ≠ 0 then none
  else mkK LEDER 20 (cnt2 m 20)
    (maxW (maxW (derBW m t) (derBW m v)) (satPredW (derBW m b))) (leinternW m t v b)

def mkLet : FunDecl := lfn (t, v, b) locals (x, y, z, s, r, q) {
  if (t | v | b) >> 32 != 0 { abort };
  x := call der_b(t);
  y := call der_b(v);
  z := call der_b(b);
  s := CTL.u64[20] + CTL.u64[21];
  r := call intern_letE(t, v, b);
  if CTL.u64[20] + CTL.u64[21] != s {
    q := (r & 134217727) * 2 + ((r >> 27) & 1);
    if len(LEDER.u64) <= q { abort };
    x := x + (y - x) * u64(x < y);
    z := z - u64(0 < z) + u64(z == 32767);
    LEDER.u64[q] := x + (z - x) * u64(x < z)
  };
  return r
}

/-! ## `mk_proj(n, i, e)` -/

/-- **The model of `mk_proj`.** -/
def mkProjW (m : Mem) (n i e : Word) : Option (Word × Mem) :=
  if (n ||| e) >>> 32 ≠ 0 then none
  else mkK PJDER 32 (cnt2 m 32) (derBW m e) (pjinternW m n i e)

def mkProj : FunDecl := lfn (n, i, e) locals (x, s, r, q) {
  if (n | e) >> 32 != 0 { abort };
  x := call der_b(e);
  s := CTL.u64[32] + CTL.u64[33];
  r := call intern_proj(n, i, e);
  if CTL.u64[32] + CTL.u64[33] != s {
    q := (r & 134217727) * 2 + ((r >> 27) & 1);
    if len(PJDER.u64) <= q { abort };
    PJDER.u64[q] := x
  };
  return r
}

/-! ## The specs -/

section specs
variable (p : Prog) (hd : p.lookup "der_b" = some derB)

include hd in
theorem mkApp_spec (hpf : p.lookup "app_find" = some appFind)
    (hpp : p.lookup "app_push" = some appPush) (hpi : p.lookup "intern_app" = some internApp)
    (hp : p.lookup "mk_app" = some mkApp) (n : Nat) (s₀ : St) (f a : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_app" [f, a]
    ⦃fun r s' => LocEq s' s₀ ∧ mkAppW s₀.mem f a = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, mkApp]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        derB_spec p hd n, internApp_spec p hpf hpp hpi n] <;>
      finish [mkAppW, derPutW, cnt2, maxW, tierW, idxW]

include hd in
theorem mkLam_spec (hpf : p.lookup "lam_find" = some lamFind)
    (hpp : p.lookup "lam_push" = some lamPush) (hpi : p.lookup "intern_lam" = some internLamL)
    (hp : p.lookup "mk_lam" = some mkLam) (n : Nat) (s₀ : St) (t b : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_lam" [t, b]
    ⦃fun r s' => LocEq s' s₀ ∧ mkLamW s₀.mem t b = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, mkLam]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        derB_spec p hd n, internLamL_spec p hpf hpp hpi n] <;>
      finish [mkLamW, derPutW, cnt2, maxW, satPredW, tierW, idxW]

include hd in
theorem mkForall_spec (hpf : p.lookup "forall_find" = some forallFind)
    (hpp : p.lookup "forall_push" = some forallPush) (hpi : p.lookup "intern_forall" = some internForallL)
    (hp : p.lookup "mk_forall" = some mkForall) (n : Nat) (s₀ : St) (t b : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_forall" [t, b]
    ⦃fun r s' => LocEq s' s₀ ∧ mkForallW s₀.mem t b = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, mkForall]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        derB_spec p hd n, internForallL_spec p hpf hpp hpi n] <;>
      finish [mkForallW, derPutW, cnt2, maxW, satPredW, tierW, idxW]

include hd in
theorem mkLet_spec (hpf : p.lookup "letE_find" = some letFind)
    (hpp : p.lookup "letE_push" = some letPush) (hpi : p.lookup "intern_letE" = some internLet)
    (hp : p.lookup "mk_let" = some mkLet) (n : Nat) (s₀ : St) (t v b : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_let" [t, v, b]
    ⦃fun r s' => LocEq s' s₀ ∧ mkLetW s₀.mem t v b = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, mkLet]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        derB_spec p hd n, internLet_spec p hpf hpp hpi n] <;>
      finish (gen := 20) [mkLetW, derPutW, cnt2, maxW, satPredW, tierW, idxW]

include hd in
theorem mkProj_spec (hpf : p.lookup "proj_find" = some projFind)
    (hpp : p.lookup "proj_push" = some projPush) (hpi : p.lookup "intern_proj" = some internProj)
    (hp : p.lookup "mk_proj" = some mkProj) (n : Nat) (s₀ : St) (nm i e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_proj" [nm, i, e]
    ⦃fun r s' => LocEq s' s₀ ∧ mkProjW s₀.mem nm i e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, mkProj]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        derB_spec p hd n, internProj_spec p hpf hpp hpi n] <;>
      finish [mkProjW, derPutW, cnt2, maxW, satPredW, tierW, idxW]

end specs

end L.Arena
