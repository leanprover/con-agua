module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.FVarRange
import ConAgua.Census.Attr
public import ConAgua.Arena.LiftL
import ConAgua.Arena.GrindAttr
public import ConAgua.L.ModelGen
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `abstract1`: close a binder body, on `Inst1.lean`'s scaffolding

con-ron's `abstract1Go` (Lean twin `Arena/ExprOps.lean`) and its entry `abstract1Fast`: replace
`fvar d` by `bvar k`, bumping `k` under binders, memoized per `(node, k)` in `abs1C`, rebuilding
through the store. Differences from `instantiate1` (`Inst1.lean`, with `d ↦ k`, `v ↦ d`):

* **The cut-off is `fvarB ≤ d`** (`ab_fvb`): the packed fvar range (`der_b`'s second result,
  `derFW`), or, on the saturated branch alone (`= 32767`), the exact memoized `fr_memo`
  (`fvarRangeMemo`, `FVarRange.lean`), which clears and refills its own memo `fvarBC`.
* **The dispatch is its own function** (`ab_node`), because the cut-off's model has a memory
  effect (`fr_memo`): `abs_go(h, k, d, fu)` is `if fu == 0 { abort }; x := ab_fvb(h, fu - 1);
  if x <= d { return h }; return ab_node(h, k, d, fu - 1)`.
* **The depth counter `fu`** is the twin's `fuel` exactly: `abstract1Go` fails at
  `0`, else reads `fvarB fuel h` and runs its arms at the decremented `fuel`; every arm passes the
  same `fu` to its children, `ab_fvb(h, fu)` passes it to `fr_memo`.
* **The `fvar` arm** reads the record's index word (`viewFVarIdx`): `idx = d` gives
  `intern_bvar(k)`, else `h`.
* **The arms rebuild only on change** (`internRebuilt*`: `h` itself when every child came back
  equal), `rbAppW` … below.
* **The memo `abs1C`** is a new table: array 49 `ABMEMO`, stamp `CTL[48]`, count `CTL[49]`,
  `lfKey`'s two-word key codec. It is not in `MemosR` (`scratch_enter` clears the memos of
  `MemosR` by name, `abs1C` is not one of them; DESIGN.md, lane `exprops3`): the refinement keeps
  it in a tier of its own (`Abs1Refine.lean`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- `abs1C`: array 49, stamp `CTL[48]`, count `CTL[49]`. -/
abbrev abSch : MemoSch := ⟨ABMEMO, 48⟩

/-! ## The L code -/

/-- **The model of `fr_memo` at L fuel `n`** (the call's own fuel; `frMemo_spec` is at `n + 1`). -/
def fvbN : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, h, fu => frMemoW n m h fu

/-- Record `r` at `(h, k)` in the `abstract1` memo and return it. -/
def asetK (h k : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    match msetG abSch m₁ h k r with
    | none => none
    | some m₂ => some (r, m₂)

/-- `internRebuiltApp`: `h` itself when both children came back equal, else `mk_app`. -/
def rbAppW (m : Mem) (h f a x y : Word) : Option (Word × Mem) :=
  if x = f ∧ y = a then some (h, m) else mkAppW m x y
def rbLamW (m : Mem) (h f a x y : Word) : Option (Word × Mem) :=
  if x = f ∧ y = a then some (h, m) else mkLamW m x y
def rbForallW (m : Mem) (h f a x y : Word) : Option (Word × Mem) :=
  if x = f ∧ y = a then some (h, m) else mkForallW m x y
def rbLetW (m : Mem) (h f a b x y z : Word) : Option (Word × Mem) :=
  if x = f ∧ y = a ∧ z = b then some (h, m) else mkLetW m x y z
def rbProjW (m : Mem) (h nw iw e x : Word) : Option (Word × Mem) :=
  if x = e then some (h, m) else mkProjW m nw iw x

/-- con-ron: ConRon/Arena/ExprOps.lean:1574-1580 ConRon.Arena.fvarB -/
@[l_impl ConRon.Arena.fvarB]
def abFvb : FunDecl := lfn (h, fu) locals (x, xf, r) {
  (x, xf) := call der_b(h);
  if xf == 32767 { r := call fr_memo(h, fu); return r };
  return xf
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1608-1628 ConRon.Arena.abstract1Go -/
@[l_impl ConRon.Arena.abstract1Go]
def absGo : FunDecl := lfn (h, k, d, fu) locals (x, r) {
  if fu == 0 { abort };
  x := call ab_fvb(h, fu - 1);
  if x <= d { return h };
  r := call ab_node(h, k, d, fu - 1);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1608-1628 ConRon.Arena.abstract1Go
con-ron: ConRon/Arena/ExprOps.lean:1599-1604 ConRon.Arena.abstract1ArmFVar -/
@[l_impl ConRon.Arena.abstract1ArmFVar]
def absNode : FunDecl := lfn (h, k, d, fu) locals (x, g, t, i, r) {
  g := h >> 28;
  if g == 4 { r := call abs_app(h, k, d, fu); return r };
  if g == 5 { r := call abs_lam(h, k, d, fu); return r };
  if g == 6 { r := call abs_forall(h, k, d, fu); return r };
  if g == 1 {
    t := ⟦h⟧.tier;
    i := ⟦h⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if FVAR⟨t⟩.count <= i { abort };
    x := FVAR⟨t, i⟩.i;
    if x == d { r := call intern_bvar(k); return r };
    return h
  };
  if g == 7 { r := call abs_let(h, k, d, fu); return r };
  if g == 9 { r := call abs_proj(h, k, d, fu); return r };
  return h
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1630-1644 ConRon.Arena.abstract1ArmApp -/
@[l_impl ConRon.Arena.abstract1ArmApp]
def absApp : FunDecl := lfn (h, k, d, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  (fd, j, e0) := call ab_find(h, k);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if APP⟨t⟩.count <= i { abort };
  f := APP⟨t, i⟩.f;
  a := APP⟨t, i⟩.a;
  x := call abs_go(f, k, d, fu);
  y := call abs_go(a, k, d, fu);
  if x == f && y == a { r := h } else { r := call mk_app(x, y) };
  (fd, j, e0) := call ab_find(h, k);
  u := call ab_put(h, k, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1646-1661 ConRon.Arena.abstract1ArmBind -/
@[l_impl ConRon.Arena.abstract1ArmBind]
def absLam : FunDecl := lfn (h, k, d, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if k + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, k);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LAM⟨t⟩.count <= i { abort };
  f := LAM⟨t, i⟩.ty;
  a := LAM⟨t, i⟩.b;
  x := call abs_go(f, k, d, fu);
  y := call abs_go(a, k + 1, d, fu);
  if x == f && y == a { r := h } else { r := call mk_lam(x, y) };
  (fd, j, e0) := call ab_find(h, k);
  u := call ab_put(h, k, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1646-1661 ConRon.Arena.abstract1ArmBind -/
@[l_impl ConRon.Arena.abstract1ArmBind]
def absForall : FunDecl := lfn (h, k, d, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if k + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, k);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if FORALL⟨t⟩.count <= i { abort };
  f := FORALL⟨t, i⟩.ty;
  a := FORALL⟨t, i⟩.b;
  x := call abs_go(f, k, d, fu);
  y := call abs_go(a, k + 1, d, fu);
  if x == f && y == a { r := h } else { r := call mk_forall(x, y) };
  (fd, j, e0) := call ab_find(h, k);
  u := call ab_put(h, k, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1663-1678 ConRon.Arena.abstract1ArmLet -/
@[l_impl ConRon.Arena.abstract1ArmLet]
def absLet : FunDecl := lfn (h, k, d, fu) locals (fd, j, e0, t, i, f, a, b, x, y, z, r, u) {
  if k + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, k);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LET⟨t⟩.count <= i { abort };
  f := LET⟨t, i⟩.ty;
  a := LET⟨t, i⟩.v;
  b := LET⟨t, i⟩.b;
  x := call abs_go(f, k, d, fu);
  y := call abs_go(a, k, d, fu);
  z := call abs_go(b, k + 1, d, fu);
  if x == f && y == a && z == b { r := h } else { r := call mk_let(x, y, z) };
  (fd, j, e0) := call ab_find(h, k);
  u := call ab_put(h, k, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1680-1694 ConRon.Arena.abstract1ArmProj -/
@[l_impl ConRon.Arena.abstract1ArmProj]
def absProj : FunDecl := lfn (h, k, d, fu) locals (fd, j, e0, t, i, nm, ix, e, x, r, u) {
  (fd, j, e0) := call ab_find(h, k);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if PROJ⟨t⟩.count <= i { abort };
  nm := PROJ⟨t, i⟩.n;
  ix := PROJ⟨t, i⟩.i;
  e := PROJ⟨t, i⟩.e;
  x := call abs_go(e, k, d, fu);
  if x == e { r := h } else { r := call mk_proj(nm, ix, x) };
  (fd, j, e0) := call ab_find(h, k);
  u := call ab_put(h, k, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1719-1725 ConRon.Arena.abstract1Fast -/
@[l_impl ConRon.Arena.abstract1Fast]
def absEntry : FunDecl := lfn (e, d, k) locals (r, u) {
  u := call ab_clear();
  r := call abs_go(e, k, d, 4000000000);
  u := call ab_clear();
  return r & 4294967295
}

/-- After the walk: clear the memo again; the handle word is returned masked to 32 bits (the
callers' contract `HW`; `decE` reads the same handle). -/
def aclrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    if rdW (m₁.arr64 CTL) 48 + 2 = 0 then none else some (r &&& 4294967295, mclearG abSch m₁)

theorem aclrK_some (r : Word) (m₁ : Mem) (h0 : rdW (m₁.arr64 CTL) 48 + 2 ≠ 0) :
    aclrK (some (r, m₁)) = some (r &&& 4294967295, mclearG abSch m₁) := by simp [aclrK, h0]

grind_pattern [arena_grind] aclrK_some => aclrK (some (r, m₁))

/-! ## The program and its specs -/

/-- The walk without its entry, `fvarRangeProg` and `liftProg` (the `mk_*`, the stores). -/
def absWalkProg : Prog :=
  [("ab_find", memoFindG abSch), ("ab_put", memoPutG abSch), ("ab_clear", memoClearG abSch),
    ("ab_fvb", abFvb), ("abs_go", absGo), ("ab_node", absNode), ("abs_app", absApp),
    ("abs_lam", absLam), ("abs_forall", absForall), ("abs_let", absLet), ("abs_proj", absProj)] ++
  fvarRangeProg ++ liftProg

/-- What the specs need of the program: `absWalkProg`'s functions. -/
def AbsProg (p : Prog) : Prop := ProgHas p absWalkProg

theorem AbsProg.base {p : Prog} (hp : AbsProg p) : LiftProg p := by
  have h : ProgHas p liftProg := hp.right
  unfold LiftProg liftProgFns; repeat (first | exact ProgHas.nil | refine ProgHas.cons (h.get _) ?_)

section specs
variable (p : Prog) (hp : AbsProg p)

include hp in
/-- `fr_memo` at every fuel (`fvbN`: `frMemo_spec`, and fuel `0` aborts). -/
theorem fvbN_spec (n : Nat) (s₀ : St) (h fu : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "fr_memo" [h, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ fvbN n s₀.mem h fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases n with
  | zero => rw [invoke_eq _ (hp.get "fr_memo")]; simp only [callFn, frMemo]; vcgen [exec] <;> grind
  | succ n =>
    exact frMemo_spec p (hp.get "fm_find") (hp.get "fm_put") (hp.get "fr_go")
      (hp.get "fr_node") (hp.get "fm_clear") (hp.get "fr_memo") n s₀ h fu


end specs

/-! ## The models and the specs (generated) -/

l_model absGo_spec (p : Prog) (hp : AbsProg p)
  fns [(hp.get "ab_fvb") ↦ fvbW, (hp.get "abs_go") ↦ absW, (hp.get "ab_node") ↦ absNodeW,
    (hp.get "abs_app") ↦ absAppW, (hp.get "abs_lam") ↦ absLamW, (hp.get "abs_forall") ↦ absForallW,
    (hp.get "abs_let") ↦ absLetW, (hp.get "abs_proj") ↦ absProjW]
  specs [derB_spec p (hp.get "der_b") n, fvbN_spec p hp n,
    internBVar_spec p (hp.get "bvar_find") (hp.get "bvar_push") (hp.get "intern_bvar") n,
    memoFindG_spec abSch p _ (hp.get "ab_find") n, memoPutG_spec abSch p _ (hp.get "ab_put") n,
    mkApp_spec p (hp.get "der_b") (hp.get "app_find") (hp.get "app_push") (hp.get "intern_app") (hp.get "mk_app") n,
    mkLam_spec p (hp.get "der_b") (hp.get "lam_find") (hp.get "lam_push") (hp.get "intern_lam") (hp.get "mk_lam") n,
    mkForall_spec p (hp.get "der_b") (hp.get "forall_find") (hp.get "forall_push") (hp.get "intern_forall") (hp.get "mk_forall") n,
    mkLet_spec p (hp.get "der_b") (hp.get "letE_find") (hp.get "letE_push") (hp.get "intern_letE") (hp.get "mk_let") n,
    mkProj_spec p (hp.get "der_b") (hp.get "proj_find") (hp.get "proj_push") (hp.get "intern_proj") (hp.get "mk_proj") n]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] gen 20 heartbeats 1000000

/-- `ab_fvb` is its model. -/
theorem abFvb_spec (p : Prog) (hp : AbsProg p) (n : Nat) (s₀ : St) (h fu : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ab_fvb" [h, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ fvbW n s₀.mem h fu = some (r.headD 0, s'.mem); ⊤⦄ :=
  (absGo_spec p hp n).1 s₀ h fu

/-! ### The memo write of the generated continuations is `asetK` -/

theorem absAppW.j1_eq (h k r : Word) (m : Mem) :
    absAppW.j1 h k r m = asetK h k (some (r, m)) := by
  by_cases hf : mfindG abSch m h k = []
  · simp [absAppW.j1, asetK, msetG, hf]
  · rw [absAppW.j1.arm1 _ _ _ _ hf]; simp [asetK, msetG_eq _ _ _ _ _ hf]
    cases mputG abSch m h k r ((mfindG abSch m h k).headD 0) ((mfindG abSch m h k).tail.headD 0) <;>
      simp [absAppW.k_ab_put]

theorem absAppW.k_mk_app_eq (h k : Word) (o : Option (Word × Mem)) :
    absAppW.k_mk_app h k o = asetK h k o := by
  cases o with
  | none => rfl
  | some q => obtain ⟨r, m⟩ := q; simp [absAppW.k_mk_app, absAppW.j1_eq]

theorem absAppW.k_abs_go_2.set (h k f a x y : Word) (m₂ : Mem) :
    absAppW.k_abs_go_2 h k f a x (some (y, m₂)) = asetK h k (rbAppW m₂ h f a x y) := by
  by_cases hc : x = f ∧ y = a
  · rw [absAppW.k_abs_go_2.arm1 _ _ _ _ _ _ _ hc, absAppW.j1_eq]; simp [rbAppW, hc]
  · rw [absAppW.k_abs_go_2.arm2 _ _ _ _ _ _ _ hc, absAppW.k_mk_app_eq]; simp [rbAppW, hc]

theorem absLamW.k_abs_go_2.set (h k f a x y : Word) (m₂ : Mem) :
    absLamW.k_abs_go_2 h k f a x (some (y, m₂)) = asetK h k (rbLamW m₂ h f a x y) := by
  by_cases hc : x = f ∧ y = a
  · rw [absLamW.k_abs_go_2.arm1 _ _ _ _ _ _ _ hc, absAppW.j1_eq]; simp [rbLamW, hc]
  · rw [absLamW.k_abs_go_2.arm2 _ _ _ _ _ _ _ hc, absAppW.k_mk_app_eq]; simp [rbLamW, hc]

theorem absForallW.k_abs_go_2.set (h k f a x y : Word) (m₂ : Mem) :
    absForallW.k_abs_go_2 h k f a x (some (y, m₂)) = asetK h k (rbForallW m₂ h f a x y) := by
  by_cases hc : x = f ∧ y = a
  · rw [absForallW.k_abs_go_2.arm1 _ _ _ _ _ _ _ hc, absAppW.j1_eq]; simp [rbForallW, hc]
  · rw [absForallW.k_abs_go_2.arm2 _ _ _ _ _ _ _ hc, absAppW.k_mk_app_eq]; simp [rbForallW, hc]

theorem absLetW.k_abs_go_3.set (h k f a b x y z : Word) (m₃ : Mem) :
    absLetW.k_abs_go_3 h k f a b x y (some (z, m₃)) = asetK h k (rbLetW m₃ h f a b x y z) := by
  by_cases hc : x = f ∧ y = a ∧ z = b
  · rw [absLetW.k_abs_go_3.arm1 _ _ _ _ _ _ _ _ _ hc, absAppW.j1_eq]; simp [rbLetW, hc]
  · rw [absLetW.k_abs_go_3.arm2 _ _ _ _ _ _ _ _ _ hc, absAppW.k_mk_app_eq]; simp [rbLetW, hc]

theorem absProjW.k_abs_go.set (h k nm ix e x : Word) (m₁ : Mem) :
    absProjW.k_abs_go h k nm ix e (some (x, m₁)) = asetK h k (rbProjW m₁ h nm ix e x) := by
  by_cases hc : x = e
  · rw [absProjW.k_abs_go.arm1 _ _ _ _ _ _ _ hc, absAppW.j1_eq]; simp [rbProjW, hc]
  · rw [absProjW.k_abs_go.arm2 _ _ _ _ _ _ _ hc, absAppW.k_mk_app_eq]; simp [rbProjW, hc]

theorem absW.k_ab_fvb.ite (n : Nat) (h k d fu x : Word) (m₁ : Mem) :
    absW.k_ab_fvb n h k d fu (some (x, m₁)) =
      if x ≤ d then some (h, m₁) else absNodeW n m₁ h k d (fu - 1) := by
  by_cases hc : x ≤ d
  · rw [absW.k_ab_fvb.arm1 _ _ _ _ _ _ _ hc, ite_eq_left hc]
  · rw [absW.k_ab_fvb.arm2 _ _ _ _ _ _ _ hc, ite_eq_right hc]

theorem fvbN_succ (n : Nat) (m : Mem) (h fu : Word) : fvbN (n + 1) m h fu = frMemoW n m h fu := rfl

end L.Arena
