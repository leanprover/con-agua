import ConAgua.Arena.WhnfCoreApp

/-!
# `whnf_app` refines `whnfApp` (split from `WhnfCoreApp.lean`)

The loop as named blocks, the models of its arms, the fuel induction (`appFull_ref`) and
`whnfApp_refines`. `WhnfCoreApp.lean` has the helpers and `beta_peel`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `whnf_app`: the loop as named blocks

The loop body is the λ arm (`whnfAppLamW`: `beta_peel` and the return) and the rest
(`whnfAppRestW`: the push, then the ι step `whnfAppIotaW`, then the next round); a block spliced
into the middle of a sequence must be one statement, so the push is not a block of its own. The loop (`whnfAppW`) splices them; `whnfAppL'` splices the loop. All are
`rfl`-equal to `whnfAppL` of `WhnfCore.lean`. -/

/-- The λ-head arm of the loop body. -/
def whnfAppLamW : Stmt := lblk (mode, vis, d, v, hd, vo, vn, same, ao, an, i, top, a, node, ap, st, e2, e3, t, x) {
  if v >> 28 == 5 {
    t := ⟦v⟧.tier;
    x := ⟦v⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if LAM⟨t⟩.count <= x { abort };
    (st, e3) := call beta_peel(LAM⟨t, x⟩.b, a, ao, an, i + 1);
    CTL.u64[136] := top;
    return (st, e3)
  }
}

/-- The ι step at a constant head. -/
def whnfAppIotaW : Stmt := lblk (mode, vis, d, v, hd, vo, vn, same, ao, an, i, top, a, node, ap, st, e2, e3, t, x) {
  if hd >> 28 == 3 {
    (st, e2) := call iota_rec_at(mode, vis, d, hd, vo, vn);
    if st != 0 {
      e3 := call mk_app_n_from(e2, ao, an, i + 1);
      CTL.u64[136] := top;
      return (1, e3)
    }
  }
}

/-- The rest of the loop body after the λ arm: the push, the ι step, the next round. -/
def whnfAppRestW : Stmt := lblk (mode, vis, d, v, hd, vo, vn, same, ao, an, i, top, a, node, ap, st, e2, e3, t, x) {
  if same != 0 { ap := node } else { ap := call mk_app(v, a) };
  same := u64(ap == node);
  if len(SPN.u64) <= vo + vn { abort };
  SPN.u64[vo + vn] := a;
  vn += 1;
  CTL.u64[136] := vo + vn;
  ⟪whnfAppIotaW⟫;
  v := ap;
  i += 1
}

/-- The loop body of `whnfAppL` (WhnfCore.lean), named for its spec. -/
def whnfAppBodyW : Stmt := lblk (mode, vis, d, v, hd, vo, vn, same, ao, an, i, top, a, node, ap, st, e2, e3, t, x) {
  a := SPN.u64[ao + i];
  node := SPN.u64[ao + an + i];
  ⟪whnfAppLamW⟫;
  ⟪whnfAppRestW⟫
}

/-- The loop of `whnfAppL` (WhnfCore.lean), named for its spec. -/
def whnfAppW : Stmt := lblk (mode, vis, d, v, hd, vo, vn, same, ao, an, i, top, a, node, ap, st, e2, e3, t, x) {
  while i < an {
    ⟪whnfAppBodyW⟫
  }
}

/-- `whnfAppL`, with its loop spliced from `whnfAppW`.
con-ron: ConRon/Arena/Core.lean:2223-2254 ConRon.Arena.whnfApp -/
def whnfAppL' : FunDecl :=
    lfn (mode, vis, d, v, hd, vo, vn, same, ao, an, i) locals (top, a, node, ap, st, e2, e3, t, x) {
  top := CTL.u64[136];
  ⟪whnfAppW⟫;
  CTL.u64[136] := top;
  return (0, v)
}

theorem whnfAppL_eq : whnfAppL = whnfAppL' := rfl



/-! ## The models of the arms -/

/-- How an arm ends: by a `return` (`st`, `r`, the memory), or by falling through with the memory. -/
inductive StepOut
  | ret (st r : Word) (m : Mem)
  | cont (m : Mem)

/-- The model of the λ arm at callee fuel `k`. -/
def lamW (p : Prog) (k : Nat) (m : Mem) (v a ao an i top : Word) : Option StepOut :=
  if v >>> 28 = 5 then
    if tierW v ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m LAM (tierW v) ≤ idxW v then none
    else
      match callW p k "beta_peel" [tfld m LAM (tierW v) (idxW v) 1, a, ao, an,
          i + 1] m with
      | none => none
      | some (r, m₁) => some (.ret (r.headD 0) (r.tail.headD 0) (m₁.set64 CTL 136 top))
  else some (.cont m)

theorem whnfAppLamW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p (n + 1) whnfAppLamW
    ⦃fun r s' => match lamW p n s₀.mem (s₀.loc 3) (s₀.loc 12) (s₀.loc 8) (s₀.loc 9) (s₀.loc 10)
        (s₀.loc 11) with
      | none => False
      | some (.ret st rv m) => r = .ret [st, rv] ∧ s'.mem = m ∧
          (136 : Word).toNat < (s'.mem.arr64 CTL).size
      | some (.cont _) => r = .normal ∧ s'.mem = s₀.mem ∧
          s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = s₀.loc 7 ∧ s'.loc 8 = s₀.loc 8 ∧ s'.loc 9 = s₀.loc 9 ∧ s'.loc 10 = s₀.loc 10 ∧ s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧ s'.loc 14 = s₀.loc 14 ∧ s'.loc 15 = s₀.loc 15 ∧ s'.loc 16 = s₀.loc 16 ∧ s'.loc 17 = s₀.loc 17 ∧ s'.loc 18 = s₀.loc 18 ∧ s'.loc 19 = s₀.loc 19; ⊤⦄ := by
  rw [exec]; unfold whnfAppLamW L.Notation.blk
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM,
      evalE_tierE, evalE_idxE, st64,
      callW_spec p n "beta_peel"] <;>
    finish [lamW, tierW, idxW, St.setLoc_mem]

/-- The model of the ι arm at callee fuel `k`. -/
def iotaW (p : Prog) (k : Nat) (m : Mem) (mode vis d hd vo vn ao an i top : Word) :
    Option StepOut :=
  if hd >>> 28 = 3 then
    match callW p k "iota_rec_at" [mode, vis, d, hd, vo, vn] m with
    | none => none
    | some (r, m₃) =>
      if r.headD 0 ≠ 0 then
        match callW p k "mk_app_n_from" [r.tail.headD 0, ao, an, i + 1] m₃ with
        | none => none
        | some (r', m₄) => some (.ret 1 (r'.headD 0) (m₄.set64 CTL 136 top))
      else some (.cont m₃)
  else some (.cont m)

theorem whnfAppIotaW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p (n + 1) whnfAppIotaW
    ⦃fun r s' => match iotaW p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 4) (s₀.loc 5)
        (s₀.loc 6) (s₀.loc 8) (s₀.loc 9) (s₀.loc 10) (s₀.loc 11) with
      | none => False
      | some (.ret st rv m) => r = .ret [st, rv] ∧ s'.mem = m ∧
          (136 : Word).toNat < (s'.mem.arr64 CTL).size
      | some (.cont m) => r = .normal ∧ s'.mem = m ∧
          ∀ y, y ≠ 15 → y ≠ 16 → s'.loc y = s₀.loc y; ⊤⦄ := by
  rw [exec]; unfold whnfAppIotaW L.Notation.blk
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "iota_rec_at", callW_spec p n "mk_app_n_from"] <;>
    finish [iotaW, St.setLoc_mem]

/-- The next spine node of the walk: the saved node (`same`), else `mk_app(v, a)`. -/
def apW (p : Prog) (k : Nat) (m : Mem) (v same a node : Word) : Option (Word × Mem) :=
  if same ≠ 0 then some (node, m)
  else match callW p k "mk_app" [v, a] m with
    | none => none
    | some (r, m₁) => some (r.headD 0, m₁)

/-- How the rest of the loop body ends: by a `return`, or into the next round with the memory and
the next `v`, `vn`, `same`. -/
inductive RestOut
  | ret (st r : Word) (m : Mem)
  | cont (m : Mem) (v vn same : Word)

/-- The model of the rest of the loop body at callee fuel `k`: the push (its `CTL` write checked
in bounds, as `st64` does), then the ι arm. -/
def appRestW (p : Prog) (k : Nat) (m : Mem) (mode vis d v hd vo vn same ao an i top a node : Word) :
    Option RestOut :=
  match apW p k m v same a node with
  | none => none
  | some (ap, m₁) =>
    if m₁.len64 SPN ≤ vo + vn then none
    else if (136 : Word).toNat < (m₁.arr64 CTL).size then
      match iotaW p k ((m₁.set64 SPN (vo + vn) a).set64 CTL 136 (vo + vn + 1)) mode vis d hd vo
          (vn + 1) ao an i top with
      | none => none
      | some (.ret st r m') => some (.ret st r m')
      | some (.cont m') => some (.cont m' ap (vn + 1) (Cmp.evalW .eq ap node))
    else none

theorem whnfAppRestW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p (n + 1) whnfAppRestW
    ⦃fun r s' => match appRestW p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)
        (s₀.loc 5) (s₀.loc 6) (s₀.loc 7) (s₀.loc 8) (s₀.loc 9) (s₀.loc 10) (s₀.loc 11)
        (s₀.loc 12) (s₀.loc 13) with
      | none => False
      | some (.ret st rv m) => r = .ret [st, rv] ∧ s'.mem = m ∧
          (136 : Word).toNat < (s'.mem.arr64 CTL).size
      | some (.cont m v vn same) => r = .normal ∧ s'.mem = m ∧ s'.loc 3 = v ∧ s'.loc 6 = vn ∧
          s'.loc 7 = same ∧ s'.loc 10 = s₀.loc 10 + 1 ∧ s'.loc 0 = s₀.loc 0 ∧
          s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 4 = s₀.loc 4 ∧
          s'.loc 5 = s₀.loc 5 ∧ s'.loc 8 = s₀.loc 8 ∧ s'.loc 9 = s₀.loc 9 ∧
          s'.loc 11 = s₀.loc 11; ⊤⦄ := by
  rw [exec]; unfold whnfAppRestW L.Notation.blk
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "mk_app", fun s => Triple.step_exec (whnfAppIotaW_spec p n s)] <;>
    finish [appRestW, apW]

theorem getElem_toNat_rdW (a : Array Word) (x : Word) (h : x.toNat < a.size) :
    a[x.toNat]'h = rdW a x := by simp [rdW, h]

theorem BinOp.add_eval' (a b : Word) : BinOp.add.eval a b = a + b := rfl

/-- The model of the loop body at callee fuel `k`. -/
def bodyW (p : Prog) (k : Nat) (m : Mem) (mode vis d v hd vo vn same ao an i top : Word) :
    Option RestOut :=
  match lamW p k m v (rdW (m.arr64 SPN) (ao + i)) ao an i top with
  | none => none
  | some (.ret st r m') => some (.ret st r m')
  | some (.cont _) =>
    appRestW p k m mode vis d v hd vo vn same ao an i top (rdW (m.arr64 SPN) (ao + i))
      (rdW (m.arr64 SPN) (ao + an + i))

theorem whnfAppBodyW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p (n + 1) whnfAppBodyW
    ⦃fun r s' => match bodyW p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)
        (s₀.loc 5) (s₀.loc 6) (s₀.loc 7) (s₀.loc 8) (s₀.loc 9) (s₀.loc 10) (s₀.loc 11) with
      | none => False
      | some (.ret st rv m) => r = .ret [st, rv] ∧ s'.mem = m ∧
          (136 : Word).toNat < (s'.mem.arr64 CTL).size
      | some (.cont m v vn same) => r = .normal ∧ s'.mem = m ∧ s'.loc 3 = v ∧ s'.loc 6 = vn ∧
          s'.loc 7 = same ∧ s'.loc 10 = s₀.loc 10 + 1 ∧ s'.loc 0 = s₀.loc 0 ∧
          s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 4 = s₀.loc 4 ∧
          s'.loc 5 = s₀.loc 5 ∧ s'.loc 8 = s₀.loc 8 ∧ s'.loc 9 = s₀.loc 9 ∧
          s'.loc 11 = s₀.loc 11; ⊤⦄ := by
  rw [exec]; unfold whnfAppBodyW L.Notation.blk
  vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    fun s => Triple.step_exec (whnfAppLamW_spec p n s),
    fun s => Triple.step_exec (whnfAppRestW_spec p n s)] <;>
  simp_all [bodyW, St.setLoc_loc, St.setLoc_mem, getElem_toNat_rdW, BinOp.add_eval', SPN,
    -UInt64.toNat_add] <;>
  (split at * <;> first | grind | simp_all)

/-- How a loop ends: by a `return` (`st`, `r`, the memory) or by its condition failing (`v`, the
memory). -/
inductive AppOut
  | ret (st r : Word) (m : Mem)
  | exit (v : Word) (m : Mem)

/-- **The model of the `whnf_app` loop** at L fuel `k`. -/
def appLoop (p : Prog) (mode vis d hd vo ao an top : Word) : Nat → Mem → Word → Word → Word →
    Word → Option AppOut
  | 0, _, _, _, _, _ => none
  | k + 1, m, v, vn, same, i =>
    if i < an then
      match bodyW p k m mode vis d v hd vo vn same ao an i top with
      | none => none
      | some (.ret st r m') => some (.ret st r m')
      | some (.cont m' v' vn' same') =>
        appLoop p mode vis d hd vo ao an top k m' v' vn' same' (i + 1)
    else some (.exit v m)

theorem whnfAppW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n whnfAppW
    ⦃fun r s' => (r = .normal ∧ s'.loc 11 = s₀.loc 11 ∧
        appLoop p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 8) (s₀.loc 9)
          (s₀.loc 11) n s₀.mem (s₀.loc 3) (s₀.loc 6) (s₀.loc 7) (s₀.loc 10) =
          some (.exit (s'.loc 3) s'.mem)) ∨
      (∃ st rv, r = .ret [st, rv] ∧ (136 : Word).toNat < (s'.mem.arr64 CTL).size ∧
        appLoop p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 4) (s₀.loc 5) (s₀.loc 8) (s₀.loc 9)
          (s₀.loc 11) n s₀.mem (s₀.loc 3) (s₀.loc 6) (s₀.loc 7) (s₀.loc 10) =
          some (.ret st rv s'.mem)); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := whnfAppW) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih,
        fun s => Triple.step_exec (whnfAppBodyW_spec p n s)] <;>
      finish [appLoop]

theorem getElem_ctl136 (a : Array Word) (h : 136 < a.size) : a[136]'h = rdW a 136 := by
  simp [rdW, h]

/-- **The model of `whnf_app`** at L fuel `n + 1`. -/
def appFnW (p : Prog) (n : Nat) (m : Mem) (mode vis d v hd vo vn same ao an i : Word) :
    Option (Word × Word × Mem) :=
  match appLoop p mode vis d hd vo ao an (rdW (m.arr64 CTL) 136) (n + 1) m v vn same i with
  | none => none
  | some (.ret st r m') => some (st, r, m')
  | some (.exit v' m') => some (0, v', m'.set64 CTL 136 (rdW (m.arr64 CTL) 136))

theorem whnfApp_spec (p : Prog) (hp : p.lookup "whnf_app" = some whnfAppL) (n : Nat) (s₀ : St)
    (mode vis d v hd vo vn same ao an i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "whnf_app" [mode, vis, d, v, hd, vo, vn, same, ao, an, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      appFnW p n s₀.mem mode vis d v hd vo vn same ao an i =
        some (r.headD 0, r.tail.headD 0, s'.mem) ∧
      (136 : Word).toNat < (s₀.mem.arr64 CTL).size ∧
      (136 : Word).toNat < (s'.mem.arr64 CTL).size; ⊤⦄ := by
  rw [invoke_eq _ hp, whnfAppL_eq]
  simp only [callFn, whnfAppL']
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    fun s => Triple.step_exec (whnfAppW_spec p (n + 1) s)] <;>
  simp_all [appFnW, LocEq, St.setLoc_loc, St.setLoc_mem, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr, getElem_ctl136, CTL, size_set64] <;>
  first | assumption | grind

/-! ## `whnf_app` refines `whnfApp` -/

/-- The loop with its tail (the top put back): the `whnf_app` body after its prologue. -/
def appFull (p : Prog) (mode vis d hd vo ao an top : Word) (k : Nat) (m : Mem)
    (v vn same i : Word) : Option (Word × Word × Mem) :=
  match appLoop p mode vis d hd vo ao an top k m v vn same i with
  | none => none
  | some (.ret st r m') => some (st, r, m')
  | some (.exit v' m') => some (0, v', m'.set64 CTL 136 top)

theorem appFnW_eq (p : Prog) (n : Nat) (m : Mem) (mode vis d v hd vo vn same ao an i : Word) :
    appFnW p n m mode vis d v hd vo vn same ao an i =
      appFull p mode vis d hd vo ao an (rdW (m.arr64 CTL) 136) (n + 1) m v vn same i := by
  unfold appFnW appFull; rfl

theorem appFull_zero {p : Prog} {mode vis d hd vo ao an top : Word} {m : Mem} {v vn same i : Word} :
    appFull p mode vis d hd vo ao an top 0 m v vn same i = none := rfl

theorem appFull_exit {p : Prog} {mode vis d hd vo ao an top : Word} {k : Nat} {m : Mem}
    {v vn same i : Word} (h : ¬ i < an) :
    appFull p mode vis d hd vo ao an top (k + 1) m v vn same i =
      some (0, v, m.set64 CTL 136 top) := by
  simp [appFull, appLoop, h]

theorem appFull_body {p : Prog} {mode vis d hd vo ao an top : Word} {k : Nat} {m : Mem}
    {v vn same i : Word} (h : i < an) :
    appFull p mode vis d hd vo ao an top (k + 1) m v vn same i =
      match bodyW p k m mode vis d v hd vo vn same ao an i top with
      | none => none
      | some (.ret st r m') => some (st, r, m')
      | some (.cont m' v' vn' same') => appFull p mode vis d hd vo ao an top k m' v' vn' same' (i + 1) := by
  simp only [appFull, appLoop, h, ↓reduceIte]
  rcases bodyW p k m mode vis d v hd vo vn same ao an i top with _ | _ | _ <;> simp

theorem bodyW_lam {p : Prog} {k : Nat} {m : Mem} {mode vis d v hd vo vn same ao an i top : Word}
    (h : v >>> 28 = 5) :
    bodyW p k m mode vis d v hd vo vn same ao an i top =
      if tierW v ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
      else if tcnt m LAM (tierW v) ≤ idxW v then none
      else
        match callW p k "beta_peel" [tfld m LAM (tierW v) (idxW v) 1,
            rdW (m.arr64 SPN) (ao + i), ao, an, i + 1] m with
        | none => none
        | some (r, m₁) => some (.ret (r.headD 0) (r.tail.headD 0) (m₁.set64 CTL 136 top)) := by
  simp only [bodyW, lamW, h, ↓reduceIte]
  by_cases c1 : tierW v ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [c1]
  by_cases c2 : tcnt m LAM (tierW v) ≤ idxW v
  · simp [c1, c2]
  simp only [c1, c2, ↓reduceIte]
  rcases callW p k "beta_peel" _ m with _ | ⟨r, m₁⟩ <;> rfl

theorem bodyW_nolam {p : Prog} {k : Nat} {m : Mem} {mode vis d v hd vo vn same ao an i top : Word}
    (h : ¬ v >>> 28 = 5) :
    bodyW p k m mode vis d v hd vo vn same ao an i top =
      appRestW p k m mode vis d v hd vo vn same ao an i top (rdW (m.arr64 SPN) (ao + i))
        (rdW (m.arr64 SPN) (ao + an + i)) := by
  simp [bodyW, lamW, h]

theorem callW_zero_app (p : Prog) (f : FnName) (vs : List Word) (m : Mem) :
    callW p 0 f vs m = none := by
  simp only [callW, invoke, lookupFn]
  cases p.lookup f with
  | none | some fd => rfl

theorem decE_tag_const (e : Word) (hh : e.toNat < 2 ^ 32) :
    ((decE e).tag == ETag.const) = decide (e >>> 28 = 3) := by
  have := decE_tag_eq e hh 3 (by decide)
  by_cases h : e >>> 28 = 3
  · have h2 : (decE e).tag = UInt32.ofNat 3 := this.mpr h
    simp [h, ETag.const, h2]
  · have h2 : ¬ (decE e).tag = UInt32.ofNat 3 := fun h' => h (this.mp h')
    simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq, ETag.const]
    exact h2

/-- The twin's `whnfApp` after the ι step's answer. -/
def appStepT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (hd ap : EIdx)
    (va : Array EIdx) (same2 : Bool) (args nodes : Array EIdx) (i : Nat) (step : Option EIdx) :
    AM WhnfStep :=
  match step with
  | none => whnfApp mode r fe depth ap hd va same2 args nodes (i + 1)
  | some e2 => do
    let e3 ← mkAppNFrom e2 args (i + 1)
    pure (WhnfStep.cont e3)

theorem whnfApp_nolam (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (v hd : EIdx) (vargs : Array EIdx) (same : Bool) (args nodes : Array EIdx) (i : Nat)
    (hi : i < args.size) (hv : (v.tag == ETag.lam) = false) :
    whnfApp mode r fe depth v hd vargs same args nodes i =
      (show AM WhnfStep from do
        let ap ← internAppRebuilt nodes[i]! same v args[i]
        if hd.tag == ETag.const then do
          let step ← iotaRecAt mode r fe depth hd (vargs.push args[i]) (vargs.push args[i]).size
          appStepT mode r fe depth hd ap (vargs.push args[i]) (ap == nodes[i]!) args nodes i step
        else
          appStepT mode r fe depth hd ap (vargs.push args[i]) (ap == nodes[i]!) args nodes i none) := by
  rw [whnfApp]
  simp only [hi, dite_true, hv, Bool.false_eq_true, ite_false]
  rfl

section appRef0
variable (p : Prog) (hp : WhnfCoreProg p)

include hp in
/-- **The next spine node refines `internAppRebuilt`**: the saved node, or `mk_app`'s interning. -/
theorem apW_ref (k : Nat) (m : Mem) (a : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb : Word) (hS : CoreS dn m a vis fe MM eb)
    (v same aW nW : Word) (_hv : HW v) (_ha : HW aW) (hnW : HW nW) (ap : Word) (m₁ : Mem)
    (h : apW p k m v same aW nW = some (ap, m₁)) :
    ∃ a₁, (internAppRebuilt (decE nW) (same != 0) (decE v) (decE aW)).run a = .ok (decE ap, a₁) ∧
      CoreS dn m₁ a₁ vis fe MM eb ∧ StackKept m m₁ ∧ HW ap := by
  unfold apW at h
  by_cases hs : same ≠ 0
  · simp only [hs, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb : (same != 0) = true := by simpa using hs
    refine ⟨a, ?_, hS, StackKept.refl _, hnW⟩
    simp only [internAppRebuilt, hb, ite_true]; rfl
  · simp only [hs, ↓reduceIte] at h
    have hs' : same = 0 := by simpa using hs
    have hb : (same != 0) = false := by simp [hs']
    cases hc : callW p k "mk_app" [v, aW] m with
    | none => rw [hc] at h; simp at h
    | some q =>
    obtain ⟨r, m'⟩ := q
    rw [hc] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hok, hD, hres, hfr, hhw⟩ := callW_mkApp p hp.spine k ⟨m, Locals.init []⟩ a hS.arena
      v aW r m' hc
    have hrun := AM.run_of_ok _ _ hok
    refine ⟨AM.st (internE (.app (decE v) (decE aW))) a, ?_, ?_, StackKept.of_app_frame hfr, hhw⟩
    · simp only [internAppRebuilt, hb, Bool.false_eq_true, ite_false]
      rw [hrun, hres]
    · exact hS.of_app hD (Keeps.run (keeps_cpl_internApp _ _) hrun) hfr

theorem iotaW_nonconst {p : Prog} {k : Nat} {m : Mem} {mode vis d hd vo vn ao an i top : Word}
    (h : ¬ hd >>> 28 = 3) : iotaW p k m mode vis d hd vo vn ao an i top = some (.cont m) := by
  simp [iotaW, h]

theorem iotaW_const {p : Prog} {k : Nat} {m : Mem} {mode vis d hd vo vn ao an i top : Word}
    (h : hd >>> 28 = 3) : iotaW p k m mode vis d hd vo vn ao an i top =
      match callW p k "iota_rec_at" [mode, vis, d, hd, vo, vn] m with
      | none => none
      | some (r, m₃) =>
        if r.headD 0 ≠ 0 then
          match callW p k "mk_app_n_from" [r.tail.headD 0, ao, an, i + 1] m₃ with
          | none => none
          | some (r', m₄) => some (.ret 1 (r'.headD 0) (m₄.set64 CTL 136 top))
        else some (.cont m₃) := by
  simp [iotaW, h]

end appRef0

section appRef
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)

include hp hwc hcc in
/-- **The `whnf_app` loop refines `whnfApp`**, by induction on the L fuel. -/
theorem appFull_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (mode vis d hd vo ao an top : Word) (args nodes : Array EIdx)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (eb : Word) (m₀ : Mem)
    (hmode : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hhd : HW hd)
    (har₀ : SpineR m₀ ao an args) (hno₀ : SpineR m₀ (ao + an) an nodes)
    (hlo : ao.toNat + an.toNat + an.toNat ≤ vo.toNat) (hvot : vo.toNat ≤ top.toNat)
    (htop0 : top = spTop m₀) (hspn0 : (m₀.arr64 SPN).size < 2 ^ 63) :
    ∀ (k : Nat), k ≤ n + 1 → ∀ (a : AState) (m : Mem) (v vn same i : Word) (va : Array EIdx)
      (MM : ModeMaps),
      CoreS dn m a vis fe MM eb → HW v → SpineR m vo vn va → spTop m = vo + vn →
      top.toNat ≤ (vo + vn).toNat → (∀ j : Word, j < top → spW m j = spW m₀ j) →
      (m.arr64 SPN).size = (m₀.arr64 SPN).size → BKept m₀ m → PoolGrew m₀ m →
      ∀ st r mF, appFull p mode vis d hd vo ao an top k m v vn same i = some (st, r, mF) →
      (136 : Word).toNat < (mF.arr64 CTL).size →
      PeelPost dn vis fe MM eb m₀ a
        (whnfApp (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v) (decE hd) va
          (same != 0) args nodes i.toNat) st r mF := by
  intro k
  induction k with
  | zero => intro _ a m v vn same i va MM _ _ _ _ _ _ _ _ _ st r mF hF; rw [appFull_zero] at hF; cases hF
  | succ k ih =>
    intro hkn a m v vn same i va MM hS hv hva htop htv hb hsz hbk hpg st r mF hF h136
    have hspn := hS.spn
    have hvn64 : vo.toNat + vn.toNat < 2 ^ 64 := by have := hva.bound; omega
    have hadd : (vo + vn).toNat = vo.toNat + vn.toNat := addW _ _ hvn64
    have hlt_args : args.size = an.toNat := har₀.size
    have haoan : (ao + an).toNat = ao.toNat + an.toNat := by
      have := har₀.bound; exact addW _ _ (by omega)
    by_cases hlt : i < an
    · have hlt' : i.toNat < args.size := by
        rw [hlt_args]; exact UInt64.lt_iff_toNat_lt.mp hlt
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]; simp
        have := UInt64.lt_iff_toNat_lt.mp hlt
        have := an.toNat_lt
        omega
      have hjtop : ∀ j : Word, j < top → j < spTop m := fun j hj => by
        rw [htop, UInt64.lt_iff_toNat_lt, hadd]
        have := UInt64.lt_iff_toNat_lt.mp hj; omega
      have haoT : ao.toNat + an.toNat ≤ top.toNat := by omega
      have hnoT : (ao + an).toNat + an.toNat ≤ top.toNat := by omega
      have har : SpineR m ao an args := har₀.keepT top hsz hb haoT hspn0
      have hno : SpineR m (ao + an) an nodes := hno₀.keepT top hsz hb hnoT hspn0
      have hit : (i.toNat).toUInt64 = i := by simp
      have hxi : args[i.toNat] = decE (spW m (ao + i)) := by
        have h := har.get i.toNat hlt'
        rwa [hit] at h
      have hvv : (spW m (ao + i)).toNat < 2 ^ 32 := by
        have h := har.lt i.toNat (by rw [← har.size]; exact hlt')
        rwa [hit] at h
      by_cases hlam : v >>> 28 = 5
      · rw [appFull_body hlt, bodyW_lam hlam] at hF
        have c1 : ¬ (tierW v ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := fun c1 => by simp [c1] at hF
        have c2 : ¬ tcnt m LAM (tierW v) ≤ idxW v := fun c2 => by simp [c1, c2] at hF
        simp only [c1, c2, ↓reduceIte] at hF
        cases hcall : callW p k "beta_peel" [tfld m LAM (tierW v) (idxW v) 1,
            rdW (m.arr64 SPN) (ao + i), ao, an, i + 1] m with
        | none => rw [hcall] at hF; simp at hF
        | some q =>
        obtain ⟨r₁, m₁⟩ := q
        rw [hcall] at hF
        obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hF)
        cases k with
        | zero => rw [callW_zero_app] at hcall; cases hcall
        | succ k' =>
        have hvw : viewOK m v LAM := ⟨c1, UInt64.not_le.mp c2⟩
        obtain ⟨-, -, hbody1⟩ := view_lam m a hS.arena.1 v hv hvw hlam
        have hvb := viewBind_lam m a hS.arena.1 v hv hvw hlam
        have hbeta := betaPeel_refines' p hp hwc.instList k' ⟨m, Locals.init []⟩ a dn vis fe MM eb _
          (rdW (m.arr64 SPN) (ao + i)) ao an (i + 1) args hS hbody1 hvv har
          (by rw [htop, hadd]; omega)
        obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hrw⟩ := CoreSpec.of_callW hbeta hcall
        rw [hi1] at hok hS' hres
        have hlamtag : ((decE v).tag == ETag.lam) = true := by
          rw [decE_tag_lam v hv]; simp [hlam]
        have hrun : (whnfApp (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v)
            (decE hd) va (same != 0) args nodes i.toNat).run a =
            .ok (AM.res (betaPeel (decE (tfld m LAM (tierW v) (idxW v) 1))
              #[decE (rdW (m.arr64 SPN) (ao + i))] args (i.toNat + 1)) a,
              AM.st (betaPeel (decE (tfld m LAM (tierW v) (idxW v) 1))
              #[decE (rdW (m.arr64 SPN) (ao + i))] args (i.toNat + 1)) a) := by
          rw [whnfApp]
          simp only [hlt', dite_true, hlamtag, ite_true, StateT.run_bind, viewBind_run', hvb,
            except_ok_bind]
          have hxi' : args[i.toNat] = decE (rdW (m.arr64 SPN) (ao + i)) := hxi
          rw [hxi']
          exact AM.run_of_ok _ _ hok
        refine ⟨_, _, hrun, hres, hrw, M', ?_, hK', ?_⟩
        · exact hS'.frame_stk (MemFrame.setCtl m₁ 136 _) (by simp) (by simp)
        · subst htop0
          exact StackKept.restore (fun j hj => by
              rw [hSt'.below j (hjtop j hj)]; exact hb j hj) (hSt'.size.trans hsz)
            (hbk.trans hSt'.bstk) (hpg.trans hSt'.pool) (by rwa [size_set64] at h136)
      · -- the push, then the ι step
        have hnodeget : nodes[i.toNat]! = decE (rdW (m.arr64 SPN) (ao + an + i)) := by
          have hi2 : i.toNat < nodes.size := by rw [hno.size]; exact UInt64.lt_iff_toNat_lt.mp hlt
          have h := hno.get i.toNat hi2
          have hit2 : (ao + an) + (i.toNat).toUInt64 = ao + an + i := by rw [hit]
          rw [getElem!_pos nodes i.toNat hi2, h, hit2]; rfl
        have hnW : HW (rdW (m.arr64 SPN) (ao + an + i)) := by
          have h := hno.lt i.toNat (UInt64.lt_iff_toNat_lt.mp hlt)
          rwa [hit] at h
        rw [appFull_body hlt, bodyW_nolam hlam] at hF
        cases hap : apW p k m v same (rdW (m.arr64 SPN) (ao + i)) (rdW (m.arr64 SPN) (ao + an + i))
          with
        | none => simp [appRestW, hap] at hF
        | some q =>
        obtain ⟨ap, m₁⟩ := q
        obtain ⟨a₁, hrunAp, hS₁, hSt₁, hapW⟩ := apW_ref p hp k m a dn vis fe MM eb hS v same (rdW (m.arr64 SPN) (ao + i))
          (rdW (m.arr64 SPN) (ao + an + i)) hv hvv hnW ap m₁ hap
        simp only [appRestW, hap] at hF
        have hlen : ¬ m₁.len64 SPN ≤ vo + vn := fun hlen => by simp [hlen] at hF
        have hc136 : (136 : Word).toNat < (m₁.arr64 CTL).size := by
          by_cases hc136 : (136 : Word).toNat < (m₁.arr64 CTL).size
          · exact hc136
          · rw [ite_eq_right hlen, ite_eq_right hc136] at hF; simp at hF
        rw [ite_eq_right hlen, ite_eq_left hc136] at hF
        -- the facts after the push
        have hbd : vo.toNat + vn.toNat < (m₁.arr64 SPN).size := by
          have h : ¬ UInt64.ofNat (m₁.arr64 SPN).size ≤ vo + vn := hlen
          rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by
            have := hSt₁.size; omega), hadd] at h
          omega
        have hspn₁ : (m₁.arr64 SPN).size < 2 ^ 63 := hSt₁.size ▸ hspn
        have hva₁ : SpineR m₁ vo vn va := hva.keep hSt₁.size hSt₁.below (by rw [htop, hadd]; exact Nat.le_refl _) hspn
        have hS₂ := hS₁.frame_stk (spnCtl_frame m₁ (vo + vn) (rdW (m.arr64 SPN) (ao + i))
          (vo + vn + 1)) (by simp) (by simp)
        have hva₂ : SpineR ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
            (vo + vn + 1)) vo (vn + 1) (va.push (decE (rdW (m.arr64 SPN) (ao + i)))) :=
          (hva₁.push hspn₁ hbd _ hvv).setCtl 136 (vo + vn + 1)
        have htop₂ : spTop ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
            (vo + vn + 1)) = vo + (vn + 1) := by
          unfold spTop
          rw [rdW_set64, ite_eq_left ⟨rfl, rfl, by rw [size_set64]; exact hc136⟩, UInt64.add_assoc]
        have hvn1 : (vn + 1).toNat = vn.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; omega
        have hadd2 : (vo + (vn + 1)).toNat = vo.toNat + vn.toNat + 1 := by
          rw [← UInt64.add_assoc, addW _ _ (by rw [hadd]; have : (1 : Word).toNat = 1 := rfl; omega),
            hadd]
          have : (1 : Word).toNat = 1 := rfl
          omega
        have htv₂ : top.toNat ≤ (vo + (vn + 1)).toNat := by rw [hadd2]; omega
        have hb₂ : ∀ j : Word, j < top →
            spW ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136 (vo + vn + 1)) j =
              spW m₀ j := by
          intro j hj
          rw [spW_setCtl, spW_set64_ne _ _ _ _ (fun h => by
            have := UInt64.lt_iff_toNat_lt.mp hj
            rw [← h, hadd] at this; omega), hSt₁.below j (hjtop j hj)]
          exact hb j hj
        have hsz₂ : (((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
            (vo + vn + 1)).arr64 SPN).size = (m₀.arr64 SPN).size := by
          simp only [size_set64]; exact hSt₁.size.trans hsz
        have hbk₂ : BKept m₀ ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
            (vo + vn + 1)) :=
          hbk.trans (hSt₁.bstk.trans (BKept.of_frame (spnCtl_frame m₁ (vo + vn)
            (rdW (m.arr64 SPN) (ao + i)) (vo + vn + 1)) (by decide) (by decide)))
        have hpg₂ : PoolGrew m₀ ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
            (vo + vn + 1)) :=
          hpg.trans (hSt₁.pool.trans (PoolGrew.of_frame (spnCtl_frame m₁ (vo + vn)
            (rdW (m.arr64 SPN) (ao + i)) (vo + vn + 1)) (by decide) (by decide)))
        have hnotlam : ((decE v).tag == ETag.lam) = false := by
          rw [decE_tag_lam v hv]; simp [hlam]
        have hunf := whnfApp_nolam (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
          (decE v) (decE hd) va (same != 0) args nodes i.toNat hlt' hnotlam
        have hxi' : args[i.toNat] = decE (rdW (m.arr64 SPN) (ao + i)) := hxi
        rw [hnodeget, hxi'] at hunf
        have hkn' : k ≤ n + 1 := by omega
        by_cases hconst : hd >>> 28 = 3
        · rw [iotaW_const hconst] at hF
          generalize hm₂ : ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
            (vo + vn + 1)) = m₂ at hS₂ hva₂ htop₂ hb₂ hsz₂ hbk₂ hpg₂ hF
          cases hcI : callW p k "iota_rec_at" [mode, vis, d, hd, vo, vn + 1] m₂ with
          | none => rw [hcI] at hF; simp at hF
          | some q =>
          obtain ⟨rr, m₃⟩ := q
          rw [hcI] at hF
          simp only at hF
          cases k with
          | zero => rw [callW_zero_app] at hcI; cases hcI
          | succ k' =>
          have hiota := hcc.iota k' (hk.mono (by omega)) F ⟨m₂, Locals.init []⟩ a₁
            dn vis fe MM eb mode d hd vo (vn + 1) _ (by omega) (by omega) ⟨hS₂, hmode, hebm⟩ hhd
            hva₂ (by rw [htop₂, hadd2]; omega)
          obtain ⟨hokI, ⟨M', hS₃, hK₃, hSt₃⟩, hresI, hrwI⟩ := CoreSpec.of_callW hiota hcI
          have hva₃ : SpineR m₃ vo (vn + 1) (va.push (decE (rdW (m.arr64 SPN) (ao + i)))) :=
            hva₂.keep hSt₃.size hSt₃.below (by rw [htop₂, hadd2]; omega) (hsz₂ ▸ hspn0)
          have htop₃ : spTop m₃ = vo + (vn + 1) := hSt₃.1.trans htop₂
          have hb₃ : ∀ j : Word, j < top → spW m₃ j = spW m₀ j := fun j hj => by
            rw [hSt₃.below j (by rw [htop₂, UInt64.lt_iff_toNat_lt, hadd2]
                                 have := UInt64.lt_iff_toNat_lt.mp hj; omega)]
            exact hb₂ j hj
          have hsz₃ : (m₃.arr64 SPN).size = (m₀.arr64 SPN).size := hSt₃.size.trans hsz₂
          have hctag : ((decE hd).tag == ETag.const) = true := by
            rw [decE_tag_const hd hhd]; simp [hconst]
          by_cases hz : rr.headD 0 ≠ 0
          · rw [ite_eq_left hz] at hF
            cases hcM : callW p (k' + 1) "mk_app_n_from" [rr.tail.headD 0, ao, an, i + 1] m₃ with
            | none => rw [hcM] at hF; simp at hF
            | some q2 =>
            obtain ⟨r', m₄⟩ := q2
            rw [hcM] at hF
            obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hF)
            have haoT : ao.toNat + an.toNat ≤ top.toNat := by omega
            have hx3 : SpineR m₃ ao an args := har₀.keepT top hsz₃ hb₃ haoT hspn0
            obtain ⟨hok2, hD2, hres2, hfr2, hhw2⟩ := callW_mkAppNFrom p hp.spine (k' + 1)
              ⟨m₃, Locals.init []⟩ _ hS₃.arena (rr.tail.headD 0) ao an (i + 1) args hrwI.2 hx3
              (by rw [hi1]; have := UInt64.lt_iff_toNat_lt.mp hlt; omega) r' m₄ hcM
            have hcpl := Keeps.run (keeps_cpl_mkAppNFrom (decE (rr.tail.headD 0)) args
              (i + 1).toNat) (AM.run_of_ok _ _ hok2)
            have hS₄ := hS₃.of_app hD2 hcpl hfr2
            rw [hi1] at hok2 hres2 hS₄
            have hopt : decOptR rr = some (decE (rr.tail.headD 0)) := decOpt_ne _ _ hz
            refine ⟨WhnfStep.cont (decE (r'.headD 0)), ?a', ?run, ?hx, ?hrw, M', ?hS, hK₃, ?hSt⟩
            case run =>
              rw [hunf]
              simp only [StateT.run_bind, hrunAp, except_ok_bind, hctag, ite_true]
              rw [AM.run_of_ok _ _ hokI, hresI, hopt]
              simp only [except_ok_bind, appStepT]
              simp only [StateT.run_bind, AM.run_of_ok _ _ hok2, except_ok_bind, hres2]
              rfl
            case hx => simp [decStep]
            case hrw => exact ⟨by simp [HW], hhw2⟩
            case hS => exact hS₄.frame_stk (MemFrame.setCtl m₄ 136 _) (by simp) (by simp)
            case hSt =>
              subst htop0
              have hSt4 := StackKept.of_app_frame hfr2
              exact StackKept.restore (fun j hj => by
                  rw [hSt4.below j (by
                    rw [htop₃, UInt64.lt_iff_toNat_lt, hadd2]
                    have := UInt64.lt_iff_toNat_lt.mp hj; omega)]
                  exact hb₃ j hj) (hSt4.size.trans hsz₃)
                  ((hbk₂.trans hSt₃.bstk).trans hSt4.bstk) ((hpg₂.trans hSt₃.pool).trans hSt4.pool)
                  (by rwa [size_set64] at h136)
          · rw [ite_eq_right hz] at hF
            simp only at hF
            have hz' : rr.headD 0 = 0 := by simpa using hz
            obtain ⟨x, a', hrun', hx, hrw, M'', hS'', hK, hSt⟩ := ih (by omega) _ m₃ ap (vn + 1) _
              (i + 1) (va.push (decE (rdW (m.arr64 SPN) (ao + i)))) M' hS₃ hapW hva₃ htop₃
              (by rw [hadd2]; omega) hb₃ hsz₃ (hbk₂.trans hSt₃.bstk) (hpg₂.trans hSt₃.pool) st r mF hF h136
            rw [hi1, evalW_eq_ne ap _ hapW hnW] at hrun'
            refine ⟨x, a', ?_, hx, hrw, M'', hS'', hK₃.trans hK, hSt⟩
            rw [hunf]
            simp only [StateT.run_bind, hrunAp, except_ok_bind, hctag, ite_true]
            have hopt : decOptR rr = none := by unfold decOptR decOpt; rw [ite_eq_left hz']
            rw [AM.run_of_ok _ _ hokI, hresI, hopt]
            simp only [except_ok_bind, appStepT]
            exact hrun'
        · rw [iotaW_nonconst hconst] at hF
          simp only at hF
          obtain ⟨x, a', hrun', hx, hrw, M'', hS'', hK, hSt⟩ := ih hkn' a₁ _ ap (vn + 1) _ (i + 1)
            (va.push (decE (rdW (m.arr64 SPN) (ao + i)))) MM hS₂ hapW hva₂ htop₂ htv₂ hb₂ hsz₂ hbk₂ hpg₂
            st r mF hF h136
          have hctag : ((decE hd).tag == ETag.const) = false := by
            rw [decE_tag_const hd hhd]; simp [hconst]
          rw [hi1, evalW_eq_ne ap _ hapW hnW] at hrun'
          refine ⟨x, a', ?_, hx, hrw, M'', hS'', hK, hSt⟩
          rw [hunf]
          simp only [StateT.run_bind, hrunAp, except_ok_bind, hctag, Bool.false_eq_true, ite_false,
            appStepT]
          exact hrun'
    · rw [appFull_exit hlt] at hF
      obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hF)
      have hnlt : ¬ i.toNat < args.size := by
        rw [hlt_args]; exact fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      have hrun : (whnfApp (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v)
          (decE hd) va (same != 0) args nodes i.toNat).run a = .ok (.done (decE v), a) := by
        rw [whnfApp]; simp only [hnlt, dite_false]; rfl
      subst htop0
      refine ⟨_, _, hrun, by simp [decStep], ⟨by simp [HW], hv⟩, MM, ?_, KeptAll.refl _ _, ?_⟩
      · exact hS.frame_stk (MemFrame.setCtl m 136 _) (by simp) (by simp)
      · exact StackKept.restore (fun j hj => hb j hj) hsz hbk hpg (by rwa [size_set64] at h136)

include hp hwc hcc in
/-- **`whnf_app` refines `whnfApp`**: `vargs` the slice `(vo, vn)` at the top of the stack, the
spine's arguments and nodes the slices `(ao, an)`, `(ao + an, an)` below it. -/
theorem whnfApp_refines' (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d v hd vo vn same ao an i : Word)
    (vargs args nodes : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hv : HW v)
    (hhd : HW hd) (hva : SpineR s₀.mem vo vn vargs) (htop : spTop s₀.mem = vo + vn)
    (har : SpineR s₀.mem ao an args) (hno : SpineR s₀.mem (ao + an) an nodes)
    (hlo : ao.toNat + an.toNat + an.toNat ≤ vo.toNat) :
    CoreSpec p (n + 1) "whnf_app" [mode, vis, d, v, hd, vo, vn, same, ao, an, i]
      (whnfApp (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v) (decE hd) vargs
        (same != 0) args nodes i.toNat) decStep s₀ a₀ dn vis fe MM eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW, h136i, h136⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (whnfApp_spec p hp.app n s₀ mode vis d v hd vo vn same ao an i)
  subst hs0
  refine ⟨hloc, ?_⟩
  rw [appFnW_eq] at hW
  have hS := hs.rel
  have hvn64 : vo.toNat + vn.toNat < 2 ^ 64 := by have := hva.bound; have := hS.spn; omega
  have hadd : (vo + vn).toNat = vo.toNat + vn.toNat := addW _ _ hvn64
  obtain ⟨x, a', hrun', hx, hrw, M', hS', hK, hSt⟩ := appFull_ref p hp hwc hcc n hk F hF hn mode vis d hd
    vo ao an (spTop s.mem) args nodes dn fe eb s.mem hs.mode4 hs.eb_mode hhd har hno hlo
    (by rw [htop, hadd]; omega) rfl hS.spn (n + 1) (Nat.le_refl _) a₀ s.mem v vn same i vargs MM hS
    hv hva htop (by rw [htop]; exact Nat.le_refl _) (fun _ _ => rfl) rfl (BKept.refl _)
    (PoolGrew.refl _) _ _ _ hW h136
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hok, ?_, ?_, hrw⟩
  · rw [hst]; exact ⟨M', hS', hK, hSt⟩
  · rw [hres, hx]; simp [decStep]

end appRef

end L.Arena
