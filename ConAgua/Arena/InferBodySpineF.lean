import ConAgua.Arena.InferBodySpine

/-!
# The full-grade application spine (lane `defeq`)

`infer_spine_arg` (one argument: its type, compared with the opened domain by `defeq_arg`),
`infer_spine` (the loop, as `infer_spine_io`'s in `InferBodySpine.lean` with the argument check),
`infer_app`. The twin fragment of the argument check is `inferSpineArgT`; `spineArg_run` turns its
run into the step of `inferSpine`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-- What the full-grade spine specs need of a program. -/
structure SpineFProg (p : Prog) : Prop where
  arg : p.lookup "infer_spine_arg" = some inferSpineArgL
  spine : p.lookup "infer_spine" = some inferSpineL
  app : p.lookup "infer_app" = some inferAppL

/-! ## `infer_spine_arg` -/

/-- **The argument check of `inferSpine`**, copied: the argument's type, compared with the opened
domain. -/
def inferSpineArgT (r : CoreFnsA) (depth : Nat) (a dom : EIdx) : AM Unit := do
  let ta ← r.infer depth a
  if !(← defeqArg r depth a ta dom) then
    fail (.invalid "application type mismatch")
  else pure ()

/-- A run of the argument check is the step of `inferSpine`'s arms. -/
theorem spineArg_run {β : Type} (r : CoreFnsA) (depth : Nat) (a dom : EIdx) (K : AM β) (s s' : AState)
    (h : (inferSpineArgT r depth a dom).run s = .ok ((), s')) :
    (do
      let ta ← r.infer depth a
      if !(← defeqArg r depth a ta dom) then fail (.invalid "application type mismatch")
      else K).run s = K.run s' := by
  simp only [inferSpineArgT, StateT.run_bind] at h ⊢
  cases h1 : (r.infer depth a).run s with
  | error e => rw [h1] at h; cases h
  | ok q =>
  obtain ⟨ta, s₁⟩ := q
  rw [h1] at h
  simp only [except_ok_bind] at h ⊢
  cases h2 : (defeqArg r depth a ta dom).run s₁ with
  | error e => rw [h2] at h; cases h
  | ok q =>
  obtain ⟨b, s₂⟩ := q
  rw [h2] at h
  simp only [except_ok_bind] at h ⊢
  cases b with
  | false =>
    simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run] at h
    cases h
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    simp only [pure, StateT.pure, StateT.run] at h
    cases h; rfl

section argK
variable (p : Prog) (n : Nat) (mode vis d a dom : Word)

def argK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else some (0, m)

/-- **The model of `infer_spine_arg`** past the argument's `infer` run. -/
def argK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => argK2 (callW p n "defeq_arg" [mode, vis, d, a, r.headD 0, dom] m)

end argK

theorem inferSpineArg_spec (p : Prog) (hq : SpineFProg p) (n : Nat) (s₀ : St) (mode vis d a dom : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_spine_arg" [mode, vis, d, a, dom]
    ⦃fun r s' => LocEq s' s₀ ∧ argK1 p n mode vis d a dom
      (callW p n "infer" [mode, vis, d, a] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.arg]
  simp only [callFn, inferSpineArgL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "infer",
      callW_spec p n "defeq_arg"] <;>
  simp_all [argK1, argK2, LocEq, BinOp.eval, Cmp.eval, St.setLocs_cons, St.setLoc_loc,
    St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ]

/-- `defeq_arg` at every L fuel up to `n + 1`. -/
theorem defeqArg_any (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (he : IsEagerReduceH p) :
    ∀ n, KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a ta ty : Word), n ≤ F → n ≤ 2 ^ 62 →
    SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW ta → HW ty →
    CoreSpec p n "defeq_arg" [mode, vis, d, a, ta, ty]
      (defeqArg (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE ta) (decE ty)) decBool
      s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | k + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, ta, ty, hF, hn, hs, ha, hta, hty => by
      have hde : DefeqESlot p k := by
        cases k with
        | zero => intro F s₀ a₀ dn vis fe M eb mode d x y _ _ _ _ _
                  exact CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
        | succ j => exact defeqE_refines p hkp j (hk j (by omega)).defeq
      exact defeqArg_refines p hp k he (hk k (by omega)).defeq hde F s₀ a₀ dn vis fe M eb mode d a ta ty
        (by omega) (by omega) hs ha hta hty

/-- **`infer_spine_arg` refines the argument check** (`inferSpineArgT`) at the knot. -/
@[refines_part ConRon.Arena.inferSpine "argument check"]
theorem inferSpineArg_refines (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p)
    (hq : SpineFProg p) (he : IsEagerReduceH p) (n : Nat) (hk : KnotUpTo p n) (F : Nat)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a dom : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hdom : HW dom) :
    CoreSpec p (n + 1) "infer_spine_arg" [mode, vis, d, a, dom]
      (inferSpineArgT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE dom)) (fun _ => ())
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferSpineArg_spec p hq n s₀ mode vis d a dom)
  subst hs0
  refine ⟨hloc, ?_⟩
  obtain ⟨r₁, m₁, hc1, hW⟩ := callW_cases rfl hW
  dsimp only [argK1] at hW
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  dsimp only [argK2] at hW
  have h0 : r₂.headD 0 ≠ 0 := fun h => by rw [if_pos h] at hW; cases hW
  rw [if_neg h0] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have h₁ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).infer F s a₀ dn vis fe M eb mode d a hF hn hs ha) hc1
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  have h₂ := CoreSpec.of_callW (defeqArg_any p hp hkp he n hk F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
    mode d a (r₁.headD 0) dom hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ ha h₁.2.2.2 hdom) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  have hbt : decBool r₂ = true := by simp only [decBool, bne_iff_ne]; exact h0
  rw [hbt]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact ⟨trivial, ⟨M₂, hS₂, KeptAll.refl _ _, StackKept.refl _⟩, rfl, by
    unfold ResH HW; rw [← hr]; decide⟩

/-! ## `infer_spine`: the loop as a named block -/

/-- The loop of `inferSpineL` (Infer.lean), named for its spec. -/
def inferSpineW : Stmt := lblk (mode, vis, d, ty, ao, an, co, cn, i, a, t, x, dom, dom2, ty2, w, z, r) {
  while i < an {
    a := SPN.u64[ao + i];
    if ty >> 28 == 6 {
      t := ⟦ty⟧.tier;
      x := ⟦ty⟧.idx;
      if t != 0 && CTL.u64[1] == 0 { abort };
      if FORALL⟨t⟩.count <= x { abort };
      dom := FORALL⟨t, x⟩.ty;
      ty := FORALL⟨t, x⟩.b;
      dom2 := call inst_list(dom, co, cn, 0);
      z := call infer_spine_arg(mode, vis, d, a, dom2);
      if len(SPN.u64) <= co + cn { abort };
      SPN.u64[co + cn] := a;
      cn += 1;
      CTL.u64[136] := co + cn
    } else {
      ty2 := call inst_list(ty, co, cn, 0);
      w := call whnf(mode, vis, d, ty2);
      if w >> 28 != 6 { fail R_FUNCTION_EXPECTED_2 };
      t := ⟦w⟧.tier;
      x := ⟦w⟧.idx;
      if t != 0 && CTL.u64[1] == 0 { abort };
      if FORALL⟨t⟩.count <= x { abort };
      dom := FORALL⟨t, x⟩.ty;
      ty := FORALL⟨t, x⟩.b;
      z := call infer_spine_arg(mode, vis, d, a, dom);
      if len(SPN.u64) <= co { abort };
      SPN.u64[co] := a;
      cn := 1;
      CTL.u64[136] := co + 1
    };
    i += 1
  }
}

/-- `inferSpineL`, with its loop spliced from `inferSpineW`. -/
-- con-ron: none — `inferSpineL` itself (`rfl`), its loop a named block for the proof
def inferSpineL' : FunDecl :=
    lfn (mode, vis, d, ty, ao, an) locals (co, cn, i, a, t, x, dom, dom2, ty2, w, z, r) {
  co := CTL.u64[136];
  if len(SPN.u64) < co { abort };
  cn := 0;
  i := 0;
  ⟪inferSpineW⟫;
  r := call inst_list(ty, co, cn, 0);
  CTL.u64[136] := co;
  return r
}

theorem inferSpineL_eq : inferSpineL = inferSpineL' := rfl

/-- **The model of the full spine's loop** at L fuel `k`: the exit's `(ty, cn, memory)`. -/
def spLoop (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Option (Word × Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, mode, vis, d, ty, ao, an, i, co, cn =>
    if i < an then
      if ty >>> 28 = 6 then
        if tierW ty ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
        else if tcnt m FORALL (tierW ty) ≤ idxW ty then none
        else
          match callW p k "inst_list" [tfld m FORALL (tierW ty) (idxW ty) 0, co, cn, 0] m with
          | none => none
          | some (r₁, m₁) =>
            match callW p k "infer_spine_arg" [mode, vis, d, rdW (m.arr64 SPN) (ao + i), r₁.headD 0] m₁ with
            | none => none
            | some (_, m₂) =>
              if m₂.len64 SPN ≤ co + cn then none
              else if ¬ (co + cn).toNat < (m₂.arr64 SPN).size then none
              else if ¬ (136 : Word).toNat < (m₂.arr64 CTL).size then none
              else spLoop p k (spPush m₂ co cn (rdW (m.arr64 SPN) (ao + i))) mode vis d
                (tfld m FORALL (tierW ty) (idxW ty) 1) ao an (i + 1) co (cn + 1)
      else
        match callW p k "inst_list" [ty, co, cn, 0] m with
        | none => none
        | some (r₁, m₁) =>
          match callW p k "whnf" [mode, vis, d, r₁.headD 0] m₁ with
          | none => none
          | some (r₂, m₂) =>
            if r₂.headD 0 >>> 28 ≠ 6 then none
            else if tierW (r₂.headD 0) ≠ 0 ∧ rdW (m₂.arr64 CTL) 1 = 0 then none
            else if tcnt m₂ FORALL (tierW (r₂.headD 0)) ≤ idxW (r₂.headD 0) then none
            else
              match callW p k "infer_spine_arg" [mode, vis, d, rdW (m.arr64 SPN) (ao + i),
                  tfld m₂ FORALL (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0] m₂ with
              | none => none
              | some (_, m₃) =>
                if m₃.len64 SPN ≤ co then none
                else if ¬ co.toNat < (m₃.arr64 SPN).size then none
                else if ¬ (136 : Word).toNat < (m₃.arr64 CTL).size then none
                else spLoop p k (spPush m₃ co 0 (rdW (m.arr64 SPN) (ao + i))) mode vis d
                  (tfld m₂ FORALL (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 1) ao an
                  (i + 1) co 1
    else some (ty, cn, m)

theorem inferSpineW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n inferSpineW
    ⦃fun r s' => r = .normal ∧ s'.loc 6 = s₀.loc 6 ∧
      spLoop p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)
        (s₀.loc 8) (s₀.loc 6) (s₀.loc 7) = some (s'.loc 3, s'.loc 7, s'.mem); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := inferSpineW) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64_spec, ih,
      callW_spec p n "inst_list", callW_spec p n "whnf", callW_spec p n "infer_spine_arg",
        evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    simp_all [spLoop, spPush, Cmp.eval, LocEq, BinOp.eval, tierW, idxW, St.setLocs_cons,
      St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, size_set64, w_lt_false, Mem.arr64_set64_ne]

/-- The full spine's loop with its tail. -/
def spFull (p : Prog) (n k : Nat) (m : Mem) (mode vis d ty ao an i co cn : Word) :
    Option (Word × Mem) :=
  match spLoop p k m mode vis d ty ao an i co cn with
  | none => none
  | some (ty', cn', m') => spTail p n m' ty' co cn'

/-- **The model of `infer_spine`.** -/
def spFn (p : Prog) (n : Nat) (m : Mem) (mode vis d ty ao an : Word) : Option (Word × Mem) :=
  if m.len64 SPN < rdW (m.arr64 CTL) 136 then none
  else spFull p n (n + 1) m mode vis d ty ao an 0 (rdW (m.arr64 CTL) 136) 0

theorem inferSpine_spec (p : Prog) (hq : SpineFProg p) (n : Nat) (s₀ : St)
    (mode vis d ty ao an : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_spine" [mode, vis, d, ty, ao, an]
    ⦃fun r s' => LocEq s' s₀ ∧ spFn p n s₀.mem mode vis d ty ao an = some (r.headD 0, s'.mem) ∧
      (136 : Word).toNat < (s₀.mem.arr64 CTL).size; ⊤⦄ := by
  rw [invoke_eq _ hq.spine, inferSpineL_eq]
  simp only [callFn, inferSpineL']
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64_spec,
      fun s => Triple.step_exec (inferSpineW_spec p (n + 1) s), callW_spec p n "inst_list"] <;>
  simp_all [spFn, spFull, spTail, LocEq, BinOp.eval, St.setLocs_cons, CTL, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

/-- `infer_spine_arg` at every L fuel up to `n + 1`. -/
theorem inferSpineArg_any (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) :
    ∀ n, KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a dom : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW dom →
    CoreSpec p n "infer_spine_arg" [mode, vis, d, a, dom]
      (inferSpineArgT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE dom)) (fun _ => ())
      s₀ a₀ dn vis fe M eb
  | 0, _, _, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, dom, hs, ha, hdom =>
      inferSpineArg_refines p hp hkp hq he n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis
        fe M eb mode d a dom hs ha hdom

theorem spFull_zero (p : Prog) (n : Nat) (m : Mem) (mode vis d ty ao an i co cn : Word) :
    spFull p n 0 m mode vis d ty ao an i co cn = none := rfl

theorem spFull_exit (p : Prog) (n k : Nat) (m : Mem) (mode vis d ty ao an i co cn : Word)
    (h : ¬ i < an) : spFull p n (k + 1) m mode vis d ty ao an i co cn = spTail p n m ty co cn := by
  simp [spFull, spLoop, h]

/-- **The full spine's loop refines `inferSpine`** by induction on the loop fuel. -/
theorem spFull_ref (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) (hil : InstListOK p) (N : Nat) (hk : KnotUpTo p N) (F : Nat)
    (hF : N ≤ F) (hN : N ≤ 2 ^ 62) (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (mode d ao an : Word) (args : Array EIdx) (eb co : Word) (hmode : mode < 4)
    (heb : eb = (mode >>> 1) &&& 1) (m₀ : Mem) (har₀ : SpineR m₀ ao an args)
    (hco : co = spTop m₀) (hlo : ao.toNat + an.toNat ≤ co.toNat) :
    ∀ k, k ≤ N + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (ty i cn : Word) (acc : Array EIdx),
      CoreS dn m a vis fe M eb → HW ty → SpineR m co cn acc → spTop m = co + cn →
      (∀ j, j < co → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      BKept m₀ m → PoolGrew m₀ m → (136 : Word).toNat < (m.arr64 CTL).size →
      ∀ w mF, spFull p n k m mode vis d ty ao an i co cn = some (w, mF) →
      SpPost dn vis fe M eb m₀ a
        (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) acc args i.toNat) w mF := by
  intro k
  induction k with
  | zero => intro _ m a M ty i cn acc _ _ _ _ _ _ _ _ _ w mF hF; rw [spFull_zero] at hF; cases hF
  | succ k ih =>
    intro hkN m a M ty i cn acc hS ht hacc htop hb hsz hbk hpg h136m w mF hF
    have hspn := hS.spn
    have hco_le : co.toNat + cn.toNat ≤ (m.arr64 SPN).size := hacc.bound
    have hcn64 : co.toNat + cn.toNat < 2 ^ 64 := by omega
    have hadd : (co + cn).toNat = co.toNat + cn.toNat := addW _ _ hcn64
    have hspT : (spTop m).toNat = co.toNat + cn.toNat := by rw [htop, hadd]
    have har : SpineR m ao an args := har₀.keepT co hsz hb hlo (hsz ▸ hspn)
    have h0 : (0 : Word).toNat = 0 := rfl
    have hkeep : ∀ {m₂ : Mem}, StackKept m m₂ → (∀ j, j < co → spW m₂ j = spW m₀ j) := by
      intro m₂ hSt j hj
      have hj' : j < spTop m := by
        rw [htop, UInt64.lt_iff_toNat_lt, hadd]
        have := UInt64.lt_iff_toNat_lt.mp hj; omega
      exact (hSt.below j hj').trans (hb j hj)
    by_cases hlt : i < an
    · have hlt' : i.toNat < args.size := by rw [har₀.size]; exact UInt64.lt_iff_toNat_lt.mp hlt
      have hit : (i.toNat).toUInt64 = i := by simp
      have hxi : args[i.toNat] = decE (spW m (ao + i)) := by
        have h := har.get i.toNat hlt'; rwa [hit] at h
      have hvv : HW (spW m (ao + i)) := by
        have h := har.lt i.toNat (by rw [← har.size]; exact hlt'); rwa [hit] at h
      have hi1 := succ_toNat_of_lt hlt
      by_cases ht6 : ty >>> 28 = 6
      · -- the ∀ step: the domain opened, the argument checked and pushed
        have c1 : ¬ (tierW ty ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := fun g => by
          simp only [spFull, spLoop, hlt, ht6, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have c2 : ¬ tcnt m FORALL (tierW ty) ≤ idxW ty := fun g => by
          simp only [spFull, spLoop, hlt, ht6, c1, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have hv : viewOK m ty FORALL := ⟨c1, UInt64.not_le.mp c2⟩
        obtain ⟨-, hdom, hbody⟩ := view_forall m a hS.arena.1 ty ht hv ht6
        have hvb := viewBind_forall m a hS.arena.1 ty ht hv ht6
        cases h1 : callW p k "inst_list" [tfld m FORALL (tierW ty) (idxW ty) 0, co, cn, 0] m with
        | none => simp only [spFull, spLoop, hlt, ht6, c1, c2, h1, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        | some q =>
        obtain ⟨r₁, m₁⟩ := q
        cases h2 : callW p k "infer_spine_arg" [mode, vis, d, rdW (m.arr64 SPN) (ao + i), r₁.headD 0] m₁ with
        | none => simp only [spFull, spLoop, hlt, ht6, c1, c2, h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        | some q =>
        obtain ⟨r₂, m₂⟩ := q
        have g4 : ¬ m₂.len64 SPN ≤ co + cn := fun g => by
          simp only [spFull, spLoop, hlt, ht6, c1, c2, h1, h2, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have g5 : (co + cn).toNat < (m₂.arr64 SPN).size := Classical.byContradiction fun g => by
          simp only [spFull, spLoop, hlt, ht6, c1, c2, h1, h2, g4, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have g6 : (136 : Word).toNat < (m₂.arr64 CTL).size := Classical.byContradiction fun g => by
          simp only [spFull, spLoop, hlt, ht6, c1, c2, h1, h2, g4, g5, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have hF' : spFull p n k (spPush m₂ co cn (rdW (m.arr64 SPN) (ao + i))) mode vis d
            (tfld m FORALL (tierW ty) (idxW ty) 1) ao an (i + 1) co (cn + 1) =
            some (w, mF) := by
          simpa only [spFull, spLoop, hlt, ht6, c1, c2, h1, h2, g4, g5, g6, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] using hF
        -- the domain at the accumulator
        have hinst := hil k ⟨m, Locals.init []⟩ a dn vis fe M eb _ co cn 0 acc hS hdom hacc
          (by rw [hspT]; exact Nat.le_refl _)
        obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW hinst h1
        rw [h0] at hok1 hres1 hS₁
        -- the argument check
        have harg := CoreSpec.of_callW (inferSpineArg_any p hp hkp hq he k (hk.mono (by omega)) F
          (by omega) (by omega) ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d _ (r₁.headD 0)
          ⟨hS₁, hmode, heb⟩ hvv hrw1) h2
        obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, -, -⟩ := harg
        have hSt12 := hSt₁.trans hSt₂
        have hacc₂ : SpineR m₂ co cn acc := hacc.keep hSt12.size hSt12.below (by rw [hspT]; exact Nat.le_refl _) hspn
        obtain ⟨hacc', htop', hb', hsz', h136', hbk', hpg'⟩ := spPush_step hS₂.spn hacc₂ (hkeep hSt12)
          (hSt12.size.trans hsz) (hbk.trans hSt12.bstk) (hpg.trans hSt12.pool) g6 g5 hvv
        have hS' := hS₂.frame_stk (spnCtl_frame m₂ (co + cn) (spW m (ao + i)) (co + (cn + 1)))
          (by simp) (by simp)
        obtain ⟨x, a', hrun', hx, hrw, M', hS'', hK, hSt⟩ := ih (by omega) _ _ M₂ _ (i + 1) (cn + 1)
          _ hS' hbody hacc' htop' hb' hsz' hbk' hpg' h136' w mF hF'
        refine ⟨x, a', ?_, hx, hrw, M', hS'', hK₁.trans (hK₂.trans hK), hSt⟩
        rw [← hrun', inferSpine]
        simp only [hlt', dite_true, tag_fa_beq ty ht, ht6, decide_true, ite_true, StateT.run_bind,
          viewBind_run', hvb, except_ok_bind, hxi, hi1]
        rw [AM.run_of_ok _ _ hok1, except_ok_bind, hres1]
        exact spineArg_run _ _ _ _ _ _ _ (by dsimp only; simp only [decH]; rw [AM.run_of_ok _ _ hok2])
      · -- the `whnf` re-entry: the accumulator restarts at `#[a]`
        cases h1 : callW p k "inst_list" [ty, co, cn, 0] m with
        | none => simp only [spFull, spLoop, hlt, ht6, h1, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        | some q =>
        obtain ⟨r₁, m₁⟩ := q
        cases h2 : callW p k "whnf" [mode, vis, d, r₁.headD 0] m₁ with
        | none => simp only [spFull, spLoop, hlt, ht6, h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        | some q =>
        obtain ⟨r₂, m₂⟩ := q
        have g1 : r₂.headD 0 >>> 28 = 6 := Classical.byContradiction fun g => by
          simp only [spFull, spLoop, hlt, ht6, h1, h2, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have g2 : ¬ (tierW (r₂.headD 0) ≠ 0 ∧ rdW (m₂.arr64 CTL) 1 = 0) := fun g => by
          simp only [spFull, spLoop, hlt, ht6, h1, h2, g1, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have g3 : ¬ tcnt m₂ FORALL (tierW (r₂.headD 0)) ≤ idxW (r₂.headD 0) := fun g => by
          simp only [spFull, spLoop, hlt, ht6, h1, h2, g1, g2, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        cases h3 : callW p k "infer_spine_arg" [mode, vis, d, rdW (m.arr64 SPN) (ao + i),
            tfld m₂ FORALL (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0] m₂ with
        | none => simp only [spFull, spLoop, hlt, ht6, h1, h2, g1, g2, g3, h3, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        | some q =>
        obtain ⟨r₃, m₃⟩ := q
        have g4 : ¬ m₃.len64 SPN ≤ co := fun g => by
          simp only [spFull, spLoop, hlt, ht6, h1, h2, g1, g2, g3, h3, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have g5 : co.toNat < (m₃.arr64 SPN).size := Classical.byContradiction fun g => by
          simp only [spFull, spLoop, hlt, ht6, h1, h2, g1, g2, g3, h3, g4, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have g6 : (136 : Word).toNat < (m₃.arr64 CTL).size := Classical.byContradiction fun g => by
          simp only [spFull, spLoop, hlt, ht6, h1, h2, g1, g2, g3, h3, g4, g5, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have hF' : spFull p n k (spPush m₃ co 0 (rdW (m.arr64 SPN) (ao + i))) mode vis d
            (tfld m₂ FORALL (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 1) ao an
            (i + 1) co 1 = some (w, mF) := by
          simpa only [spFull, spLoop, hlt, ht6, h1, h2, g1, g2, g3, h3, g4, g5, g6, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] using hF
        have hinst := hil k ⟨m, Locals.init []⟩ a dn vis fe M eb ty co cn 0 acc hS ht hacc
          (by rw [hspT]; exact Nat.le_refl _)
        obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW hinst h1
        rw [h0] at hok1 hres1 hS₁
        have hw := CoreSpec.of_callW ((hk k (by omega)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
          mode d (r₁.headD 0) (by omega) (by omega) ⟨hS₁, hmode, heb⟩ hrw1) h2
        obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := hw
        have hv : viewOK m₂ (r₂.headD 0) FORALL := ⟨g2, UInt64.not_le.mp g3⟩
        obtain ⟨-, hdom, hbody⟩ := view_forall m₂ _ hS₂.arena.1 (r₂.headD 0) hrw2 hv g1
        have hvb := viewBind_forall m₂ _ hS₂.arena.1 (r₂.headD 0) hrw2 hv g1
        have harg := CoreSpec.of_callW (inferSpineArg_any p hp hkp hq he k (hk.mono (by omega)) F
          (by omega) (by omega) ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d _ _
          ⟨hS₂, hmode, heb⟩ hvv hdom) h3
        obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, -, -⟩ := harg
        have hSt13 := hSt₁.trans (hSt₂.trans hSt₃)
        have hacc0 := SpineR.empty m₃ co (by omega)
        obtain ⟨hacc', htop', hb', hsz', h136', hbk', hpg'⟩ := spPush_step (cn := 0) hS₃.spn hacc0 (hkeep hSt13)
          (hSt13.size.trans hsz) (hbk.trans hSt13.bstk) (hpg.trans hSt13.pool) g6 (by simpa using g5) hvv
        have hS' := hS₃.frame_stk (spnCtl_frame m₃ (co + 0) (spW m (ao + i)) (co + (0 + 1)))
          (by simp) (by simp)
        obtain ⟨x, a', hrun', hx, hrw, M', hS'', hK, hSt⟩ := ih (by omega) _ _ M₃ _ (i + 1) 1
          _ hS' hbody hacc' htop' hb' hsz' hbk' hpg' h136' w mF hF'
        refine ⟨x, a', ?_, hx, hrw, M', hS'', hK₁.trans (hK₂.trans (hK₃.trans hK)), hSt⟩
        rw [← hrun', inferSpine]
        have hnfa : ((decE ty).tag == ETag.forallE) = false := by rw [tag_fa_beq ty ht]; simp [ht6]
        have hfa : ((decE (r₂.headD 0)).tag == ETag.forallE) = true := by
          rw [tag_fa_beq _ hrw2]; exact decide_eq_true g1
        simp only [hlt', dite_true, hnfa, Bool.false_eq_true, ite_false, StateT.run_bind,
          AM.run_of_ok _ _ hok1, except_ok_bind, hxi, hi1]
        rw [hres1]
        simp only [decH]
        rw [AM.run_of_ok _ _ hok2, hres2]
        simp only [except_ok_bind, decH, hfa, ite_true, StateT.run_bind, viewBind_run', hvb]
        exact spineArg_run _ _ _ _ _ _ _ (by rw [AM.run_of_ok _ _ hok3])
    · rw [spFull_exit _ _ _ _ _ _ _ _ _ _ _ _ _ hlt] at hF
      obtain ⟨x, a', hrun, hx, hrw, M', hS', hK, hSt⟩ :=
        spTail_ref p hil n dn vis fe eb co m₀ hco m a M ty cn acc hS ht hacc htop hb hsz hbk hpg w mF hF
      have hnlt : ¬ i.toNat < args.size := by
        rw [har₀.size]; exact fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      refine ⟨x, a', ?_, hx, hrw, M', hS', hK, hSt⟩
      rw [inferSpine]
      simp only [hnlt, dite_false]
      exact hrun

/-- **`infer_spine` refines `inferSpine`** at the knot, the head's type `ty` and the arguments the
slice `(ao, an)` below the top. -/
@[refines ConRon.Arena.inferSpine]
theorem inferSpine_refines (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (ht : HW ty) (har : SpineR s₀.mem ao an args)
    (hlo : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpec p (n + 1) "infer_spine" [mode, vis, d, ty, ao, an]
      (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) #[] args 0) decH s₀ a₀ dn vis
        fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW, h136⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferSpine_spec p hq n s₀ mode vis d ty ao an)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold spFn at hW
  obtain ⟨hc, hW⟩ := of_ite_none hW
  have hcle := len64_not_lt hS.spn hc
  obtain ⟨x, a', hrun', hx, hrw, M', hS', hK, hSt⟩ := spFull_ref p hp hkp hq he hil n hk F hF hn n dn
    vis fe mode d ao an args eb _ hs.mode4 hs.eb_mode s.mem har rfl hlo (n + 1) (Nat.le_refl _) s.mem
    a₀ M ty 0 0 #[] hS ht (SpineR.empty _ _ hcle) (by simp [spTop]) (fun _ _ => rfl) rfl (BKept.refl _) (PoolGrew.refl _) h136 _ _ hW
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [h0] at hrun'
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hok, ?_, by rw [hres, hx]; rfl, hrw⟩
  rw [hst]; exact ⟨M', hS', hK, hSt⟩

/-- `infer_spine` at every L fuel up to `n + 1`. -/
theorem inferSpine_any (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) (hil : InstListOK p) :
    ∀ n, KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx), SlotPre s₀ a₀ dn vis fe M eb mode →
    HW ty → SpineR s₀.mem ao an args → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p n "infer_spine" [mode, vis, d, ty, ao, an]
      (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) #[] args 0) decH s₀ a₀ dn
        vis fe M eb
  | 0, _, _, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, ty, ao, an, args, hs, ht, har, hlo =>
      inferSpine_refines p hp hkp hq he hil n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis
        fe M eb mode d ty ao an args hs ht har hlo

/-! ## `infer_app` -/

section appK
variable (p : Prog) (n : Nat) (mode vis d top : Word)

def appK3 (ao an : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => appIOK4 top (callW p n "infer_spine" [mode, vis, d, r.headD 0, ao, an] m)

/-- **The model of `infer_app`** past `head_and_args`' run. -/
def appK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => appK3 p n mode vis d top (r.tail.headD 0) (r.tail.tail.headD 0)
      (callW p n "infer" [mode, vis, d, r.headD 0] m)

end appK

theorem inferApp_spec (p : Prog) (hq : SpineFProg p) (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_app" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ appK2 p n mode vis d (rdW (s₀.mem.arr64 CTL) 136)
      (callW p n "head_and_args" [e] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.app]
  simp only [callFn, inferAppL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64_spec,
      callW_spec p n "head_and_args", callW_spec p n "infer", callW_spec p n "infer_spine"] <;>
  simp_all [appK2, appK3, appIOK4, LocEq, BinOp.eval, St.setLocs_cons, CTL, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

/-- `inferBody`'s `.app` arm is `inferApp`. -/
@[refines_part ConRon.Arena.inferBody "app"]
theorem inferBody_app (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)
    (f x : EIdx) (hv : a.store.view e = some (.app f x)) :
    (inferBody r fe d e).run a = (inferApp r fe d e).run a := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]

/-- **`infer_app` refines `inferApp`** at the knot, at an `app` handle. -/
@[refines ConRon.Arena.inferApp]
theorem inferApp_refines (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (hsp : SpineProg p) (he : IsEagerReduceH p) (hil : InstListOK p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hHe : HW e)
    (h4 : e >>> 28 = 4) :
    CoreSpec p (n + 1) "infer_app" [mode, vis, d, e]
      (inferApp (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decH s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferApp_spec p hq n s₀ mode vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  obtain ⟨r₁, m₁, hc1, hW⟩ := callW_cases rfl hW
  dsimp only [appK2] at hW
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  dsimp only [appK3] at hW
  obtain ⟨r₃, m₃, hc3, hW⟩ := callW_cases rfl hW
  dsimp only [appIOK4] at hW
  have h136 : (136 : Word).toNat < (m₃.arr64 CTL).size := by
    refine Classical.byContradiction fun h => ?_; rw [if_neg h] at hW; cases hW
  rw [if_pos h136] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨t₁, ht₁, -, hf₁, hg₁, hhw, ho1, htop1, xs, hha, hxs⟩ := triple_of_callW
    (headAndArgs_app p hsp n s a₀ hS.arena.1 e hHe h4 hS.spn) hc1
  rw [ht₁] at hf₁ hg₁ htop1 hxs
  have hS₁ := hS.frame_stk hf₁ (by simp) (by simp)
  have hb1 := hxs.bound
  have hspn₁ := hS₁.spn
  have hadd : (r₁.tail.headD 0 + r₁.tail.tail.headD 0).toNat =
      (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat := addW _ _ (by omega)
  have htopN : (spTop m₁).toNat = (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat := by
    rw [htop1, ← ho1, hadd]
  have h₂ := CoreSpec.of_callW (hK.infer F ⟨m₁, Locals.init []⟩ a₀ dn vis fe M eb mode d (r₁.headD 0)
    hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hhw) hc2
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := h₂
  have hxs₂ : SpineR m₂ (r₁.tail.headD 0) (r₁.tail.tail.headD 0) xs :=
    hxs.keep hSt₂.size hSt₂.below (by rw [htopN]; exact Nat.le_refl _) hspn₁
  have h₃ := CoreSpec.of_callW (inferSpine_any p hp hkp hq he hil n hk F hF hn ⟨m₂, Locals.init []⟩ _
    dn vis fe M₂ eb mode d (r₂.headD 0) _ _ xs ⟨hS₂, hs.mode4, hs.eb_mode⟩ hrw2 hxs₂
    (by rw [hSt₂.1, htopN]; exact Nat.le_refl _)) hc3
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := h₃
  have hrun : (inferApp (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)).run a₀ =
      .ok (decE (r₃.headD 0), AM.st (inferSpine (coreKnot (decMode mode) fe id F) fe
        d.toNat (decE (r₂.headD 0)) #[] xs 0)
        (AM.st ((coreKnot (decMode mode) fe id F).infer d.toNat (decE (r₁.headD 0))) a₀)) := by
    simp only [inferApp, StateT.run_bind, hha, except_ok_bind]
    have e1 := AM.run_of_ok _ _ hok2
    simp only [decH] at hres2
    rw [hres2] at e1
    rw [e1, except_ok_bind, AM.run_of_ok _ _ hok3, hres3]; rfl
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok, ?_, by rw [hres, decH, hr], by unfold ResH; rw [← hr]; exact hrw3⟩
  rw [hst, ← hm]
  refine ⟨M₃, hS₃.frame_stk (MemFrame.setCtl m₃ 136 _) (by simp) (by simp), hK₂.trans hK₃, ?_⟩
  have hSt23 := hSt₂.trans hSt₃
  exact StackKept.restoreG (hg₁.trans hSt23.toGrew) h136

end L.Arena
