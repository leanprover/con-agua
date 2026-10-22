import ConAgua.Arena.InferBodyLet

/-!
# The application spines of both bodies (lane `defeq`)

`infer_spine_io`/`infer_app_io` (the io grade: no argument check) and `infer_spine`/
`infer_spine_arg`/`infer_app` (the full grade). The loop of each spine is a named block
(`inferSpineIOW`, spliced into `inferSpineIOL'`, `rfl`-equal to `Infer.lean`'s `inferSpineIOL`), its
model is by L fuel (`spioLoop`, callees through `callW`), the block spec by induction on the
fuel, the refinement by induction on the fuel (`spioFull_ref`, the pattern of `WhnfCoreApp.lean`'s
`peelFull_ref`): the arguments are the slice `(ao, an)` below the entry top `co`, the accumulator
the slice `(co, cn)` at the top; a callee keeps the stack below the top (`StackKept`), so the
arguments survive it.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- A word store as a spec: the bound and the new memory. -/
theorem st64_spec (a : ArrId) (i v : Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ st64 a i v
    ⦃fun _ s' => i.toNat < (s₀.mem.arr64 a).size ∧ s' = { s₀ with mem := s₀.mem.set64 a i v }; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  subst hs
  simp only [st64, StateT.run_bind, StateT.run_get, pure_bind] at hrun
  split at hrun
  · rename_i h
    simp only [StateT.run_set, pure] at hrun
    cases hrun
    exact ⟨h, rfl⟩
  · simp [throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift] at hrun
    cases hrun

theorem w_lt_false {a b : Word} (h : b ≤ a) : (a < b) = False := eq_false (UInt64.not_lt.mpr h)

/-! ## `infer_spine_io`: the loop as a named block -/

/-- The loop of `inferSpineIOL` (Infer.lean), named for its spec. -/
def inferSpineIOW : Stmt := lblk (mode, vis, d, ty, ao, an, co, cn, i, a, t, x, ty2, w, r) {
  while i < an {
    a := SPN.u64[ao + i];
    if ty >> 28 == 6 {
      t := (ty >> 27) & 1;
      x := ty & 134217727;
      if t != 0 && CTL.u64[1] == 0 { abort };
      if CTL.u64[30 + t] <= x { abort };
      if len(SPN.u64) <= co + cn { abort };
      SPN.u64[co + cn] := a;
      cn += 1;
      CTL.u64[136] := co + cn;
      ty := FAREC.u64[x * 4 + t * 2 + 1]
    } else {
      ty2 := call inst_list(ty, co, cn, 0);
      w := call whnf(mode, vis, d, ty2);
      if w >> 28 != 6 { abort };
      t := (w >> 27) & 1;
      x := w & 134217727;
      if t != 0 && CTL.u64[1] == 0 { abort };
      if CTL.u64[30 + t] <= x { abort };
      if len(SPN.u64) <= co { abort };
      SPN.u64[co] := a;
      cn := 1;
      CTL.u64[136] := co + 1;
      ty := FAREC.u64[x * 4 + t * 2 + 1]
    };
    i += 1
  }
}

/-- `inferSpineIOL`, with its loop spliced from `inferSpineIOW`. -/
-- con-ron: none — `inferSpineIOL` itself (`rfl`), its loop a named block for the proof
def inferSpineIOL' : FunDecl :=
    lfn (mode, vis, d, ty, ao, an) locals (co, cn, i, a, t, x, ty2, w, r) {
  co := CTL.u64[136];
  if len(SPN.u64) < co { abort };
  cn := 0;
  i := 0;
  ⟪inferSpineIOW⟫;
  r := call inst_list(ty, co, cn, 0);
  CTL.u64[136] := co;
  return r
}

theorem inferSpineIOL_eq : inferSpineIOL = inferSpineIOL' := rfl

/-- The pushed accumulator's memory: the argument at `co + cn`, the top `co + cn + 1`. -/
def spPush (m : Mem) (co cn a : Word) : Mem := (m.set64 SPN (co + cn) a).set64 CTL 136 (co + (cn + 1))

/-- **The model of the io spine's loop** at L fuel `k`: the exit's `(ty, cn, memory)`. -/
def spioLoop (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Option (Word × Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, mode, vis, d, ty, ao, an, i, co, cn =>
    if i < an then
      if ty >>> 28 = 6 then
        if tierW ty ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
        else if rdW (m.arr64 CTL) (30 + tierW ty) ≤ idxW ty then none
        else if m.len64 SPN ≤ co + cn then none
        else if ¬ (co + cn).toNat < (m.arr64 SPN).size then none
        else if ¬ (136 : Word).toNat < (m.arr64 CTL).size then none
        else spioLoop p k (spPush m co cn (rdW (m.arr64 SPN) (ao + i))) mode vis d
          (rdW (m.arr64 FAREC) (idxW ty * 4 + tierW ty * 2 + 1)) ao an (i + 1) co (cn + 1)
      else
        match callW p k "inst_list" [ty, co, cn, 0] m with
        | none => none
        | some (r₁, m₁) =>
          match callW p k "whnf" [mode, vis, d, r₁.headD 0] m₁ with
          | none => none
          | some (r₂, m₂) =>
            if r₂.headD 0 >>> 28 ≠ 6 then none
            else if tierW (r₂.headD 0) ≠ 0 ∧ rdW (m₂.arr64 CTL) 1 = 0 then none
            else if rdW (m₂.arr64 CTL) (30 + tierW (r₂.headD 0)) ≤ idxW (r₂.headD 0) then none
            else if m₂.len64 SPN ≤ co then none
            else if ¬ co.toNat < (m₂.arr64 SPN).size then none
            else if ¬ (136 : Word).toNat < (m₂.arr64 CTL).size then none
            else spioLoop p k (spPush m₂ co 0 (rdW (m.arr64 SPN) (ao + i))) mode vis d
              (rdW (m₂.arr64 FAREC) (idxW (r₂.headD 0) * 4 + tierW (r₂.headD 0) * 2 + 1)) ao an
              (i + 1) co 1
    else some (ty, cn, m)

theorem inferSpineIOW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n inferSpineIOW
    ⦃fun r s' => r = .normal ∧ s'.loc 6 = s₀.loc 6 ∧
      spioLoop p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)
        (s₀.loc 8) (s₀.loc 6) (s₀.loc 7) = some (s'.loc 3, s'.loc 7, s'.mem); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := inferSpineIOW) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64_spec, ih,
      callW_spec p n "inst_list", callW_spec p n "whnf"] <;>
    simp_all [spioLoop, spPush, Cmp.eval, LocEq, BinOp.eval, tierW, idxW, St.setLocs_cons,
      St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, size_set64, w_lt_false, Mem.arr64_set64_ne]

/-- The tail of a spine: the result type at the accumulator, the top put back. -/
def spTail (p : Prog) (n : Nat) (m : Mem) (ty co cn : Word) : Option (Word × Mem) :=
  match callW p n "inst_list" [ty, co, cn, 0] m with
  | none => none
  | some (r, m₁) => if (136 : Word).toNat < (m₁.arr64 CTL).size then some (r.headD 0, m₁.set64 CTL 136 co)
      else none

/-- The io spine's loop with its tail, at loop fuel `k` and tail fuel `n`. -/
def spioFull (p : Prog) (n k : Nat) (m : Mem) (mode vis d ty ao an i co cn : Word) :
    Option (Word × Mem) :=
  match spioLoop p k m mode vis d ty ao an i co cn with
  | none => none
  | some (ty', cn', m') => spTail p n m' ty' co cn'

/-- **The model of `infer_spine_io`.** -/
def spioFn (p : Prog) (n : Nat) (m : Mem) (mode vis d ty ao an : Word) : Option (Word × Mem) :=
  if m.len64 SPN < rdW (m.arr64 CTL) 136 then none
  else spioFull p n (n + 1) m mode vis d ty ao an 0 (rdW (m.arr64 CTL) 136) 0

/-- What the spine specs need of a program. -/
structure SpineInferProg (p : Prog) : Prop where
  spineIO : p.lookup "infer_spine_io" = some inferSpineIOL
  appIO : p.lookup "infer_app_io" = some inferAppIOL

theorem inferSpineIO_spec (p : Prog) (hq : SpineInferProg p) (n : Nat) (s₀ : St)
    (mode vis d ty ao an : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_spine_io" [mode, vis, d, ty, ao, an]
    ⦃fun r s' => LocEq s' s₀ ∧ spioFn p n s₀.mem mode vis d ty ao an = some (r.headD 0, s'.mem) ∧
      (136 : Word).toNat < (s₀.mem.arr64 CTL).size; ⊤⦄ := by
  rw [invoke_eq _ hq.spineIO, inferSpineIOL_eq]
  simp only [callFn, inferSpineIOL']
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64_spec,
      fun s => Triple.step_exec (inferSpineIOW_spec p (n + 1) s), callW_spec p n "inst_list"] <;>
  simp_all [spioFn, spioFull, spTail, LocEq, BinOp.eval, St.setLocs_cons, CTL, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

/-! ## Pushing onto the accumulator -/

theorem SpineR.empty (m : Mem) (co : Word) (h : co.toNat ≤ (m.arr64 SPN).size) : SpineR m co 0 #[] :=
  ⟨rfl, by simpa using h, fun i hi => by simp at hi, fun i hi => by simp at hi⟩

/-- **A push onto the accumulator at the top**: the slice grows by the word, the top with it, the
stack below the accumulator is kept. -/
theorem spPush_step {m m₀ : Mem} {co cn v : Word} {acc : Array EIdx}
    (hspn : (m.arr64 SPN).size < 2 ^ 63) (hacc : SpineR m co cn acc)
    (hb : ∀ j, j < co → spW m j = spW m₀ j) (hsz : (m.arr64 SPN).size = (m₀.arr64 SPN).size)
    (h136 : (136 : Word).toNat < (m.arr64 CTL).size)
    (hbd : (co + cn).toNat < (m.arr64 SPN).size) (hv : HW v) :
    SpineR (spPush m co cn v) co (cn + 1) (acc.push (decE v)) ∧
      spTop (spPush m co cn v) = co + (cn + 1) ∧
      (∀ j, j < co → spW (spPush m co cn v) j = spW m₀ j) ∧
      ((spPush m co cn v).arr64 SPN).size = (m₀.arr64 SPN).size ∧
      (136 : Word).toNat < ((spPush m co cn v).arr64 CTL).size := by
  have hco_le := hacc.bound
  have hcn64 : co.toNat + cn.toNat < 2 ^ 64 := by omega
  have hadd : (co + cn).toNat = co.toNat + cn.toNat := addW _ _ hcn64
  refine ⟨(hacc.push hspn (by rw [← hadd]; exact hbd) v hv).setCtl 136 (co + (cn + 1)), ?_, ?_,
    by simp only [spPush, size_set64]; exact hsz, by simp only [spPush, size_set64]; exact h136⟩
  · unfold spTop spPush
    rw [rdW_set64, if_pos ⟨rfl, rfl, by rw [size_set64]; exact h136⟩]
  · intro j hj
    simp only [spPush]
    rw [spW_setCtl, spW_set64_ne _ _ _ _ (fun h => by
      have := UInt64.lt_iff_toNat_lt.mp hj
      rw [← h, hadd] at this; omega)]
    exact hb j hj

/-! ## `infer_spine_io` refines `inferSpineIO` -/

/-- The conclusion of a spine run from an inner memory: the twin's run, the result, the relation,
the stack kept from the entry memory `m₀`. -/
def SpPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word)
    (m₀ : Mem) (a : AState) (T : AM EIdx) (w : Word) (mF : Mem) : Prop :=
  ∃ x a', T.run a = .ok (x, a') ∧ x = decE w ∧ HW w ∧
    ∃ M', CoreS dn mF a' vis fe M' eb ∧ KeptAll M M' eb ∧ StackKept m₀ mF

theorem tag_fa_beq (e : Word) (he : HW e) :
    ((decE e).tag == ETag.forallE) = decide (e >>> 28 = 6) := by
  by_cases h : e >>> 28 = 6
  · simp [h, (decE_tag_forall e he).mpr h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    exact fun h' => h ((decE_tag_forall e he).mp h')

theorem succ_toNat_of_lt {i an : Word} (h : i < an) : (i + 1).toNat = i.toNat + 1 := by
  rw [UInt64.toNat_add]; simp
  have := UInt64.lt_iff_toNat_lt.mp h
  have := an.toNat_lt
  omega

/-- The tail of a spine at its exit: the result at the accumulator, the top put back. -/
theorem spTail_ref (p : Prog) (hil : InstListOK p) (n : Nat) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (eb co : Word) (m₀ : Mem) (hco : co = spTop m₀) :
    ∀ (m : Mem) (a : AState) (M : ModeMaps) (ty cn : Word) (acc : Array EIdx),
      CoreS dn m a vis fe M eb → HW ty → SpineR m co cn acc → spTop m = co + cn →
      (∀ j, j < co → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      ∀ w mF, spTail p n m ty co cn = some (w, mF) →
      SpPost dn vis fe M eb m₀ a (instantiateListFast coreWalkFuel (decE ty) acc 0) w mF := by
  intro m a M ty cn acc hS ht hacc htop hb hsz w mF hF
  have hco_le := hacc.bound
  have hspn := hS.spn
  have hcn64 : co.toNat + cn.toNat < 2 ^ 64 := by omega
  have hadd : (co + cn).toNat = co.toNat + cn.toNat := addW _ _ hcn64
  unfold spTail at hF
  obtain ⟨r₁, m₁, h1, hF⟩ := callW_cases (K := fun res => match res with
    | none => none
    | some (r, m₁) => if (136 : Word).toNat < (m₁.arr64 CTL).size then
        some (r.headD 0, m₁.set64 CTL 136 co) else none) rfl hF
  dsimp only at hF
  by_cases h136 : (136 : Word).toNat < (m₁.arr64 CTL).size
  · rw [if_pos h136] at hF
    simp only [Option.some.injEq, Prod.mk.injEq] at hF
    obtain ⟨rfl, rfl⟩ := hF
    have hinst := hil n ⟨m, Locals.init []⟩ a dn vis fe M eb ty co cn 0 acc hS ht hacc
      (by rw [htop, hadd]; exact Nat.le_refl _)
    obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hrw⟩ := CoreSpec.of_callW hinst h1
    have h0 : (0 : Word).toNat = 0 := rfl
    rw [h0] at hok hres hS'
    refine ⟨_, _, AM.run_of_ok _ _ hok, hres, hrw, M', ?_, hK', ?_⟩
    · exact hS'.frame_stk (MemFrame.setCtl m₁ 136 co) (by simp) (by simp)
    · exact peel_restore hco hb hsz hSt' htop hcn64 h136
  · rw [if_neg h136] at hF; cases hF

theorem spioFull_zero (p : Prog) (n : Nat) (m : Mem) (mode vis d ty ao an i co cn : Word) :
    spioFull p n 0 m mode vis d ty ao an i co cn = none := rfl

theorem spioFull_exit (p : Prog) (n k : Nat) (m : Mem) (mode vis d ty ao an i co cn : Word)
    (h : ¬ i < an) : spioFull p n (k + 1) m mode vis d ty ao an i co cn = spTail p n m ty co cn := by
  simp [spioFull, spioLoop, h]

/-- **The io spine's loop refines `inferSpineIO`** by induction on the loop fuel. -/
theorem spioFull_ref (p : Prog) (hil : InstListOK p) (N : Nat) (hk : KnotUpTo p N) (F : Nat)
    (hF : N ≤ F) (hN : N ≤ 2 ^ 62) (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (mode d ao an : Word) (args : Array EIdx) (eb co : Word) (hmode : mode < 4)
    (heb : eb = (mode >>> 1) &&& 1) (m₀ : Mem) (har₀ : SpineR m₀ ao an args)
    (hco : co = spTop m₀) (hlo : ao.toNat + an.toNat ≤ co.toNat) :
    ∀ k, k ≤ N + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (ty i cn : Word) (acc : Array EIdx),
      CoreS dn m a vis fe M eb → HW ty → SpineR m co cn acc → spTop m = co + cn →
      (∀ j, j < co → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      (136 : Word).toNat < (m.arr64 CTL).size →
      ∀ w mF, spioFull p n k m mode vis d ty ao an i co cn = some (w, mF) →
      SpPost dn vis fe M eb m₀ a
        (inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE ty) acc
          args i.toNat) w mF := by
  intro k
  induction k with
  | zero => intro _ m a M ty i cn acc _ _ _ _ _ _ _ w mF hF; rw [spioFull_zero] at hF; cases hF
  | succ k ih =>
    intro hkN m a M ty i cn acc hS ht hacc htop hb hsz h136m w mF hF
    have hspn := hS.spn
    have hco_le : co.toNat + cn.toNat ≤ (m.arr64 SPN).size := hacc.bound
    have hcn64 : co.toNat + cn.toNat < 2 ^ 64 := by omega
    have hadd : (co + cn).toNat = co.toNat + cn.toNat := addW _ _ hcn64
    have hspT : (spTop m).toNat = co.toNat + cn.toNat := by rw [htop, hadd]
    have har : SpineR m ao an args := har₀.keepT co hsz hb hlo (hsz ▸ hspn)
    by_cases hlt : i < an
    · have hlt' : i.toNat < args.size := by rw [har₀.size]; exact UInt64.lt_iff_toNat_lt.mp hlt
      have hit : (i.toNat).toUInt64 = i := by simp
      have hxi : args[i.toNat] = decE (spW m (ao + i)) := by
        have h := har.get i.toNat hlt'; rwa [hit] at h
      have hvv : HW (spW m (ao + i)) := by
        have h := har.lt i.toNat (by rw [← har.size]; exact hlt'); rwa [hit] at h
      have hi1 := succ_toNat_of_lt hlt
      by_cases ht6 : ty >>> 28 = 6
      · -- the ∀ step: the argument is pushed
        simp only [spioFull, spioLoop, hlt, ht6, ↓reduceIte] at hF
        by_cases c1 : tierW ty ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
        · rw [if_pos c1] at hF; cases hF
        rw [if_neg c1] at hF
        by_cases c2 : rdW (m.arr64 CTL) (30 + tierW ty) ≤ idxW ty
        · rw [if_pos c2] at hF; cases hF
        rw [if_neg c2] at hF
        by_cases c3 : m.len64 SPN ≤ co + cn
        · rw [if_pos c3] at hF; cases hF
        rw [if_neg c3] at hF
        by_cases c4 : ¬ (co + cn).toNat < (m.arr64 SPN).size
        · rw [if_pos c4] at hF; cases hF
        rw [if_neg c4] at hF
        by_cases c5 : ¬ (136 : Word).toNat < (m.arr64 CTL).size
        · rw [if_pos c5] at hF; cases hF
        rw [if_neg c5] at hF
        have hv : viewOK m ty 30 := ⟨c1, UInt64.not_le.mp c2⟩
        obtain ⟨-, -, hbody⟩ := view_forall m a hS.arena.1 ty ht hv ht6
        have hvb := viewBind_forall m a hS.arena.1 ty ht hv ht6
        obtain ⟨hacc', htop', hb', hsz', h136'⟩ := spPush_step hspn hacc hb hsz h136m
          (by simpa using c4) hvv
        have hS' := hS.frame_stk (spnCtl_frame m (co + cn) (spW m (ao + i)) (co + (cn + 1)))
          (by simp) (by simp)
        obtain ⟨x, a', hrun', hx, hrw, M', hS'', hK, hSt⟩ := ih (by omega) _ a M _ (i + 1) (cn + 1)
          _ hS' hbody hacc' htop' hb' hsz' h136' w mF hF
        refine ⟨x, a', ?_, hx, hrw, M', hS'', hK, hSt⟩
        rw [← hrun', inferSpineIO]
        simp only [hlt', dite_true, tag_fa_beq ty ht, ht6, decide_true, ite_true, StateT.run_bind,
          viewBind_run', hvb, except_ok_bind, hxi, hi1]
      · -- the `whnf` re-entry: the accumulator restarts at `#[a]`
        cases h1 : callW p k "inst_list" [ty, co, cn, 0] m with
        | none => simp only [spioFull, spioLoop, hlt, ht6, h1, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        | some q =>
        obtain ⟨r₁, m₁⟩ := q
        cases h2 : callW p k "whnf" [mode, vis, d, r₁.headD 0] m₁ with
        | none => simp only [spioFull, spioLoop, hlt, ht6, h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        | some q =>
        obtain ⟨r₂, m₂⟩ := q
        have g1 : r₂.headD 0 >>> 28 = 6 := Classical.byContradiction fun g => by
          simp only [spioFull, spioLoop, hlt, ht6, h1, h2, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have g2 : ¬ (tierW (r₂.headD 0) ≠ 0 ∧ rdW (m₂.arr64 CTL) 1 = 0) := fun g => by
          simp only [spioFull, spioLoop, hlt, ht6, h1, h2, g1, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have g3 : ¬ rdW (m₂.arr64 CTL) (30 + tierW (r₂.headD 0)) ≤ idxW (r₂.headD 0) := fun g => by
          simp only [spioFull, spioLoop, hlt, ht6, h1, h2, g1, g2, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have g4 : ¬ m₂.len64 SPN ≤ co := fun g => by
          simp only [spioFull, spioLoop, hlt, ht6, h1, h2, g1, g2, g3, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have g5 : co.toNat < (m₂.arr64 SPN).size := Classical.byContradiction fun g => by
          simp only [spioFull, spioLoop, hlt, ht6, h1, h2, g1, g2, g3, g4, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have g6 : (136 : Word).toNat < (m₂.arr64 CTL).size := Classical.byContradiction fun g => by
          simp only [spioFull, spioLoop, hlt, ht6, h1, h2, g1, g2, g3, g4, g5, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
        have hF' : spioFull p n k (spPush m₂ co 0 (rdW (m.arr64 SPN) (ao + i))) mode vis d
            (rdW (m₂.arr64 FAREC) (idxW (r₂.headD 0) * 4 + tierW (r₂.headD 0) * 2 + 1)) ao an
            (i + 1) co 1 = some (w, mF) := by
          simpa only [spioFull, spioLoop, hlt, ht6, h1, h2, g1, g2, g3, g4, g5, g6, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] using hF
        -- `inst_list` at the accumulator, then `whnf`
        have hinst := hil k ⟨m, Locals.init []⟩ a dn vis fe M eb ty co cn 0 acc hS ht hacc
          (by rw [hspT]; exact Nat.le_refl _)
        obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW hinst h1
        have h0 : (0 : Word).toNat = 0 := rfl
        rw [h0] at hok1 hres1 hS₁
        have hw := CoreSpec.of_callW ((hk k (by omega)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
          mode d (r₁.headD 0) (by omega) (by omega) ⟨hS₁, hmode, heb⟩ hrw1) h2
        obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := hw
        have hSt12 := hSt₁.trans hSt₂
        have hb₂ : ∀ j, j < co → spW m₂ j = spW m₀ j := by
          intro j hj
          have hj' : j < spTop m := by
            rw [htop, UInt64.lt_iff_toNat_lt, hadd]
            have := UInt64.lt_iff_toNat_lt.mp hj; omega
          exact (hSt12.2.2 j hj').trans (hb j hj)
        have hsz₂ : (m₂.arr64 SPN).size = (m₀.arr64 SPN).size := hSt12.2.1.trans hsz
        have hv : viewOK m₂ (r₂.headD 0) 30 := ⟨g2, UInt64.not_le.mp g3⟩
        obtain ⟨-, -, hbody⟩ := view_forall m₂ _ hS₂.arena.1 (r₂.headD 0) hrw2 hv g1
        have hvb := viewBind_forall m₂ _ hS₂.arena.1 (r₂.headD 0) hrw2 hv g1
        have hacc0 := SpineR.empty m₂ co (by omega)
        obtain ⟨hacc', htop', hb', hsz', h136'⟩ := spPush_step (cn := 0) hS₂.spn hacc0 hb₂ hsz₂ g6
          (by simpa using g5) hvv
        have hS' := hS₂.frame_stk (spnCtl_frame m₂ (co + 0) (spW m (ao + i)) (co + (0 + 1)))
          (by simp) (by simp)
        obtain ⟨x, a', hrun', hx, hrw, M', hS'', hK, hSt⟩ := ih (by omega) _ _ M₂ _ (i + 1) 1
          _ hS' hbody hacc' htop' hb' hsz' h136' w mF hF'
        refine ⟨x, a', ?_, hx, hrw, M', hS'', hK₁.trans (hK₂.trans hK), hSt⟩
        rw [← hrun', inferSpineIO]
        have hnfa : ((decE ty).tag == ETag.forallE) = false := by rw [tag_fa_beq ty ht]; simp [ht6]
        have hfa : ((decE (r₂.headD 0)).tag == ETag.forallE) = true := by
          rw [tag_fa_beq _ hrw2]; exact decide_eq_true g1
        simp only [hlt', dite_true, hnfa, Bool.false_eq_true, ite_false, StateT.run_bind,
          AM.run_of_ok _ _ hok1, except_ok_bind, hxi, hi1]
        rw [hres1]
        simp only [decH, show (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)).whnf =
          (coreKnot (decMode mode) fe id F).whnf from rfl]
        rw [AM.run_of_ok _ _ hok2, hres2]
        simp only [except_ok_bind, decH, hfa, ite_true, StateT.run_bind, viewBind_run', hvb]
        rfl
    · rw [spioFull_exit _ _ _ _ _ _ _ _ _ _ _ _ _ hlt] at hF
      obtain ⟨x, a', hrun, hx, hrw, M', hS', hK, hSt⟩ :=
        spTail_ref p hil n dn vis fe eb co m₀ hco m a M ty cn acc hS ht hacc htop hb hsz w mF hF
      have hnlt : ¬ i.toNat < args.size := by
        rw [har₀.size]; exact fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      refine ⟨x, a', ?_, hx, hrw, M', hS', hK, hSt⟩
      rw [inferSpineIO]
      simp only [hnlt, dite_false]
      exact hrun

theorem len64_not_lt {m : Mem} {co : Word} (hspn : (m.arr64 SPN).size < 2 ^ 63)
    (h : ¬ m.len64 SPN < co) : co.toNat ≤ (m.arr64 SPN).size := by
  have h' := UInt64.not_lt.mp h
  rw [UInt64.le_iff_toNat_le, Mem.len64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at h'
  exact h'

/-- **`infer_spine_io` refines `inferSpineIO`** at the io view of the knot, the head's type `ty`
and the arguments the slice `(ao, an)` below the top. -/
@[refines ConRon.Arena.inferSpineIO]
theorem inferSpineIO_refines (p : Prog) (hq : SpineInferProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (ht : HW ty) (har : SpineR s₀.mem ao an args)
    (hlo : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpec p (n + 1) "infer_spine_io" [mode, vis, d, ty, ao, an]
      (inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE ty) #[]
        args 0) decH s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW, h136⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferSpineIO_spec p hq n s₀ mode vis d ty ao an)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold spioFn at hW
  by_cases hc : s.mem.len64 SPN < rdW (s.mem.arr64 CTL) 136
  · rw [if_pos hc] at hW; cases hW
  rw [if_neg hc] at hW
  have hcle := len64_not_lt hS.spn hc
  obtain ⟨x, a', hrun', hx, hrw, M', hS', hK, hSt⟩ := spioFull_ref p hil n hk F hF hn n dn vis fe
    mode d ao an args eb _ hs.mode4 hs.eb_mode s.mem har rfl hlo (n + 1) (Nat.le_refl _) s.mem a₀ M
    ty 0 0 #[] hS ht (SpineR.empty _ _ hcle) (by simp [spTop]) (fun _ _ => rfl) rfl h136 _ _ hW
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [h0] at hrun'
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hok, ?_, by rw [hres, hx]; rfl, hrw⟩
  rw [hst]; exact ⟨M', hS', hK, hSt⟩

end L.Arena
