import ConAgua.Arena.InstLP
import ConAgua.Arena.LsRefine
import ConAgua.Census.Attr

/-!
# The level-list functions of `InstLP.lean`: models and specs

Word-level models (`…W`) of `sle_go`, `slp_go`, `sls_go`, `spn_pool`, `spn_ls`,
`rec_fire_levels`, each proved by `vcgen` + `finish` from its callees' models.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## `sle_go` / `sls_go`: substitute and intern each element of a slice -/

section elems
variable (A : ArrId)

mutual
/-- **The model of `sle_go`** (`A = EREC`) and `sls_go` (`A = POOL`). -/
def slElemW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, o, l, b, ko, kc, vo, vc =>
    if l = 0 then some m
    else slElemK n o l b ko kc vo vc (lvSubIntW n m (rdW (m.arr64 A) o) ko kc vo vc)

/-- After the element: check, store, the rest. -/
def slElemK (n : Nat) (o l b ko kc vo vc : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (h, m₁) =>
    if 4294967296 ≤ h then none else slElemW n (m₁.set64 SPN b h) (o + 1) (l - 1) (b + 1) ko kc vo vc
end

theorem slElemW_nil (n : Nat) (m : Mem) (o l b ko kc vo vc : Word) (h : l = 0) :
    slElemW A (n + 1) m o l b ko kc vo vc = some m := by rw [slElemW]; simp [h]
theorem slElemW_cons (n : Nat) (m : Mem) (o l b ko kc vo vc : Word) (h : l ≠ 0) :
    slElemW A (n + 1) m o l b ko kc vo vc =
      slElemK A n o l b ko kc vo vc (lvSubIntW n m (rdW (m.arr64 A) o) ko kc vo vc) := by
  rw [slElemW]; simp [h]
theorem slElemK_some (n : Nat) (o l b ko kc vo vc h : Word) (m₁ : Mem) :
    slElemK A n o l b ko kc vo vc (some (h, m₁)) =
      if 4294967296 ≤ h then none else slElemW A n (m₁.set64 SPN b h) (o + 1) (l - 1) (b + 1) ko kc vo vc := by
  rw [slElemK]

end elems

grind_pattern [arena_grind] slElemW_nil => slElemW A (n + 1) m o l b ko kc vo vc
grind_pattern [arena_grind] slElemW_cons => slElemW A (n + 1) m o l b ko kc vo vc
attribute [arena_grind =] slElemK_some

/-! ## `slp_go`: the parameters' substitutes -/

/-- The level of a parameter `w`: its value interned, or the parameter node. -/
def slpOne (n : Nat) (m : Mem) (w : Word) : Option (Word × Word) → Option (Word × Mem)
  | none => none
  | some (f, v) => if f ≠ 0 then lvInternW n m v else pinternW m w

mutual
/-- **The model of `slp_go`.** -/
def slpW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, o, l, b, ko, kc, vo, vc =>
    if l = 0 then some m
    else slpK n o l b ko kc vo vc
      (slpOne n m (rdW (m.arr64 EREC) o) (lookupW SPN POOL n m ko kc vo vc (rdW (m.arr64 EREC) o)))

/-- After the parameter: check, store, the rest. -/
def slpK (n : Nat) (o l b ko kc vo vc : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (h, m₁) =>
    if 4294967296 ≤ h then none else slpW n (m₁.set64 SPN b h) (o + 1) (l - 1) (b + 1) ko kc vo vc
end

theorem slpW_nil (n : Nat) (m : Mem) (o l b ko kc vo vc : Word) (h : l = 0) :
    slpW (n + 1) m o l b ko kc vo vc = some m := by rw [slpW]; simp [h]
theorem slpW_cons (n : Nat) (m : Mem) (o l b ko kc vo vc : Word) (h : l ≠ 0) :
    slpW (n + 1) m o l b ko kc vo vc = slpK n o l b ko kc vo vc
      (slpOne n m (rdW (m.arr64 EREC) o) (lookupW SPN POOL n m ko kc vo vc (rdW (m.arr64 EREC) o))) := by
  rw [slpW]; simp [h]
theorem slpK_some (n : Nat) (o l b ko kc vo vc h : Word) (m₁ : Mem) :
    slpK n o l b ko kc vo vc (some (h, m₁)) =
      if 4294967296 ≤ h then none else slpW n (m₁.set64 SPN b h) (o + 1) (l - 1) (b + 1) ko kc vo vc := by
  rw [slpK]
theorem slpOne_hit (n : Nat) (m : Mem) (w f v : Word) (hf : f ≠ 0) :
    slpOne n m w (some (f, v)) = lvInternW n m v := by simp [slpOne, hf]
theorem slpOne_miss (n : Nat) (m : Mem) (w v : Word) : slpOne n m w (some (0, v)) = pinternW m w := by
  simp [slpOne]

grind_pattern [arena_grind] slpW_nil => slpW (n + 1) m o l b ko kc vo vc
grind_pattern [arena_grind] slpW_cons => slpW (n + 1) m o l b ko kc vo vc
attribute [arena_grind =] slpK_some
grind_pattern [arena_grind] slpOne_hit => slpOne n m w (some (f, v))
attribute [arena_grind =] slpOne_miss

/-! ## `spn_pool`, `spn_ls`: the stack slice to the pool, interned -/

/-- **The model of `spn_pool`.** -/
def spnPoolW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, b, d, l =>
    if l = 0 then some m
    else spnPoolW n (m.set64 POOL d (rdW (m.arr64 SPN) b)) (b + 1) (d + 1) (l - 1)

theorem spnPoolW_nil (n : Nat) (m : Mem) (b d l : Word) (h : l = 0) :
    spnPoolW (n + 1) m b d l = some m := by simp [spnPoolW, h]
theorem spnPoolW_cons (n : Nat) (m : Mem) (b d l : Word) (h : l ≠ 0) :
    spnPoolW (n + 1) m b d l = spnPoolW n (m.set64 POOL d (rdW (m.arr64 SPN) b)) (b + 1) (d + 1) (l - 1) := by
  simp [spnPoolW, h]
grind_pattern [arena_grind] spnPoolW_nil => spnPoolW (n + 1) m b d l
grind_pattern [arena_grind] spnPoolW_cons => spnPoolW (n + 1) m b d l

theorem spnPoolW_size (n : Nat) : ∀ (m m' : Mem) (b d l : Word), spnPoolW n m b d l = some m' →
    ∀ A, (m'.arr64 A).size = (m.arr64 A).size := by
  induction n with
  | zero => intro m m' b d l h; simp [spnPoolW] at h
  | succ n ih =>
    intro m m' b d l h A
    by_cases hl : l = 0
    · rw [spnPoolW_nil n m b d l hl] at h; cases h; rfl
    · rw [spnPoolW_cons n m b d l hl] at h
      rw [ih _ _ _ _ _ h A]
      by_cases hA : A = POOL
      · subst hA; exact Mem.size_arr64_set64 _ _ _ _
      · rw [Mem.arr64_set64_ne _ _ _ _ _ hA]
grind_pattern [arena_grind] spnPoolW_size => spnPoolW n m b d l, (m'.arr64 A).size

/-- After the copy: the top raised, the list interned, the handle checked. -/
def spnLsK (l : Word) (top : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m₁ =>
    match lsinternW (m₁.set64 CTL 0 (top + l)) top l with
    | none => none
    | some (h, m₂) => if 4294967296 ≤ h then none else some (h, m₂)

@[arena_grind =] theorem spnLsK_some (l top : Word) (m₁ : Mem) :
    spnLsK l top (some m₁) = match lsinternW (m₁.set64 CTL 0 (top + l)) top l with
      | none => none
      | some (h, m₂) => if 4294967296 ≤ h then none else some (h, m₂) := rfl

/-- **The model of `spn_ls`.** -/
def spnLsW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, b, l =>
    if m.len64 POOL < m.top then none
    else if m.len64 POOL - m.top < l then none
    else spnLsK l m.top (spnPoolW n m b m.top l)

/-! ## `rec_fire_levels` (a model over its callees' runs, `callW`) -/

/-- After the keys: the branch of the fire kind, the list interned, the stack top put back. -/
def rflK (p : Prog) (n : Nat) (fk fvo fvc qo qc pc vo vc : Word) :
    Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (bs, m₁) =>
    if fk ≠ 0 then
      if m₁.len64 SPN < spTop m₁ then none
      else if m₁.len64 SPN - spTop m₁ < fvc then none
      else match callW p n "sle_go" [fvo, fvc, spTop m₁, bs.headD 0, pc, vo, vc] m₁ with
        | none => none
        | some (_, m₂) => match callW p n "spn_ls" [spTop m₁, fvc] m₂ with
          | none => none
          | some (rs, m₃) => some (rs.headD 0, m₃.set64 CTL 136 (bs.headD 0))
    else
      if m₁.len64 SPN < spTop m₁ then none
      else if m₁.len64 SPN - spTop m₁ < qc then none
      else match callW p n "slp_go" [qo, qc, spTop m₁, bs.headD 0, pc, vo, vc] m₁ with
        | none => none
        | some (_, m₂) => match callW p n "spn_ls" [spTop m₁, qc] m₂ with
          | none => none
          | some (rs, m₃) => some (rs.headD 0, m₃.set64 CTL 136 (bs.headD 0))

/-- **The model of `rec_fire_levels`** at L fuel `n + 1` (its callees at `n`). -/
def recFireLevelsW (p : Prog) (n : Nat) (m : Mem) (fk fvo fvc po pc us qo qc : Word) :
    Option (Word × Mem) :=
  match callW p n "ls_node" [us] m with
  | none => none
  | some (vs, m₀) => rflK p n fk fvo fvc qo qc pc (vs.headD 0) (vs.tail.headD 0)
      (callW p n "keys_push" [po, pc] m₀)

/-! ## The specs -/

/-- A memory read as `rdW` (as `InferBodyIntern.lean`'s `ld64_rdW_spec`, not imported here). -/
theorem lp_ld64_spec (a : ArrId) (i : Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ ld64 a i
    ⦃fun r s' => s' = s₀ ∧ r = rdW (s₀.mem.arr64 a) i ∧ i.toNat < (s₀.mem.arr64 a).size; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  subst hs
  simp only [ld64, StateT.run_bind, StateT.run_get, pure_bind] at hrun
  split at hrun
  · rename_i h
    simp only [pure] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨rfl, by simp [rdW, h], h⟩
  · simp [throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift] at hrun
    cases hrun

/-- What the list functions need of the program. -/
structure LsProg (p : Prog) : Prop extends LvSubProg p where
  sle_go : p.lookup "sle_go" = some sleGo
  sls_go : p.lookup "sls_go" = some slsGo
  slp_go : p.lookup "slp_go" = some slpGo
  spn_pool : p.lookup "spn_pool" = some spnPool
  spn_ls : p.lookup "spn_ls" = some spnLs
  rec_fire_levels : p.lookup "rec_fire_levels" = some recFireLevelsL
  lit_hash : p.lookup "lit_hash" = some litHash
  limbs_eq : p.lookup "limbs_eq" = some limbsEq
  ls_match : p.lookup "ls_match" = some lsMatch
  ls_find : p.lookup "ls_find" = some lsFind
  ls_push : p.lookup "ls_push" = some lsPush
  intern_ls : p.lookup "intern_ls" = some internLs

section spec
variable (p : Prog) (hL : LsProg p)
include hL

theorem sleGo_spec (n : Nat) : ∀ (s₀ : St) (o l b ko kc vo vc : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sle_go" [o, l, b, ko, kc, vo, vc]
    ⦃fun _ s' => LocEq s' s₀ ∧ slElemW EREC n s₀.mem o l b ko kc vo vc = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l b ko kc vo vc; rw [invoke_eq _ hL.sle_go]; simp only [callFn, sleGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l b ko kc vo vc
    rw [invoke_eq _ hL.sle_go]
    simp only [callFn, sleGo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        lvSubInt_spec p hL.toLvSubProg n, ih] <;>
      finish

theorem slsGo_spec (n : Nat) : ∀ (s₀ : St) (o l b ko kc vo vc : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sls_go" [o, l, b, ko, kc, vo, vc]
    ⦃fun _ s' => LocEq s' s₀ ∧ slElemW POOL n s₀.mem o l b ko kc vo vc = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l b ko kc vo vc; rw [invoke_eq _ hL.sls_go]; simp only [callFn, slsGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l b ko kc vo vc
    rw [invoke_eq _ hL.sls_go]
    simp only [callFn, slsGo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        lvSubInt_spec p hL.toLvSubProg n, ih] <;>
      finish

theorem slpGo_spec (n : Nat) : ∀ (s₀ : St) (o l b ko kc vo vc : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "slp_go" [o, l, b, ko, kc, vo, vc]
    ⦃fun _ s' => LocEq s' s₀ ∧ slpW n s₀.mem o l b ko kc vo vc = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l b ko kc vo vc; rw [invoke_eq _ hL.slp_go]; simp only [callFn, slpGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l b ko kc vo vc
    rw [invoke_eq _ hL.slp_go]
    simp only [callFn, slpGo]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        lpLookup_spec p hL.lp_lookup n, lvIntern_spec p hL.toLvInternProg n,
        internParam_spec p hL.param_find hL.param_push hL.intern_param n, ih] <;>
      finish

theorem spnPool_spec (n : Nat) : ∀ (s₀ : St) (b d l : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "spn_pool" [b, d, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ spnPoolW n s₀.mem b d l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ b d l; rw [invoke_eq _ hL.spn_pool]; simp only [callFn, spnPool]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ b d l
    rw [invoke_eq _ hL.spn_pool]
    simp only [callFn, spnPool]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish

theorem spnLs_spec (n : Nat) (s₀ : St) (b l : Word) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 63) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "spn_ls" [b, l]
    ⦃fun r s' => LocEq s' s₀ ∧ spnLsW n s₀.mem b l = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.spn_ls]
  simp only [callFn, spnLs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        spnPool_spec p hL n,
        internLs_spec p hL.lit_hash hL.limbs_eq hL.ls_match hL.ls_find hL.ls_push hL.intern_ls n] <;>
      finish [spnLsW]

theorem recFireLevels_spec (n : Nat) (s₀ : St) (fk fvo fvc po pc us qo qc : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "rec_fire_levels" [fk, fvo, fvc, po, pc, us, qo, qc]
    ⦃fun r s' => LocEq s' s₀ ∧
      recFireLevelsW p n s₀.mem fk fvo fvc po pc us qo qc = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.rec_fire_levels]
  simp only [callFn, recFireLevelsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lp_ld64_spec, st64,
      callW_spec p n "ls_node", callW_spec p n "keys_push", callW_spec p n "sle_go",
      callW_spec p n "slp_go", callW_spec p n "spn_ls"] <;>
  simp_all [recFireLevelsW, rflK, spTop, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc,
    St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

end spec

end L.Arena
