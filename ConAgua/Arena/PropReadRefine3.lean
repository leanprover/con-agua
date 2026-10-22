import ConAgua.Arena.PropReadRefine2
import ConAgua.Arena.InferBodyDisp

/-!
# The prop-ness readers: `headTypePW`, `typeSortPW` (helper `defeq2-prop`)

`head_type_res` (`peelPisW` then `residualPW`), the `.const` arm shared by `headTypePW` and
`headProofPW` (`cArm_ok`, over the datum of the constant's type), `head_type_pw`, `type_sort_pw`.

**The level parameters' names** (`ConstLpsDen`): `substPWAt` reads a stored constant's level
parameters back (`readNamesM`), which fails on a dangling name; `StoreDen` does not state it yet.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

open ConLeche (Name Level PropWhen)

/-- **Hypothesis: a stored constant's level-parameter names read back** (under `CoreS`, for every
constant the view finds that is not a projection table). To be folded into `StoreDen` (the
environment loader stores only names it interned). -/
def ConstLpsDen : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word), CoreS dn m a vis fe M eb →
    ∀ (c : NIdx) (ci : IConstantInfo) (cv : IConstantVal), fe.find? c = some ci →
      ci.isTowerEntry = false → (∀ s, ci.toConstantVal.run s = .ok (cv, s)) →
      ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks

/-! ## Twin fragments -/

/-- `headTypePW`'s residual: `peelPisW` then `residualPW`. -/
def htResT (fe : IFEnv) (f k : Nat) (ty : EIdx) : AM (Option PropWhen) := do
  let res ← ConRon.Arena.peelPisW fe f k ty
  ConRon.Arena.residualPW res

/-- The `.const` arm of `headTypePW` / `headProofPW`, at the datum `T` of the constant's type. -/
def cArmT (fe : IFEnv) (T : EIdx → AM (Option PropWhen)) (I : NIdx) (us : LsIdx) :
    AM (Option PropWhen) :=
  match fe.find? I with
  | some ci =>
    if ci.isTowerEntry then pure none else do
      let cv ← ci.toConstantVal
      match ← viewLsLen us with
      | none => failDanglingLs
      | some usl =>
      if usl = cv.levelParams.length then do
        match ← T cv.type with
        | some pw => substPWAt cv.levelParams us pw
        | none => pure none
      else pure none
  | none => pure none

/-! ## Run forms of the callees -/

section calls
variable {p : Prog} (hp : PropReadProg p) (hden : CoreDen)
include hp hden

theorem rpw_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {fl h : Word}
    (hh : fl ≠ 0 → HW h) {r : List Word} (hc : callW p n "residual_pw" [fl, h] m = some (r, m')) :
    ∃ res, (ConRon.Arena.residualPW (decOpt fl h)).run a = .ok (res, a) ∧
      RdAfter dn m m' a a vis fe M eb ∧
      PWD (nameN a.store.lss.ls.ns) m' (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) res := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (residualPW_spec p hp.rpw n ⟨m, Locals.init []⟩ fl h) hc
  rw [ht] at hW
  exact rpw_ok hp hden hS hh hW

theorem spa_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    {lo lc us k o c : Word} {lps : List NIdx} {pw : PropWhen}
    (hl : hslice? (m.arr64 EREC) lo.toNat lc.toNat = some lps)
    (hks : ∃ ks, lps.mapM (denoteN a.store.ns) = some ks) (hus : HW us)
    (hls : ∃ ls, denoteLs a.store.lss (decI us) = some ls)
    (hd : PWD (nameN a.store.lss.ls.ns) m k o c (some pw)) {r : List Word}
    (hc : callW p n "subst_pw_at" [lo, lc, us, k, o, c] m = some (r, m')) :
    ∃ res a', (substPWAt lps (decI us) pw).run a = .ok (res, a') ∧
      RdAfter dn m m' a a' vis fe M eb ∧
      PWD (nameN a.store.lss.ls.ns) m' (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) res := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (substPWAt_spec p hp.spa hp.lsnode n ⟨m, Locals.init []⟩ lo lc us k o c) hc
  rw [ht] at hW
  exact spa_ok hp hden hS hl hks hus hls hd hW

/-- **`head_type_res` refines `htResT`.** -/
theorem htr_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {f k ty : Word}
    (hf : f.toNat ≤ coreWalkFuel) (hty : HW ty) {r : List Word}
    (hc : callW p n "head_type_res" [vis, f, k, ty] m = some (r, m')) :
    ∃ res, (htResT fe f.toNat k.toNat (decE ty)).run a = .ok (res, a) ∧
      RdAfter dn m m' a a vis fe M eb ∧
      PWD (nameN a.store.lss.ls.ns) m' (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) res := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (headTypeRes_spec p hp n ⟨m, Locals.init []⟩ vis f k ty) hc
  rw [ht] at hW
  rcases hc1 : callW p n "peel_pis_w" [vis, f, k, ty] m with _ | ⟨r₁, m₁⟩
  · rw [hc1] at hW; cases hW
  rw [hc1] at hW
  obtain ⟨hrun₁, hRd₁, hb₁⟩ := ppw_ok hp n hS hf hty hc1
  simp only [htrK] at hW
  rcases hc2 : callW p n "residual_pw" [r₁.headD 0, r₁.tail.headD 0] m₁ with _ | ⟨r₂, m₂⟩
  · rw [hc2] at hW; cases hW
  rw [hc2] at hW
  simp only [t3W, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨h1, h2, h3, rfl⟩ := hW
  obtain ⟨res, hrun₂, hRd₂, hd⟩ := rpw_call hp hden hRd₁.rel hb₁ hc2
  refine ⟨res, ?_, hRd₁.trans hRd₂, ?_⟩
  · simp only [htResT, StateT.run_bind, hrun₁, except_ok_bind, hrun₂]
  · rw [← h1, ← h2, ← h3]; exact hd

end calls

/-! ## The `.const` arm -/

/-- A decoded record of kind `6` is a projection table. -/
theorem decCI_kind6 {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI a dn q.toNat = some ci) (hab : ArrExt a b)
    (hsz : b.size < 2 ^ 63) (h6 : rdW b q = 6) : ci.isTowerEntry = true := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  have hrd : rdW b q = w := by
    have := rdW_ext hab hsz (k := 0) (by decide) (by simpa using hq); simpa using this
  rw [hrd] at h6; subst h6
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some,
    show UInt64.toNat 6 = 6 from rfl, Option.bind_eq_some_iff] at h
  obtain ⟨tbl, -, hc⟩ := h
  cases hc; rfl

section arm
variable {p : Prog} (hp : PropReadProg p) (hden : CoreDen) (hlps : ConstLpsDen)
include hp hden hlps

/-- **The `.const` arm** (`head_type_const`, `head_proof_const`) refines `cArmT` at the sub-call
`sub` that refines `T`. -/
theorem cArm_ok {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {sub : Word → Mem → Option (List Word × Mem)}
    {T : EIdx → AM (Option PropWhen)}
    (hsub : ∀ {m₁ m₂ : Mem} {a₁ : AState} {ty : Word} {r : List Word},
      CoreS dn m₁ a₁ vis fe M eb → HW ty → sub ty m₁ = some (r, m₂) →
      ∃ res a₂, (T (decE ty)).run a₁ = .ok (res, a₂) ∧ RdAfter dn m₁ m₂ a₁ a₂ vis fe M eb ∧
        PWD (nameN a₁.store.lss.ls.ns) m₂ (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) res)
    (hS : CoreS dn m a vis fe M eb) {cn us k o c : Word} (hcn : HW cn) (hus : HW us)
    (hls : ∃ ls, denoteLs a.store.lss (decI us) = some ls)
    (hW : cArmK1 p n us sub (callW p n "env_find" [cn, vis] m) = some (k, o, c, m')) :
    ∃ res a', (cArmT fe T (decI cn) (decI us)).run a = .ok (res, a') ∧
      RdAfter dn m m' a a' vis fe M eb ∧ PWD (nameN a.store.lss.ls.ns) m' k o c res := by
  rcases hc1 : callW p n "env_find" [cn, vis] m with _ | ⟨r₁, m₁⟩
  · rw [hc1] at hW; cases hW
  rw [hc1] at hW
  obtain ⟨rfl, hfind, hfound⟩ := pr_envFind hp hS.env hcn hc1
  simp only [cArmK1] at hW
  by_cases h0 : r₁.headD 0 = 0
  · simp only [h0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    have hnone : fe.find? (decI cn) = none := by rw [hfind]; simp only [decFound, h0, ↓reduceIte]
    exact ⟨none, a, by simp only [cArmT, hnone]; rfl, RdAfter.refl hS, rfl⟩
  simp only [h0, ↓reduceIte] at hW
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  by_cases h6 : rdW (m₁.arr64 EREC) (r₁.tail.headD 0) = 6
  · simp only [h6, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    have htw := decCI_kind6 hci (erecP_ext _) hS.erec h6
    exact ⟨none, a, by simp only [cArmT, hfind', htw, ↓reduceIte]; rfl, RdAfter.refl hS, rfl⟩
  simp only [h6, ↓reduceIte] at hW
  obtain ⟨htw, cv, hcvr, hcv⟩ := decCI_kind_ne6 hci (erecP_ext _) h6
  obtain ⟨hw1, -, hw4, hty, hsl⟩ := infer_decCV_words hcv hS.erec
  by_cases hne : lsNodeW m₁ us = []
  · simp [hne] at hW
  simp only [hne, ↓reduceIte] at hW
  obtain ⟨ids, hv, hlen1, hlen2⟩ := lsNodeW_view hS.arena.1 hus hne
  have hvl := LsStore.viewLen_of_view _ _ _ hv
  have hpre : (cArmT fe T (decI cn) (decI us)).run a =
      (if ids.length = cv.levelParams.length then do
        match ← T cv.type with
        | some pw => substPWAt cv.levelParams (decI us) pw
        | none => pure none
      else pure none).run a := by
    simp only [cArmT, hfind', htw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, hcvr,
      except_ok_bind, show ∀ x, (viewLsLen x).run a = .ok (a.store.lss.viewLen x, a) from
        fun _ => rfl, hvl]
  have hlen : ids.length = cv.levelParams.length ↔
      (lsNodeW m₁ us).tail.headD 0 = rdW (m₁.arr64 EREC) (r₁.tail.headD 0 + 3) := by
    rw [hlen1, hslice?_length hsl, ← hlen2]
    exact ⟨fun h => UInt64.toNat_inj.mp h, fun h => by rw [h]⟩
  by_cases hl : (lsNodeW m₁ us).tail.headD 0 ≠ rdW (m₁.arr64 EREC) (r₁.tail.headD 0 + 3)
  · simp only [hl, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    have : ¬ ids.length = cv.levelParams.length := fun h => hl (hlen.mp h)
    exact ⟨none, a, by rw [hpre]; simp only [this, ↓reduceIte]; rfl, RdAfter.refl hS, rfl⟩
  simp only [hl, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  have hlen' : ids.length = cv.levelParams.length := hlen.mpr (by simpa using hl)
  -- the datum of the type
  rcases hc2 : sub (rdW (m₁.arr64 EREC) (r₁.tail.headD 0 + 4)) m₁ with _ | ⟨r₂, m₂⟩
  · rw [hc2] at hW; cases hW
  rw [hc2] at hW
  obtain ⟨res₂, a₂, hrun₂, hRd₂, hd₂⟩ := hsub hS hw4 hc2
  rw [decE_eq, ← hty] at hrun₂
  have hpre2 : (cArmT fe T (decI cn) (decI us)).run a =
      (match res₂ with
        | some pw => substPWAt cv.levelParams (decI us) pw
        | none => pure none).run a₂ := by
    rw [hpre]; simp only [hlen', ↓reduceIte, StateT.run_bind, hrun₂, except_ok_bind]
  simp only [cArmK2] at hW
  have hst := hRd₂.2.2.2
  by_cases hk0 : r₂.headD 0 = 0
  · simp only [hk0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    have hn : res₂ = none := hd₂.none_iff.mp hk0
    exact ⟨none, a₂, by rw [hpre2, hn]; rfl, hRd₂, rfl⟩
  simp only [hk0, ↓reduceIte] at hW
  obtain ⟨pw, rfl⟩ : ∃ pw, res₂ = some pw := by
    rcases res₂ with _ | pw
    · exact absurd (hd₂.none_iff.mpr rfl) hk0
    · exact ⟨pw, rfl⟩
  rcases hc3 : callW p n "subst_pw_at" [rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 2),
      rdW (m₂.arr64 EREC) (r₁.tail.headD 0 + 3), us, r₂.headD 0, r₂.tail.headD 0,
      r₂.tail.tail.headD 0] m₂ with _ | ⟨r₃, m₃⟩
  · rw [hc3] at hW; cases hW
  rw [hc3] at hW
  simp only [t3W, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨h1, h2, h3, rfl⟩ := hW
  have herec := hRd₂.erec
  obtain ⟨ks, hks⟩ := hlps dn m₁ a vis fe M eb hS _ ci cv hfind' htw hcvr
  obtain ⟨res₃, a₃, hrun₃, hRd₃, hd₃⟩ := spa_call hp hden hRd₂.rel (by rw [herec]; exact hsl)
    ⟨ks, by rw [hst]; exact hks⟩ hus (by rw [hst]; exact hls) (by rw [hst]; exact hd₂) hc3
  refine ⟨res₃, a₃, by rw [hpre2]; exact hrun₃, hRd₂.trans hRd₃, ?_⟩
  rw [hst] at hd₃
  rw [← h1, ← h2, ← h3]; exact hd₃

end arm

end L.Arena
