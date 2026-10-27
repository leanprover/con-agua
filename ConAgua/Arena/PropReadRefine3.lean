import ConAgua.Arena.PropReadRefine2
import ConAgua.Arena.InferBodyDisp
import ConAgua.Census.Attr

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


namespace L.Arena

open ConLeche (Name Level PropWhen)

/-- **Hypothesis: a stored constant's level-parameter names read back** (under `CoreS`, for every
constant the view finds). To be folded into `StoreDen` (the environment loader stores only names
it interned). -/
def ConstLpsDen : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word), CoreS dn m a vis fe M eb →
    ∀ (c : NIdx) (ci : IConstantInfo), fe.find? c = some ci →
      ∃ ks, ci.toConstantVal.levelParams.mapM (denoteN a.store.ns) = some ks

/-! ## Twin fragments -/

/-- `headTypePW`'s residual: `peelPisW` then `residualPW`. -/
def htResT (fe : IFEnv) (f k : Nat) (ty : EIdx) : AM (Option PropWhen) := do
  let res ← ConRon.Arena.peelPisW fe f k ty
  ConRon.Arena.residualPW res

/-- The `.const` arm of `headTypePW` / `headProofPW`, at the datum `T` of the constant's type. -/
def cArmT (fe : IFEnv) (T : EIdx → AM (Option PropWhen)) (I : NIdx) (us : LsIdx) :
    AM (Option PropWhen) :=
  match fe.find? I with
  | some ci => do
    let cv := ci.toConstantVal
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

@[refines ConRon.Arena.residualPW]
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
    (residualPW_spec p (hp.get "residual_pw") n ⟨m, Locals.init []⟩ fl h) hc
  rw [ht] at hW
  exact rpw_ok hp hden hS hh hW

@[refines ConRon.Arena.substPWAt]
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
    (substPWAt_spec p (hp.get "subst_pw_at") (hp.get "ls_node") n ⟨m, Locals.init []⟩ lo lc us k o c) hc
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
  rcases hc1 : callW p n "peel_pis_w" [vis, f, k, ty] m with _ | ⟨r₁, m₁⟩ <;> rw [hc1] at hW
  · cases hW
  obtain ⟨hrun₁, hRd₁, hb₁⟩ := ppw_ok hp n hS hf hty hc1
  simp only [htrK] at hW
  rcases hc2 : callW p n "residual_pw" [r₁.headD 0, r₁.tail.headD 0] m₁ with _ | ⟨r₂, m₂⟩ <;>
    rw [hc2] at hW
  · cases hW
  simp only [t3W, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨h1, h2, h3, rfl⟩ := hW
  obtain ⟨res, hrun₂, hRd₂, hd⟩ := rpw_call hp hden hRd₁.rel hb₁ hc2
  refine ⟨res, ?_, hRd₁.trans hRd₂, ?_⟩
  · simp only [htResT, StateT.run_bind, hrun₁, except_ok_bind, hrun₂]
  · rw [← h1, ← h2, ← h3]; exact hd

end calls

/-! ## The `.const` arm -/

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
  rcases hc1 : callW p n "env_find" [cn, vis] m with _ | ⟨r₁, m₁⟩ <;> rw [hc1] at hW
  · cases hW
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
  have hcv := decCI_cvA hci (erecP_ext _)
  generalize hcvr : ci.toConstantVal = cv at hcv
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
    simp only [cArmT, hfind', StateT.run_bind, hcvr,
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
  simp only [hl, ↓reduceIte] at hW
  have hlen' : ids.length = cv.levelParams.length := hlen.mpr (by simpa using hl)
  -- the datum of the type
  rcases hc2 : sub (rdW (m₁.arr64 EREC) (r₁.tail.headD 0 + 4)) m₁ with _ | ⟨r₂, m₂⟩ <;>
    rw [hc2] at hW
  · cases hW
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
  obtain ⟨ks, hks⟩ := hlps dn m₁ a vis fe M eb hS _ ci hfind'
  rw [hcvr] at hks
  obtain ⟨res₃, a₃, hrun₃, hRd₃, hd₃⟩ := spa_call hp hden hRd₂.rel (by rw [herec]; exact hsl)
    ⟨ks, by rw [hst]; exact hks⟩ hus (by rw [hst]; exact hls) (by rw [hst]; exact hd₂) hc3
  refine ⟨res₃, a₃, by rw [hpre2]; exact hrun₃, hRd₂.trans hRd₃, ?_⟩
  rw [hst] at hd₃
  rw [← h1, ← h2, ← h3]; exact hd₃

end arm

/-! ## `head_type_pw`, `type_sort_pw` -/

theorem pr_getD1 (l : List Word) : l.getD 1 0 = l.tail.headD 0 := by
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩ <;> rfl
theorem pr_getD2 (l : List Word) : l.getD 2 0 = l.tail.tail.headD 0 := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩ <;> rfl

/-- `headTypePW`'s `.const` arm is `cArmT` at `htResT`. -/
theorem headTypePW_const (fe : IFEnv) (f : Nat) (root : EIdx) (d : Nat) (h : EIdx) (k : Nat)
    (a : AState) (I : NIdx) (us : LsIdx) (hv : a.store.view h = some (.const I us)) :
    (headTypePW fe f root d h k).run a = (cArmT fe (htResT fe f k) I us).run a := by
  simp only [headTypePW, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, cArmT, htResT,
    bind_assoc]
  rfl

section htp
variable {p : Prog} (hp : PropReadProg p) (hden : CoreDen) (hlps : ConstLpsDen)
include hp hden hlps

/-- **`head_type_pw` refines `headTypePW`.** -/
@[refines ConRon.Arena.headTypePW]
theorem htp_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {f root d h k : Word}
    (hf : f.toNat ≤ coreWalkFuel) (hroot : HW root) (_hh : HW h) {r : List Word}
    (hc : callW p n "head_type_pw" [vis, f, root, d, h, k] m = some (r, m')) :
    ∃ res a', (headTypePW fe f.toNat (decE root) d.toNat (decE h) k.toNat).run a = .ok (res, a') ∧
      RdAfter dn m m' a a' vis fe M eb ∧
      PWD (nameN a.store.lss.ls.ns) m' (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) res := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (headTypePW_spec p hp n ⟨m, Locals.init []⟩ vis f root d h k) hc
  rw [ht] at hW
  generalize r.headD 0 = x₀ at hW ⊢
  generalize r.tail.headD 0 = x₁ at hW ⊢
  generalize r.tail.tail.headD 0 = x₂ at hW ⊢
  have hR := hS.arena.1
  unfold htpW at hW
  by_cases hne : L.Ind.eViewW m h = []
  · simp [hne] at hW
  simp only [hne, ↓reduceIte] at hW
  obtain ⟨v, hv, hVR⟩ := L.Ind.eViewW_ok m a hR h hne
  generalize L.Ind.eViewW m h = w at hW hVR
  have hpre : (headTypePW fe f.toNat (decE root) d.toNat (decE h) k.toNat).run a =
      (match v with
        | .const I us =>
          (match fe.find? I with
          | some ci => do
              let cv := ci.toConstantVal
              match ← viewLsLen us with
              | none => failDanglingLs
              | some usl =>
              if usl = cv.levelParams.length then do
                let res ← ConRon.Arena.peelPisW fe f.toNat k.toNat cv.type
                match ← ConRon.Arena.residualPW res with
                | some pw => substPWAt cv.levelParams us pw
                | none => pure none
              else pure none
          | none => pure none)
        | .fvar _ ty => htResT fe f.toNat k.toNat ty
        | .bvar i =>
          if i < d.toNat then do
            match ← binderDom (d.toNat - 1 - i) (decE root) with
            | some D => htResT fe f.toNat k.toNat D
            | none => pure none
          else pure none
        | _ => pure none).run a := by
    simp only [headTypePW, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
    rcases v <;> rfl
  rcases v with i | ⟨i, ty⟩ | u | ⟨I, us⟩ | ⟨g, x⟩ | ⟨ty, b⟩ | ⟨ty, b⟩ | ⟨ty, vv, b⟩ | l | ⟨sn, i, pe⟩
  -- bvar
  · obtain ⟨hg, hi⟩ := hVR
    simp only [vG, vX, hg, show (0 : Word) ≠ 3 by decide, show (0 : Word) ≠ 1 by decide,
      ↓reduceIte, true_and] at hW
    rw [pr_getD1] at hi
    by_cases hlt : w.tail.headD 0 < d
    · simp only [hlt, ↓reduceIte] at hW
      have hlt' : i < d.toNat := by rw [← hi]; exact UInt64.lt_iff_toNat_lt.mp hlt
      have hdi : (d - 1 - w.tail.headD 0).toNat = d.toNat - 1 - i := by
        have h1 : (d - 1).toNat = d.toNat - 1 := pr_word_sub1 d (by intro e; subst e; simp at hlt')
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h1]; omega), h1, hi]
      rcases hb : bdW m (d - 1 - w.tail.headD 0) root with _ | ⟨bf, bd⟩ <;> rw [hb] at hW
      · cases hW
      obtain ⟨hbrun, hbb⟩ := bdW_ok m a hR _ _ _ bf bd (Nat.le_refl _) hroot hb
      rw [hdi] at hbrun
      simp only [htpK] at hW
      by_cases hb0 : bf = 0
      · simp only [hb0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
        refine ⟨none, a, ?_, RdAfter.refl hS, rfl⟩
        rw [hpre]; simp only [hlt', ↓reduceIte, StateT.run_bind, hbrun, except_ok_bind, hb0,
          decOpt]; rfl
      simp only [hb0, ↓reduceIte] at hW
      rcases hc2 : callW p n "head_type_res" [vis, f, k, bd] m with _ | ⟨r₂, m₂⟩ <;> rw [hc2] at hW
      · cases hW
      simp only [t3W, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
      obtain ⟨res, hrun₂, hRd₂, hd₂⟩ := htr_call hp hden hS hf (hbb hb0) hc2
      refine ⟨res, a, ?_, hRd₂, hd₂⟩
      rw [hpre]; simp only [hlt', ↓reduceIte, StateT.run_bind, hbrun, except_ok_bind, decOpt, hb0]
      exact hrun₂
    · simp only [hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
      have hlt' : ¬ i < d.toNat := by
        rw [← hi]; exact fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      exact ⟨none, a, by rw [hpre]; simp only [hlt', ↓reduceIte]; rfl, RdAfter.refl hS, rfl⟩
  -- fvar
  · obtain ⟨hg, -, hty, hty'⟩ := hVR
    rw [pr_getD2] at hty hty'
    simp only [vG, vY, hg, show (1 : Word) ≠ 3 by decide, ↓reduceIte] at hW
    rcases hc2 : callW p n "head_type_res" [vis, f, k, w.tail.tail.headD 0] m with _ | ⟨r₂, m₂⟩ <;>
      rw [hc2] at hW
    · cases hW
    simp only [t3W, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    obtain ⟨res, hrun₂, hRd₂, hd₂⟩ := htr_call hp hden hS hf hty hc2
    refine ⟨res, a, ?_, hRd₂, hd₂⟩
    rw [hpre, ← hty']; exact hrun₂
  -- sort
  · obtain ⟨hg, -⟩ := hVR
    simp only [vG, hg, show (2 : Word) ≠ 3 by decide, show (2 : Word) ≠ 1 by decide,
      show (2 : Word) ≠ 0 by decide, false_and, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    exact ⟨none, a, by rw [hpre]; rfl, RdAfter.refl hS, rfl⟩
  -- const
  · obtain ⟨hg, hn, hn', husw, hus'⟩ := hVR
    rw [pr_getD1] at hn hn'
    rw [pr_getD2] at husw hus'
    simp only [vG, vX, vY, hg, ↓reduceIte] at hW
    rcases hc2 : callW p n "head_type_const" [vis, f, k, w.tail.headD 0, w.tail.tail.headD 0] m
      with _ | ⟨r₂, m₂⟩
    · rw [hc2] at hW; cases hW
    rw [hc2] at hW
    simp only [t3W, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    cases n with
    | zero => rw [callW_zero] at hc2; cases hc2
    | succ n =>
    obtain ⟨t₂, ht₂, -, hW₂⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (headTypeConst_spec p hp n ⟨m, Locals.init []⟩ vis f k _ _) hc2
    rw [ht₂] at hW₂
    have hls := (hden dn m a vis fe M eb hS).constLs _ _ _ hv
    rw [← hus'] at hls
    obtain ⟨res, a', hrun, hRd, hd⟩ := cArm_ok hp hden hlps
      (sub := fun ty m => callW p n "head_type_res" [vis, f, k, ty] m) (T := htResT fe f.toNat k.toNat)
      (fun hS₁ hty hc => by
        obtain ⟨res, h1, h2, h3⟩ := htr_call hp hden hS₁ hf hty hc
        exact ⟨res, _, h1, h2, h3⟩) hS hn husw hls hW₂
    refine ⟨res, a', ?_, hRd, hd⟩
    rw [headTypePW_const fe _ _ _ _ _ a I us hv, ← hn', ← hus']; exact hrun
  -- the other tags
  all_goals
    have hg : w.headD 0 ≠ 3 ∧ w.headD 0 ≠ 1 ∧ w.headD 0 ≠ 0 := by
      first
      | (rw [hVR.1]; decide)
      | (rw [hVR]; decide)
    simp only [vG, hg.1, hg.2.1, hg.2.2, false_and, ↓reduceIte, Option.some.injEq,
      Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    exact ⟨none, a, by rw [hpre]; rfl, RdAfter.refl hS, rfl⟩

/-- **`type_sort_pw` refines `typeSortPW`.** -/
@[refines ConRon.Arena.typeSortPW ConRon.Arena.typeSortPWGo]
theorem tsp_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {f rt : Word}
    (hf : f.toNat ≤ coreWalkFuel) (hrt : HW rt) {r : List Word}
    (hc : callW p n "type_sort_pw" [vis, f, rt] m = some (r, m')) :
    ∃ res a', (typeSortPW fe f.toNat (decE rt)).run a = .ok (res, a') ∧
      RdAfter dn m m' a a' vis fe M eb ∧
      PWD (nameN a.store.lss.ls.ns) m' (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) res := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (typeSortPW_spec p hp n ⟨m, Locals.init []⟩ vis f rt) hc
  rw [ht] at hW
  generalize r.headD 0 = x₀ at hW ⊢
  generalize r.tail.headD 0 = x₁ at hW ⊢
  generalize r.tail.tail.headD 0 = x₂ at hW ⊢
  have hR := hS.arena.1
  unfold tspW at hW
  rcases hL : tsLoopW m f rt 0 with _ | ⟨f', rr, d⟩ <;> rw [hL] at hW
  · cases hW
  simp only at hW
  have hcwf : coreWalkFuel < 2 ^ 64 := by simp [coreWalkFuel]
  obtain ⟨hrun, hrr, -, hn6⟩ := tsLoopW_ok m a hR fe (decE rt) _ f rt 0 f' rr d (Nat.le_refl _) hrt
    (by simp; omega) hL
  simp only [UInt64.toNat_zero] at hrun
  by_cases hf0 : f' = 0
  · simp [hf0] at hW
  simp only [hf0, ↓reduceIte] at hW
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (pr_word_ne0 f' hf0)
  have hfm := pr_word_sub1 f' hf0
  have hj' : j = (f' - 1).toNat := by omega
  have hnf : ((decE rr).tag == ETag.forallE) = false := by
    rw [tag_beq_w rr hrr 6 (by decide) ETag.forallE rfl 6 rfl]; simp [hn6]
  have hpre : (typeSortPW fe f.toNat (decE rt)).run a =
      (if (decE rr).tag == ETag.sort then pure (some .never) else do
        let fn ← getAppFn (f' - 1).toNat (decE rr)
        let n ← numArgs (f' - 1).toNat (decE rr)
        headTypePW fe (f' - 1).toNat (decE rt) d.toNat fn n : AM (Option PropWhen)).run a := by
    rw [typeSortPW, hrun, hj, typeSortPWGo, ← hj']
    simp only [hnf, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : rr >>> 28 = 2
  · simp only [h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    have hs : ((decE rr).tag == ETag.sort) = true := by
      rw [tag_beq_w rr hrr 2 (by decide) ETag.sort rfl 2 rfl]; simp [h2]
    exact ⟨some .never, a, by rw [hpre]; simp only [hs, ↓reduceIte]; rfl, RdAfter.refl hS, rfl⟩
  simp only [h2, ↓reduceIte] at hW
  have hs : ((decE rr).tag == ETag.sort) = false := by
    rw [tag_beq_w rr hrr 2 (by decide) ETag.sort rfl 2 rfl]; simp [h2]
  rcases hA : acaW m rr (f' - 1) with _ | ⟨cnt, fn⟩ <;> rw [hA] at hW
  · cases hW
  simp only at hW
  obtain ⟨hgaf, hna, hfn, -⟩ := acaW_ok hR hrr hA
  rcases hc2 : callW p n "head_type_pw" [vis, f' - 1, rt, d, fn, cnt] m with _ | ⟨r₂, m₂⟩ <;>
    rw [hc2] at hW
  · cases hW
  simp only [t3W, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
  have hf' : (f' - 1).toNat ≤ coreWalkFuel := by
    obtain ⟨-, -, hsum, -⟩ := tsLoopW_ok m a hR fe (decE rt) _ f rt 0 f' rr d (Nat.le_refl _) hrt
      (by simp; omega) hL
    simp only [UInt64.toNat_zero] at hsum
    omega
  obtain ⟨res, a', hrun₂, hRd₂, hd₂⟩ := htp_call hp hden hlps hS hf' hrt hfn hc2
  refine ⟨res, a', ?_, hRd₂, hd₂⟩
  rw [hpre]
  simp only [hs, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, hgaf, except_ok_bind, hna]
  exact hrun₂

end htp

end L.Arena
